#lang pl 03

#|

BNF for the PUWAE language:
     <PUWAE> ::= <num>
             | { + <PUWAE> <PUWAE> }
             | { - <PUWAE> <PUWAE> }
             | { * <PUWAE> <PUWAE> }
             | { / <PUWAE> <PUWAE> }
             | { with { <id> <PUWAE> } <PUWAE> }
             | <id>
             | { post <POST> ... }

     <POST> ::= <PUWAE>
             | +
             | -
             | *
             | /

|#

(define-type PostfixItem = (U PUWAE '+ '- '* '/))

;; PUWAE abstract syntax trees
(define-type PUWAE
  [Num  Number]
  [Add  PUWAE PUWAE]
  [Sub  PUWAE PUWAE]
  [Mul  PUWAE PUWAE]
  [Div  PUWAE PUWAE]
  [Id   Symbol]
  [With Symbol PUWAE PUWAE]
  [Post (Listof PostfixItem)])


(: parse-post-item : Sexpr -> PostfixItem)
;; parse an s-expression to a post-item
(define (parse-post-item x)
  (match x ['+ '+] ['- '-] ['* '*] ['/ '/]
    [else (parse-sexpr x)]))


(: parse-sexpr : Sexpr -> PUWAE)
;; parses s-expressions into PUWAEs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'post more) (Post (map parse-post-item more))]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))


(: parse : String -> PUWAE)
;; parses a string containing a PUWAE expression to a PUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "5") => (Num 5))
(test (parse "{post 1 2 3}") => (Post (list (Num 1) (Num 2) (Num 3))))
(test (parse "{* {post 1 2 +} {post 3 4 +}}") =>
      (Mul (Post (list (Num 1) (Num 2) '+)) (Post (list (Num 3) (Num 4) '+))))
(test (parse "{with {x {post 3 4 +}} {post 1 2 + x *}}") =>
     (With 'x (Post (list (Num 3) (Num 4)'+))
           (Post (list (Num 1) (Num 2) '+ (Id 'x) '*))))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <WAE>s, `x' is some <id>,
   `y' is a *different* <id>)
      N[v/x]                = N
      {+ E1 E2}[v/x]        = {+ E1[v/x] E2[v/x]}
      {- E1 E2}[v/x]        = {- E1[v/x] E2[v/x]}
      {* E1 E2}[v/x]        = {* E1[v/x] E2[v/x]}
      {/ E1 E2}[v/x]        = {/ E1[v/x] E2[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
|#

(: subst : PUWAE Symbol PUWAE -> PUWAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (: post-subst : PostfixItem -> PostfixItem)
  (define (post-subst item)
    (if (symbol? item)
        (if (eq? item from) to item)
        (subst item from to)))
  (cases expr
    [(Num n) expr]
    [(Add l r) (Add (subst l from to) (subst r from to))]
    [(Sub l r) (Sub (subst l from to) (subst r from to))]
    [(Mul l r) (Mul (subst l from to) (subst r from to))]
    [(Div l r) (Div (subst l from to) (subst r from to))]
    [(Id name) (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst named-expr from to)
           (if (eq? bound-id from)
             bound-body
             (subst bound-body from to)))]
    [(Post items) (Post (map post-subst items))]))

;(test (subst (Post '+ (Num 1)) 'x (Num 3)) => (Post '+ (Num 1)))
(test (subst (Add (Id 'x) (Num 5)) 'x (Num 3)) => (Add (Num 3) (Num 5)))
(test (subst (Post (list (Id 'x) (Num 5))) 'x (Num 3)) =>
      (Post (list (Num 3) (Num 5))))
(test (subst (Post (list '+ '- '* '/)) '+ (Num 3)) =>
      (Post (list (Num 3) '- '* '/)))
;(test (subst (Post (list '+ '-)) '+ '-) =>
;      (Post (list '- '- )))

#| Formal specs for `eval':
     eval(N)         = N
     eval({+ E1 E2}) = eval(E1) + eval(E2)
     eval({- E1 E2}) = eval(E1) - eval(E2)
     eval({* E1 E2}) = eval(E1) * eval(E2)
     eval({/ E1 E2}) = eval(E1) / eval(E2)
     eval(id)        = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
|#

#|

(: post-eval : (Listof PostfixItem) (Listof Number) -> Number)
;; evaluates a postfix sequence of items, using a stack
(define (post-eval items stack)
  (if (null? items)
    (match stack
     ; [(list: l) (error 'post-eval "leftover values ~s" l)]
     ; [else 0])
      )
    (let ([1st  (first items)]
          [more (rest items)])
      (: pop2-and-apply : (Number Number -> Number) -> Number)
      (define (pop2-and-apply func)
        (match stack fill-in))
      (cond [(eq? '+ 1st) (pop2-and-apply fill-in)]
            [(eq? '- 1st) (pop2-and-apply fill-in)]
            [(eq? '* 1st) (pop2-and-apply fill-in)]
            [(eq? '/ 1st) (pop2-and-apply fill-in)]
            [else (post-eval fill-in)]))))


(test (post-eval (list (Num 10) (Num 2) '* (Add (Num 3) (Num 2)) '/) (list))
  -> 4)
|#

(: eval : PUWAE -> Number)
;; evaluates PUWAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Add l r) (+ (eval l) (eval r))]
    [(Sub l r) (- (eval l) (eval r))]
    [(Mul l r) (* (eval l) (eval r))]
    [(Div l r) (/ (eval l) (eval r))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  (Num (eval named-expr))))]
    [(Id name) (error 'eval "free identifier: ~s" name)]
    ;[(Post items) ]
    ;; delete this else
    [else -1]))

(: run : String -> Number)
;; evaluate a PUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;(test (run "{post 3 1 -}") => 2)

;; tests
(test (run "5") => 5)
(test (run "{+ 5 5}") => 10)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x 5} {* x x}}") => 25)
(test (run "{with {x 5} {/ x x}}") => 1)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
(test (run "{with {x 1} y}") =error> "free identifier")
(test (run "{with {x 5} {! x}}") =error> "bad syntax in (! x)")
(test (run "{with {x 5 6} x}") =error> "bad `with' syntax in (with (x 5 6) x")
(test (run "{with {x} x}") =error> "bad `with' syntax in (with (x) x")