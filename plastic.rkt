#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(define (run-interpreter prog)
  (define types (foldl extract-data (hash) prog))
  (define I*
    (compose (curry interpret types #hash())
             expand-top))
  (I* prog))


(define (expand-top stx)
  (define Ex expand-top)
  (match stx
    ; eliminate data form (which was already extracted)
    [`((define-data ,xs ...) ,ys ...)
     (Ex ys)]
    [`((define ,id ,init) ,expr)
     `((,id → ,(Ex expr)) ,(Ex init))]
    [`((define ,id ,init) ,xs ...)
     `((,id → ,(Ex xs)) ,(Ex init))]
    [_ stx]))


(define (extract-data stx types)
  (match stx
    [`(define-data ,type ,cs ...) ; below hack for n-ary constructors
     (foldl (λ (c env) (hash-set env (if (list? c) (first c) c) type)) types cs)]
    [a types]))


(define (interpret types env prog)
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define I (curry interpret types env))
  (println prog)
  (match prog
    [(? constructor-id? id) id]
    [(? symbol? id) (hash-ref env id)]
    [(? number? d) d]

    [`(,(and (? symbol? id) (not (? constructor-id?))) → ,body) `(c: ,id ,body ,env)] ;simple lc
    [`(,pat → ,body) `(c-new: ,pat ,body ,env)] ;other patterns
    [`(,(? constructor-id? id) ,xs ...)
     `(,id ,@(map I xs))] ; this case is dangerously order-dep (can capture →)

    [`(λ ,cases ...) `(c-fall: ,env ,@cases)] ;fallthru form
    [`(c-fall: ,blah ...) prog] ; hack
    ; above: need to fix fallthough code below rewriting to c-fall:

    [`(,(app I `(c: ,id ,body ,c-env)) ,(app I a-val))
     (interpret types (hash-set c-env id a-val) body)]
    [`(,(app I `(c-new: ,pat ,body ,c-env)) ,(app I a-val))
     (match (pattern-match types a-val c-env pat)
       ['no-match 'no-match]
       [new-env (interpret types new-env body)])]
    [`(,(app I `(c-fall: ,c-env ,case1 ,cases ...)) ,(app I a-val))
     (match (interpret types c-env `(,case1 ,a-val))
       ['no-match (I `((c-fall: ,c-env ,@cases) ,a-val))]
       [result result])]))


(require racket/hash)
(define (pattern-match types arg c-env pat) ; returns env
  (define (constructor-id? id)
    (hash-has-key? types id))
  (match pat
    [(? constructor-id? d)
     (if (equal? d arg) ;polymorphic equality extended by define-data?
         c-env
         'no-match)]
    [(? symbol? id) (hash-set c-env id arg)]
    [`(,(? constructor-id? id) ,p-args ...)
     (define (cons-help p-arg a-arg env)
       (match (pattern-match types a-arg c-env p-arg)
         ['no-match 'no-match]
         [new-env (hash-union env new-env)]))
     (match arg
       [`(,(== id) ,a-args ...)
        (foldr cons-help (hash) p-args a-args)]
       [_ 'no-match])]
    #;[`(cons ,p0 ,p1)
       (match arg
         [`(cons ,a0 ,a1) ;rewrite to not use pattern-matching lol
          (match* ((pattern-match a0 c-env p0)
                   (pattern-match a1 c-env p1))
            [('no-match _) 'no-match]
            [(_ 'no-match) 'no-match]
            [(e0 e1) (hash-union e0 e1)])]
         [_ 'no-match])]
    ))

#|

need no-match symbol to handle failure to match

matching attempt 1: expand pattern to lc at compile-time
`(((p-dat d) → expr) whatever)
becomes
(if (== d (eval expr)
     void
     no-match)
p== is same except 'd' gets evald too
`(((p-var d) → expr) target)
is regular evaluation
p? straightforward
as is p-app
`(((p-cons a b) → expr) whatever)
becomes
(if (eval expr) list
(let f (first ee
(let s (second ee

actually: if we know the expr is a cons
`(((p-cons a b) → expr) (cons x y))
`((λ (a) (λ (b) expr) y) x) dummy)
 
(eval `((λ (a) ) whatever)

|#

(module+ test
  (require rackunit)

  (test-equal? "define"
               (expand-top '((define-data Void void)
                             (define x void)
                             x))
               '((x → x) void))
  
  (test-equal? "two defines"
               (expand-top '((define-data Bool
                               true
                               false)
                             (define x true)
                             (define y false)
                             y))
               '((x → ((y → y) false)) true))
  
  (test-equal? "two defines 2"
               (expand-top '((define-data Bool
                               true
                               false)
                             (define x true)
                             (define y false)
                             x))
               '((x → ( (y → x) false)) true))
  
  (test-equal? "two defines scope"
               (expand-top '((define-data Void void)
                             (define x void)
                             (define y x) y))
               '((x → ((y → y) x)) void))

  (test-equal? "just literal"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define q true)
                                  false))
               'false)


  (test-equal? "cons with var"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define-data List
                                    null
                                    (cons Bool List))
                                  (define a true)
                                  (cons true a)))
               '(cons true true))
  
  (test-equal? "cons identity"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define-data List
                                    null
                                    (cons Bool List))
                                  (define identity
                                    (λ #;(List → List)
                                      (null → null)
                                      ((cons a b) → (cons a b))))
                                  (identity (cons true true))))
               '(cons true true))

  (test-equal? "cons flip"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define-data List
                                    null
                                    (cons Bool List))
                                  (define flip
                                    (λ #;(List → List)
                                      (null → null)
                                      ((cons a b) → (cons b a))))
                                  (flip (cons true null))))
               '(cons null true))
  
  #;
  (test-equal? "enumerative type"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define identity
                                    (λ (Bool → Bool)
                                      (true → true)
                                      (false → false)))
                                  (define identity2
                                    (λ (Bool → Bool)
                                      (a → a)))
                                  (identity true)))
               'true)

  #;
  (test-equal? "maybe"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define-data Maybe-Bool
                                    Nothing
                                    (Just Bool))

                                  (define identity
                                    (λ (Bool → Bool)
                                      (true → true)
                                      (false → false)))
                                  
                                  (identity true)))
               'true)

  #;
  (test-equal? "recursive datatype"
               (run-interpreter '((define-data Nat
                                    zero
                                    (S Nat))
                                  (define-data Maybe-Nat
                                    nothing
                                    (just Nat))
                                  ; idea: pred xcept with maybe to handle 0
                                  (define pred
                                    (λ (Nat → Maybe-Nat)
                                      ((S a) → (just a))
                                      (zero → nothing)))
                                  #;(define add
                                      (λ (Nat → (Nat → Nat))
                                        (a → (λ (Nat → Nat) ; or make nested fns not require type ann?
                                               (zero → a) 
                                               ((S b) → (S ((add a) b))))))) ; xcept no recursion...
                                  ; re above: maybe need explicit fun to differentiate from application
                                  (add (S zero) (S (S zero)))))
               0)

  #;
  (test-equal? "nullary partial application"
               (run-interpreter '((define f (λ (x) 9))
                                  ((f) 9)))
               9)

  #;
  (test-equal? "0-ary"
               (run-interpreter '((define f (λ () 7))
                                  (f)))
               7)

  (test-equal? "simplest closure"
               (run-interpreter '((define q 1) ((x → x) 1)))
               1)

  #;
  (test-equal? "multivariate application"
               (run-interpreter '((define q 1) ((λ (x y) 1) 2 3)))
               1)

  #;
  (test-equal? "multivariate curried"
               (run-interpreter '((define q 1) (((λ (x y) (+ x y)) 7) 5)))
               12)

  #;
  (test-equal? "intermediate fn"
               (run-interpreter '((define f ((λ (x y) (+ x y)) 7))
                                  (f 5)))
               12)

  #;
  (test-equal? "rube goldberg"
               (run-interpreter '((define f ((λ (x y) (+ x y)) 7))
                                  (define g ((λ (x y z) (+ (f 2) (+ x z))) 6))
                                  (define h (g 4))
                                  (f (h 1))))
               23)

  #;
  (test-equal? "ignore errors within uncalled lambdas?"
               (run-interpreter '((define f (λ () (bad blood))) 0))
               0)

  #;
  (test-exn "non-numeric return"
            (to-regexp ERROR-wot)
            (lambda () (run-interpreter '((define q 1)(λ (x) x)))))

  #;
  (test-exn "duplicate names"
            (to-regexp ERROR-dup)
            ; Note that the `run-interpreter` call is wrapped in a function to
            ; *delay evaluation*. More on that in class!
            (lambda () (run-interpreter '((define f 0)
                                          (define g 1)
                                          (define f 2)
                                          (f (h 1))))))

  #;
  (test-exn "nullary application on unary fn"
            (to-regexp ERROR-wot)
            (lambda () (run-interpreter '((define f (λ (x) 0))
                                          (f)))))


  #;
  (test-exn "nullary function too many args"
            (to-regexp ERROR-tma)
            (lambda () (run-interpreter '((define f (λ () 0))
                                          (f 1)))))
  #;
  (test-exn "too many args"
            (to-regexp ERROR-tma)
            ; Note that the `run-interpreter` call is wrapped in a function to
            ; *delay evaluation*. More on that in class!
            (lambda () (run-interpreter '((define f (λ (x y z) (+ x y z)))
                                          (f 1 2 3 4)))))

  #;
  (test-exn "call add on function"
            (to-regexp ERROR-pte)
            (lambda () (run-interpreter '((define q 1)(+ 1 (λ (x) x))))))

  ; This test illustrates how to check that an appropriate exception is raised.
  #; (test-exn "Simple undefined identifier test"
               (to-regexp ERROR-uid)
               (lambda () (run-interpreter '((define q 1) a))))


  #;
  (test-equal? "..."
               (run-interpreter '((x → x) 1))
               1)

  #;
  (test-equal? "..."
               (run-interpreter '((x → x) 1))
               1)

  


  )
