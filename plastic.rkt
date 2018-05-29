#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(define (run-interpreter prog)
  #;(define original-data
      '((define-data Maybe-Bool
            nothing
            (just Bool))
        (define-data Nat
            zero
            (S Nat))
        (define-data List-Bool
            null
            (cons Bool List))))
  #;(define nullary-type-lookup
      #hash((true . Bool)
            (false . Bool)
            (nothing . Maybe-Bool)
            (zero . Nat)
            (null . List-Bool)))
  #;(define n-ary-type-lookup
      #hash(((just Bool) . Maybe-Bool)
            ((S Nat) . Nat)
            ((Cons Bool List-Bool) . List-Bool)))
  #;(define type-lookup-hash nullary-type-lookup)
  #;#;(println "prog:")(println prog)
  (define types (extract-all-data (hash) prog))
  #;#;(println "types:")(println types)
  #;(define types '(cons S true null))
  (define I*
    (compose (curry interpret types #hash())
             explicitize
             expand-top))
  (I* prog))


(define (expand-top stx)
  (define Ex expand-top)
  (match stx
    ; also eliminate data?
    [`((define-data ,xs ...) ,ys ...)
     (Ex ys)]
    [`((define ,id ,init) ,expr)
     `((,id → ,(Ex expr)) ,(Ex init))]
    [`((define ,id ,init) ,xs ...)
     `((,id → ,(Ex xs)) ,(Ex init))]
    [_ stx]))


(define (extract-all-data types stx)
  (foldl extract-data types stx))

(define (extract-data stx types)
  (match stx
    [`(define-data ,type ,cs ...) ; below hack for n-ary constructors
     (foldl (λ (c env) (hash-set env (if (list? c) (first c) c) type)) types cs)]
    [a types]))

; make certain forms explicit
(define (explicitize stx)
  (define Ex explicitize)
  (define Px pattern-explicitize)
  (match stx
    ['null `(dat null)]
    ['true `(dat true)]
    [(? symbol?) `(var ,stx)]
    [(? number?) `(dat ,stx)]
    [`(,pat → ,expr)
     `(,(Px pat) → ,(Ex expr))]
    [`(λ ,cases ...)
     `(λ ,@(map Ex cases))]
    [`(cons ,a ,b) `(cons ,(Ex a) ,(Ex b))]
    ; turn lists into cons or leave seperate?
    [`(,f ,x) `(app ,(Ex f) ,(Ex x))]
    [_ stx]))

(define (pattern-explicitize stx)
  (define Px pattern-explicitize)
  (match stx
    ['null `(p-dat null)]
    ['true `(p-dat true)]
    [(? symbol?) `(p-var ,stx)]
    [(? number?) `(p-dat ,stx)] ; or use P==
    [`(cons ,a ,b) `(cons ,(Px a) ,(Px b))]
    [_ stx]))


(define (type-check t-env prog)
  (define T (curry type-check t-env))
  (match prog
    [`(var ,x) (hash-ref t-env x)]
    [`(dat ,(or (? number? d) (? (curry hash-ref t-env) d))) d] ;fix
    [`(λ (,p-type → ,r-type) (,pats → ,tems) ...)
     ; check if p-type, r-type valid types
     (map (λ (pat tem)
            (match* ((T pat) (T tem)) ; might need to have sep fn for pat
              [((== p-type) (== r-type))
               'yes]
              [(_ _) 'no])
            ) pats tems)] ; prob should fold
    #;[stx stx]))

(define (interpret types env prog)
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define I (curry interpret types env))
  #;(println prog)
  (match prog
    [`(var ,x) (hash-ref env x)] ;fix
    [`(dat ,d) d]
    ; should above case handle nullary constructors?
    [(? constructor-id? id) id] ;hack!!!!
    
    #;[`(cons ,a ,b) `(cons ,(I a) ,(I b))]
    ; adapt above to constructor case:
    [`(,(? constructor-id? id) ,a ,b)
     `(,id ,(I a) ,(I b))]
    [`((p-var ,id) → ,body) `(c: ,id ,body ,env)] ;simple lc
    [`(,pat → ,body) `(c-new: ,pat ,body ,env)] ;other patterns
    [`(λ ,cases ...) `(c-fall: ,env ,@cases)] ;fallthru form
    [`(c-fall: ,blah ...) prog] ; hack
    ; above: need to fix fallthough code below rewriting to c-fall:

    [`(app ,(app I `(c: ,id ,body ,c-env)) ,(app I a-val))
     (interpret types (hash-set c-env id a-val) body)]
    [`(app ,(app I `(c-new: ,pat ,body ,c-env)) ,(app I a-val))
     (match (pattern-match a-val c-env pat)
       ['no-match 'no-match]
       [new-env (interpret types new-env body)])]
    [`(app ,(app I `(c-fall: ,c-env ,case1 ,cases ...)) ,(app I a-val))
     (match (interpret types c-env `(app ,case1 ,a-val))
       ['no-match (I `(app (c-fall: ,c-env ,@cases) ,a-val))]
       [result result])]))


(require racket/hash)
(define (pattern-match arg c-env pat) ; returns env
  (define (constructor-id? id)
    (member id '(cons S)))
  (match pat
    [`(p-var ,id) (hash-set c-env id arg)]
    [`(p-dat ,d) 
     (if (equal? d arg) ;polymorphic equality extended by define-data?
         c-env
         'no-match)]
    ['true 'true] ; hack
    [`(,(? constructor-id? id) ,p0)
     (match arg
       [`(,(== id) ,a0)
        (pattern-match a0 c-env p0)]
       [_ 'no-match])]
    [`(,(? constructor-id? id) ,p0 ,p1)
     (match arg
       [`(,(== id) ,a0 ,a1)
        (match* ((pattern-match a0 c-env p0)
                 (pattern-match a1 c-env p1))
          [('no-match _) 'no-match]
          [(_ 'no-match) 'no-match]
          [(e0 e1) (hash-union e0 e1)])]
       [_ 'no-match])]
    #;[`(,(? constructor-id? id) ,p-args ...)
       (println "bzzz")
       (define (tt env p-arg a-arg)
         (match (pattern-match a-arg c-env p-arg)
           ['no-match 'no-match]
           [new-env (hash-union env new-env)]))
       (match arg
         [`(,(== id) ,a-args ...)
          (foldr tt (hash) p-args a-args)]
         [_ 'no-match])]
    
    #;[`(cons ,p0 ,p1) ; in this case, maybe be many things to add
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

  (test-equal? "defines -> local lambda app"
               ((compose explicitize expand-top) '((define x 1) x))
               #;'((x → x) 1)
               '(app ((p-var x) → (var x)) (dat 1)))
  
  (test-equal? "multi define"
               ((compose explicitize expand-top) '((define x 1) (define y 2) y))
               #;'((x → ((y → y) 2)) 1)
               '(app ((p-var x) → (app ((p-var y) → (var y)) (dat 2))) (dat 1)))
  
  (test-equal? "multi define 2"
               ((compose explicitize expand-top) '((define x 1) (define y 2) x))
               '(app ((p-var x) → (app ((p-var y) → (var x)) (dat 2))) (dat 1)))
  
  (test-equal? "define scope"
               ((compose explicitize expand-top) '((define x 1) (define y x) y))
               #;'((x → ((y → y) x)) 1)
               '(app ((p-var x) → (app ((p-var y) → (var y)) (var x))) (dat 1)))

  (test-equal? "Numeric literal" (run-interpreter '((define q 1) 3)) 3)

  #;(test-equal? "addition"
                 (run-interpreter '((define q 1) (+ 1 2 (+ (+ 3) 4 5) 6)))
                 21)


  (test-equal? "cons 0"
               (run-interpreter '((define-data Bool
                                    true
                                    false)
                                  (define-data List
                                    null
                                    (cons Bool List))
                                  (define a true)
                                  (cons true true)))
               '(cons true true))
  
  (test-equal? "basic cons"
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

  (test-equal? "flip cons"
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
