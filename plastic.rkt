#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(require racket/hash)

#| plastic!

Plastic is the lambda calculus with pattern-matching and ADTs.

Metaphor (metonym) : Plastic -> Lego -> ADTs

It has no built-in data types; any type you want must be
declared with its define-data form. A define-data form with
only nullary constructors is essentially an enum, and one
with only a single n-ary constructor is essentially a struct.

|#

#; (grammar:
    (prog ((define-data type-id
             constructor-dec
             ...)
           ...
           (define id expr)
           ...
           expr))
    (expr (constructor-instance
           id
           (λ #;type
             (pattern → expr)
             ...)
           (expr expr)
           ))
    (pattern (0-ary-cons-id
              (n-ary-cons-id pattern ...))
             id)
    (constructor-dec (0-ary-cons-id
                      (n-ary-cons-id type-id ...)))
    (constructor-instance (0-ary-cons-id
                           (n-ary-cons-id expr ...)))
    )

#|

Current design factors out all static checking.
(including arity of constructors)
This could be added as a seperate layer

|#

(define (run prog)
  (define types (foldl extract-data (hash) prog))
  #;(println types)
  ((compose (curry interpret types #hash())
            expand-top)
   prog))

(define (expand-top stx)
  (define Ex expand-top)
  (match stx
    ; eliminate data form (which was already extracted)
    [`((define-data ,xs ...) ,ys ...)
     (Ex ys)]
    ; rewrite defines into lambdas
    [`((define ,id ,init) ,expr)
     `((,id → ,(Ex expr)) ,(Ex init))]
    [`((define ,id ,init) ,xs ...)
     `((,id → ,(Ex xs)) ,(Ex init))]
    [_ stx]))


(define (extract-data stx types)
  (match stx
    [`(define-data ,type ,cs ...)
     (foldl (λ (c env)
              (match c
                [`(,x ,xs ...) (hash-set env x `(,@xs → ,type))]
                ; gADT-style fn type sigs for non-nullary constructors
                [_ (hash-set env c type)]))
            types cs)]
    [_ types]))

#;(define (foldM f acc ls)
    (match ls
      ['() acc]
      [`(,x ,xs ...)
       (match (f x acc)
         ['no-match (foldM f 'no-match xs)]
         [res res])]))


(define (interpret types env prog)
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define I (curry interpret types env))
  #;(println prog)
  (match prog
    [(? constructor-id? id) id]
    ; added not clause to make following case less order-dependent
    [`(,(? constructor-id? id) ,(and xs (not (== '→))) ...)
     `(,id ,@(map I xs))]
    [(? symbol? id) (hash-ref env id)]
    
    ; λ here means 'fallthrough' and (_ → _) is actually a lambda
    [`(,pat → ,body) `(c: ,pat ,body ,env)]
    [`(λ ,cases ...) `(c-fall: ,env ,@cases)]

    ; fallthrough case
    [`(,(app I `(c-fall: ,c-env ,cases ...)) ,(app I a-val))
     (define (f a-case acc)
       (match acc
         ['no-match (interpret types c-env `(,a-case ,a-val))]
         [result result]))
     (foldl f 'no-match cases)]

    ; actual application case
    [`(,(app I `(c: ,pat ,body ,c-env)) ,(app I a-val))
     (match (pattern-match types c-env a-val pat)
       ['no-match 'no-match]
       [new-env (interpret types new-env body)])]
    ))



(define (pattern-match types c-env arg pat) ; returns env
  (define Pm (curry pattern-match types c-env))
  (define (constructor-id? id)
    (hash-has-key? types id))
  (match pat
    ; nullary datum case:
    [(? constructor-id? d)
     (match arg
       [(== d) c-env]
       [_ 'no-match])]
    ; var case:
    [(? symbol? id)
     (hash-set c-env id arg)]
    ; constructor case:
    [`(,(? constructor-id? id) ,p-args ...)
     (define (f p-arg a-arg env)
       (match (Pm a-arg p-arg)
         ['no-match 'no-match]
         [new-env (hash-union env new-env)]))
     (match arg
       [`(,(== id) ,a-args ...)
        (foldl f (hash) p-args a-args)] ; changed from foldr; test
       [_ 'no-match])]
    ))


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
               '((x → ((y → x) false)) true))
  
  (test-equal? "two defines scope"
               (expand-top '((define-data Void void)
                             (define x void)
                             (define y x)
                             y))
               '((x → ((y → y) x)) void))

  (test-equal? "only literal"
               (run '((define-data Bool
                        true
                        false)
                      (define q true)
                      false))
               'false)

  (test-equal? "simple closure"
               (run '((define-data Bool
                        true
                        false)
                      (define q true)
                      ((x → x) true)))
               'true)

  (test-equal? "cons with var"
               (run '((define-data Bool
                        true
                        false)
                      (define-data List
                        null
                        (cons Bool List))
                      (define a true)
                      (cons true a)))
               '(cons true true))
  
  (test-equal? "cons identity"
               (run '((define-data Bool
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
               (run '((define-data Bool
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
  
  
  (test-equal? "identity 2"
               (run '((define-data Bool
                        true
                        false)
                      (define identity2
                        (λ #;(Bool → Bool)
                          (a → a)))
                      (identity2 true)))
               'true)

  (test-equal? "maybe"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define identity
                        (λ #;(Bool → Bool)
                          (true → true)
                          (false → false)))
                      (just (identity true))))
               '(just true))

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




  )
