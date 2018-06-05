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
  (define types (foldl extract-data #hash() prog))
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
    [`(,pats ... → ,body) `(c: ,env ,body ,@pats)]
    [`(λ ,cases ...) `(c-fall: ,env ,@cases)]

    ; fallthrough case
    [`(,(app I `(c-fall: ,c-env ,cases ...)) ,(app I a-vals) ...)
     (foldl (λ (a-case acc)
              (match acc
                ['no-match (interpret types c-env `(,a-case ,@a-vals))]
                [result result]))
            'no-match
            cases)]

    ; application: notice how pattern-match handles lists
    ; of arguments the same as it does constructors
    [`(,(app I `(c: ,c-env ,body ,pats ...)) ,(app I args) ...)
     (match (pattern-match types c-env args pats)
           ['no-match 'no-match]
           [new-env (interpret types new-env body)])]))


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
    [(? list?)
       (foldl (λ (arg pat env)
                (pattern-match types env arg pat))
              c-env
              arg
              pat)]))


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

  (test-equal? "and"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define and
                        (λ #;(Bool Bool → Bool)
                          (true true → true)
                          (false true → false)
                          (true false → false)
                          (false false → false)))
                      (just (and true false))))
               '(just false))

  (test-equal? "const-left"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define-data List
                        null
                        (cons Bool List))
                      (define right-proj
                        (λ #;(Bool Bool → Bool)
                          (a true → true)
                          (a b → (cons b a))))
                      (right-proj true false)))
               '(cons false true))

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
