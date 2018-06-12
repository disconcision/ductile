#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(require racket/hash)
(require "plastic-exhaust-typed.rkt")
#| plastic!

Plastic is the lambda calculus with pattern-matching and ADTs.

Metaphor (metonym) : Plastic -> Lego -> ADTs

It has no built-in data types; any type you want must be
declared with its data form. A data form with
only nullary constructors is essentially an enum, and one
with only a single n-ary constructor is essentially a struct.

|#

#; (grammar:
    (prog ((data type-id
                 constructor-dec
                 ...)
           ...
           (define id expr-or-lambda)
           ...
           expr))
    (expr (0-ary-cons-id
           (n-ary-cons-id expr ...)
           id
           (expr expr)))
    (lambda ((λ type
               (pattern → expr)
               ...)))
    (expr-or-lambda (expr
                     lambda))
    (pattern (0-ary-cons-id
              (n-ary-cons-id pattern ...)
              id))
    (constructor-dec (0-ary-cons-id
                      (n-ary-cons-id type-id ...))))

#|

Current design factors out all static checking.
(including arity of constructors)
This could be added as a seperate layer

|#

(define (run prog)
  (define types (foldl extract-data #hash() prog))
  (static-check types prog) ; make sure the data-defines dont screw this up
  (define env-defs (foldl (run-defs types) #hash() prog))
  (interpret types env-defs (last prog)))

(define ((run-defs types) stx env)
  (match stx
    [`(data ,_ ...) env]
    [`(define ,id ,init)
     (hash-set env id (interpret types env init))]
    [_ env]))


#| returns a hash containing the type data extracted
   from the data forms |#
(define (extract-data stx types)
  (match stx
    [`(data ,type ,cs ...)
     (foldl (λ (c env)
              (match c
                [`(,x ,xs ...) (hash-set env x `(,@xs → ,type))]
                ; gADT-style fn type sigs for non-nullary constructors
                [_ (hash-set env c `(→ ,type))]))
            types cs)]
    [_ types]))


(define (interpret types env prog)
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define I (curry interpret types env))
  (match prog
    [(? constructor-id? id) id]
    ; added not clause to make following case less order-dependent
    [`(,(? constructor-id? id) ,(and xs (not (== '→))) ...)
     `(,id ,@(map I xs))]
    [(? symbol? id) (hash-ref env id)]
    
    ; λ here means 'fallthrough' and (_ → _) is actually a lambda
    [`(,pats ... → ,body) `(c: ,env ,body ,@pats)]
    [`(λ ,type ,cases ...) `(c-fall: ,env ,@cases)]

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


#| matches arg to pat and returns a hash of bound variables.
   probably should specify that pattern-matching shouldn't be
   used in this implementation, but actually using pattern
   matching doesn't really let you gloss over any of the logic.|#
(define (pattern-match types c-env arg pat)
  (define constructor-id?
    (curry hash-has-key? types))
  (cond [(and (constructor-id? pat)
              (equal? arg pat))
         c-env]
        [(and (not (constructor-id? pat))
              (symbol? pat))
         (hash-set c-env pat arg)]
        [(list? pat)
         (foldl (λ (arg pat env)
                  (if (equal? env 'no-match)
                      'no-match
                      (pattern-match types env arg pat)))
                c-env
                arg
                pat)]
        [else 'no-match]))


(module+ test
  (require rackunit)

  #;(test-equal? "define"
                 (expand-top '((data Void void)
                               (define x void)
                               x))
                 '((x → x) void))
  
  #;(test-equal? "two defines"
                 (expand-top '((data Bool
                                     true
                                     false)
                               (define x true)
                               (define y false)
                               y))
                 '((x → ((y → y) false)) true))
  
  #;(test-equal? "two defines 2"
                 (expand-top '((data Bool
                                     true
                                     false)
                               (define x true)
                               (define y false)
                               x))
                 '((x → ((y → x) false)) true))
  
  #;(test-equal? "two defines scope"
                 (expand-top '((data Void void)
                               (define x void)
                               (define y x)
                               y))
                 '((x → ((y → y) x)) void))

  (test-equal? "only literal"
               (run '((data Bool
                            true
                            false)
                      (define q true)
                      false))
               'false)

  (test-equal? "simple closure"
               (run '((data Bool
                            true
                            false)
                      (define q true)
                      ((x → x) true)))
               'true)

  (test-equal? "cons with var"
               (run '((data Bool
                            true
                            false)
                      (data List
                            null
                            (cons Bool List))
                      (define a true)
                      (cons true a)))
               '(cons true true))
  
  (test-equal? "cons identity"
               (run '((data Bool
                            true
                            false)
                      (data List
                            null
                            (cons Bool List))
                      (define identity
                        (λ (List → List)
                          (null → null)
                          ((cons a b) → (cons a b))))
                      (identity (cons true true))))
               '(cons true true))

  (test-equal? "cons flip"
               (run '((data Bool
                            true
                            false)
                      (data List
                            null
                            (cons Bool List))
                      (define flip
                        (λ (List → List)
                          (null → null)
                          ((cons a b) → (cons b a))))
                      (flip (cons true null))))
               '(cons null true))
  
  
  (test-equal? "identity 2"
               (run '((data Bool
                            true
                            false)
                      (define identity2
                        (λ (Bool → Bool)
                          (a → a)))
                      (identity2 true)))
               'true)

  (test-equal? "maybe"
               (run '((data Bool
                            true
                            false)
                      (data Maybe-Bool
                            Nothing
                            (just Bool))
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (false → false)))
                      (just (identity true))))
               '(just true))

  (test-equal? "and"
               (run '((data Bool
                            true
                            false)
                      (data Maybe-Bool
                            Nothing
                            (just Bool))
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (false true → false)
                          (true false → false)
                          (false false → false)))
                      (just (and true false))))
               '(just false))

  (test-equal? "const-left"
               (run '((data Bool
                            true
                            false)
                      (data Maybe-Bool
                            Nothing
                            (just Bool))
                      (data List
                            null
                            (cons Bool List))
                      (define right-proj
                        (λ (Bool Bool → Bool)
                          (a true → true)
                          (a b → (cons b a))))
                      (right-proj true false)))
               '(cons false true))


  #;(test-equal? "haskdefs"
                 (rewrite-haskdefs '((and :: Bool Bool → Bool)
                                     (and a true = true)
                                     (and a b = (cons b a))
                                     (id :: Bool → Bool)
                                     (id a = a)
                                     true))
                 '((define and
                     (λ (Bool Bool → Bool)
                       (a true → true)
                       (a b → (cons b a))))
                   (define id
                     (λ (Bool → Bool)
                       (a → a)))
                   true))

  (define haskell-style-test
    '((data Bool
            true
            false)
  
      (data ListBool
            null
            (cons Bool List))
  
      (and :: Bool Bool → Bool)
      (and true true = true)
      (and a b = false)

      (or :: Bool Bool → Bool)
      (or true a = true)
      (or a true = true)
      (or a b = false)
  
      (and (or true false)
           (or false false))))
  
  #;(check-equal? (rewrite-haskdefs haskell-style-test)
                  '((data Bool
                          true
                          false)
                    (data ListBool
                          null
                          (cons Bool List))
                    (define and
                      (λ (Bool Bool → Bool)
                        (true true → true)
                        (a b → false)))
                    (define or
                      (λ (Bool Bool → Bool)
                        (true a → true)
                        (a true → true)
                        (a b → false)))
                    (and (or true false) (or false false))))

  #;(check-equal? (run haskell-style-test)
                  'false)

  #;(test-exn "non-exhaustive"
              (regexp (regexp-quote
                       "error: not exhaustive:  (Bool Bool) ((true a) (a true))"))
              (thunk (run '((data Bool
                                  true
                                  false)
  
                            (data ListBool
                                  null
                                  (cons Bool List))
  
                            (and :: Bool Bool → Bool)
                            (and true true = true)
                            (and a b = false)

                            (or :: Bool Bool → Bool)
                            (or true a = true)
                            (or a true = true)
  
                            (and (or true false)
                                 (or false false))))))


  )
