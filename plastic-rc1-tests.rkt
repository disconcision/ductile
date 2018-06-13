#lang racket

(require "plastic-rc1.rkt")


(module+ test
  (require rackunit)
  (define-syntax-rule (test-error? name stx error)
    (test-exn name (regexp (regexp-quote error)) (thunk stx)))
  (define-syntax-rule (test-exhaust? name stx)
    (test-error? name stx "non-exhaustive"))

  (test-equal? "minimum program"
               (run '((data Void void)
                      void))
               'void)

  (test-equal? "define value and evaluate identifier"
               (run '((data Void void)
                      (define x void)
                      x))
               'void)

  (test-equal? "scope: define value referenced in next define"
               (run '((data Void void)
                      (define x void)
                      (define y x)
                      y))
               'void)

  (test-equal? "define fn; appplication"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (void → void)))
                      (identity void)))
               'void)

  ;(test-error? name stx error)
  (test-error? "define fn empty"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          ))
                      (identity void)))
               "non-exhaustive")

  (test-equal? "define fn 2"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (identity void)))
               'void)

  (test-equal? "scope: define fn, applied in next define"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (define x (identity void))
                      x))
               'void)

  (test-equal? "scope: define fn, applied inside λ in next define fn"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (define f
                        (λ (Void → Void)
                          (void → (identity void))))
                      (f void)))
               'void)

  (test-equal? "Bool: scope: defines shadowing; should we disallow this in spec?"
               (run '((data Bool true false)
                      (define x true)
                      (define x false)
                      x))
               'false)

  (test-equal? "Bool : define fn identity"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (a → a)))
                      (identity true)))
               'true)

  (test-equal? "Bool : define fn identity (second implementation)"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (false → false)))
                      (identity false)))
               'false)

  (test-equal? "Bool : define fn identity (third implementation)"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (a → a)))
                      (identity false)))
               'false)

  (test-error? "Bool : error: define fn: minimal non-trivial non-exhaustive"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)))
                      (identity true)))
               "non-exhaustive")

  (test-equal? "define/apply not"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not true)))
               'false)

  (test-equal? "scope: identifier as argument in application"
               (run '((data Bool true false)
                      (define x false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not x)))
               'true)

  (test-equal? "fn aliasing:  identifier as function in application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (define f not)
                      (f false)))
               'true)

  (test-equal? "fn aliasing:  identifier as function in application in application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (define f not)
                      (not (f false))))
               'false)

  (test-equal? "application inside application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not (not true))))
               'true)
  
  (test-equal? "scope: identifier as argument in application in application"
               (run '((data Bool true false)
                      (define x true)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not (not x))))
               'true)

  (test-equal? "define/apply not; alternative implementation"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (a → true)))
                      (not true)))
               'false)

  (test-error? "simplest no-exhaustive"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)))
                      (not true)))
               "non-exhaustive")
  
  (test-equal? "define values x2"
               (run '((data Bool true false)
                      (define x true)
                      (define y false)
                      y))
               'false)

  (test-equal? "define/apply binary fn: neither"
               (run '((data Bool true false)
                      (define neither
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a a → false)))
                      (neither true false)))
               'false)

  (test-equal? "Color : enum-only type with more than two values"
               (run '((data Color red green blue)
                      red))
               'red)
  
  (test-equal? "Box : minimal struct-only data constructor"
               (run '((data Void void)
                      (data Wrap-Void
                            (box Void))
                      (box void)))
               '(box void))

  (test-equal? "Maybe : minimal non-trivial ADT (is both enum- and struct-like)"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (just (just true))))
               '(just (just true)))

  (test-equal? "Nat : minimal recursive data type"
               (run '((data Nat
                            zero
                            (S Nat))
                      (S (S (S zero)))))
               '(S (S (S zero))))

  (test-equal? "Pair-Bool : minimal binary constructor"
               (run '((data Bool true false)
                      (data Pair (pair Bool Bool))
                      (pair true false)))
               '(pair true false))

  (test-equal? "Pair-Bool : define/apply fn: flip"
               (run '((data Bool true false)
                      (data Pair (pair Bool Bool))
                      (define flip
                        (λ (Pair → Pair)
                          ((pair a b) → (pair b a))))
                      (flip (pair true false))))
               '(pair false true))

  (test-equal? "List-Bool : less fun without recursion"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (define a true)
                      (cons true a)))
               '(cons true true))
  

  (test-equal? "Maybe-List-Bool : Triply nested types"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (data Maybe-List-Bool
                            nothing
                            (just List-Bool))
                      (just (cons true null))))
               '(just (cons true null)))

  
  (test-equal? "Maybe-List-Bool : define/apply fn: first"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (data Maybe-List-Bool
                            nothing
                            (just List-Bool))
                      (define maybe-first
                        (λ (List-Bool → Maybe-List-Bool)
                          (null → nothing)
                          ((cons a b) → a)))
                      (maybe-first (cons true null))))
               'true)
  
 

  (test-equal? "Bool: define/apply fn: and"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (false true → false)
                          (true false → false)
                          (false false → false)))
                      (and true false)))
               'false)

  (test-equal? "Bool: define/apply fn: and (second implementation)"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a a → false)))
                      (and false true)))
               'false)

  (test-error? "Bool: error: define/apply fn: and 1"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (true a → false)))
                      (and false true)))
               "non-exhaustive")

  (test-error? "Bool: error: define/apply fn: and 2"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a true → false)))
                      (and false true)))
               "non-exhaustive")


  ; uh oh implementation issues
  #;(test-error? "Maybe-List-Bool : error: define/apply fn: first 1"
                 (run '((data Bool true false)
                        (data List-Bool
                              null
                              (cons Bool List-Bool))
                        (data Maybe-List-Bool
                              nothing
                              (just List-Bool))
                        (define maybe-first
                          (λ (List-Bool → Maybe-List-Bool)
                            (null → nothing)
                            ((cons a null) → a)
                            #;((cons a (cons b (cons c d))) → a)))
                        (maybe-first (cons true (cons false null)))))
                 "non-exhaustive")
  
  ; to-do: more deeply recursive exhaustiveness tests

  ; to-do: more computation on the template side of λs
  

  )