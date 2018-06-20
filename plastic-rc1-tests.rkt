#lang racket

(require "plastic-rc1.rkt")


(module+ test
  (require rackunit)
  (define-syntax-rule (test-error? name stx error)
    (test-exn name (regexp (regexp-quote error)) (thunk stx)))
  (define-syntax-rule (test-exhaust? name stx)
    (test-error? name stx "non-exhaustive"))
  
  (test-equal? "Void : minimum program"
               (run '((data Void void)
                      void))
               'void)

  (test-equal? "Void : define value and evaluate identifier"
               (run '((data Void void)
                      (define x void)
                      x))
               'void)

  (test-equal? "Void : scope : define referencing previous define"
               (run '((data Void void)
                      (define x void)
                      (define y x)
                      y))
               'void)

  (test-equal? "Void : define/apply fn"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (void → void)))
                      (identity void)))
               'void)

  (test-error? "Void : non-exhaustive : empty unary function"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)))
                      (identity void)))
               "non-exhaustive")

  (test-equal? "Void : define/apply identity"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (identity void)))
               'void)

  (test-equal? "Void : define result of application of previously defined function"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (define x (identity void))
                      x))
               'void)

  (test-equal? "Void : define function whose body references previously defined function"
               (run '((data Void void)
                      (define identity
                        (λ (Void → Void)
                          (a → a)))
                      (define f
                        (λ (Void → Void)
                          (void → (identity void))))
                      (f void)))
               'void)

  (test-equal? "Bool : scope: define shadowing; should we disallow this in spec?"
               (run '((data Bool true false)
                      (define x true)
                      (define x false)
                      x))
               'false)

  (test-equal? "Bool : two defines with different values, reference second"
               (run '((data Bool true false)
                      (define x true)
                      (define y false)
                      y))
               'false)
  
  (test-equal? "Bool : define/apply unary (identity)"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (a → a)))
                      (identity true)))
               'true)

  (test-equal? "Bool : define/apply unary (identity, second implementation)"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (false → false)))
                      (identity false)))
               'false)

  (test-equal? "Bool : define/apply unary (identity, third implementation)"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (a → a)))
                      (identity false)))
               'false)

  (test-equal? "Bool : exhaustive : redundant wildcard"
               (run '((data Bool true false)
                      (define identity
                        (λ (Bool → Bool)
                          (true → true)
                          (false → false)
                          (a → a)))
                      (identity false)))
               'false)

  (test-equal? "Bool : define/apply constant-true : exhaustive using only wildcard"
               (run '((data Bool true false)
                      (define constant-true
                        (λ (Bool → Bool)
                          (a → true)))
                      (constant-true false)))
               'true)

  (test-equal? "Bool : define/apply constant-true : exhaustive + inaccessible case"
               (run '((data Bool true false)
                      (define constant-true
                        (λ (Bool → Bool)
                          (a → true)
                          (true → true)))
                      (constant-true false)))
               'true)

  (test-equal? "Bool : define/apply constant-true : inaccessible incorrect case"
               (run '((data Bool true false)
                      (define constant-true
                        (λ (Bool → Bool)
                          (a → true)
                          (false → false)))
                      (constant-true false)))
               'true)

  (test-error? "Bool : non-exhaustive : minimum non-empty unary"
               (run '((data Bool true false)
                      (define f
                        (λ (Bool → Bool)
                          (true → true)))
                      (f true)))
               "non-exhaustive")

  (test-equal? "Bool : define/apply unary : not"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not true)))
               'false)

  (test-equal? "Bool : define/apply unary : not, second implementation"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (a → true)))
                      (not true)))
               'false)

  (test-equal? "Bool : scope : identifier as argument in application"
               (run '((data Bool true false)
                      (define x false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not x)))
               'true)

  (test-equal? "Bool : aliasing :  identifier as function in application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (define f not)
                      (f false)))
               'true)

  (test-equal? "Bool : aliasing :  identifier as function in application in application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (define f not)
                      (not (f false))))
               'false)

  (test-equal? "Bool : application inside application"
               (run '((data Bool true false)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not (not true))))
               'true)
  
  (test-equal? "Bool : scope : identifier as argument in application in application"
               (run '((data Bool true false)
                      (define x true)
                      (define not
                        (λ (Bool → Bool)
                          (true → false)
                          (false → true)))
                      (not (not x))))
               'true)

  (test-equal? "Bool : define/apply binary : neither"
               (run '((data Bool true false)
                      (define neither
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a a → false)))
                      (neither true false)))
               'false)

  (test-equal? "Bool : define/apply binary : and"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (false true → false)
                          (true false → false)
                          (false false → false)))
                      (and true false)))
               'false)

  (test-equal? "Bool: define/apply binary : and, second implementation"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a a → false)))
                      (and false true)))
               'false)

  (test-error? "Bool: non-exhaustive binary : misses (and false _)"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (true a → false)))
                      (and false true)))
               "non-exhaustive")

  (test-error? "Bool: non-exhaustive binary : misses (and true false)"
               (run '((data Bool true false)
                      (define and
                        (λ (Bool Bool → Bool)
                          (true true → true)
                          (a true → false)))
                      (and false true)))
               "non-exhaustive")

  (test-equal? "Bool: define/apply ternary function"
               (run '((data Bool true false)
                      (define f
                        (λ (Bool Bool Bool → Bool)
                          (true true true → true)
                          (true a false → false)
                          (a a a → true)))
                      (f true false false)))
               'false)

  (test-equal? "Color : minimal enum-only type with more than two values"
               (run '((data Color red green blue)
                      red))
               'red)

  (test-equal? "Color : define/apply function with more than two cases"
               (run '((data Color red green blue)
                      (define identity
                        (λ (Color → Color)
                          (red → red)
                          (blue → blue)
                          (green → green)))
                      green))
               'green)

  (test-equal? "Color : repeated application of unary function inside function body"
               (run '((data Color red green blue)
                      (define swap-red-blue
                        (λ (Color → Color)
                          (red → blue)
                          (blue → red)
                          (green → green)))
                      (define f
                        (λ (Color → Color)
                          (a → (swap-red-blue (swap-red-blue (swap-red-blue a))))))
                      (f blue)))
               'red)

  (test-error? "Color : non-exhaustive : unary function on ternary type (RGB minus B)"
               (run '((data Color red green blue)
                      (define identity
                        (λ (Color → Color)
                          (red → red)
                          (green → green)))
                      red))
               "non-exhaustive")
  
  (test-equal? "Box : minimal struct-only type"
               (run '((data Void void)
                      (data Boxed-Void
                            (box Void))
                      (box void)))
               '(box void))

  (test-equal? "Box : identifier inside constructor"
               (run '((data Void void)
                      (data Boxed-Void
                            (box Void))
                      (define a void)
                      (box a)))
               '(box void))

  (test-equal? "Pair-Bool : minimal binary constructor"
               (run '((data Bool true false)
                      (data Pair (pair Bool Bool))
                      (pair true false)))
               '(pair true false))

  (test-equal? "Pair-Bool : highly nested binary constructors"
               (run '((data Bool true false)
                      (data Pair (pair Bool Bool))
                      (pair (pair (pair true false) false) (pair (pair true false) false))))
               '(pair (pair (pair true false) false) (pair (pair true false) false)))

  (test-equal? "Pair-Bool : define/apply (flip)"
               (run '((data Bool true false)
                      (data Pair (pair Bool Bool))
                      (define flip
                        (λ (Pair → Pair)
                          ((pair a b) → (pair b a))))
                      (flip (pair true false))))
               '(pair false true))

  (test-equal? "Nat : minimal recursive data type"
               (run '((data Nat
                            zero
                            (S Nat))
                      (S zero)))
               '(S zero))
  
  (test-equal? "Nat : highly nested unary constructors"
               (run '((data Nat
                            zero
                            (S Nat))
                      (S (S (S (S zero))))))
               '(S (S (S (S zero)))))

  (test-equal? "Nat : exhaustive : constant-zero (using only wildcard)"
               (run '((data Nat
                            zero
                            (S Nat))
                      (define constant-zero
                        (λ (Nat → Nat)
                          (a → zero)))
                      (constant-zero zero)))
               'zero)

  (test-equal? "Maybe-Bool : minimal non-trivial ADT (both enum- and struct-like)"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (just true)))
               '(just true))

  (test-error? "Maybe-Bool : non-exhaustive : only nothing"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (define f
                        (λ (Maybe-Bool → Bool)
                          (nothing → false)))
                      true))
               "non-exhaustive")

  (test-error? "Maybe-Bool : non-exhaustive : only (just true))"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (define f
                        (λ (Maybe-Bool → Bool)
                          ((just true) → false)))
                      true))
               "non-exhaustive")
  
  (test-error? "Maybe-Bool : non-exhaustive : only (just _))"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (define f
                        (λ (Maybe-Bool → Bool)
                          ((just a) → false)))
                      true))
               "non-exhaustive")
  
  (test-error? "Maybe-Bool : non-exhaustive : nothing, (just false)"
               (run '((data Bool true false)
                      (data Maybe-Bool
                            nothing
                            (just Bool))
                      (define f
                        (λ (Maybe-Bool → Bool)
                          (nothing → false)
                          ((just false) → false)))
                      true))
               "non-exhaustive")

  (test-equal? "List-Bool : define/apply unary : length-one?"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (define length-one?
                        (λ (List-Bool → Bool)
                          (null → false)
                          ((cons a null) → true)
                          ((cons a (cons b c)) → false)))
                      (length-one? null)))
               'false)

  (test-error? "List-Bool : non-exhaustive, complete signature : null, (cons true null)"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (define f
                        (λ (List-Bool → Bool)
                          (null → false)
                          ((cons true null) → false)))
                      (f null)))
               "non-exhaustive")

  (test-error? "List-Bool : non-exhaustive, complete signature : misses triply+-nested cons"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (define length-one?
                        (λ (List-Bool → Bool)
                          (null → false)
                          ((cons a null) → true)
                          ((cons a (cons b null)) → false)))
                      (length-one? null)))
               "non-exhaustive")

  (test-error? "List-Bool : non-exhaustive : misses (cons _ (cons false _))"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (define length-one?
                        (λ (List-Bool → Bool)
                          (null → false)
                          ((cons a (cons b (cons c d))) → false)
                          ((cons a null) → true)
                          ((cons a (cons true null)) → false)))
                      (length-one? null)))
               "non-exhaustive")
  
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

  (test-equal? "Maybe-List-Bool : define/apply : maybe-first"
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

  (test-equal? "Maybe-List-Bool : define/apply : maybe-rest"
               (run '((data Bool true false)
                      (data List-Bool
                            null
                            (cons Bool List-Bool))
                      (data Maybe-List-Bool
                            nothing
                            (just List-Bool))
                      (define maybe-rest
                        (λ (List-Bool → Maybe-List-Bool)
                          (null → nothing)
                          ((cons a b) → b)))
                      (maybe-rest null)))
               'nothing)
  
  (test-error? "Maybe-List-Bool : non-exhaustive : missing only triply-nested cons"
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
                          ((cons a (cons b null)) → a)
                          #;((cons a (cons b (cons c null))) → a)
                          ((cons a (cons b (cons c (cons d e)))) → a)))
                      (maybe-first (cons true (cons false null)))))
               "non-exhaustive")

  (test-equal? "Maybe-List-Nat : complex test"
               (run '((data Nat zero (S Nat))
                      (data List-Nat
                            null
                            (cons Nat List-Nat))
                      (data Maybe-List-Nat
                            nothing
                            (just List-Nat))
                      (define a-list
                        (cons zero (cons (S zero) (cons (S (S zero)) null))))
                      (define maybe-first
                        (λ (List-Nat → Maybe-List-Nat)
                          (null → nothing)
                          ((cons a b) → b)))
                      (define maybe-rest
                        (λ (List-Nat → Maybe-List-Nat)
                          (null → nothing)
                          ((cons a b) → b)))
                      (define f
                        (λ (List → Maybe-List-Nat)
                          ((cons zero b) → (maybe-rest b))
                          ((cons (S a) b) → (maybe-first b))
                          (a → nothing)))
                      (maybe-rest a-list)))
               '(cons (S zero) (cons (S (S zero)) null)))
  

  )