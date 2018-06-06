#lang racket


; factorial :: Integer -> Integer  
; factorial n = product [1..n]


; TODOS:
; 1. need to (wrap) nullaries at some point before exhaust
; 2. need to rename variables/wildcards to type-names
;    OR
; 2alt. need to send in initial type vector (from sig)
;       and deal with ?????????? THINK MORE ABOUT THIS


; plaskell syntax:

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
  
  (main = (and (or true false)
               (or false false))))


; after data phase:

'(#;#hash((true . Bool)
          (false . Bool)
          (null . ListBool)
          (cons . (Bool List → List)))
  (define and
    (λ:: (Bool Bool → Bool)
         (true true → true)
         (a b → false)))
  (define or
    (λ:: (Bool Bool → Bool)
         (true a → true)
         (a true → true)
         (a b → false)))
  (and (or true false) (or false false)))


; after define phase:

'(#;#hash((true . Bool)
          (false . Bool)
          (null . ListBool)
          (cons . (Bool List → List)))
  #;#hash((and . (λ:: (Bool Bool → Bool)
                      (true true → true)
                      (a b → false)))
          (or . (λ:: (Bool Bool → Bool)
                     (true a → true)
                     (a true → true)
                     (a b → false))))
  (and (or true false) (or false false)))