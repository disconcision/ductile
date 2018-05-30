;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "2017-fall-reader.rkt" "csc104")((modname plastic-sketch) (compthink-settings #hash((prefix-types? . #f))))
#lang racket

#|

Current design factors out all static checking.
Static checking possibilities:
1. type-checking with explicit declarations:
decorate all λ-forms (and eliminate λ-less arrows) with a type-dec
constructor checking (including constructor arity) should be able to
piggy-back on this checking (do we even need to distinguish fns/constructors?)
2. exhaustiveness checking:
simpler if we have type decs... otherwise we need more logic to determine
which type we're trying to exhaust. for only nullary constructors: begin
with a set of all instances of the type; remove as they are seen, or
until a wildcard is found. if we reach the end of the list and the set
is non-empty, then it's not exhaustive.
for n-ary constructors:
idea 1: recursively fill initial set.
i.e. for n-ary constructors, add all variants to se
problem: recursive types (seems fatal)
the below is exhaustive:
[zero ?]
[(S zero) ?]
[(S (S zero)) ?]
[(S a) ?]
if type is recusive, seems like we'd eventually need a wildcard
non-exhaustive case: (no case for (S (S zero)))
[zero ?]
[(S zero) ?]
[(S (S (S a))) ?]

maybe restrict exhaustiveness check to non-recursive,
non-mututally-recursive types

|#


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
  #;#;(println "types:")(println types)
  #;(define types '(cons S true null))


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