#lang racket

(require racket/hash)

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

exhaustiveness refs: TODO

|#


; type stripper
(define (strip-types stx)
  (match stx
    [`(λ ,type ,cases ...)
     `(λ ,@cases)]
    [`(,xs ...) (map strip-types stx)]
    [_ stx]))

; type checker
; NOT FINISHED
(define (type-check types t-env stx)
  (define T (curry type-check types t-env))
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define (Tpat env parent-type stx) ;returns pair of type and env
    (match stx
      [(? constructor-id? id) (hash-ref types id)]
      [`(,(? constructor-id? id) ,(app Tpat `(,types ,envs)) ...)
       (match parent-type
         [types (apply hash-union envs)] ; fix this
         [_ (error "pat typefail")])]
      [(? symbol? id)
       (hash-set t-env id parent-type)]
      ; need to get this type from parent?
      ; base case (not inside constructor: get from type-dec
      ))
  (match stx
    [(? constructor-id? id) (hash-ref types id)]
    [`(,(? constructor-id? id) ,(and xs (not (== '→))) ...)
     (match (hash-ref types id)
       [`(,arg-types ... → ,ret-type)
        (match (map T xs)
          [(== arg-types) ret-type]
          [_ (error "n-ary constructor typefail")])])]
    [(? symbol? id) (hash-ref t-env id)]
    [`(λ (,dec-arg-type → ,dec-ret-type) ,cases ...)
     (define (f c env)
       (define Tloc (curry type-check types env))
       (match c
         [`(,(app (curry Tpat env dec-arg-type) `(,c-arg-type ,new-env)) → ,(app Tloc c-ret-type))
          (if (and (equal? dec-arg-type c-arg-type)
                   (equal? dec-ret-type c-ret-type))
              `(,dec-arg-type → ,dec-ret-type)
              (error "lambda typefail"))
          ]))
     (foldl f t-env cases)]
    [`(,(app T `(,param-type → ,ret-type)) ,(app T arg-type))
     (match arg-type
       [(== param-type) ret-type]
       [_ (error "app typefail")])]
    ))


; make certain forms explicit
(define (explicitize stx)
  (define Ex explicitize)
  (define Px pattern-explicitize)
  (define constructor-id? 0)
  (match stx
    [(? constructor-id? id) `(dat ,id)]
    [(? symbol? id) `(var ,id)]
    [`(,pat → ,expr)
     `(fun ,(Px pat) ,(Ex expr))]
    [`(λ ,cases ...)
     `(fal ,@(map Ex cases))]
    #;[`(cons ,a ,b) `(cons ,(Ex a) ,(Ex b))]
    [`(,(? constructor-id? id) ,xs ...)
     `(dat ,id ,@(map Ex xs) )]
    [`(,f ,x) `(app ,(Ex f) ,(Ex x))]
    #;[_ stx]))

; make pattern forms explicit
; needs to be adapted to ADTs
(define (pattern-explicitize stx)
  (define Px pattern-explicitize)
  (define constructor-id? 0)
  (match stx
    [(? constructor-id? id) `(p-dat ,id)]
    [(? symbol?) `(p-var ,stx)]
    [`(,(? constructor-id? id) ,xs ...)
     `(p-dat ,id ,@(map Px xs) )]
    #;[`(cons ,a ,b) `(cons ,(Px a) ,(Px b))]
    #;[_ stx]))