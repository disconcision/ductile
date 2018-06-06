#lang racket

; PATTERN MATCHING EXHAUSTIVENESS CHECKING
; following Maranget from "Warnings for pattern matching"

; first i present a simplified version of Maranget's algorithm
; thereafter follows an incomplete version of his general algo

; some utility functions
(define transpose (curry apply map list))
(define (row M) (curry list-ref M))
(define (col M) (curry list-ref (transpose M)))

#| simplifying assumptions:
 
   0. proceed without types for now

   1. all patterns are linear, so we can reduce named
   pattern variables to a generic wildcard

   2. we will omit or-patterns, and indeed everything
   but wildcards, literals, and lists thereof
|#


; exhaustiveness:

; fixed type for now:
(define types #hash((true . Bool)
                    (false . Bool)
                    (pair . (Bool Bool → Bool))))

; utility fns:

(define constructor? (curry hash-has-key? types))
(define complete-signature (hash-keys types))

(define (num-args constructor)
  (match (hash-ref types constructor)
    [(? list? ls) (- (length ls) 2)]
    [_ 0]))

(define (complete? signature)
  (set=? signature (list->set complete-signature)))

(define (signature-in column)
  (for/fold ([old-set (set)])
            ([pattern column])
    (match pattern
      [`(,constructor ,_ ...) (set-add old-set constructor)]
      [_ old-set])))

; generates the 'Default Matrix' D from a matrix M
(define (D M)
  (apply append 
         (for/list ([row M])
           (match row
             [`((,(? constructor?) ,rs ...) ,ps ...)
              `()]
             [`(_ ,ps ...)
              `(,ps)]))))

; generates the 'Specialized Matrix' S from a matrix M
(define (S c M)
  (apply append
         (for/list ([row M]) 
           (match row
             [`(_ ,ps ...) ; note this is literal '_ 
              `((,@(make-list (num-args c) '_) ,@ps))]
             [`((,(== c) ,rs ...) ,ps ...)
              `((,@rs ,@ps))]
             [`((,(not (== c)) ,_ ...) ,_ ...)
              `()]))))

; returns true iff M is non-exhaustive
(define (NE M)
  (match M
    [`() #true]
    [`(() ..1) #false]
    [(app transpose `(,first-col ,_ ...))
     (if (complete? (signature-in first-col))
         (for/or ([constructor complete-signature])
           (NE (S constructor M)))
         (NE (D M)))]))


; tests for exhaustiveness:
(require rackunit)


(check-equal? (NE '((_)))
              #f)

(check-equal? (NE '((_ _)))
              #f)

(define M1 '(( (true)     )
             ( (pair _ _) )))

(check-equal? (D M1) '())
(check-equal? (S 'true M1) '(()))
(check-equal? (S 'pair M1) '((_ _)))
(check-equal? (S 'false M1) '())
(check-equal? (NE M1) #t)

(define M2 '(( (true)          )
             ( (pair (true) _) )
             ( (pair _ (true)) )
             (  _              )))

(check-equal? (D M2) '(()))
(check-equal? (S 'true M2) '(() ())) ; DOUBLE CHECK THIS
(check-equal? (S 'pair M2) '(((true) _)
                             (_ (true))
                             (_ _)))
(check-equal? (S 'false M2) '(())) ; THIS TOO
(check-equal? (NE M2) #f)

(define M3 '(( (true)          )
             ( (false)         )
             ( (pair _ _)      )))

(check-equal? (S 'true M3) '(()))
(check-equal? (S 'pair M3) '((_ _)))
(check-equal? (S 'false M3) '(()))
(check-equal? (NE M3) #f)


(check-equal? (NE '((_)))
              #f)

(check-equal? (NE '(((true)
                     (_))))
              #t)

(check-equal? (NE '(((true))))
              #t)

(check-equal? (NE '(((true))
                    ((false))))
              #t)

(check-equal? (NE '(((true))
                    ((false))
                    ((pair (true) _))))
              #t)

(check-equal? (NE '(((true))
                    ((false))
                    ((pair (true) _))
                    ((pair _ (true)))))
              #t)

(check-equal? (NE '(((true))
                    ((false))
                    ((pair (true) _))
                    ((pair _ (true)))
                    (_)))
              #f)

; grammar
#; (pattern ((cons pattern pattern)
             (just pattern)
             void
             null))

#; (define constants '(cons just null void))

(define Msample '(( (cons null _)  (cons (cons _ _) _)    )
                  ( (just null)    (cons _ (cons null _)) )
                  ( (cons _ _)     (cons null (cons _ _)) )
                  (  null           _                     )
                  (  void           _                     )))



; incomplete notes on generalizing the algorithm:


(define/match (instance? pattern value)
  [(  '_        _        ) #true]
  [( (? constructor?) (? constructor?) ) (equal? pattern value)]
  [( (? list?) (? list?) ) (and (equal? (length pattern) (length value))
                                (andmap instance? pattern value))]
  [(  _         _        ) #false])
(define (M-instance? M v) (ormap (curryr instance? v) M))
(define Msample-transpose (transpose Msample))
(define (dimensions M)
  `(,(length M) ,(length (first M))))

#| let M be a match matrix and q a vector of values whose
   length is the same as the number of columns of M.

we want U* to satisty:
   ∃v (and (not (M-instance? M v)) (instance? q v)))

we attempt to implement U* as U

note important invariant:
U is invariant under reordering of rows
this will allow us to usefully decompose M
  without worrying about interaction

 |#
(define (U M q)
  (match* (M q)
    [(`()  _) #true] ; empty matrix
    [(`(() ...) `()) #false] ; matrix of empty rows
    [(`((,x ,xs...) ...) `(,q1 ,qs ...))
     (match q1
       [`(,(? constructor? c) ,rs ...)
        (U (S c M) (S c q))]
       [`_
        (if (complete? (signature-in x))
            ; actually maybe note that first col of M is x
            (ormap (λ (c) (U (S c M) (S c q)))
                   (signature-in x))
            #t)] ; count signature. for exhaustiveness, skip incomp case
       )]
    ))

#|
  U lets us define the following:
|#
(define (exhaustive? M)
  (not (U M (make-list '_ (length (transpose M))))))
(define (redundant? M row) ; remove row from M first
  (not (U M row)))





#| hints for exhaustiveness checking:


0. consider lists of patterns expressed in matrix form

1. notice that pattern variable names don't matter;
they can all be replaced by a generic wildcard

2. notice that changing pattern order doesn't affect exhaustiveness

3. consider the match matrix one column at a time.

4. following on 2, for each constructor, we can form a specialized
version of the original matrix where we eliminate any rows whose
first column begins with any other constructor. now all of these
specialized matrixes have to be exhaustive

5. notice that since each entry in the first col of these
specialized matrices has the same constructor, we can
just eliminate that constructor, and add its arguments
as columns in the specialized matrix.

|#


#| INITIAL NOTES ON EXHAUSTIVENESS

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
