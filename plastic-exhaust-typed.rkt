#lang racket

(provide static-check)


(define (static-check types stx)
  (match stx
    [`(λ (,typevec ... → ,_)
        (,ts ... → ,_) ...)
     (if ((compose (curry NE* types typevec)
                     (wrap-nullary-constructors types))
            ts)
       (error "error: not exhaustive: " typevec ts)
       stx)]
    [(? list?) (map (curry static-check types) stx)]
    [_ stx]))


(define transpose (curry apply map list))

(define (wrap-nullary-constructors types)
  (define constructor? (curry hash-has-key? types))
  (match-lambda
    [(? list? stx) (map (wrap-nullary-constructors types) stx)]
    [(? constructor? c)
     #:when (= 2 (length (hash-ref types c)))
     `(,c)]
    [stx stx]))


(define (NE* types typevec M)

  (define constructor? (curry hash-has-key? types))

  (define wildcard? (conjoin symbol?
                             (disjoin (curry equal? '_)
                                      (negate constructor?))))
  
  (define (input-signature constructor)
    (match (hash-ref types constructor)
      [`(,sig ... → ,_) sig]))

  (define (all-constructors type)
    (for/fold ([ls '()])
              ([(k v) types])
      (match v
        [`(,_ ... → ,(== type))
         (cons k ls)]
        [_ ls])))

  (define (complete? type signature)
    (set=? signature (list->set (all-constructors type))))
  
  (define (signature-in column)
    (for/fold ([old-set (set)])
              ([pattern column])
      (match pattern
        [`(,constructor ,_ ...)
         (set-add old-set constructor)]
        [_ old-set])))
  
  (define (D M)
    (apply
     append 
     (for/list ([row M])
       (match row
         [`((,(? constructor?) ,_ ...) ,_ ...)
          `()]
         [`(,(? wildcard?) ,xs ...)
          `(,xs)]))))
  
  (define (S c M)
    (apply
     append
     (for/list ([row M]) 
       (match row
         [`(,(? wildcard?) ,xs ...)
          `((,@(make-list (length (input-signature c)) '_) ,@xs))]
         [`((,(== c) ,xs ...) ,ys ...)
          `((,@xs ,@ys))]
         [`((,(not (== c)) ,_ ...) ,_ ...)
          `()]))))
  
  (match M
    [`() #true]
    [`(() ..1) #false]
    [(app transpose `(,first-col ,_ ...))
     (match typevec
       [`(,type ,tail-types ...)
        (if (complete? type (signature-in first-col))
            (for/or ([c (all-constructors type)])
              (NE* types `(,@(input-signature c) ,@tail-types)
                   (S c M)))
            (NE* types tail-types
                 (D M)))])]))





(require rackunit)


(define test-fn1
  (let ([types #hash((true . (→ Bool))
                     (false . (→ Bool))
                     (pair . (Bool Bool → Bool)))]
        [typevec '(Bool)])
    (compose (curry NE* types typevec)
             (wrap-nullary-constructors types))))

(check-equal? (test-fn1
               '((true)
                 (false)
                 ((pair true _))
                 ((pair _ true))
                 (_)))
              #f)

(check-equal? (test-fn1
               '((true)
                 (false)
                 ((pair true _))
                 ((pair _ true))))
              #t)

(define test-fn2
  (let ([types #hash((true . (→ Bool))
                     (false . (→ Bool))
                     (cons . (Bool List → List))
                     (null . (→ List)))]
        [typevec '(List)])
    (compose (curry NE* types typevec)
             (wrap-nullary-constructors types))))


(check-equal? (test-fn2
               '(((cons _ _))
                 (null)))
              #f)

(check-equal? (test-fn2
               '(((cons _ false))
                 (null)))
              #t)

(check-equal? (test-fn2
               '(((cons true _))
                 ((cons _ true))))
              #t)

(check-equal? (test-fn2
               '((_)
                 ((cons true _))
                 ((cons _ true))))
              #f)

(check-equal? (test-fn2
               '(((cons true _))
                 ((cons _ true))
                 (null)))
              #t)

(check-equal? (test-fn2
               '((null)
                 ((cons a b))))
              #f)

(check-equal? (test-fn2
               '(((cons null a))
                 ((cons a null))))
              #t)

