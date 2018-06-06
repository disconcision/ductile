#lang racket

(define transpose (curry apply map list))

(define (NE* types M)

  (define (complete-signature type)
    (for/fold ([ls '()])
              ([(k v) types])
      (match v
        [(or `(,_ ... → ,(== type)) (== type))
         (cons k ls)]
        [_ ls])))

  (define set-of-types
    (for/fold ([ts (set)])
              ([(k v) types])
      (match v
        [(or `(,_ ... → ,x) x) (set-add ts x)]
        [_ ts])))
  
  (define constructor? (curry hash-has-key? types))
  (define type? (curry set-member? set-of-types))
  
  (define (make-signature constructor)
    (match (hash-ref types constructor)
      [`(,sig ... → ,_) sig]
      [_ '()]))

  (define (complete? type signature)
    (set=? signature (list->set (complete-signature type))))
  
  (define (signature-in column)
    (for/fold ([old-set (set)])
              ([pattern column])
      (match pattern
        [`(,constructor ,_ ...) (set-add old-set constructor)]
        [_ old-set])))
  
  (define (D M)
    (apply append 
           (for/list ([row M])
             (match row
               [`((,(? constructor?) ,rs ...) ,ps ...)
                `()]
               [`(,(? type?) ,ps ...)
                `(,ps)]))))
  
  (define (S c M)
    (apply append
           (for/list ([row M]) 
             (match row
               [`(,(? type?) ,ps ...) ; note this is literal '_ 
                `((,@(make-signature c) ,@ps))]
               [`((,(== c) ,rs ...) ,ps ...)
                `((,@rs ,@ps))]
               [`((,(not (== c)) ,_ ...) ,_ ...)
                `()]))))
  (match M
    [`() #true]
    [`(() ..1) #false]
    [(app transpose `(,first-col ,_ ...))
     (define type (match (first first-col)
                    [(? type? t) t]
                    [`(,(? constructor? c) ,_ ...)
                     (match (hash-ref types c)
                       [(or `(,_ ... → ,x) x) x]
                       )]))
     (if (complete? type (signature-in first-col))
         (for/or ([constructor (complete-signature type)])
           (NE* types (S constructor M)))
         (NE* types (D M)))]))


(define ext-bool #hash((true . Bool)
                       (false . Bool)
                       (pair . (Bool Bool → Bool))))
(require rackunit)
(check-equal? (NE* ext-bool '(((true))
                              ((false))
                              ((pair (true) Bool))
                              ((pair Bool (true)))
                              (Bool)))
              #f)

(check-equal? (NE* ext-bool '(((true))
                              ((false))
                              ((pair (true) Bool))
                              ((pair Bool (true)))))
              #t)

(define types2 #hash((true . Bool)
                     (false . Bool)
                     (cons . (Bool List → List))
                     (null . List)))


