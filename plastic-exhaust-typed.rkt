#lang racket

(define transpose (curry apply map list))

(define (NE* types M)
  (define constructor? (curry hash-has-key? types))
  (define (complete-signature type)
    (for/fold ([ls '()])
              ([(k v) types])
      (match v
        [(or `(,_ ... → ,(== type)) (== type))
         (cons k ls)]
        [_ ls])))

  (define (num-args constructor)
    (match (hash-ref types constructor)
      [(? list? ls) (- (length ls) 2)]
      [_ 0]))

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
               [`(_ ,ps ...)
                `(,ps)]))))
  
  (define (S c M)
    (apply append
           (for/list ([row M]) 
             (match row
               [`(_ ,ps ...) ; note this is literal '_ 
                `((,@(make-signature c) ,@ps))]
               [`((,(== c) ,rs ...) ,ps ...)
                `((,@rs ,@ps))]
               [`((,(not (== c)) ,_ ...) ,_ ...)
                `()]))))
  (match M
    [`() #true]
    [`(() ..1) #false]
    [(app transpose `(,first-col ,_ ...))
     (if (complete? type (signature-in first-col))
         (for/or ([constructor (complete-signature type)])
           (NE* (S constructor M)))
         (NE* (D M)))]))