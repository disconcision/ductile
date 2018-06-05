#lang racket

(require racket/hash)


; concrete pattern-matching clause for manual cons pattern:
; (excerpted from plastic/pattern-match)
#;[`(cons ,p0 ,p1)
   (match arg
     [`(cons ,a0 ,a1) ;rewrite to not use pattern-matching lol
      (match* ((Pm a0 p0)
               (Pm a1 p1))
        [('no-match _) 'no-match]
        [(_ 'no-match) 'no-match]
        [(e0 e1) (hash-union e0 e1)])]
     [_ 'no-match])]


; pattern matching to lc-ish compilation tests
(define (compiler pat-tem)
  (match pat-tem
    [`(,pat ,tem)
     `(λ (e) (ifls e)
        ,(match pat
           [(? 'XXX-constructor-id?)
            0]
           [(? symbol?)
            0]
           [`(,(? 'XXX-constructor-id?) ,xs ...)
            0]))]))


; below needs to be non-strict in stx
#;(define (ifne name stx)
    (λ (X)
      (if (equal? name X)
          stx
          'no-match)))
#;(define (ifls e stx)
    (λ (X)
      (if (list? e)
          stx
          'no-match)))

#;(module+ test
    (require rackunit)
    (check-equal? (compiler '(a tem))
                  '(λ (a)
                     tem))
    (check-equal? (compiler '(null tem))
                  '(λ (e)
                     (ifne null tem
                           e)))
    ; below: check if evaluated expression e is list first?
    (check-equal? (compiler '((just a) tem))
                  '(λ (e) (ifls e
                                (ifne just ((λ (a)
                                              tem)
                                            (car (cdr e)))
                                      (car e))
                                )))
  
    (check-equal? (compiler '((cons a b) tem))
                  '(λ (e) (ifls e
                                (ifne cons
                                      ((λ (a)
                                         ((λ (b) tem)
                                          (car (cdr (cdr e)))))
                                       (car (cdr e)))
                                      (car e))
                                )))

    ; do we need to check for null? is thre a situation in
    ; which the first symbol could match and the list is
    ; a different length?
  
    ; here A and B (but not a, b, c) are constructor names:
    (check-equal? (compiler '((A a b B c) tem))
                  '(λ (e) (ifls e
                                (ifne A
                                      ((λ (a)
                                         ((λ (b)
                                            (ifne B
                                                  ((λ (c)
                                                     tem)
                                                   (car (cdr (cdr (cdr (cdr e))))))
                                                  (car (cdr (cdr (cdr e))))))
                                          (car (cdr (cdr e)))))
                                       (car (cdr e)))
                                      (car e)))))

    ; more sensible format:
    (check-equal? (compiler '((A a b B c) tem))
                  '(λ (e) (ifls e
                                (ifne A (car e)
                                      (let a (car (cdr e))
                                        (let b (car (cdr (cdr e)))
                                          (ifne B (car (cdr (cdr (cdr e))))
                                                (let c (car (cdr (cdr (cdr (cdr e)))))
                                                  tem))))))))
    )



; type stripper
(define (strip-types stx)
  (match stx
    [`(λ ,type ,cases ...)
     `(λ ,@cases)]
    [`(,xs ...) (map strip-types stx)]
    [_ stx]))

; type checker
; DETAILED SKETCH - NOT TEST DRIVEN
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