#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(define (run-interpreter prog)
  (define I*
    (compose (curry interpret #hash((⊥ . ⊥)))
             explicitize
             #;expand
             expand-top))
  (I* prog))

(define (expand-top stx)
  (define Ex expand-top)
  (match stx
    [`((define ,id ,init) ,expr)
     `((,id → ,(Ex expr)) ,(Ex init))]
    [`((define ,id ,init) ,xs ...)
     `((,id → ,(Ex xs)) ,(Ex init))]
    [_ stx]))

; make certain forms explicit
(define (explicitize stx)
  (define Ex explicitize)
  (define Px pattern-explicitize)
  (match stx
    ['null `(dat null)]
    [(? symbol?) `(var ,stx)]
    [(? number?) `(dat ,stx)]
    [`(,pat → ,expr)
     `(,(Px pat) → ,(Ex expr))]
    [`(cons ,a ,b) `(cons ,(Ex a) ,(Ex b))]
    ; turn lists into cons or leave seperate?
    #;[`(list ,xs ...) `(list ,@(map Ex xs))]
    [`(+ ,xs ...) `(+ ,@(map Ex xs))]
    [`(,f ,x) `(app ,(Ex f) ,(Ex x))]
    [_ stx]))

(define (pattern-explicitize stx)
  (define Px pattern-explicitize)
  (match stx
    ['null `(p-lit null)]
    [(? symbol?) `(p-var ,stx)]
    [(? number?) `(p-dat ,stx)] ; or use P==
    ; for now we just leave the following as-is:
    #;[`(P== ,pat) ?]
    #;[`(Papp ,f ,pat) ?]
    #;[`(P? ,pred ,pat) ?]
    #;[`(Pcons ,pcar ,pcdr) ?]
    #;[`(Plist ,a ...) ?]
    [_ stx]))

(define (expand stx)
  (define Ex expand)
  (match stx
    [`(,x → ,body)
     `(,x → ,(Ex body))]
    [`(+ ,xs ...) `(+ ,@(map Ex xs))]
    [`(,f ,x) `(,(Ex f) ,(Ex x))]
    [_ stx]))

(define (interpret env prog)
  (define I (curry interpret env))
  (match prog
    [`(var ,x) (hash-ref env x (λ () (void)))]
    [`(dat ,d) d]
    [`(+ ,xs ...) (apply + (map I xs))]
    [`((p-var ,id) → ,body) `(c: ,id ,body ,env)]
    [`(app ,(app I `(c: ,id ,body ,c-env)) ,(app I a-vals))
     (interpret (hash-set c-env id a-vals) body)]))

; modified interpret for fallthrough
#; (define (interpret env prog)
     (define I (curry interpret env))
     (match prog
       [`(var ,x) (hash-ref env x (λ () (void)))]
       [`(dat ,d) d]
       [`(+ ,xs ...) (apply + (map I xs))]
       [`(app fun) 'function-fallthrough]
       [`(app (fun ,r ,rs ...) ,arg)
        (let ([e-arg (I arg)]
              [whatever (I r)])
          ; or use seperate fn for matching? need to return env...
          (if (equal? 'no-match (I `(blah ,e-arg ,r)))
              (I `((fun ,@rs) e-arg))
              whatever))]
       #;[`(fun [(p-var ,id) → ,body]
                [pat → tem] ...) 0]
       #;[`(blah ,arg (p-lit ,d))
          (if (equal? d (I arg))
              '() ; no bindings?
              'no-match)]
       #;[`(((p-cons a b) → ,tem) ,arg)]
       [`((p-var ,id) → ,body) `(c: ,id ,body ,env)] ; always bind
       [`(app ,(app I `(c: ,id ,body ,c-env)) ,(app I a-vals))
        (interpret (hash-set c-env id a-vals) body)]))


#|

need no-match symbol to handle failure to match

matching attempt 1: expand pattern to lc at compile-time
`(((p-dat d) → expr) whatever)
becomes
(if (== d (eval expr)
     void
     no-match)
p== is same except 'd' gets evald too
`(((p-var d) → expr) target)
is regular evaluation
p? straightforward
as is p-app
`(((p-cons a b) → expr) whatever)
becomes
(if (eval expr) list
(let f (first ee
(let s (second ee

actually: if we know the expr is a cons
`(((p-cons a b) → expr) (cons x y))
`((λ (a) (λ (b) expr) y) x) dummy)
 
(eval `((λ (a) ) whatever)

|#

(module+ test
  (require rackunit)

  (test-equal? "defines -> local lambda app"
               ((compose explicitize expand-top) '((define x 1) x))
               #;'((x → x) 1)
               '(app ((p-var x) → (var x)) (dat 1)))
  
  (test-equal? "multi define"
               ((compose explicitize expand-top) '((define x 1) (define y 2) y))
               #;'((x → ((y → y) 2)) 1)
               '(app ((p-var x) → (app ((p-var y) → (var y)) (dat 2))) (dat 1)))
  
  (test-equal? "multi define 2"
               ((compose explicitize expand-top) '((define x 1) (define y 2) x))
               '(app ((p-var x) → (app ((p-var y) → (var x)) (dat 2))) (dat 1)))
  
  (test-equal? "define scope"
               ((compose explicitize expand-top) '((define x 1) (define y x) y))
               #;'((x → ((y → y) x)) 1)
               '(app ((p-var x) → (app ((p-var y) → (var y)) (var x))) (dat 1)))

  (test-equal? "Numeric literal" (run-interpreter '((define q 1) 3)) 3)

  (test-equal? "addition"
               (run-interpreter '((define q 1) (+ 1 2 (+ (+ 3) 4 5) 6)))
               21)

  #;
  (test-equal? "nullary partial application"
               (run-interpreter '((define f (λ (x) 9))
                                  ((f) 9)))
               9)

  #;
  (test-equal? "0-ary"
               (run-interpreter '((define f (λ () 7))
                                  (f)))
               7)

  (test-equal? "simplest closure"
               (run-interpreter '((define q 1) ((x → x) 1)))
               1)

  #;
  (test-equal? "multivariate application"
               (run-interpreter '((define q 1) ((λ (x y) 1) 2 3)))
               1)

  #;
  (test-equal? "multivariate curried"
               (run-interpreter '((define q 1) (((λ (x y) (+ x y)) 7) 5)))
               12)

  #;
  (test-equal? "intermediate fn"
               (run-interpreter '((define f ((λ (x y) (+ x y)) 7))
                                  (f 5)))
               12)

  #;
  (test-equal? "rube goldberg"
               (run-interpreter '((define f ((λ (x y) (+ x y)) 7))
                                  (define g ((λ (x y z) (+ (f 2) (+ x z))) 6))
                                  (define h (g 4))
                                  (f (h 1))))
               23)

  #;
  (test-equal? "ignore errors within uncalled lambdas?"
               (run-interpreter '((define f (λ () (bad blood))) 0))
               0)

  #;
  (test-exn "non-numeric return"
            (to-regexp ERROR-wot)
            (lambda () (run-interpreter '((define q 1)(λ (x) x)))))

  #;
  (test-exn "duplicate names"
            (to-regexp ERROR-dup)
            ; Note that the `run-interpreter` call is wrapped in a function to
            ; *delay evaluation*. More on that in class!
            (lambda () (run-interpreter '((define f 0)
                                          (define g 1)
                                          (define f 2)
                                          (f (h 1))))))

  #;
  (test-exn "nullary application on unary fn"
            (to-regexp ERROR-wot)
            (lambda () (run-interpreter '((define f (λ (x) 0))
                                          (f)))))


  #;
  (test-exn "nullary function too many args"
            (to-regexp ERROR-tma)
            (lambda () (run-interpreter '((define f (λ () 0))
                                          (f 1)))))
  #;
  (test-exn "too many args"
            (to-regexp ERROR-tma)
            ; Note that the `run-interpreter` call is wrapped in a function to
            ; *delay evaluation*. More on that in class!
            (lambda () (run-interpreter '((define f (λ (x y z) (+ x y z)))
                                          (f 1 2 3 4)))))

  #;
  (test-exn "call add on function"
            (to-regexp ERROR-pte)
            (lambda () (run-interpreter '((define q 1)(+ 1 (λ (x) x))))))

  ; This test illustrates how to check that an appropriate exception is raised.
  #; (test-exn "Simple undefined identifier test"
               (to-regexp ERROR-uid)
               (lambda () (run-interpreter '((define q 1) a))))


  #;
  (test-equal? "..."
               (run-interpreter '((x → x) 1))
               1)

  #;
  (test-equal? "..."
               (run-interpreter '((x → x) 1))
               1)

  


  )
