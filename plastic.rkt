#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(require racket/hash)

#| plastic!

Plastic is the lambda calculus with pattern-matching and ADTs.

Metaphor (metonym) : Plastic -> Lego -> ADTs

It has no built-in data types; any type you want must be
declared with its define-data form. A define-data form with
only nullary constructors is essentially an enum, and one
with only a single n-ary constructor is essentially a struct.

|#

#; (grammar:
    (prog ((define-data type-id
             constructor-dec
             ...)
           ...
           (define id expr)
           ...
           expr))
    (expr (constructor-instance
           id
           (λ #;type
             (pattern → expr)
             ...)
           (expr expr)
           ))
    (pattern (0-ary-cons-id
              (n-ary-cons-id pattern ...))
             id)
    (constructor-dec (0-ary-cons-id
                      (n-ary-cons-id type-id ...)))
    (constructor-instance (0-ary-cons-id
                           (n-ary-cons-id expr ...)))
    )

#|

Current design factors out all static checking.
(including arity of constructors)
This could be added as a seperate layer

|#

(define (run prog)
  (define types (foldl extract-data #hash() prog))
  #;(println types)
  ((compose (curry interpret types #hash())
            expand-top)
   prog))

(define (expand-top stx)
  (define Ex expand-top)
  (match stx
    ; eliminate data form (which was already extracted)
    [`((define-data ,xs ...) ,ys ...)
     (Ex ys)]
    ; rewrite defines into lambdas
    [`((define ,id ,init) ,expr)
     `((,id → ,(Ex expr)) ,(Ex init))]
    [`((define ,id ,init) ,xs ...)
     `((,id → ,(Ex xs)) ,(Ex init))]
    [_ stx]))


#| this rewrites a sequence of haskell-style inline function
   defs with an expr on the end into a sequence of defines.
   if this was done without the intermediary defines, the
   method needs to be adapted since matching on the (now nested)
   accumulator gets harder. (maybe do it bottom-up?) |#
(define (rewrite-haskdefs stx)
  (foldl
   (λ (c acc)
     (match* (c acc)
       ; first partial def (acc is empty)
       [(`(,fn-name ,params ... → ,body)
         `())
        `((define ,fn-name (λ (,@params → ,body))))]
       ; check if we're still on the same fn
       [(`(,fn-name ,params ... → ,body)
         `(,xs ... (define ,prev-fn-name (λ ,ys ...))))
        (if (equal? fn-name prev-fn-name)
            `(,@xs (define ,prev-fn-name (λ ,@ys (,@params → ,body))))
            `(,@xs (define ,prev-fn-name (λ ,@ys))
                   (define ,fn-name (λ (,@params → ,body)))))]
       ; append trailing expr
       [(expr res) `(,@res ,expr)]))
   '()
   stx))


#| returns a hash containing the type data extracted
   from the define-data forms |#
(define (extract-data stx types)
  (match stx
    [`(define-data ,type ,cs ...)
     (foldl (λ (c env)
              (match c
                [`(,x ,xs ...) (hash-set env x `(,@xs → ,type))]
                ; gADT-style fn type sigs for non-nullary constructors
                [_ (hash-set env c type)]))
            types cs)]
    [_ types]))


(define (interpret types env prog)
  (define (constructor-id? id)
    (hash-has-key? types id))
  (define I (curry interpret types env))
  #;(println prog)
  (match prog
    [(? constructor-id? id) id]
    ; added not clause to make following case less order-dependent
    [`(,(? constructor-id? id) ,(and xs (not (== '→))) ...)
     `(,id ,@(map I xs))]
    [(? symbol? id) (hash-ref env id)]
    
    ; λ here means 'fallthrough' and (_ → _) is actually a lambda
    [`(,pats ... → ,body) `(c: ,env ,body ,@pats)]
    [`(λ ,cases ...) `(c-fall: ,env ,@cases)]

    ; fallthrough case
    [`(,(app I `(c-fall: ,c-env ,cases ...)) ,(app I a-vals) ...)
     (foldl (λ (a-case acc)
              (match acc
                ['no-match (interpret types c-env `(,a-case ,@a-vals))]
                [result result]))
            'no-match
            cases)]

    ; application: notice how pattern-match handles lists
    ; of arguments the same as it does constructors
    [`(,(app I `(c: ,c-env ,body ,pats ...)) ,(app I args) ...)
     (match (pattern-match types c-env args pats)
       ['no-match 'no-match]
       [new-env (interpret types new-env body)])]))


#| matches arg to pat and returns a hash of bound variables.
   probably should specify that pattern-matching shouldn't be
   used in this implementation, but actually using pattern
   matching doesn't really let you gloss over any of the logic.|#
(define (pattern-match types c-env arg pat)
  (define constructor-id?
    (curry hash-has-key? types))
  (cond [(and (constructor-id? pat)
              (equal? arg pat))
         c-env]
        [(and (not (constructor-id? pat))
              (symbol? pat))
         (hash-set c-env pat arg)]
        [(list? pat)
         (foldl (λ (arg pat env)
                  (pattern-match types env arg pat))
                c-env
                arg
                pat)]
        [else 'no-match]))


(module+ test
  (require rackunit)

  (test-equal? "define"
               (expand-top '((define-data Void void)
                             (define x void)
                             x))
               '((x → x) void))
  
  (test-equal? "two defines"
               (expand-top '((define-data Bool
                               true
                               false)
                             (define x true)
                             (define y false)
                             y))
               '((x → ((y → y) false)) true))
  
  (test-equal? "two defines 2"
               (expand-top '((define-data Bool
                               true
                               false)
                             (define x true)
                             (define y false)
                             x))
               '((x → ((y → x) false)) true))
  
  (test-equal? "two defines scope"
               (expand-top '((define-data Void void)
                             (define x void)
                             (define y x)
                             y))
               '((x → ((y → y) x)) void))

  (test-equal? "only literal"
               (run '((define-data Bool
                        true
                        false)
                      (define q true)
                      false))
               'false)

  (test-equal? "simple closure"
               (run '((define-data Bool
                        true
                        false)
                      (define q true)
                      ((x → x) true)))
               'true)

  (test-equal? "cons with var"
               (run '((define-data Bool
                        true
                        false)
                      (define-data List
                        null
                        (cons Bool List))
                      (define a true)
                      (cons true a)))
               '(cons true true))
  
  (test-equal? "cons identity"
               (run '((define-data Bool
                        true
                        false)
                      (define-data List
                        null
                        (cons Bool List))
                      (define identity
                        (λ #;(List → List)
                          (null → null)
                          ((cons a b) → (cons a b))))
                      (identity (cons true true))))
               '(cons true true))

  (test-equal? "cons flip"
               (run '((define-data Bool
                        true
                        false)
                      (define-data List
                        null
                        (cons Bool List))
                      (define flip
                        (λ #;(List → List)
                          (null → null)
                          ((cons a b) → (cons b a))))
                      (flip (cons true null))))
               '(cons null true))
  
  
  (test-equal? "identity 2"
               (run '((define-data Bool
                        true
                        false)
                      (define identity2
                        (λ #;(Bool → Bool)
                          (a → a)))
                      (identity2 true)))
               'true)

  (test-equal? "maybe"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define identity
                        (λ #;(Bool → Bool)
                          (true → true)
                          (false → false)))
                      (just (identity true))))
               '(just true))

  (test-equal? "and"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define and
                        (λ #;(Bool Bool → Bool)
                          (true true → true)
                          (false true → false)
                          (true false → false)
                          (false false → false)))
                      (just (and true false))))
               '(just false))

  (test-equal? "const-left"
               (run '((define-data Bool
                        true
                        false)
                      (define-data Maybe-Bool
                        Nothing
                        (just Bool))
                      (define-data List
                        null
                        (cons Bool List))
                      (define right-proj
                        (λ #;(Bool Bool → Bool)
                          (a true → true)
                          (a b → (cons b a))))
                      (right-proj true false)))
               '(cons false true))

  #;
  (test-equal? "recursive datatype"
               (run-interpreter '((define-data Nat
                                    zero
                                    (S Nat))
                                  (define-data Maybe-Nat
                                    nothing
                                    (just Nat))
                                  ; idea: pred xcept with maybe to handle 0
                                  (define pred
                                    (λ (Nat → Maybe-Nat)
                                      ((S a) → (just a))
                                      (zero → nothing)))
                                  #;(define add
                                      (λ (Nat → (Nat → Nat))
                                        (a → (λ (Nat → Nat) ; or make nested fns not require type ann?
                                               (zero → a) 
                                               ((S b) → (S ((add a) b))))))) ; xcept no recursion...
                                  ; re above: maybe need explicit fun to differentiate from application
                                  (add (S zero) (S (S zero)))))
               0)


  (test-equal? "haskdefs 1"
               (rewrite-haskdefs '((and a true → true)
                                   (and a b → (cons b a))
                                   (id a → a)
                                   true))
               '((define and
                   (λ #;(Bool Bool → Bool)
                     (a true → true)
                     (a b → (cons b a))))
                 (define id
                   (λ #;(Bool → Bool)
                     (a → a)))
                 true))


  )
