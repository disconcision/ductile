#lang racket #| CSC324 SUMMER A1 PROPOSAL |#

(require racket/hash)
(provide run)

#| plastic!

Plastic is the lambda calculus with pattern-matching and ADTs.

Metaphor (metonym) : Plastic -> Lego -> ADTs

It has no built-in data types; any type you want must be
declared with its data form. A data form with
only nullary constructors is essentially an enum, and one
with only a single n-ary constructor is essentially a struct.

|#

#; (grammar:
    (TERMINALS (type-id ; these all form seperate namespaces
                cons-id
                id))
    (prog ((data type-id
                 constructor-dec
                 ...)
           ...
           (define id expr-or-lambda)
           ...
           expr))
    (expr (id
           cons-id
           (cons-id expr ...)
           (id expr ...)))
    (lambda ((λ type
               (pattern → expr)
               ...)))
    (expr-or-lambda (expr
                     lambda))
    (pattern (cons-id
              (cons-id pattern ...)
              id))
    (constructor-dec (cons-id
                      (cons-id type-id ...))))

#|

Current design factors out all static checking.
(including arity of constructors)
This could be added as a seperate layer

|#

(define (run prog)
  (define types (foldl collate-data #hash() prog))
  (static-check types prog)
  (define env-defs (foldl (run-defs types) #hash() prog))
  (interpret types env-defs (last prog)))

(define ((run-defs types) stx env)
  (match stx
    [`(data ,_ ...) env]
    [`(define ,id ,init)
     (hash-set env id (interpret types env init))]
    [_ env]))


#| returns a hash containing the type data extracted
   from the data forms |#
(define (collate-data stx types)
  (match stx
    [`(data ,type ,cs ...)
     (for/fold ([env types])
               ([c cs])
       (match c
         [`(,x ,xs ...) (hash-set env x `(,@xs → ,type))]
         [_ (hash-set env c `(→ ,type))]))]
    [_ types]))

(define ((constructor-id? types) id)
  (hash-has-key? types id))

(define (interpret types env prog)
  (define I (curry interpret types env))
  (match prog
    [(? (constructor-id? types) id) id]
    ; added not clause to make following case less order-dependent
    [`(,(? (constructor-id? types) id) ,(and xs (not (== '→))) ...)
     `(,id ,@(map I xs))]
    [(? symbol? id) (hash-ref env id)]
    
    ; λ here means 'fallthrough' and (_ → _) is actually a lambda
    [`(,pats ... → ,body) `(c: ,env ,body ,@pats)]
    [`(λ ,type ,cases ...) `(c-fall: ,env ,@cases)]

    ; fallthrough case
    [`(,(app I `(c-fall: ,c-env ,cases ...)) ,(app I a-vals) ...)
     (for/fold ([acc 'no-match])
               ([a-case cases])
       (match acc
         ['no-match (interpret types c-env `(,a-case ,@a-vals))]
         [result result]))]

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
  (cond [(and ((constructor-id? types) pat)
              (equal? arg pat))
         c-env]
        [(and (not ((constructor-id? types) pat))
              (symbol? pat))
         (hash-set c-env pat arg)]
        [(list? pat)
         (for/fold ([env c-env])
                   ([a arg]
                    [p pat])
           (if (equal? env 'no-match)
               'no-match
               (pattern-match types env a p)))]
        [else 'no-match]))


(define (static-check types stx)
  (match stx
    [`(λ (,typevec ... → ,_)
        (,ts ... → ,_) ...)
     (if ((compose (curry NE* types typevec)
                   (wrap-nullary-constructors types))
          ts)
         (error "non-exhaustive")
         stx)]
    [(? list?) (map (curry static-check types) stx)]
    [_ stx]))


(define transpose (curry apply map list))

(define (wrap-nullary-constructors types)
  (match-lambda
    [(? list? stx) (map (wrap-nullary-constructors types) stx)]
    [(? (constructor-id? types) c)
     #:when (= 2 (length (hash-ref types c)))
     `(,c)]
    [stx stx]))


(define (NE* types typevec M)

  (define (wildcard? stx)
    (conjoin symbol?
             (disjoin (curry equal? '_)
                      (negate (constructor-id? types)))))
  
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
         [`((,(? (constructor-id? types)) ,_ ...) ,_ ...)
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


