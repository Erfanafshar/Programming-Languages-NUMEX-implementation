;; PL Project - Spring 2020
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) 

;; definition of structures for NUMEX programs

(struct var  (s)                        #:transparent)  ;; a variable
(struct num  (n)                        #:transparent)  ;; a constant integer
(struct bool (b)                        #:transparent)  ;; a boolean value

(struct plus  (e1 e2)                   #:transparent)  ;; addition 
(struct minus  (e1 e2)                  #:transparent)  ;; subtraction
(struct mult  (e1 e2)                   #:transparent)  ;; multiplication
(struct div  (e1 e2)                    #:transparent)  ;; divison
(struct neg  (e1)                       #:transparent)  ;; negation

(struct andalso  (e1 e2)                #:transparent)  ;; logical conjunction
(struct orelse  (e1 e2)                 #:transparent)  ;; logical disjunction

(struct cnd  (e1 e2 e3)                 #:transparent)  ;; conditional expressions
(struct iseq  (e1 e2)                   #:transparent)  ;; comparison expressions
(struct ifnzero  (e1 e2 e3)             #:transparent)  ;; not zero conditional expressions
(struct ifleq  (e1 e2 e3 e4)            #:transparent)  ;; less than or equal conditional expressions

(struct apair  (e1 e2)                  #:transparent)  ;; pair constructor
(struct 1st  (e1)                       #:transparent)  ;; first part of a pair
(struct 2nd  (e1)                       #:transparent)  ;; second part of a pair

(struct munit   ()                      #:transparent)  ;; unit value
(struct ismunit (e)                     #:transparent)  ;; checking for (munit)

(struct queue (e q)                     #:transparent)  ;; queue constructor
(struct enqueue (e q)                   #:transparent)  ;; enter e into q
(struct dequeue (q)                     #:transparent)  ;; delete from q
(struct extract (q)                     #:transparent)  ;; returns queue's top element

(struct with  (s e1 e2)                 #:transparent)  ;; let expressions
(struct letrec (s1 e1 s2 e2 s3 e3 e4)   #:transparent)  ;; a letrec expression for recursive definitions

(struct lam  (name arg body)            #:transparent)  ;; a recursive 1-argument function
(struct apply (func expr)               #:transparent)  ;; function application
(struct closure (env func)              #:transparent)  ;; a function with enviroment to evaluate that function


;; Problem 1

;; Part a
(define (racketlist->numexlist xs)
  (if (null? xs)
      (munit)
      (apair (car xs)(racketlist->numexlist (cdr xs)))
))

;; Part b
(define (numexlist->racketlist xs)
  (if (munit? xs)
      '()
      (cons (apair-e1 xs)(numexlist->racketlist (apair-e2 xs)))
))


;; Problem 2

;; lookup a variable in an environment
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation")]
        [(equal? str (car (car env))) (cdr (car env))]
        [#t (envlookup (cdr env) str)] 
))

(define (eval-exp e)
  (eval-under-env e null
))

(define (eval-under-env e env)
  (cond
    [(var? e)
     (envlookup env (var-s e)
    )]

    [(num? e)
     (cond [(integer? (num-n e)) e]
           [#t (error "not a NUMEX number")]
    )]

    [(bool? e)
     (cond [(boolean? (bool-b e)) e]
           [#t (error "not a NUMEX boolean")]
    )]
    

    [(plus? e) 
     (let ([v1 (eval-under-env (plus-e1 e) env)]
           [v2 (eval-under-env (plus-e2 e) env)])
       (if (and (num? v1)(num? v2))
           (num (+ (num-n v1)(num-n v2)))
           (error "not numbers in NUMEX addition"))
    )]

    [(minus? e)
     (let ([v1 (eval-under-env (minus-e1 e) env)]
           [v2 (eval-under-env (minus-e2 e) env)])
       (if (and (num? v1)(num? v2))
           (num (- (num-n v1)(num-n v2)))
           (error "not numbers in NUMEX subtration"))
    )]

    [(mult? e)
     (let ([v1 (eval-under-env (mult-e1 e) env)]
           [v2 (eval-under-env (mult-e2 e) env)])
       (if (and (num? v1)(num? v2))
           (num (* (num-n v1)(num-n v2)))
           (error "not numbers in NUMEX multiplication"))
    )]

    [(div? e) 
     (let ([v1 (eval-under-env (div-e1 e) env)]
           [v2 (eval-under-env (div-e2 e) env)])
       (if (and (num? v1)(num? v2))
           (if (equal? (num-n v2) 0)
               (error "second number is 0 in NUMEX division")
               (num (quotient (num-n v1)(num-n v2))))
           (error "not numbers in NUMEX division"))
    )]

    [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (cond
             [(num? v1) (num (- (num-n v1)))]
             [(bool? v1) (if(false? (bool-b v1)) (bool #t) (bool #f))]
             [#t (error "not numbers or booleans in NUMEX negation")])
    )]

    
    [(andalso? e)
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (if (bool? v1)
               (if (equal? (bool-b v1) #f) (bool #f) 
                   (let ([v2 (eval-under-env (andalso-e2 e) env)])
                     (if (bool? v2)
                         (bool (bool-b v2))
                         (error "not booleans in NUMEX andalso"))))
               (error "not booleans in NUMEX andalso"))
    )]

    [(orelse? e)
     (let ([v1 (eval-under-env (orelse-e1 e) env)])
       (if (bool? v1)
           (if (equal? (bool-b v1) #t) (bool #t) 
               (let ([v2 (eval-under-env (orelse-e2 e) env)])
                 (if (bool? v2)
                     (bool (bool-b v2))
                     (error "not booleans in NUMEX orelse"))))
           (error "not booleans in NUMEX orelse"))
    )]

    
    [(cnd? e)
          (let ([v1 (eval-under-env (cnd-e1 e) env)])
            (if (bool? v1)
                (if(equal? (bool-b v1) #t)
                   (eval-under-env (cnd-e2 e) env)
                   (eval-under-env (cnd-e3 e) env))
                (error "not a boolean in NUMEX conditional"))
    )]

    [(iseq? e) 
     (let ([v1 (eval-under-env (iseq-e1 e) env)]
           [v2 (eval-under-env (iseq-e2 e) env)])
       (cond
         [(and (num? v1)(num? v2))
          (if (equal? (num-n v1)  (num-n v2)) (bool #t) (bool #f)) ]
         [(and (bool? v1)(bool? v2))
          (if(eq? (bool-b v1)  (bool-b v2)) (bool #t) (bool #f)) ]
         [#t (bool #f)])
    )]

    [(ifnzero? e)
           (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
             (if (num? v1)
                 (if (equal? (num-n v1)  0)
                     (eval-under-env (ifnzero-e3 e) env)
                     (eval-under-env (ifnzero-e2 e) env))
                 (error "not a number in NUMEX ifnzero"))
    )]

    [(ifleq? e)
           (let ([v1 (eval-under-env (ifleq-e1 e) env)]
                 [v2 (eval-under-env (ifleq-e2 e) env)])
              (if (and (num? v1) (num? v2))
                  (if (> (num-n v1) (num-n v2))
                      (eval-under-env (ifleq-e4 e) env)
                      (eval-under-env (ifleq-e3 e) env))
                  (error "not a number in NUMEX ifleq"))
    )]
    

    [(apair? e)
     (let ([v1 (eval-under-env (apair-e1 e) env)]
           [v2 (eval-under-env (apair-e2 e) env)])
       (apair v1 v2)
    )]

    [(1st? e)
     (let ([v1 (eval-under-env (1st-e1 e) env)])
       (if (apair? v1)
           (apair-e1 v1)
           (error "not a pair in NUMEX 1st"))
    )]

    [(2nd? e)
     (let ([v1 (eval-under-env (2nd-e1 e) env)])
       (if (apair? v1)
           (apair-e2 v1)
           (error "not a pair in NUMEX 2nd"))
    )]
    

    [(munit? e) e]

    [(ismunit? e)
     (let ([v1 (eval-under-env (ismunit-e e) env)])
       (if (munit? v1) (bool #t) (bool #f))
    )]
    

    [(queue? e)
	(let ([v1 (eval-under-env (queue-e e) env)]
		  [v2 (eval-under-env (queue-q e) env)])
	(cond 
	[(munit? v2) (queue v1 v2)]
	[(queue? v2) (queue v1 v2)]
	[#t (error "not a queue in NUMEX queue")]
        )
    )]

    [(enqueue? e)
    (let ([v1 (eval-under-env (enqueue-e e) env)]
          [v2 (eval-under-env (enqueue-q e) env)])
      (if (queue? v2)
          (queue v1 v2)
          (error "not a queue in NUMEX enqueue"))
    )]

    [(dequeue? e)
     (let ([v1 (eval-under-env (dequeue-q e) env)])
       (if (queue? v1)
           (let ([v2 (eval-under-env (queue-q v1) env)]
                 [v3 (eval-under-env (queue-e v1) env)])
             (if (munit? v2)
                 (munit)
                 (queue v3 (eval-under-env (dequeue v2) env) )
                 ))
           (error "not a queue in NUMEX dequeue"))
    )]

    [(extract? e)
     (let ([v1 (eval-under-env (extract-q e) env)])
       (if (queue? v1)
           (let ([v2 (eval-under-env (queue-q v1) env)])
             (if (munit? v2)
                 (queue-e v1)
                 (eval-under-env (extract v2) env)
                 ))
           (error "not a queue in NUMEX extract"))
    )]
    

    [(with? e)
     (let ([v1 (eval-under-env (with-e1 e) env)])
       (if (string? (with-s e))
           (eval-under-env (with-e2 e) (cons (cons (with-s e) v1) env))
           (error "not a string in NUMEX with"))
    )]

    [(letrec? e)
     (eval-under-env
      (letrec-e4 e)
      (cons
       (cons (letrec-s1 e) (letrec-e1 e)) 
       (cons
        (cons (letrec-s2 e) (letrec-e2 e))
        (cons
         (cons (letrec-s3 e) (letrec-e3 e))
         env
         )
        )
       )
      )
    ]

    
    [(lam? e)
     (closure env e
    )]

    [(apply? e)
     (let ([clos (eval-under-env (apply-func e) env)])
       (if (closure? clos)
           (let ([exp (eval-under-env (apply-expr e) env)]
                 [fun (closure-func clos)])
             (if (null? (lam-name fun))
                 (eval-under-env (lam-body fun) (cons (cons (lam-arg fun) exp) (closure-env clos)))
                 (eval-under-env (lam-body fun) (cons (cons (lam-name fun) clos) (cons (cons (lam-arg fun) exp) (closure-env clos))))))
           (if (lam? clos)
               (eval-under-env (apply clos (apply-expr e)) env)
               (error "not a closure in NUMEX with")))
    )]

    [(closure? e) e]

    
    [#t
     (error (format "bad NUMEX expression: ~v" e))]
))


        