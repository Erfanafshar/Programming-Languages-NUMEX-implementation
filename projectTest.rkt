#lang racket

(require "project.rkt")

; This file uses Racket's unit-testing framework, which is convenient but not required of you.

(require rackunit)


(define tests
  (test-suite
   "Project Tests"

   ; arithmetic functions test
   (check-equal? (eval-exp (plus (num 2) (num 2))) (num 4) "test1")
   (check-equal? (eval-exp (minus (num -5) (num 2))) (num -7) "test2")
   (check-equal? (eval-exp (mult (num 5) (num 2))) (num 10) "test3")
   (check-equal? (eval-exp (div (num -5) (num -2))) (num 2) "test4")
   (check-exn exn:fail?
              (lambda () (eval-exp (div (num 5) (num 0)))
              "test5"))

   (check-equal? (eval-exp (plus (num -5) (neg (minus (num -2) (num 3)))))
                           (num 0) "test6")

    (check-equal? (eval-exp (neg (mult (num 5) (plus
                                                (div (num -2) (num 3))
                                                (minus (num 1) (num -1)
                                                       )))))
                           (num -10) "test7")
   (check-exn exn:fail?
              (lambda () (eval-exp (plus (num 5.2) (num 0.0)))
              "test8"))

   

   ; logical functions test
   (check-equal? (eval-exp (andalso (bool #t) (bool #t))) (bool #t) "test9")
   (check-equal? (eval-exp (orelse (bool #t) (bool #f))) (bool #t) "test10")
   (check-equal? (eval-exp (orelse (bool #t) (num 2))) (bool #t) "test12")
   (check-equal? (eval-exp (andalso (bool #f) (div (num 2) (num 0)))) (bool #f) "test13")
   (check-equal? (eval-exp (andalso (bool #t) (neg (bool #t)))) (bool #f) "test14")
   (check-equal? (eval-exp (orelse (iseq (num 2) (num 2)) (bool #f))) (bool #t) "test15")
   (check-equal? (eval-exp (neg (iseq (bool #t) (bool #f)))) (bool #t) "test16")
   (check-equal? (eval-exp (iseq (num 2) (bool #f))) (bool #f) "test17")
   (check-equal? (eval-exp (iseq (num 2) (num -2))) (bool #f) "test18") 
   (check-equal? (eval-exp (neg (ismunit (apair (num 3) (munit))))) (bool #t) "test19")

   (check-exn exn:fail?
              (lambda () (eval-exp (plus (num 5) (bool #t)))
              "test20"))
(check-exn exn:fail?
              (lambda () (eval-exp (minus (bool #f) (bool #t)))
              "test21"))
(check-exn exn:fail?
              (lambda () (eval-exp (div (num 5) (bool #f)))
              "test22"))
(check-exn exn:fail?
              (lambda () (eval-exp (mult (bool #t) (num -2)))
              "test23"))
   (check-exn exn:fail?
              (lambda () (eval-exp (num "hi"))
              "test24"))
     (check-exn exn:fail?
              (lambda () (eval-exp (num (num 3)))
              "test25"))
   (check-exn exn:fail?
              (lambda () (eval-exp (bool (bool #t)))
              "test26"))
   (check-exn exn:fail?
              (lambda () (eval-exp (plus (munit) (num 2)))
              "test27"))
   (check-exn exn:fail?
              (lambda () (eval-exp (1st (munit)))
              "test28"))
   (check-exn exn:fail?
              (lambda () (eval-exp (2nd (num 3)))
              "test29"))



        
(check-equal? (eval-exp (neg (num 0))) (num 0) "test30")
(check-equal? (eval-exp (neg (neg (num -11)))) (num -11) "test31")
   
   ; condition
   (check-equal? (eval-exp (cnd (bool #t) (plus (num 1) (num 2)) (num "-1"))) (num 3) "test32")
   (check-equal? (eval-exp (cnd (iseq (bool #t) (bool #f)) (munit) (bool #f))) (bool #f) "test33")
   (check-equal? (eval-exp (cnd (bool #f) (num 2) (bool #t))) (bool #t) "test34")
(check-exn exn:fail?
              (lambda () (eval-exp (cnd (num 2) (num 2) (bool #t)))
              "test35"))

(check-exn exn:fail?
              (lambda () (eval-exp (cnd (munit) (num 2) (bool #t)))
              "test36"))

(check-equal? (eval-exp (cnd (andalso (neg (bool #t)) (bool 2))
                             (plus (num 1) (num 2))
                             (mult (num -1) (num -2))
                             )) (num 2) "test37")


   (check-equal? (eval-exp (ifnzero (num 4) (num 1) (num 0))) (num 1) "test38")
   (check-equal? (eval-exp (ifnzero (mult (num 0) (num 4)) (num 1) (bool #t))) (bool #t) "test39")
  (check-exn exn:fail?
              (lambda () (eval-exp (ifnzero (bool #t) (num 2) (bool #t)))
              "test40"))

     (check-exn exn:fail?
              (lambda () (eval-exp (var munit)))
              "test41")

     (check-exn exn:fail?
              (lambda () (eval-exp (var (num 2))))
              "test42")

     (check-exn exn:fail?
              (lambda () (eval-exp (div (munit) (bool #f)))
              "test43"))
     
   (check-exn exn:fail?
              (lambda () (eval-exp (neg (munit))))
              "test44")

   (test-equal? "test46"
    (list (num 3) (num 4) (bool #t))
    (numexlist->racketlist (apair (num 3) (apair (num 4) (apair (bool #t) (munit))))))


(test-equal? "test47"
    (apair (list (num 42) (var "x")) (apair (list (bool #t) (var "y")) (munit)))
    (racketlist->numexlist (list (list (num 42) (var "x")) (list (bool #t) (var "y"))))
  )

  (test-equal? "test48"
   (apair (var "foo") (apair (num 17) (munit)))
   (racketlist->numexlist (list (var "foo") (num 17))))


         
   (check-equal? (racketlist->numexlist '(1 #t 3 #f))
                  (apair 1 (apair #t (apair 3 (apair #f (munit))))) "test49")
   (check-equal? (racketlist->numexlist '()) (munit) "test50")
   
   (check-equal? (numexlist->racketlist (apair #t (apair 2 (apair #f (apair 4 (munit))))))
                  '(#t 2 #f 4) "test51")
   (check-equal? (numexlist->racketlist (munit)) '() "test52")
   

  
   (check-equal? (eval-exp (ifleq (num 4) (num 5) (num 1) (bool #t))) (num 1) "test53")
   (check-equal? (eval-exp (ifleq (num 4) (num 4) (bool #f) (munit))) (bool #f) "test54")
   (check-equal? (eval-exp (ifleq (num 4) (num -4) (num 1) (num 0))) (num 0) "test55")
  
(check-exn exn:fail?
              (lambda () (eval-exp (ifleq (bool #t) (num -4) (num 1) (num 0))))
              "test56")
(check-exn exn:fail?
              (lambda () (eval-exp (ifleq (apair (munit) (munit)) (num -4) (num 1) (num 0))))
              "test57")

(test-equal? "test58"
               (num 2)
               (eval-exp (with "f1"
                               (lam "f1" "a" (with "x" (var "a") (lam "f2" "z" (plus (var "x") (num 1)))))
                               (with "f3" (lam "f3" "f" (with "x" (num 1729) (apply (var "f") (munit)))) 
                                     (apply (var "f3") (apply (var "f1") (num 1)))))))

(test-equal? "test59"
               (num 43)
               (eval-exp (apply (lam "incr" "x" (plus (var "x") (num 1))) (num 42))))


(test-equal? "test60"
               (bool #t)
               (eval-exp (apply (lam "neg" "x" (neg (var "x"))) (bool #f))))


(test-equal? "test61"
               (num 10)
               (eval-exp (apply (lam "mul" "x" (neg (mult (var "x") (num 2)))) (num -5))))

(test-equal? "test62"
               (bool #f)
               (eval-exp (ifleq (plus (num 3) (num 2)) (mult (num 2) (num 5))
                                (andalso (bool #t) (bool #f)) (neg (plus "wrong" "bad")))))

(test-equal? "test63"
               (num 2)
               (eval-exp (ifnzero (plus (num 2) (num -2))
                                  (neg (plus "wrong" "bad"))
                                  (mult (num 2) (num 1)))))

   (check-equal? (eval-exp (with "s" (num 4)
                                 (div (num 12) (var "s")))) (num 3) "test64")

  (test-equal? "test65"
     (apair (num 21) (bool #t))
     (eval-exp (apair (1st (apair (mult (num 7) (num 3)) (num 2)))
                 (2nd (apair (num 3) (bool #t)))
                 )))

   
   (check-equal? (eval-exp (1st (apair (num 3) (bool #t)))) (num 3) "test67")
   (check-equal? (eval-exp (2nd (apair (num 3) (bool #t)))) (bool #t) "test68")
   (check-equal? (eval-exp (ismunit (munit))) (bool #t) "test69")
   (check-equal? (eval-exp (apply (lam "a" "b" (ifleq (var "b") (num 5) (plus (var "b") (num 3))
                                                      (apply (var "a") (mult (num 2) (num 3)))))
                                  (num 2))) (num 5) "test70")
   
(check-equal? (eval-exp (apply (lam "fact" "n" 
           (cnd (iseq (var "n") (num 0)) 
                   (num 1) 
                   (mult (var "n") (apply (var "fact") (minus (var "n") (num 1))
           )))) (num 5)))
               (num 120) "test71")

   (check-exn exn:fail?
              (lambda () (eval-exp (neg (munit))))
              "test75")
   
   
     (check-exn exn:fail?
              (lambda () (eval-exp (num #t))
              "test80"))

        (check-exn exn:fail?
              (lambda () (eval-exp (bool "hi"))
              "test81"))

         (check-exn exn:fail?
              (lambda () (eval-exp (bool 22))
              "test82"))

         (check-exn exn:fail?
              (lambda () (eval-exp (bool (num 3)))
              "test83"))

         (check-exn exn:fail?
              (lambda () (eval-exp (num (bool #t)))
              "test84"))

   (check-equal? (eval-exp (plus (plus (num 1) (num 2)) (minus (num 3) (num 4)))) (num 2) "test85")
 (check-equal? (eval-exp (mult (mult (num 3) (num 2)) (mult (num 3) (num 4)))) (num 72) "test86")
   (check-exn exn:fail? (lambda () (eval-exp (mult (num 3) (munit)))) "test87")

   (check-equal? (eval-exp (num -5)) (num -5) "test88")
   (check-equal? (eval-exp (munit)) (munit) "test89")
    (check-equal? (eval-exp (closure '() (lam null "x" (var "x"))))
                 (closure '() (lam null "x" (var "x"))) "test90")


    (check-equal? (eval-exp (with "x" (andalso (bool #t) (bool #t)) (orelse (bool #f) (var "x")))) (bool #t) "test 91")
   (check-equal? (eval-exp (with "x" (num 1) (var "x"))) (num 1) "test92")
   (check-exn exn:fail? (lambda () (eval-exp (var "x"))) "test93")
   
    (check-equal? (eval-exp (lam null "x" (var "x")))
                 (closure '() (lam null "x" (var "x"))) "test94")
   (check-equal? (eval-exp (with "x" (num 1) (lam null "a" (var "x"))))
                 (closure (list (cons "x" (num 1))) (lam null "a" (var "x"))) "test95")


      (check-exn exn:fail? (lambda () (eval-exp (ifleq "1" (num 2) (num 3) (num 4)))) "test96")
      (check-exn exn:fail? (lambda () (eval-exp (ifnzero "1" (num 2) (num 3) ))) "test97")

      (check-equal? (eval-exp (apair (num 1) (num 1))) (apair (num 1) (num 1)) "test98")
   (check-equal? (eval-exp (with "x" (num 1) (apair (var "x") (var "x"))))
                 (apair (num 1) (num 1)) "test99")


   (check-equal? (eval-exp (1st (apair (num 1) (bool #t)))) (num 1) "test100")
   (check-equal? (eval-exp (with "x" (apair (num 1) (bool #t)) (1st (var "x")))) (num 1) "test101")
   (check-exn exn:fail? (lambda () (eval-exp (1st (plus (num 1) (num 2))))) "test102")


   (check-equal? (eval-exp (2nd (apair (num 1) (bool #t)))) (bool #t) "test103")
   (check-equal? (eval-exp (with "x" (apair (num 1) (bool #t)) (2nd (var "x")))) (bool #t) "test104")
   (check-exn exn:fail? (lambda () (eval-exp (2nd (plus (num 1) (bool #t))))) "test105")

   (check-equal? (eval-exp (ismunit (munit))) (bool #t) "test106")
   (check-equal? (eval-exp (with "x" (munit) (ismunit (var "x")))) (bool #t) "test107")
   (check-equal? (eval-exp (ismunit (num 0))) (bool #f) "test108")
   (check-equal? (eval-exp (with "x" (num 0) (ismunit (var "x")))) (bool #f) "test109")


   (check-equal? (eval-exp (with "double" (lam "double" "x" (plus (var "x") (var "x")))
                                  (apply (var "double") (num 10))))
                 (num 20) "test110")

      (check-equal?
    (eval-exp
     (with "range"
           (lam "range" "lo"
                (lam null "hi"
                     (ifleq  (var "hi") (var "lo") (munit)
                                (apair (var "lo") (apply (apply (var "range") (plus (num 1) (var "lo"))) (var "hi"))))))
           (apply (apply (var "range") (num 5)) (num 8))))
    (apair (num 5) (apair (num 6) (apair (num 7)  (munit)))) "test111")


      (check-equal?
 (eval-exp (apply (lam "a" "b" (ifleq (num 5) (var "b") (plus (var "b") (num 3))
                         (apply (var "a") (mult (num 2) (num 3))  ))) (num 2))
             )(num 9) "test112")


;;

      (check-equal?
 (eval-exp (apply (apply (apply (lam "a" "b" (lam "x" "y" (lam "w" "r" (neg (mult (plus (var "b") (var "y")) (var "r"))))))
                       (num 2))
                       (num 3))
                       (num 5))
            ) (num -25) "test114")

;;

   (check-exn exn:fail? (lambda () (eval-exp (apply (num 1) (num 2)))) "test116")

      (check-exn exn:fail? (lambda () (eval-exp (list (num 1) (num 2)))) "test117")


(check-equal? (eval-exp (letrec "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1))))) "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1))))) "parameter-number-3" (num 0) (apply (var "is-odd") (num 11)))) (bool #t) "test132")
(check-equal? (eval-exp (letrec "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1))))) "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1))))) "parameter-number-3" (num 0) (apply (var "is-odd") (num 10)))) (bool #f) "test133")
(check-equal? (eval-exp (letrec "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1))))) "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1))))) "parameter-number-3" (num 0) (apply (var "is-even") (num 11)))) (bool #f) "test134")
(check-equal? (eval-exp (letrec "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1))))) "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1))))) "parameter-number-3" (num 0) (apply (var "is-even") (num 10)))) (bool #t) "test135")

(check-equal? (eval-exp (enqueue (num 0) (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (munit))))))) (queue (num 0) (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (munit)))))) "test136")
(check-equal? (eval-exp (enqueue (num 0) (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (queue (num 5) (munit)))))))) (queue (num 0) (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (queue (num 5) (munit))))))) "test137")
(check-equal? (eval-exp (dequeue (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (munit))))))) (queue (num 1) (queue (num 2) (queue (num 3) (munit)))) "test38")
(check-equal? (eval-exp (dequeue (queue (num 1) (queue (num 2) (queue (num 3) (munit)))))) (queue (num 1) (queue (num 2) (munit))) "test39")
(check-equal? (eval-exp (extract (queue (num 1) (queue (num 2) (queue (num 3) (queue (num 4) (munit))))))) (num 4) "test140")
(check-equal? (eval-exp (extract (queue (num 0) (queue (num 1) (queue (num 2) (queue (num 3) (munit))))))) (num 3) "test141")

   ))


(require rackunit/text-ui)
(require rackunit/log)
;; runs the test
;(run-tests tests)


(define result (run-tests tests))

(define out (open-output-file "grade.txt" #:exists 'replace))
(pretty-write (- 100 result) out #:newline? #t)
(pretty-write (test-log) out #:newline? #f)
(close-output-port out)

;(define out2 (open-output-file "summary.txt" #:exists 'replace))
;(write (test-log) out2)
;(close-output-port out2)