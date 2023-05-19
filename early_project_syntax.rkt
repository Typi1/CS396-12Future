#lang racket

(require redex)

;; NOTES FOR LATER REVIEW
;; - note that with the current transition function for the C machine, a regular bind and future bind aren't inherantly equal
;; this is because we can use the form (let (x M) N) in the syntax to allow for simplification in the M term to a value,
;; but this functionality is missing from the futures ver. To remedy this I added (let (x (future M)) N) to the syntax,
;; but we should ask if we can do that. I'd argue yes, because the purpose of the C-machine in the
;; paper is to be a version of the language where a term with and a term without a future are
;; functionally equivalent. 
;;
;;
;;




;;
;;
;; BASIC SYNTAX
;;
;;

(define-language DefF
  (M N O ::= x
     (let (x v) M)
     (let (x (future M)) N)
     (let (x (car y)) M)
     (let (x (cdr y)) M)
     (let (x (if y M N)) O)
     (let (x (apply y z)) M)
     ) ;; TERMS
  (u v ::= b x (λ (x) M) (cons x y)) ;; VALUES
  (x y z ::= variable-not-otherwise-mentioned) ;; VARS
  (b c ::= nil integer) ;; CONST
  #:binding-forms
  (λ (x) M #:refers-to x)
  (let (x v) M #:refers-to x)
  (let (x (future M)) N #:refers-to x)
  (let (x (car y)) M #:refers-to x)
  (let (x (cdr y)) M #:refers-to x)
  (let (x (if y M N)) O #:refers-to x)
  (let (x (apply y z)) M #:refers-to x)
  )
(default-language DefF)

;;
;;
;; C-MACHINE RUNTIME LANGUAGE
;;
;;

;; additional syntax for runtime
(define-extended-language C
  DefF
  (S ::= M error) ;; state can be a term or an error
  (V ::= c x (λ (x) M) (cons V_1 V_2)) ;; differs from DefF values (runtime values). Note cons having runtime values rather than DefF values
  (F ::= V error) ;; final state must be a value or an error (NOT a term)
  (A ::= c procedure (cons A A)) ;; answer is either a constant, the keyword "procedure", or a cons of answers
  (E ::= hole (let (x E) M) (let (x (future E)) M)) ;; evaluation contexts
  (M N O ::= V
     (let (x V) M)
     (let (x (future V)) M)
     (let (x (car V)) M)
     (let (x (cdr V)) M)
     (let (x (if V M N)) O)
     (let (x (apply V V)) M)
     (let (x M) N)
     (let (x (future M)) N) ;; ASK IF WE CAN DO THIS
  ))

;; transition rules
(define -->C
  (reduction-relation
   C
   ;; bind. pops a let statement
   [--> (in-hole E (let (x V) M))
        (in-hole E (substitute M x V))
   ;;[--> (let (x_1 E) (let (x_2 V) M))
   ;;     (let (x_1 E) (substitute M x_2 V))
    bind]
   
   ;; future-id. same as bind here since future has no current functionality differences. pops a let statement
   [--> (in-hole E (let (x (future V)) M))
        (in-hole E (substitute M x V))
   ;;[--> (let (x_1 E) (let (x_2 (future V)) M))
   ;;     (let (x_1 E) (substitute M x_2 V))
    future-id]
   ;; car. pops a let statement
   [--> (in-hole E (let (x (car (cons V_1 V_2))) M))
        (in-hole E (substitute M x V_1))
   ;;[--> (let (x_1 E) (let (x_2 (car (cons V_1 V_2))) M))
   ;;     (let (x_1 E) (substitute M x_2 V_1))
    car]
   [--> (in-hole E (let (x (car V)) M))
   ;;[--> (let (x_1 E) (let (x_2 (car V)) M))
        error ;; if car is called on a value that isn't cons
    car_fail]
   ;; cdr. pops a let statement
   [--> (in-hole E (let (x (cdr (cons V_1 V_2))) M))
        (in-hole E (substitute M x V_2))
   ;;[--> (let (x_1 E) (let (x_2 (cdr (cons V_1 V_2))) M))
   ;;     (let (x_1 E) (substitute M x_2 V_2))
    cdr]
   [--> (in-hole E (let (x (cdr V)) M))
   ;;[--> (let (x_1 E) (let (x_2 (cdr V)) M))
        error ;; if cdr is called on a value that isn't cons
    cdr_fail]
   ;; if. pops a let statement and pushes a new one
   [--> (in-hole E (let (x (if nil M_1 M_2)) M_3)) ;; if the value is nil, then choose M_2
        (in-hole E (let (x M_2) M_3))
        if_else]
   [--> (in-hole E (let (x (if V M_1 M_2)) M_3)) ;; if the value is NOT nil, then choose M_1
        (in-hole E (let (x M_1) M_3))
        if_then
    ]
   ;;[--> (let (x_1 E) (let (x_2 (if nil M_1 M_2)) M_3)) ;; if the value is nil, then choose M_2
   ;;     (let (x_1 E) (let (x_2 M_2) M_3))
   ;; if_else] 
   ;;[--> (let (x_1 E) (let (x_2 (if V M_1 M_2)) M_3)) ;; if the value is NOT nil, then choose M_1
   ;;     (let (x_1 E) (let (x_2 M_1) M_3))
   ;; if_then]
   
   ;; apply. pops a let statement and pushes a new one
   [--> (in-hole E (let (x (apply (λ (y) N) V)) M))
        (in-hole E (let (x (substitute N y V)) M))
        apply]
   ;;[--> (let (x_1 E) (let (x_2 (apply (λ (y) N) V)) M)) ;; successful apply where the first value is a function
   ;;     (let (x_1 E) (let (x_2 (substitute N y V)) M)) 
   ;; apply]
   [--> (in-hole E (let (x (apply V_1 V_2)) M))
        error
        (side-condition (not (redex-match? C (λ (x) M) (term V_1))))
        apply_fail]
   ;;[--> (let (x_1 E) (let (x_2 (apply V_1 V_2)) M)) ;; if the first value isn't a function, error
   ;;     error
   ;;     (side-condition (not (redex-match? C (λ (x) M) (term V_1)))) 
   ;; apply_fail]
   

   
   ))



;; load function
(define (load-C p)
  (cond
    [(redex-match? C M p) (term ,p)]
    [else (raise "load: expected a valid C program")]))

;; unload function
(define-metafunction C
  unload-C : V -> A
  [(unload-C c)
   c]
  [(unload-C (λ (x) M))
   procedure]
  [(unload-C (cons V_1 V_2))
   (cons (unload-C V_1) (unload-C V_2))]
  )

;; evaluator function
;; load input term into C, evaluate, then return either unload or error
(define (eval-C inp)
  (let ([res (first (apply-reduction-relation*
                      -->C
                      (load-C (term ,inp))))])
    ;;(print (term ,res))
    (cond
      [(and (redex-match? C V (term ,res)) (not (redex-match? C x (term ,res)))) (term (unload-C ,res))
                                      ]
      [else (term error)]
      )))


;(redex-match? C M (term (let (x (apply y z)) x)
;                        ))
;   
;(load-C (term (let (x 2) x)))
;
;(apply-reduction-relation*
;  -->C
;  (load-C (term (let (y 2) y))
;          ))
;
;(apply-reduction-relation*
;  -->C
;  (load-C (term (let (y 2) (let (x 3) (let (z 1) x))))
;          ))
;
;(traces
;  -->C
;  (load-C (term (let (y 2) (let (x 3) (let (z 1) x))))
;          ))
;
;
;(apply-reduction-relation*
;  -->C
;  (load-C (term (let (y (λ (x) x)) (let (z 2) (let (x (apply y z)) x))))
;          ))
;
;(traces -->C (load-C (term (let (y (λ (x) x)) (let (z 2) (let (x (apply y z)) x))))
;          ))
;
;(apply-reduction-relation*
; -->C
; (load-C (term (let (y (let (x 2) x)) y))
;         ))

;;
;; test "just value" returns
;;
(test-equal
 (term
  (unload-C
   ,(first
     (apply-reduction-relation*
      -->C  
      (load-C (term
               1
               ))))))
  (term
   1
   )
  )

(test-equal
 (term
  (unload-C
   ,(first
     (apply-reduction-relation*
      -->C  
      (load-C (term
               (λ (x) (let (x 2) x))
               ))))))
  (term
   procedure
   )
  )

(test-equal
 (term
  (unload-C
   ,(first
     (apply-reduction-relation*
      -->C  
      (load-C (term
               (cons 1 (λ (x) x))
               ))))))
  (term
   (cons 1 procedure)
   )
  )
(test-equal
 (eval-C (term 1)) ;; integer
 (term 1))
(test-equal
 (eval-C (term (λ (x) x))) ;; procedure
 (term procedure))
(test-equal
 (eval-C (term (λ (x) (let (y 2) x))))
 (term procedure))
(apply-reduction-relation* ;; just checking the output. Note that this should be fine since a procedure value doesn't need its body to be a value, can be a term. so let is fine in the body position of this.
      -->C  
      (load-C (term
               (λ (x) (let (y 2) x))
               )))
(test-equal
 (eval-C (term (cons 1 (λ (x) x)))) ;; cons of integer and procedure
 (term (cons 1 procedure)))
(test-equal
 (eval-C (term x)) ;; while free id is a valid value, it isn't a valid answer return, so error
 (term error))

;;
;; test bind
;;

;; simple 1 term bindings
(test-equal
 (eval-C (term (let (x 3) x)))
 (term 3))
(test-equal
 (eval-C (term (let (x (λ (x) x)) x)))
 (term procedure))
(test-equal
 (eval-C (term (let (x (cons 1 3)) x)))
 (term (cons 1 3)))
(test-equal
 (eval-C (term (let (x t) x)))
 (term error))

;; nested bindings
(test-equal
 (eval-C (term (let (x 4) (let (y 2) y))))
 (term 2))
(test-equal
 (eval-C (term (let (x 4) (let (y 2) x))))
 (term 4))
(test-equal
 (eval-C (term (let (x 4) (let (x 2) x)))) ;; prioritize inner scope
 (term 2))
(test-equal
 (eval-C (term (let (x (let (y 2) y)) x)))
 (term 2))
(test-equal
 (eval-C (term (let (x (let (x 2) x)) x)))
 (term 2))
(test-equal
 (eval-C (term (let (x (let (x 2) x)) (let (x 10) x))))
 (term 10))
(test-equal
 (eval-C (term (let (x (λ (x) (let (y 4) y))) (let (a (apply x 1)) a)))) ;; sneaky apply test
 (term 4))
(test-equal
 (eval-C (term (let (x 4) (let (y (λ (y) x)) y))))
 (term procedure))
(test-equal
 (eval-C (term (let (x 2) (let (y (cons 1 (λ (x) x))) (let (a (cons x y)) a)))))
 (term (cons 2 (cons 1 procedure))))

;;
;; test future binds
;;

(test-equal
 (eval-C (term (let (x (future 3)) x)))
 (eval-C (term (let (x 3) x))))
(test-equal
 (eval-C (term (let (x (future (λ (x) x))) x)))
 (eval-C (term (let (x (λ (x) x)) x))))
(test-equal
 (eval-C (term (let (x (future (cons 1 3))) x)))
 (eval-C (term (let (x (cons 1 3)) x))))
(test-equal
 (eval-C (term (let (x (future t)) x)))
 (eval-C (term (let (x t) x))))
(test-equal
 (eval-C (term (let (x (future 4)) (let (y (future 2)) y)))) 
 (eval-C (term (let (x 4) (let (y 2) y)))))
(test-equal
 (eval-C (term (let (x (future 4)) (let (y (future 2)) x))))
 (eval-C (term (let (x 4) (let (y 2) x)))))
(test-equal
 (eval-C (term (let (x (future 4)) (let (x (future 2)) x)))) ;; prioritize inner scope
 (eval-C (term (let (x 4) (let (x 2) x)))))
(redex-match? C M (term (let (y (future 2)) y)))
(redex-match? C M (term (let (x (future (let (y (future 2)) y))) x)))
(test-equal
 (eval-C (term (let (x (future (let (y (future 2)) y))) x))) ;; NOTE THIS (and some others below) DOESN'T WORK IF THE ADDED SYNTAX ISN'T PRESENT bc then nothing matches the future with a term M (that evaluates to V) instead of direct V
 (eval-C (term (let (x (let (y 2) y)) x))))
(test-equal
 (eval-C (term (let (x (future (let (x 2) x))) x)))
 (eval-C (term (let (x (let (x 2) x)) x))))
(test-equal
 (eval-C (term (let (x (future (let (x 2) x))) (let (x (future 10)) x))))
 (eval-C (term (let (x (let (x 2) x)) (let (x 10) x)))))
(test-equal
 (eval-C (term (let (x (future (λ (x) (let (y (future 4)) y)))) (let (b (future (let (a (apply x 1)) a))) b)))) ;; sneaky apply test
 (term 4))
(test-equal
 (eval-C (term (let (x 4) (let (y (future (λ (y) x))) y))))
 (eval-C (term (let (x 4) (let (y (λ (y) x)) y)))))
(test-equal
 (eval-C (term (let (x 2) (let (y (future (cons 1 (λ (x) x)))) (let (a (cons x y)) a)))))
 (eval-C (term (let (x 2) (let (y (future (cons 1 (λ (x) x)))) (let (a (future (cons x y))) a))))))

;;
;; test car and cdr
;;

(test-equal
 (eval-C (term (let (x (car (cons 1 2))) x)))
 (term 1))
(test-equal
 (eval-C (term (let (x (cdr (cons 1 2))) x)))
 (term 2))
(test-equal
 (eval-C (term (let (x (cons 1 2)) (let (y (cons x 3)) (let (a (car y)) a)))))
 (term (cons 1 2)))
(test-equal
 (eval-C (term (let (x (cons 1 2)) (let (y (cons x 3)) (let (a (cdr y)) a)))))
 (term 3))
(test-equal
 (eval-C (term (let (x (cons 1 2)) (let (y (cons x 3)) (let (b (car (let (a (car y)) a))) b)))))
 (term 1))
(test-equal
 (eval-C (term (let (x (cons 1 2)) (let (y (cons x 3)) (let (b (cdr (let (a (car y)) a))) b)))))
 (term 2))

(test-results)