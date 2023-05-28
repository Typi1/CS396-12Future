#lang racket

(require redex)

;; NOTES FOR LATER REVIEW
;; 
;; pairs are treated as PValue, when they aren't necessarily.
;;
;;




;;
;;
;; BASIC SYNTAX
;;
;;

(define PCounter 0)

(define-language DefF
  (M N O ::= x
     v
     (let (x v) M)
     (let (x (future M)) N)
     (let (x (car y)) M)
     (let (x (cdr y)) M)
     (let (x (if y M N)) O)
     (let (x (apply y z)) M)
     
     ) ;; TERMS
  (u v ::= b x (λ (x) M) (cons v v) (car y)) ;; VALUES
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
(define-extended-language PCEK
  DefF
  (ErrorString string)
  (S ::= (M E K) error (f-let (p S_1) S_2) (error ErrorString))
  ;(E ::= ((x V) ...)) ;; eval context var -> value
  (E ::= () (x V E)) ;; eval context var -> value
  (b c ::= nil integer) ;; 
  (PValue ::=  c x ((λ (x) M) E) pair)
  (pair ::= (cons PValue PValue))
  (V ::= PValue (ph p mt) (ph p V)) ;; differs from DefF values (runtime values). Note cons having runtime values rather than DefF values
  (p ::= string) ; TODO should this be a variable?
  (A ::= c procedure (cons A A)) ;; answer is either a constant, the keyword "procedure", or a cons of answers
  (activation-record ::= (ar x M E) (ar-t x M E))
  (K ::= mt (activation-record K))
  (F ::= (x E mt) error) ;; final state must be a value or an error (NOT a term)
)

(define-metafunction PCEK
  generate-p : -> p
  [(generate-p) ,(symbol->string (gensym))]) ; also can do by counting largest p
  ;[(generate-p) ,(begin (set! PCounter (add1 PCounter))
   ;                     PCounter)])

(define-metafunction PCEK
  match-p : p_1 p_2 -> boolean
  [(match-p p_1 p_1) #t]
  [(match-p p_1 p_2) #f])

;(define-metafunction PCEK
;  lookup : x E -> V
;  [(lookup x ((x V) (x_1 V_1) ...)) V]
;  [(lookup x ((x_1 V_1) (x_2 V_2) ...)) (lookup x ((x_2 V_2) ...))]
;  [(lookup x ()) error])

(define-metafunction PCEK
  lookup : x E -> V
  [(lookup x ()) error]
  [(lookup x (x V E)) V]
  [(lookup x (x_1 V_1 E_1)) (lookup x E_1)])

;(define-metafunction PCEK
;  extend : x V E -> E
;  [(extend x V ((x_1 V_1) ...)) ((x V) (x_1 V_1) ...)])

(define-metafunction PCEK
  extend : x V E -> E
  [(extend x V E) (x V E)])

;(define-metafunction PCEK
;  update-p : p V E -> E
;  [(update-p p V ((x_1 V_1) ... (x (ph p mt)) (x_2 V_2) ...))
;   ((x_1 V_1) ... (x (ph p V)) (x_2 V_2) ...)]
;  [(update-p p V ()) error])

(define-metafunction PCEK
  update-p : p V E -> E
  [(update-p p V ()) ()]
  [(update-p p V (x (ph p mt) E_1)) (x (ph p V) (update-p p V E_1))]
  [(update-p p V (x V_1 E_1)) (x V_1 (update-p p V E_1))]
  )

(define-metafunction PCEK
  unload-PCEK : V -> A
  [(unload-PCEK c)
   c]
  [(unload-PCEK (λ (x) M))
   procedure]
  [(unload-PCEK (cons V_1 V_2))
   (cons (unload-PCEK V_1) (unload-PCEK V_2))]
  [(unload-PCEK (ph p V))
   (unload-PCEK V)]
  )

(define-metafunction PCEK
  touch : V -> V or mt ; TODO FIX ANY
  [(touch (ph p mt))
   mt]
  [(touch (ph p V))
   V]
  [(touch PValue) PValue]
  )

(define-metafunction PCEK
  substitute-S : S p V -> S
  [(substitute-S (f-let (p S_1) S_2) p V)
   (f-let (p (substitute-S S_1 p V)) S_2)]
  [(substitute-S (f-let (p_1 S_1) S_2) p V)
   (f-let (p_1 (substitute-S S_1 p V)) (substitute-S S_2 p V))]
  [(substitute-S (M E K) p V)
   (M (substitute-E E p V) (substitute-K K p V))]
  [(substitute-S error p V)
   error]
  )

(define-metafunction PCEK
  substitute-E : E p V -> E
  [(substitute-E E p V) (update-p p V E)]
  )

(define-metafunction PCEK
  substitute-K : K p V -> K
  [(substitute-K mt p V)
   mt]
  [(substitute-K ((ar x M E) K) p V)
   ((ar x M (substitute-E E p V)) (substitute-K K p V))]
  [(substitute-K ((ar-t x M E) K) p V)
   ((ar-t x M (substitute-E E p V)) (substitute-K K p V))]
  )

(define-metafunction PCEK
  -->R : S -> S or none
  [(-->R S)
   ,(let ([state (apply-reduction-relation -->PCEK (term S))])
      (cond
        [(equal? state '()) (term none)]
        [else (term ,(first state))]))])

;(define-metafunction PCEK
;  contains-free M x -> #t or #f
  
  


;;
;;
;; TRANSITION RULES
;;
;;

(define -->PCEK
  (reduction-relation
   PCEK
   [--> ((let (x c) M) E K)
        (M (extend x c E) K)
        bind-const]
   
   [--> ((let (x y) M) E K)
        (M (extend x (lookup y E) E) K)
        bind-var]
   
   [--> ((let (x (λ (y) N)) M) E K)
        (M (extend x ((λ (y) N) E) E) K) ; TODO should use FV(N)
        bind-lam]

   [--> ((let (x (cons y_1 y_2)) M) E K)
        (M (extend x (cons PValue_1 PValue_2) E) K)
        (where PValue_1 (touch (lookup y_1 E)))
        (where PValue_2 (touch (lookup y_2 E)))
        bind-cons]

   [--> (x E ((ar y M E_1) K))
        (M (extend y (lookup x E) E_1) K)
        return]

   [--> ((let (x (car y)) M) E K)
        (M (extend x V_1 E) K)
        (where (cons V_1 V_2) (touch (lookup y E)))
        car]

   [--> ((let (x (car y)) M) E K)
        error
        (side-condition (not (redex-match? PCEK mt (term (touch (lookup y E))))))
        (side-condition (not (redex-match? PCEK pair (term (touch (lookup y E))))))
        car-fail]

   [--> ((let (x (cdr y)) M) E K)
        (M (extend x V_2 E) K)
        (where (cons V_1 V_2) (touch (lookup y E)))
        cdr]

   [--> ((let (x (cdr y)) M) E K)
        error
        (side-condition (not (redex-match? PCEK mt (term (touch (lookup y E))))))
        (side-condition (not (redex-match? PCEK pair (term (touch (lookup y E))))))
        cdr-fail]
   
   [--> ((let (x (if y M_1 M_2)) M) E K)
        (M_2 E ((ar x M E) K))
        (side-condition (redex-match? PCEK nil (term (touch (lookup y E)))))
        if-else]

   [--> ((let (x (if y M_1 M_2)) M) E K)
        (M_1 E ((ar x M E) K))
        (side-condition (not (redex-match? PCEK nil (term (touch (lookup y E))))))
        (side-condition (not (redex-match? PCEK mt (term (touch (lookup y E))))))
        if-then]

   [--> ((let (x (apply y z)) M) E K)
        (N (extend x_* (touch (lookup z E)) E_*) ((ar x M E) K))
        (where ((λ (x_*) N) E_*) (touch (lookup y E)))
        apply]

   [--> ((let (x (apply y z)) M) E K)
        error
        (side-condition (not (redex-match? PCEK ((λ (x_*) N) E_*) (term (touch (lookup y E))))))
        (side-condition (not (redex-match? PCEK mt (term (touch (lookup y E))))))
        apply-fail]

   [--> ((let (x (future N)) M) E K)
        (N E ((ar-t x M E) K))
        future]

   [--> (x E ((ar-t y M E_1) K))
        (M (extend y (lookup x E) E_1) K)
        future-id]

   [--> (M E (activation-record_1 ((ar-t x N E_1) K_2)))
        (f-let (p (M E (activation-record_1 mt))) (N (extend x (ph p mt) E_1) K_2))
        (where p (generate-p))
        fork]

   [--> (f-let (p (x E mt)) S)
        (substitute-S S p (touch (lookup x E)))
        join]

   [--> (f-let (p error) S)
        error
        join-error]

   [--> (f-let (p_2 (f-let (p_1 S_1) S_2)) S_3)
        (f-let (p_1 S_1) (f-let (p_2 S_2) S_3)) ; TODO? p1 not in FP(S_3)
        lift]

   [--> (f-let (p S_1) S_2)
        (f-let (p S_1*) S_2)
        (where S_1* (-->R S_1))
        parallel_S1]

   [--> (f-let (p S_1) S_2)
        (f-let (p S_1) S_2*)
        (where S_2* (-->R S_2))
        ;(where none (-->R S_1))
        parallel_S2]
   ))


(define (load-PCEK p)
  (cond
    [(redex-match? PCEK M p) (term (,p () mt))]
    [else (raise "load: expected a valid PCEK program")]))


;; evaluator function
;; load input term into PCEK, evaluate, then return either unload or error
(define (eval-PCEK inp)
  (let ([res (first (apply-reduction-relation*
                     -->PCEK
                     (load-PCEK (term ,inp))))])
    (cond
      [(equal? res 'error) 'error]
      [else (term (unload-PCEK (lookup ,(first res) ,(second res))))])))


(define (all-equal? lst)
  (cond
    [(empty? (rest lst))
     #t]
    [else
     (and (equal? (first lst) (second lst)) (all-equal? (rest lst)))]))


(define (eval res)
  (cond
    [(equal? res 'error) 'error]
    [else (term (unload-PCEK (lookup ,(first res) ,(second res))))]))


(define (eval-S inp)
  (let* ([res (apply-reduction-relation* -->PCEK (term ,inp))]
         [as (map eval res)])
    (cond
      [(not (all-equal? as)) (term (error "multiple outcomes"))]
      [else (first as)])))

;
;
;
; TESTS

(test-equal
 (eval-PCEK (term (let (y 2) (let (x 3) (let (z 1) x)))))
 (term 3))

(test-equal
 (eval-PCEK
  (term
   (let (y 1) (let (x (car y)) x))
   ))
 (term error))

(test-equal
 (eval-PCEK
  (term
   (let (a 1)
     (let (b 2)
       (let (y (cons a b))
         (let (x (car y)) x))))
   ))
 (term 1))

(test-equal
 (eval-PCEK
  (term
   (let (x 3) (let (y (future x)) y))
   ))
 (term 3))

(test-equal
 (eval-PCEK
  (term
   (let (c1 nil)
     (let (c2 3)
       (let (c3 4)
         (let (x (λ (y)
                   (let (z (if y c2 c3)) z)))
           (let (y 1)
             (let (z (apply x y))
               z))))))
   ))
 (term 3))



(test-equal
 (eval-PCEK
  (term
   (let (c1 nil)
     (let (c2 3)
       (let (c3 4)
         (let (x (λ (y)
                   (let (z (if y c2 c3)) z)))
           (let (y nil)
             (let (z (apply x y))
               z))))))
   ))
 (term 4))

(test-equal
 (eval-PCEK
  (term
   (let (x (future
            (let (c1 1)
              (let (c2 2)
                (let (c3 3)
                  (let (c4 (if c1 c2 c3)) c4))))))
     x)
   ))
 (term 2))

(test-equal
 (eval-PCEK
  (term
   (let (x (future
            (let (c1 nil)
              (let (c2 2)
                (let (c3 nil)
                  (let (c4 (if c1 c2 c3)) c4))))))
     (let (c5 4)
       (let (c6 5)
         (let (y (if x c5 c6)) y))))
   ))
 (term 5))

(test-equal
 (eval-PCEK
  (term
   (let (x (future
            (let (c1 nil)
              (let (c2 2)
                (let (c3 nil)
                  (let (c4 (if c1 c2 c3)) c4))))))
     (let (y (future
              (let (c7 1) c7)))
       (let (c5 x)
         (let (c6 5)
           (let (z (if x y c6)) z)))))
   ))
 (term 5))

;(test-equal
; (eval-PCEK
;  (term
;      (let (c1 1)
;     (let (c2 2)
;       (let (c3 3)
;         (let (c4 nil)
;           (let (l3 (cons c3 c4))
;             (let (l2 (cons c2 l3))
;               (let (l1 (cons c1 l2))
;                 (let (second (λ (lst)
;                                (let (rest (cdr lst))
;                                  (let (ret (car rest))
;                                    ret))))
;                   (let (l1_sec (future
;                                 (let (l1_sec_temp (apply second l1))
;                                   l1_sec_temp)))
;                     (let (l2_sec (future
;                                   (let (l2_sec_temp (apply second l2))
;                                     l2_sec_temp)))
;                       (let (l3 (cons l1_sec l2_sec))
;                         l3)))))))))))
;
;   ))
; (term (cons 2 3)))


;(traces
; -->PCEK
; (load-PCEK
;  (term
;   (let (x (future
;            (let (c1 1)
;              (let (c2 2)
;                (let (c3 3)
;                  (let (l2 (cons c2 c3))
;                    (let (l1 (cons c1 l2))
;                      l1)))))))
;     (let (y (cdr x))
;       (let (second (λ (lst)
;                      (let (rest (cdr lst))
;                        (let (ret (car rest))
;                          ret))))
;         (let (x2 (future (apply second x)))
;           (let (y2 (future (apply second y)))
;             (let (x2y2 (cons x2 y2))
;               x2y2))))))
;   )))

;(traces
; -->PCEK
; (load-PCEK
;  (term
;   (let (c1 1)
;     (let (c2 2)
;       (let (c3 3)
;         (let (c4 nil)
;           (let (l3 (cons c3 c4))
;             (let (l2 (cons c2 l3))
;               (let (l1 (cons c1 l2))
;                 (let (second (λ (lst)
;                                  (let (ret (car lst))
;                                    ret)))
;                   (let (l1_sec (future
;                                 (let (l1_sec_temp (apply second l1))
;                                   l1_sec_temp)))
;                     (let (l2_sec (future
;                                   (let (l2_sec_temp (apply second l2))
;                                     l2_sec_temp)))
;                       (let (l3 (cons l1_sec l2_sec))
;                         l3)))))))))))
;   )))

(traces
 -->PCEK
 (load-PCEK
  (term
   (let (cnil nil)
     (let (cone 1)
       (let (not (λ (x)
                   (let (ret (if x cnil cone))
                     ret)))
         (let (y (future
                  (let (y_temp (apply not cnil)) y_temp)))
           (let (z (future
                    (let (z_temp (apply not cone)) z_temp)))
                      y)))))
   )))


;(print (apply-reduction-relation*
;                     -->PCEK
;                     (load-PCEK (term
;                                    (let (c1 1)
;     (let (c2 2)
;       (let (c3 3)
;         (let (c4 nil)
;           (let (l3 (cons c3 c4))
;             (let (l2 (cons c2 l3))
;               (let (l1 (cons c1 l2))
;                 (let (second (λ (lst)
;                                  (let (ret (car lst))
;                                    ret)))
;                   (let (l1_sec (future
;                                 (let (l1_sec_temp (apply second l1))
;                                   l1_sec_temp)))
;                     (let (l2_sec (future
;                                   (let (l2_sec_temp (apply second l2))
;                                     l2_sec_temp)))
;                       (let (l3 (cons l1_sec l2_sec))
;                         l3)))))))))))
;                                 ))))



(test-results)











