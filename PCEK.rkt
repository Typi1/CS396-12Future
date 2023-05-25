#lang racket

(require redex)

;; NOTES FOR LATER REVIEW
;; 
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
  (S ::= (M E K) error (f-let (p S_1) S_2))
  (E ::= ((x V) ...)) ;; eval context var -> value
  (b c ::= nil integer) ;; 
  (PValue ::=  c x ((λ (x) M) E) pair)
  (pair ::= (cons V V))
  (p ::= symbol) ; TODO should this be a variable?
  (V ::= PValue (ph p mt) (ph p V)) ;; differs from DefF values (runtime values). Note cons having runtime values rather than DefF values
  (A ::= c procedure (cons A A)) ;; answer is either a constant, the keyword "procedure", or a cons of answers
  (activation-record ::= (ar x M E) (ar-t x M E))
  (K ::= mt (activation-record K))
  (F ::= (x E mt) error) ;; final state must be a value or an error (NOT a term)
  ;(A ::= c procedure (cons A A)) ;; answer is either a constant, the keyword "procedure", or a cons of answers
;  (M N O ::= V
;     (let (x V) M)
;     (let (x (future M)) N)
;     (let (x (car V)) M)
;     (let (x (cdr V)) M)
;     (let (x (if V M N)) O)
;     (let (x (apply V V)) M)
;     (let (x M) N)
;  )
  )

(define-metafunction PCEK
  generate-p : -> p
  [(generate-p) (gensym)]) ; also can do by counting largest p

(define-metafunction PCEK
  match-p : p_1 p_2 -> boolean
  [(match-p p_1 p_1) #t]
  [(match-p p_1 p_2) #f])

(define-metafunction PCEK
  lookup : x E -> V 
  [(lookup x ((x V) (x_1 V_1) ...)) V]
  [(lookup x ((x_1 V_1) (x_2 V_2) ...)) (lookup x ((x_2 V_2) ...))]
  [(lookup x ()) error])

(define-metafunction PCEK
  extend : x V E -> E
  [(extend x V ((x_1 V_1) ...)) ((x V) (x_1 V_1) ...)])

(define-metafunction PCEK
  update-p : p V E -> E
  [(update-p p V ((x (ph p mt)) (x_1 V_1) ...)) ((x (ph p V)) (x_1 V_1) ...)]
  [(update-p p V ((x_1 V_1) (x_2 V_2) ...)) (update p V ((x_2 V_2) ...))]
  [(update-p p V ()) error])

(define-metafunction PCEK
  unload-PCEK : V -> A
  [(unload-PCEK V)
   V]
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
  [(substitute-S (M E K))
   (M (substitute-E E p V) (substitute-K K p V))]
  [(substitute-S error)
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

   [--> ((let (x (cons y z)) M) E K)
        (M (extend x (cons (lookup y E) (lookup z E)) E) K)
        bind-cons]

   [--> (x E ((ar y M E_1) K))
        (M (extend y (lookup x E) E_1) K)
        return]

   [--> ((let (x (car y)) M) E K)
        (M (extend x V_1 E) K)
        (where (cons V_1 V_2) (touch (lookup y E)))
        car]

;   [--> ((let (x (car y)) M) E K)
;        (M (extend x V_1 E) K)
;        (where (V_1 V_2) (touch (lookup y E)))]
;
;   [--> ((let (x (car y)) M) E K)
;        (M (extend x V_1 E) K) ; TODO might be a simpler way to do this
;        (where (V_1 V_2) (touch (lookup y E)))
;        (side-condition (redex-match? PCEK (touch (lookup y E)) (term pair)))]

   [--> ((let (x (car y)) M) E K)
        error
        (side-condition (not (redex-match? PCEK mt (term (touch (lookup y E))))))
        (side-condition (not (redex-match? PCEK pair (term (touch (lookup y E))))))
        car-fail]

   [--> ((let (x (cdr y)) M) E K)
        (M (extend x (cdr (touch (lookup y E))) E) K)
        (side-condition (redex-match? PCEK pair (term (touch (lookup y E)))))
        cdr]

   [--> ((let (x (cdr y)) M) E K)
        error
        (side-condition (not (redex-match? PCEK (touch (lookup y E)) (term mt))))
        cdr-fail]
   
   [--> ((let (x (if y M_1 M_2)) M) E K)
        (M_2 E ((ar x M E) K))
        (side-condition (redex-match? PCEK (touch (lookup y E)) (term nil)))
        if-else]

   [--> ((let (x (if y M_1 M_2)) M) E K)
        (M_1 E ((ar x M E) K))
        (side-condition (not (redex-match? PCEK (touch (lookup y E)) (term mt))))
        if-then]

   ;[--> ((let (x (apply y z)) M) E K)  USE WHERE

   [--> ((let (x (future N)) M) E K)
        (N E ((ar-t x M E) K))
        future]

   [--> (x E ((ar-t y M E_1) K))
        (M (extend y (lookup x E) E_1) K)
        future-id]

   [--> (M E (activation-record_1 ((ar-t x N E_1) K_2)))
        (f-let (p (M E (activation-record_1 mt))) (N (extend x (ph (generate-p) mt) E_1) K_2))
        fork]

   [--> (f-let (p (x E mt)) S)
        (substitute-S S p (lookup x E))
        join]

   [--> (f-let (p error) S)
        error
        join-error]

   [--> (f-let (p_2 (f-let (p_1 S_1) S_2)) S_3)
        (f-let (p_1 S_1) (f-let (p_2 S_2) S_3)) ; TODO? p1 not in FP(S_3)
        lift]
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
    (term (unload-PCEK (lookup ,(first res) ,(second res))))))


(test-equal
 (eval-PCEK (term (let (y 2) (let (x 3) (let (z 1) x)))))
 (term 3))

;(test-equal
; (eval-PCEK (term (let (y 1) (let (x (if y 2 3)) x))))
; (term 2))

;(traces
;  -->PCEK
;  (load-PCEK
;   (term
;    (let (y 1) (let (x (if y 2 3)) x))
;    )))

;(traces
;  -->PCEK
;  (load-PCEK
;   ;((let (x (if y M_1 M_2)) M) E K)
;   (term
;    (let (x 1)
;      (let (y 2)
;        (let (z (cons x y)) z)))
;    )))

(traces
 -->PCEK
 (load-PCEK
  (term
   (let (a 1)
     (let (b 2)
       (let (y (cons a b))
         (let (x (car y)) x)))))))














