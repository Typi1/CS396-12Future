#lang racket
(require racket/future)
(require future-visualizer)
(require future-visualizer/trace)


;; USE OF FUTURES EXAMPLE (from https://docs.racket-lang.org/guide/parallelism.html#%28part._effective-futures%29)

;; a function
(define (any-double? l)
  (for/or ([i (in-list l)])
    (for/or ([i2 (in-list l)])
      (= i2 (* 2 i)))))

;; functions that create lists via many operations
(define l1 (for/list ([i (in-range 10000)])
             (+ (* 2 i) 1)))
(define l2 (for/list ([i (in-range 10000)])
             (- (* 2 i) 1)))

;; taking the values from running both functions above. NO PARALLELISM
(time (or (any-double? l1)
          (any-double? l2)))

;; taking the values from running both functions above. WITH PARALLELISM
(time
 (let ([f (future (lambda () (any-double? l2)))])
   (or (any-double? l1)
       (touch f))))

(visualize-futures
 (let ([f1 (future (lambda () (any-double? l2)))]
       [f2 (future (lambda () (any-double? l2)))])
   (or (any-double? l1)
       (touch f1)
       (touch f2))))

(define x (future (λ () (+ 1 1))))

(touch x)






;; Multithreaded futures examples

;; fibonacci
(define (fibonacci n)
  (if (<= n 1)
      n
      (let ([x (fibonacci (sub1 n))]
            [y (fibonacci (- n 2))])
        (+ x y))))

;; fibonacci with futures derived from https://www.cs.unb.ca/~bremner/teaching/cs3383/examples/parfib.rkt/
(define (fut-fibonacci n)
  (if (<= n 1)
      n
      (let ([x (future (λ () (fut-fibonacci (sub1 n))))]
            [y (fut-fibonacci (- n 2))])
        (+ (touch x) y))))

(time (fibonacci 10))
(visualize-futures (fut-fibonacci 10))


;; computing pi examples
;; no futures used
(define (compute-pi k)
  (if (< k 0)
      0
      (let* ([next (compute-pi (sub1 k))]
             [this (* (/ 1 (arithmetic-shift 1 (* 4 k)))
                      (- (/ 4. (+ (* 8 k) 1))
                         (/ 2. (+ (* 8 k) 4))
                         (/ 1. (+ (* 8 k) 5))
                         (/ 1. (+ (* 8 k) 6))))])
        (+ this next))))

(time (compute-pi 6000))

;; 
(define (compute-pi-futures1 k)
  (if (< k 0)
      0
      (let ([next (future (λ () (compute-pi-futures1 (sub1 k))))]
            [this (* (/ 1.0 (arithmetic-shift 1 (* 4 k)))
                      (- (/ 4.0 (+ (* 8.0 k) 1.0))
                         (/ 2.0 (+ (* 8.0 k) 4.0))
                         (/ 1.0 (+ (* 8.0 k) 5.0))
                         (/ 1.0 (+ (* 8.0 k) 6.0))))])
        (+ this (touch next)))))

(visualize-futures (compute-pi-futures1 6000))

;; 
(define (compute-pi-futures2 k)
  (if (< k 0)
      0
      (let ([next (compute-pi-futures1 (sub1 k))]
            [this (future (λ () (* (/ 1.0 (arithmetic-shift 1 (* 4 k)))
                                   (- (/ 4.0 (+ (* 8.0 k) 1.0))
                                      (/ 2.0 (+ (* 8.0 k) 4.0))
                                      (/ 1.0 (+ (* 8.0 k) 5.0))
                                      (/ 1.0 (+ (* 8.0 k) 6.0))))))])
        (+ next (touch this)))))

(visualize-futures (compute-pi-futures2 6000))

;; a function (example of future time)

(define l3 (for/list ([i (in-range 1000)])
             (+ (* 2 i) 1)))

(define (any-double?2 l)
  (for/or ([i (in-list l)])
    (for/or ([i2 (in-list l)])
      (= i2 (touch (future (λ () (* 2 i))))))))


(time (any-double? l3))
(time (any-double?2 l3))






