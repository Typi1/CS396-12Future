#lang racket

(require racket/future
         future-visualizer/trace
         future-visualizer)


(define (compute-pi k [k-start 0])
  (if (= k (sub1 k-start))
      0
      (let ([next (compute-pi (sub1 k))]
            [this (* (/ 1 (arithmetic-shift 1 (* 4 k))) (- (/ 4. (+ (* 8 k) 1))
                                          (/ 2. (+ (* 8 k) 4))
                                          (/ 1. (+ (* 8 k) 5))
                                          (/ 1. (+ (* 8 k) 6))))])
            (+ this next))))

(define (compute-pi-paral k)
  (if (<= k -1)
      0
      (let ([next (future (lambda () (compute-pi-paral (sub1 k))))]
            [this (* (/ 1 (arithmetic-shift 1 (* 4 k))) (- (/ 4. (+ (* 8 k) 1))
                                          (/ 2. (+ (* 8 k) 4))
                                          (/ 1. (+ (* 8 k) 5))
                                          (/ 1. (+ (* 8 k) 6))))])
            (+ this (touch next)))))

(visualize-futures (compute-pi-paral 1000))

;(define (compute-pi k [k-start 0])
;  (if (= k (sub1 k-start))
;      0
;      (let ([next (compute-pi (sub1 k))]
;            [this (* (/ 1 (arithmetic-shift 1 (* 4 k))) (- (/ 4. (+ (* 8 k) 1))
;                                          (/ 2. (+ (* 8 k) 4))
;                                          (/ 1. (+ (* 8 k) 5))
;                                          (/ 1. (+ (* 8 k) 6))))])
;
;(define (compute-pi-paral-2 k [batch-size 1000])
;  (if (< k 0)
;      0
;      (let ([next (future (lambda () (compute-pi-paral-2 (- k batch-size))))]
;            [this (compute-pi k (max (- k batch-size) 0))])
;            (+ this (touch next)))))



