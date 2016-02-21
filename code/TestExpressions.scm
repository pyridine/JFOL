;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   TestExpressions.scm
;;;;
;;;; Sentences and building blocks to use.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "ExprUtil.scm")

(define ra (relation 'A (constant 'a)))
(define rb (relation 'B (constant 'b)))
(define rc (relation 'C (constant 'c)))


(define frozen
  (list
   ;;conclusion
   (relation 'loves (constant 'elsa) (constant 'anna))
   ;;premises
   (universal 'x (universal 'y (binary 'IMP
				       (relation 'kisses (variable 'x) (variable 'y))
				       (relation 'loves  (variable 'x) (variable 'y)))))
   (relation 'kisses (constant 'elsa) (constant 'anna))))

(define frozen-failure
  (list
   ;;conclusion
   (relation 'loves (constant 'elsa) (constant 'anna))
   ;;premises
   (universal 'x (universal 'y (binary 'IMP (relation 'kisses (variable 'x) (variable 'y)) (relation 'loves (variable 'x) (variable 'y)))))
   (relation 'kisses (constant 'anna) (constant 'hans))))



;;Problems from Language, Truth, and Logic
(define cube
  (lambda (var)
    (relation 'cube (variable var))))
(define small
  (lambda (var)
    (relation 'small (variable var))))

(define 13-2
  (list
   ;;c
   (universal 'x (small 'x))
   ;;p
   (binary 'EQUIV
	   (universal 'x (cube 'x))
	   (universal 'x (small 'x)))
   (universal 'x (cube 'x))
   )
  )
