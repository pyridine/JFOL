;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   TestExpressions.scm
;;;;
;;;; Sentences and building blocks to use.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "ExprUtil.scm")

(define ra (relation 'A (constant 'a)))
(define rb (relation 'B (constant 'b)))
(define rc (relation 'C (constant 'c)))


;;A sentence which is provable.
(define fol1
  (neg
   (binary 'IMP
	   (exists 'w
		   (all 'x
			(relation 'R (variable 'x) (variable 'w) (function 'F (variable 'x) (variable 'w)))))
	   (exists 'w
		   (all 'x
			(exists 'y
				(relation 'R (variable 'x) (variable 'w) (variable 'y))))))))

