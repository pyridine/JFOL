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
	   (exists 'y
		   (all 'u
			(exists 'v
				(relation 'R (variable 'u) (variable 'y) (variable 'v))))))))


;;A pair of sentences which are unifiable.
(define unis
  (cons
   ;;If x both hates and loves Hatsune Miku, then X is ambivalent.
   (binary 'IMP
	   (binary 'AND
		   (relation 'Loves (variable 'x) (constant 'Hatsune-Miku))
		   (relation 'Hates (variable 'x) (constant 'Hatsune-Miku)))
	   (relation 'Is-Ambivalent-About (variable 'x) (constant 'Hatsune-Miku)))

   (binary 'IMP
	   (binary 'AND
		   (relation 'Loves (variable 'x) (variable 'y))
		   (relation 'Hates (variable 'x) (variable 'y)))
	   (relation 'Is-Ambivalent-About (variable 'x) (variable 'y)))))


(define u
  (binary 'OR (relation 'Loves (variable 'x) (constant 'me)) (neg (relation 'Loves (variable 'x) (constant 'me)))))


(define m
  (binary 'OR (relation 'Loves (constant 'she) (variable 'w)) (neg (relation 'Loves (constant 'she) (variable 'w)))))

;;Although unifiable, unify-two-expressions seems to try forever.
(define r1 (relation 'R (function 'F2 (variable 'y)) (variable 'y) (variable 'v)))
(define r2 (relation 'R (variable 'x) (function 'F1 (constant 'C1)) (function 'F (variable 'x) (function 'F1 (constant 'C1)))))

;;An argument

(define argu
  (list
   ;;conclusion
   (relation 'loves (constant 'elsa) (constant 'anna))
   ;;premises
   (universal 'x (universal 'y (binary 'IMP (relation 'kisses (variable 'x) (variable 'y)) (relation 'loves (variable 'x) (variable 'y)))))
   (relation 'kisses (constant 'elsa) (constant 'anna))))

(define foo
  (list
   (existential 'x (variable 'x))
   (existential 'x (relation 'fucking (variable 'x) (constant 'ay)))
   ))

		
(define g1
  (list
   (relation 'p (variable 'x) (function 'f (variable 'y)))
   (relation 'p (function 'g (variable 'y)) (function 'f (constant 'a)))
   (relation 'q (variable 'c) (variable 'z))))

(define g2
  (list
   (neg (relation 'p (function 'g (constant 'a)) (variable 'z)))
   (relation 'r (variable 'x) (constant 'a))))

