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

;;Problems from Language, Truth, and Logic;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mayv
  (lambda (v)
    (if (symbol? v) (variable v) v)))

(define cube
  (lambda (var)
    (relation 'cube (mayv var))))

(define tet
  (lambda (a)
    (relation 'tet (mayv a))))

(define dodec
  (lambda (a)
    (relation 'dodec (mayv a))))

(define small
  (lambda (var)
    (relation 'small (mayv var))))

(define medium
  (lambda (var)
    (relation 'medium (mayv var))))

(define large
  (lambda (var)
    (relation 'large (mayv var))))

(define leftof
  (lambda (a b)
    (relation 'leftof (mayv a) (mayv b))))

(define rightof
  (lambda (a b)
    (relation 'rightof (mayv a) (mayv b))))

(define samecol
  (lambda (a b)
    (relation 'samecol (mayv a) (mayv b))))

(define larger
  (lambda (a b)
    (relation 'larger (mayv a) (mayv b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 13-2
  (list
   ;;c
   (universal 'x (small 'x))
   ;;p
   (binary 'EQUIV
	   (universal 'x (cube 'x))
	   (universal 'x (small 'x)))
   (universal 'x (cube 'x))))

;;invvalid argument
(define 13-4
  (list
   (neg (universal 'x (cube 'x)))
   (neg (universal 'x (binary 'AND (cube 'x) (small 'x))))))

;;The hellish argument from helly hell that I spent over an hour trying to figure out
;;The solver can't solve it, but I do think it should NOT be able to be solved.
;;So good on my solver, I guess.
(define 13-29
  (list
   ;;c
   (existential 'x (cube 'x))
   ;;p
   (universal 'x (binary 'IMP
			 (small 'x)
			 (cube 'x)))
   (existential 'x (binary 'IMP
			   (neg (cube 'x))
			   (existential 'y (small 'y))))))

;;this one may appear to use tarski semantics, but actually the premises do that work.
;;This one is complicated and is a good test of my system.
;;VALID BUT CAN'T SOLVE!!
(define 13-39
  (list
   ;;c
   (universal 'x (binary 'IMP
			 (cube 'x)
			 (universal 'y (binary 'IMP
					       (tet 'y)
					       (larger 'x 'y)))))
   ;;p
   (universal 'x (binary 'IMP
			 (cube 'x)
			 (universal 'y (binary 'IMP
					       (dodec 'y)
					       (larger 'x 'y)))))
   (universal 'x (binary 'IMP
			 (dodec 'x)
			 (universal 'y (binary 'IMP
					       (tet 'y)
					       (larger 'x 'y)))))
   (existential 'x (dodec 'x))
   (universal 'x (universal 'y (universal 'z (binary 'IMP
						     (binary 'AND
							     (larger 'x 'y)
							     (larger 'y 'z))
						     (larger 'x 'z)))))))

(define 13-33
  (list
   ;;c
   (universal 'x (binary 'IMP
			 (tet 'x)
			 (binary 'OR
				 (large 'x)
				 (medium 'x))))
   ;;p
   (neg (existential 'x (binary 'AND
				(tet 'x)
				(small 'x))))
   (universal 'y (binary 'OR
			 (small 'y)
			 (binary 'OR
				 (medium 'y)
				 (large 'y))))))
