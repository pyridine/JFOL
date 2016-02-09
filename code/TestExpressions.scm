(load "ExprUtil.scm")



(define ta (constant 'A))
(define nta (negation ta))

(define tb (constant 'B))
(define ntb (negation tb))

(define tc (constant 'C))
(define ntc (negation tc))

(define td (constant 'D))
(define ntd (negation td))

(define fol1
  (all 'X
   (exists 'Y
    (relation 'Loves (list (variable 'Y) (variable 'X))))))

(define fol2
  (all 'X
   (exists 'Y
    (relation 'Fucks (list (variable 'W) (variable 'R))))))

(define fol3
  (all 'A
       (exists 'B
	       (binary 'IMP
		       (exists 'C (relation 'LOVES (list (constant 'mary)) (variable 'C)))
		       (relation 'EATS (list (constant 'dog) (variable 'A)))))
       )
  )

;;not (A and not A)
(define taut1
  (negation
   (binary 'AND ta nta)))

;;proof by cases
(define taut2
  (binary
   'IMP
   (string-propositions
    'AND
    (binary 'OR ta tb)
    (binary 'IMP ta tc)
    (binary 'IMP tb tc))
   tc))

;;Modus ponens
(define taut3
  (binary
   'IMP
   (binary
    'AND
    ta
    (binary 'IMP ta tb))
   tb))

;;Modus tollens
(define taut4
  (binary
   'IMP
   (binary
    'AND
    (binary 'IMP ta tb)
    (negation tb))
   (negation ta)))

;;Transitivity
(define taut5
  (binary
   'IMP
   (binary
    'AND
    (binary 'IMP ta tb)
    (binary 'IMP tb tc))
    (binary 'IMP ta tc)))
