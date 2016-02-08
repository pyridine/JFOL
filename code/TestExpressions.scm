(load "ExprUtil.scm")

(define ta (letter 'A))
(define nta (negation ta))

(define tb (letter 'B))
(define ntb (negation tb))

(define tc (letter 'C))
(define ntc (negation tc))

(define td (letter 'D))
(define ntd (negation td))

(define fol1
  (all 'X
   (exists 'Y
    (relation 'Loves (list (variable 'Y) (variable 'X))))))

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
