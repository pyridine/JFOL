(load "ExprUtil.scm")

(define ta (constant 'A))
(define tb (constant 'B))
(define tc (constant 'C))
(define td (constant 'D))

(define vx (variable 'X))
(define vy (variable 'Y))
(define vz (variable 'Z))
(define vr (variable 'R))
(define vw (variable 'W))
(define vu (variable 'U))

(define jerry (constant 'JERRY))
(define beth (constant 'BETH))
(define summer (constant 'SUMMER))
(define mary (constant 'MARY))
(define bob (constant 'BOB))
(define dog (constant 'DOG))
(define cat (constant 'CAT))


(define u1 (func 'FUNC beth vy jerry))
(define u2 (func 'FUNC beth (func 'LAMBDA vw mary) jerry))
(define u3 (func 'FUNC vr (func 'LAMBDA vw mary) jerry))
(define u4 (func 'FUNC vr (func 'LAMBDA vu mary) jerry))

(define fol1
  (all 'X (exists 'Y (relation 'Loves vx vy))))

(define fol2
  (all 'X
   (exists 'Y
    (relation 'Hates vw vr))))

(define fol3
  (all 'X
       (exists 'Y
	       (binary 'IMP
		       (exists 'W (relation 'LOVES  mary vx))
		       (relation 'EATS dog vy)))))

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

;;Should have a disagreement pair with d2
(define d1
	  (func 'F
	   (func 'G
		 (const 'A)
		 (var 'X))
	   (func 'H
		 (const 'C)
		 (func 'J
		       (var 'Y)
		       (var 'X)))))
(define d2
	  (func 'F
	   (func 'G
		 (const 'A)
		 (var 'X))
	   (func 'H
		 (const 'C)
		 (func 'K
		       (var 'Z)))))
