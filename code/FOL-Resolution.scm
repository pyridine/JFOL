;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   FOL-Resolution.scm
;;;;
;;;; Implements FOL Resolution,
;;;; on expressions in Prenex, Skolemized, Clause Form (CNF)
;;;; including only the connectives AND, NOT, and OR.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "Unification.scm")
(load "Simplification")

;;The Y rule: from Ax{e(x)}, conclude e(c) for ANY closed term c.
;;151: We replace Y with Y(x), for x being a free variable whose value we will determine later.
;;
;;The idea is: can values for free variables be found that result in closed branches?
;; For instance, if we have  P(t1) and ~P(t2), can we satisfy t1=t2?

;;211: we can drop the quantifiers altogether, and work with the list C1, C2, ... CK of clauses containing free variables.
;;     But remember the quantifiers are implicitly present. So we never work with any clause directly, but rather with
;;     the result of renaming variables, replacing them with new free variables, effectively applicating Y rule.
;;     So we apply the Resolution rule to two clauses C1 and C2 containing free variables. 


(define Create-FOL-Resolution-Premise
  (lambda
      (conclusion . premises)

    456789
 
      )

  )


;;
