(load "ExprUtils.scm")

;;Applies all the simplification rules
;;I'm using for the FOL solver.
(define standard-form
  (lambda (e)

    (skolemize
     (prenex
      (make-variables-unique e))) ;;Important, for variables might occur free and bound in the same sentence. We don't want that!!!
    
    )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;;======================================;;
;;     SIMPLIFICATION PROCEDURES        ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Converts e into prenex form.................
(define prenex
  (lambda (e)
    )
  )

;;Skolemizes e.
;;If properly skolemized, the delta rule is never needed in a proof!
;;ASSUMES E IS:
;;    1. No variable in e is both free and bound (all are unique)
;;    2. In prenex form
(define skolemize
  (lambda (e)
    1
    )
  )
