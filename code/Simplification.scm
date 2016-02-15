(load "ExprUtil.scm")
(load "Replacement.scm")

;;Applies all the simplification rules
;;I'm using for the FOL solver.
;;WARNING: ASSUMES e IS "NAMED APART" - no two quantifiers use the same variable, and no bound variable is also free.
(define standard-form
  (lambda (e)
    (skolemize
     (prenex
      (reduce-connectives e)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;;======================================;;
;;     SIMPLIFICATION PROCEDURES        ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Converts e into prenex form.................

(define prenex-rules'(
    (not (universal ?x ?e))             (existential ?x (not ?e))   
    (not (existential ?x ?e))           (universal ?x (not ?e))   
    (binary ?c (universal ?x ?a) ?b)    (universal ?x (binary ?c ?a ?b))
    (binary ?c ?b (universal ?x ?a))    (universal ?x (binary ?c ?b ?a))
    (binary ?c (existential ?x ?a) ?b)  (existential ?x (binary ?c ?a ?b))
    (binary ?c ?b (existential ?x ?a))  (existential ?x (binary ?c ?b ?a))
    ))

(define prenex
  (lambda (e)
    (apply-pattern-rules-deep-while prenex-rules e)))

(define connective-equivalence-rules '(
    (not (not ?a))           (?a)
    (binary IMP ?a ?b)       (binary 'OR (not ?a) ?b)
    (binary EQUIV ?a ?b)     (binary 'AND (binary 'IMP ?a ?b) (binary 'IMP ?b ?a)) ;;this will in turn be reduced by the previous rule
    (binary INEQUIV ?a ?b)   (not (binary 'EQUIV ?a ?b)) ;;ditto
    (binary NAND ?a ?b)      (not (binary 'AND ?a ?b))
    (binary NOR ?a ?b)       (not (binary 'OR ?a ?b))
    (binary REVIMP ?a ?b)    (binary 'IMP ?b ?a)
    (binary NOTIMP ?a ?b)    (not (binary 'IMP ?a ?b))
    (binary NOTREVIMP ?a ?b) (not (binary 'REVIMP ?a ?b))
    ))

(define reduce-connectives
  (lambda (e)
    (apply-pattern-rules-deep-while connective-equivalence-rules e)))

;;Skolemizes e.
;;If properly skolemized, the delta rule is never needed in a proof!
;;ASSUMES E IS:
;;    1. No variable in e is both free and bound (all are unique)
;;    2. In prenex form
(define skolemize
  (lambda (e)
    e))
