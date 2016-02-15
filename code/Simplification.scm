;;WARNING: EACH FUNCTION HERE ASSUMES e IS "NAMED APART" - no two quantifiers use the same variable, and no bound variable is also free.
(load "ExprUtil.scm")
(load "Replacement.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     SIMPLIFICATION RULES             ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define prenex-rules'(
    (not (universal ?x ?e))             (existential ?x (not ?e))   
    (not (existential ?x ?e))           (universal ?x (not ?e))   
    (binary ?c (universal ?x ?a) ?b)    (universal ?x (binary ?c ?a ?b))
    (binary ?c ?b (universal ?x ?a))    (universal ?x (binary ?c ?b ?a))
    (binary ?c (existential ?x ?a) ?b)  (existential ?x (binary ?c ?a ?b))
    (binary ?c ?b (existential ?x ?a))  (existential ?x (binary ?c ?b ?a))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     SIMPLIFICATION PROCEDURES        ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prenex
  (lambda (e)
    (apply-pattern-rules-deep-while prenex-rules e)))

(define reduce-connectives
  (lambda (e)
    (apply-pattern-rules-deep-while connective-equivalence-rules e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     SKOLEMNIZATION          ...      ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;EVERY ALGORITHM THAT FOLLOWS IN THIS SECTION ASSUMES E IS IN PRENEX FORM. Otherwise skolemization is waaayyyyy too difficult.
;;also assumes e's connectives have been reduced, but I don't think this is a strict requirement?
;;If properly skolemized, the delta rule is never needed in a proof!
;;WARNING: Skolemnization introduces symbols. Because I will only be skolemnizing the !single! premise
;;         of any solving procedure, these symbols will only be new to the input expression.
;;
;;The algorithm follows.
;;
;;############################################################
;;1. e is in prenex form. (all quantifiers occur "first")
;;2. e's connectives have been reduced.
;;############################################################
;;1. Locate the first existential form. Let its scoped variable be called "E".
;;2. Replace that existential subexpression from e with garbage in a new expression, `e.
;;3. list all scoped variables in `e (variables occuring as the sig of the quantifiers of the expression. This will be all universally quantified variables that occurred before the existential, because this is the FIRST existential form and e is in prenex.) Call this list [x1,x2,...,xn]
;;4. If that list is nil, then create a new constant symbol that does not occur in the expression. Call it C.
;;5. Create a function symbol that is new to the expression. The caveat of 4 applies as well. Call it f.
;;4. Create a variable-substitution (different from pattern substitutions) ($E . f([C/x1,x2...xn]) ) . (I.e., a function of either that new constant, or each of the variables.)
;;5. Remove that first existential subexpression from e.
;;5. Apply the variable substitution to e.

(define first-existential-variable
  (lambda (e)
    (if (quantifier? e)
	(if (existential? e)
	    (get-variable e)
	    (first-existentially-quantified-variable (get-sh e)))
	#f)))

;;Assumes there is in fact a first existential expression,
;;and replaces it, in its entirety, with a garbage constant.
;;Will fuck up if e doesn't meet the assumptions. (prenex is another.)
(define sklurge-first-existential
  (lambda (e)
    (if (existential? e)
	;;Replace it with a garbage constant.
	(constant (new-constant-symbol e))
	;;Then e is a universal. Replace it with itself, but with the inner EXISTS sklurged.
	(universal (get-variable e) (sklurge-first-existential (get-sh e))))))

;;Same assumptions apply to sklurge-first-existential.
;;Returns an expression with the first existential blipped out of existence as were it were never there.....
(define remove-first-existential
  (lambda (e)
    (if (existential? e)
	;;Replace it with its innards!!!! D:
	(get-sh e)
	;;Then e is a universal. Replace it with itself, but with the inner EXISTS sklurged.
	(universal (get-variable e) (remove-first-existential (get-sh e))))))

(define single-skolemize
  (lambda (e)
    (let  ((first-exi-var (first-existential-variable e)))
      (if first-exi-var
	  (let* ((sklurged-e          (sklurge-first-existential e))
		 (scoped-exi-vars     (list-variables-scoped sklurged-e))
		 (skolem-arguments    (if (null? scoped-exi-vars)
				          (list (constant (new-constant-symbol e)))
				          (map variable scoped-exi-vars)))
		 (skolem-function     (apply function (cons (new-function-symbol e) skolem-arguments)))
		 (skolem-substitution (list (cons first-exi-var skolem-function)))
		 (exiless-e           (remove-first-existential e)))
	    (apply-substitution exiless-e skolem-substitution))
	  #f))))

(define skolemize
  (lambda (e)
    (apply-until-stasis single-skolemize e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;==================================================================;;
;;     !!!!!!      STANDARD                FORM      !!!!           ;;
;;==================================================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Applies all the simplification rules
;;I'm using for the FOL solver.
;;Semantically, (standard-form e) is satisfiable if and only if e is.
(define standard-form
  (lambda (e)
    (skolemize (prenex (reduce-connectives e)))))
