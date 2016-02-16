;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Simplification.scm
;;;;
;;;; Defines procedures which manipulate expressions to turn
;;;; them into standard form.
;;;; See the very end of this file for procedures like
;;;; "standard-form", which are the culmination of the procedures
;;;; and rule-sets defined in this file.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  WARNING!!!
;;=============================
;;
;; EACH FUNCTION HERE ASSUMES INPUT EXPRESSION E IS "NAMED APART" - no two quantifiers use the same variable, and no bound variable is also free.
;; I have not provided a procedure to "name apart" variables in an expression, so the user must type sentences that way.
;;
;; Make sure you uniqueify the variables before combining your argument steps into the single resolution premise.
;;
(load "ExprUtil.scm")
(load "VariableSubstitution.scm")
(load "Replacement.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     SIMPLIFICATION RULES             ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Fully applying this ruleset results in a sentence composed only of NOT, OR, and AND.
(define connective-equivalence-rules '(
    (binary NOTREVIMP ?a ?b) (neg (binary 'REVIMP ?a ?b))
    (binary NOTIMP ?a ?b)    (neg (binary 'IMP ?a ?b))
    (binary REVIMP ?a ?b)    (binary 'IMP ?b ?a)
    (binary NOR ?a ?b)       (neg (binary 'OR ?a ?b))
    (binary NAND ?a ?b)      (neg (binary 'AND ?a ?b))
    (binary INEQUIV ?a ?b)   (neg (binary 'EQUIV ?a ?b)) 
    (binary EQUIV ?a ?b)     (binary 'AND (binary 'IMP ?a ?b) (binary 'IMP ?b ?a)) 
    (binary IMP ?a ?b)       (binary 'OR (neg ?a) ?b)
    (neg (neg ?a))           (?a)
    ))

(define prenex-rules
  '(
    (neg (universal ?x ?e))             (existential ?x (neg ?e))   
    (neg (existential ?x ?e))           (universal ?x (neg ?e))   
    (binary ?c (universal ?x ?a) ?b)    (universal ?x (binary ?c ?a ?b))
    (binary ?c ?b (universal ?x ?a))    (universal ?x (binary ?c ?b ?a))
    (binary ?c (existential ?x ?a) ?b)  (existential ?x (binary ?c ?a ?b))
    (binary ?c ?b (existential ?x ?a))  (existential ?x (binary ?c ?b ?a))
    ))

;;These a/b rulesets assume the input sentence only consists of NOT, OR, and AND.
(define alpha-component-rules-multimatch
  '((binary AND ?a ?b)           ((?a)     (?b))
    (neg (binary OR ?a ?b))      ((neg ?a) (neg ?b))
    (neg (binary IMP ?a ?b))     ((?a)     (neg ?b))
    (neg (binary REVIMP ?a ?b))  ((neg ?a) (?b))
    (neg (binary NAND ?a ?b))    ((?a)     (?b))
    (binary NOR ?a ?b)           ((neg ?a) (neg ?b))
    (binary NOTIMP ?a ?b)        ((?a)     (neg ?b))
    (binary NOTREVIMP ?a ?b)     ((neg ?a) (?b))
    ))

(define beta-component-rules-multimatch
  '(
    (binary OR ?a ?b)               ((?a) (?b)) 
    (neg (binary AND ?a ?b))        ((neg ?a) (neg ?b))
    (binary IMP ?a ?b)              ((neg ?a) (?b))
    (binary REVIMP ?a ?b)           ((?a)     (neg ?b))
    (binary NAND ?a ?b)             ((neg ?a) (neg ?b))
    (neg (binary NOR ?a ?b))        ((?a)     (?b))
    (neg (binary NOTIMP ?a ?b))     ((neg ?a) (?b))
    (neg (binary NOTREVIMP ?a ?b))  ((?a)     (neg ?b))
    ))

(define trivial-component-rules
  '((neg (neg ?a)) (?a)))

(define alpha-components
  (lambda (expr) (apply-pattern-rules-condy-multi-result alpha-component-rules-multimatch expr)))

(define beta-components
  (lambda (expr) (apply-pattern-rules-condy-multi-result beta-component-rules-multimatch expr)))

(define double-U-component
  (lambda (expr) (apply-pattern-rules-condy trivial-component-rules expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     SIMPLE-PLICATION PROCEDURES      ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prenex
  (lambda (e)
    (apply-pattern-rules-deep-while prenex-rules e)))

;;Reduce just the secondary connectives.
(define reduce-connectives
  (lambda (e)
    (apply-pattern-rules-deep-while connective-equivalence-rules e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     CNF AND DNF PROCEDURES           ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Remember, "clause form", CNF, is a list of lists of expressions,
;;where the superlist is semantically each clause conjuncted together,
;;and each sublist is each expression disjuncted together.
;;
;;Dual Clause form is the inversion of conj/disj.

;;all these apply-[c/d]nf-[alpha/beta]-rule functions returns a LIST OF CLAUSES to add to the proof

;;The parent clause, minus the locus from which c1 and c2 resulted,
;;is transformed into (<parent items - locus> U {c1,c2})
(define -normal-form-inexpr-replace
  (lambda (comps parent-clause-minus-locus)
    (list
     (append comps parent-clause-minus-locus))))

;;The parent clause minus its locus is transformed into two clauses:
;;  (<parent-ml> U c1), (<parent-ml> U c2)
(define -normal-form-twoexpr-replace
  (lambda (comps parent-clause-minus-locus)
    (list
     (append (list (car comps)) parent-clause-minus-locus)
     (append (cdr comps) parent-clause-minus-locus))))

;;Performs one step of the "clause form algorithm".
;;Input and output is clause form.
(define --x-clause-form-iteration
  (lambda (clause-list a-func b-func)
    (let* ((unfinished-clause-ref (first-member-ref
				   (lambda (x) (if x #t #f))
				   (map (a-member-is non-literal?) clause-list))))
      (if unfinished-clause-ref
	  (let* ((unfinished-clause                         (list-ref clause-list unfinished-clause-ref))
		 (locus-ref                                 (first-member-ref non-literal? unfinished-clause))
		 (locus                                     (list-ref unfinished-clause locus-ref))
		 (clause-list-minus-unfinished-clause       (list-remove-ref clause-list unfinished-clause-ref))
		 (unfinished-clause-minus-locus             (list-remove-ref unfinished-clause locus-ref)))
	    (let ((alphas      (alpha-components locus))
		  (betas       (beta-components locus))
		  (double-U    (double-U-component locus)))
	      (if double-U
		  (append (list (list double-U)) unfinished-clause-minus-locus)
		  (append
		   clause-list-minus-unfinished-clause
		   (if alphas
		       (a-func alphas unfinished-clause-minus-locus)
		       (if betas
			   (b-func betas  unfinished-clause-minus-locus)
			   (error "FUCK")))))))
	  clause-list))))

;;Returns a list of lists of expressions from a single expression e, representing each conjunct in the clause form of e.
(define x-clause-form
  (lambda (e a-func b-func) 
    (apply-until-stasis
     (lambda (a)
       (--x-clause-form-iteration a -normal-form-twoexpr-replace -normal-form-inexpr-replace))
     (list (list e)))))

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
	    (first-existential-variable (get-sh e)))
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
;;     !!!!!!      STANDARD                FORMS     !!!!           ;;
;;==================================================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; WARNING:
;;
;; Turning an expression into clause-form before applying resolution seems
;; to slurp crucial information for the resolution itself.

(define clause-form-to-expression
  (lambda (c) ;;clause form is a conjunction of disjunctions.
    (string-proposition-list 'and (map (lambda (sc) (string-proposition-list 'or sc)) c))))

;; Conjunctive-Normal Form (clause form)
(define clause-form-of-unquantified
  (lambda (e)
    (begin
      (x-clause-form e -normal-form-twoexpr-replace -normal-form-inexpr-replace))))

(define clause-form-expression-of-prenex-skolemized
  (lambda (e)
    (let ((quants (list-variables-scoped e))
	  (stripped-e (strip-quantifiers e)))
      (add-universal-quantifiers (clause-form-to-expression (clause-form-of-unquantified stripped-e)) quants))))

(define print-clause
  (lambda (clause) (string-append "[" (recurse-string pe clause " | ") "]")))

;;Applies all the simplification rules
;;I'm using for the FOL solver.
;;Semantically, (standard-form e) is satisfiable if and only if e is.
;;A valid expression.
(define standard-form
  (lambda (e)
    (skolemize (prenex (reduce-connectives e)))))

(define resolution-form
  (lambda (e)
    (strip-quantifiers (standard-form e))))

;;;;INCREDIBLY IMPORTANT NOTE:
;;;;   CONVERTING THE SENTENCE TO CNF MIGHT LEAVE IN THE DUST A STEP THAT WAS NECESSARY FOR RESOLUTION!
