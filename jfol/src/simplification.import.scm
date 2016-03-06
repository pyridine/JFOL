(declare (unit simplification))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Simplification.scm
;;;;
;;;; Defines procedures which manipulate expressions to turn
;;;; them into standard form.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  TAKE NOTE
;;==================
;; EACH FUNCTION HERE ASSUMES INPUT EXPRESSION IS "NAMED APART" - no two quantifiers use the same variable, and no bound variable is also free.
;; I have not provided a procedure to "name apart" variables in an expression, so the user must type sentences that way.
;;
;; (P: Make sure you uniquify the variables before combining your argument steps into the single resolution premise.)

(module simplification (alpha-components beta-components double-U-component prenex skolemize reduce-connectives strip-quantifiers)
  (import chicken)
  (import scheme)
  (reexport pattern-matcher)
  (reexport basic-fol)
  
  ;;======================================;;
  ;;     SIMPLIFICATION RULES             ;;
  ;;======================================;;

  ;;Fully applying this ruleset results in a sentence composed only of NOT, OR, and AND.
  (define connective-equivalence-rules
    '((binary NOTREVIMP ?a ?b) (neg (binary 'REVIMP ?a ?b))
      (binary NOTIMP ?a ?b)    (neg (binary 'IMP ?a ?b))
      (binary REVIMP ?a ?b)    (binary 'IMP ?b ?a)
      (binary NOR ?a ?b)       (neg (binary 'OR ?a ?b))
      (binary NAND ?a ?b)      (neg (binary 'AND ?a ?b))
      (binary INEQUIV ?a ?b)   (neg (binary 'EQUIV ?a ?b)) 
      (binary EQUIV ?a ?b)     (binary 'AND (binary 'IMP ?a ?b) (binary 'IMP ?b ?a)) 
      (binary IMP ?a ?b)       (binary 'OR (neg ?a) ?b)
      (neg (neg ?a))           (?a)))

  (define prenex-rules
    '((neg (universal ?x ?e))             (existential ?x (neg ?e))   
      (neg (existential ?x ?e))           (universal ?x (neg ?e))   
      (binary ?c (universal ?x ?a) ?b)    (universal ?x (binary ?c ?a ?b))
      (binary ?c ?b (universal ?x ?a))    (universal ?x (binary ?c ?b ?a))
      (binary ?c (existential ?x ?a) ?b)  (existential ?x (binary ?c ?a ?b))
      (binary ?c ?b (existential ?x ?a))  (existential ?x (binary ?c ?b ?a))))

  ;;These a/b rulesets assume the input sentence only consists of NOT, OR, and AND.
  (define alpha-component-rules-multimatch
    '((binary AND ?a ?b)           ((?a)     (?b))
      (neg (binary OR ?a ?b))      ((neg ?a) (neg ?b))
      (neg (binary IMP ?a ?b))     ((?a)     (neg ?b))
      (neg (binary REVIMP ?a ?b))  ((neg ?a) (?b))
      (neg (binary NAND ?a ?b))    ((?a)     (?b))
      (binary NOR ?a ?b)           ((neg ?a) (neg ?b))
      (binary NOTIMP ?a ?b)        ((?a)     (neg ?b))
      (binary NOTREVIMP ?a ?b)     ((neg ?a) (?b))))

  (define beta-component-rules-multimatch
    '((binary OR ?a ?b)               ((?a) (?b)) 
      (neg (binary AND ?a ?b))        ((neg ?a) (neg ?b))
      (binary IMP ?a ?b)              ((neg ?a) (?b))
      (binary REVIMP ?a ?b)           ((?a)     (neg ?b))
      (binary NAND ?a ?b)             ((neg ?a) (neg ?b))
      (neg (binary NOR ?a ?b))        ((?a)     (?b))
      (neg (binary NOTIMP ?a ?b))     ((neg ?a) (?b))
      (neg (binary NOTREVIMP ?a ?b))  ((?a)     (neg ?b))))

  (define trivial-component-rules
    '((neg (neg ?a)) (?a)))

  (define alpha-components
    (lambda (expr) (apply-pattern-rules-condy-multi-result alpha-component-rules-multimatch expr)))

  (define beta-components
    (lambda (expr) (apply-pattern-rules-condy-multi-result beta-component-rules-multimatch expr)))

  (define double-U-component
    (lambda (expr) (apply-pattern-rules-condy trivial-component-rules expr)))
  
  ;;======================================;;
  ;;     SIMPLE-PLICATION PROCEDURES      ;;
  ;;======================================;;

  (define prenex
    (lambda (e)
      (apply-pattern-rules-deep-while prenex-rules e)))

  
  ;;Reduce just the secondary connectives.
  (define reduce-connectives
    (lambda (e)
      (apply-pattern-rules-deep-while connective-equivalence-rules e)))

  (define strip-quantifiers
    (lambda (e)
      (if (quantifier? e)
	  (strip-quantifiers (get-sh e))
	  e)))

  ;;This is intended to be used in the following manner:
  ;;
  ;;Before stripping quantifiers from e (before translating it into CNF),
  ;;store these quantifiers with list-variables-scoped.
  ;;You can add them back this procedure without modifing the list.
  (define add-universal-quantifiers
    (lambda (e quantlist)
      (if (null? quantlist)
	  e
	  (universal (car quantlist) (add-universal-quantifiers e (cdr quantlist))))))

  ;;======================================;;
  ;;     SKOLEMNIZATION          ...      ;;
  ;;======================================;;

  ;;EVERY ALGORITHM THAT FOLLOWS IN THIS SECTION ASSUMES E IS IN PRENEX FORM. Otherwise skolemization is waaayyyyy too difficult.
  ;;also assumes e's connectives have been reduced, but I don't think this is a strict requirement?
  ;;If properly skolemized, the delta rule is never needed in a proof!
  ;;WARNING: Skolemnization introduces symbols. Because I will only be skolemnizing the !single! premise
  ;;         of any solving procedure, these symbols will only be new to the input expression.
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
  )
