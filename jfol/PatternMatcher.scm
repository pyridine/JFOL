;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Replacement.scm
;;;;
;;;; This file defines fundamental procedures for pattern-based
;;;; expression manipulation.
;;;; Special thanks to The Schematics of Computation (1995),
;;;; chapter 10.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; WARNING
;; ==============================
;;
;; Match and Replace patterns unfortunately, do not have the same syntax.
;; Here are the differences:
;;
;;   1. In a Match pattern, writing '(binary IMP ?a ?b) is fine.
;;      But in a Replace pattern, binary types must be re-quoted: '(binary 'OR (neg ?b) ?a)
;;      I believe this also applies to any other cadr-named expression, like quantifiers, relations, functions....
;;
;; Also, remember to use "neg" and not "not" to specify a negation expression.
;;
;;
(load "FOLUtil.scm")

;; Is the symbol a pattern variable?
(define pattern-variable?
  (lambda (x)
    (and
     (symbol? x)
     (char=? (string-ref (symbol->string x) 0) #\?))))

;;Does the matching of pat-var with targ-exp agree with
;;the variable substitutions so far?
(define agrees-with?
  (lambda (patvar target-expression answers)
    (let ((x (assv patvar answers)))
      (if x
	  (equal? (cdr x) target-expression)
	  #t))))

;;Add (patvar.targexp) to the substitution so far.
(define add-answer
  (lambda (patvar targexp answers)
    (if (assv patvar answers)
	answers ;;This patvar is already included in answers.
	(cons (cons patvar targexp) answers))))

;;Do add-answer only if it agrees with the sub.
(define attempt-add-answer
  (lambda (patvar targexp answers)
    (if (agrees-with? patvar targexp answers)
	(add-answer patvar targexp answers)
	#f)))

;;a basic matcher for a "named" expression
(define helper-basic-named
 (lambda (named-t name-getter pat expr answers)
   (and (is-type? expr named-t)
	(if (pattern-variable? (cadr pat))
	    (attempt-add-answer (cadr pat) (name-getter expr) answers)
	    (if (equal? (cadr pat) (name-getter expr)) answers #f)))))

;;helper function for expr-match?
(define expr-match-helper
  (letrec ((helper-quantifier
	    (lambda (type pat expr answers)
	      (let ((nanswers (helper-basic-named type get-variable pat expr answers)))
		(if nanswers
		    (expr-match-helper (caddr pat) (get-sh expr) nanswers)
		    #f))))
	   (helper-arglist
	    (lambda (type pat expr answers)
	      (let ((nanswers (helper-basic-named type get-name pat expr answers)))
		(if nanswers
		    (letrec ((recursing-list-matcher
			      (lambda (pattern-list manswers first-targ . rest-targs)
				(let ((aanswers (expr-match-helper (car pattern-list) first-targ manswers)))
				  (if aanswers
				      (if (null? (cdr pattern-list))
					  (if (null? rest-targs) aanswers #f)
					  (if (null? rest-targs)
					      #f
					      (apply recursing-list-matcher (cons (cdr pattern-list) (cons aanswers rest-targs)))))
				      #f)))))
		      (apply recursing-list-matcher (cons (cddr pat) (cons nanswers (get-args expr)))))
		    #f)))))
    (lambda (pat expr answers)
      (cond
       ((null? pat) #f) ;;;;;uuuhhhh...
       ((null? expr) #f);;;;;;;;;;;;;;;
       ;; ANYTHING AT ALL
       ((pattern-variable? pat)
	(attempt-add-answer pat expr answers))
       ((pattern-variable? (car pat))
	(attempt-add-answer (car pat) expr answers))
       ;; TRUE
       ((equal? (car pat) 'true)
	(if (equal? expr true) answers #f))
       ;; FALSE
       ((equal? (car pat) 'false)
	(if (equal? expr false) answers #f))
       ;; VARIABLES
       ((equal? (car pat) 'variable)
	(helper-basic-named variable-t get-variable pat expr answers))
       ;; CONSTANTS
       ((equal? (car pat) 'constant)
	(helper-basic-named constant-t get-name pat expr answers))
       ;; NEGATION
       ((equal? (car pat) 'neg)
	(and (is-type? expr not-t)
	     (expr-match-helper (cadr pat) (get-sh expr) answers))) ;;Don't forget the cadr! not the cdr! Yeesh.
       ;; BINARIES : We won't strictly check if the pattern has a true binary connective symbol...
       ((equal? (car pat) 'binary)
	(let ((nans (if (is-type? expr (cadr pat))
			answers
			(if (pattern-variable? (cadr pat))
			    (attempt-add-answer (cadr pat) (get-type expr) answers)
			    #f))))  
	  (if nans
	      (let ((new-answers (expr-match-helper (caddr pat) (get-lh expr) nans)))
		(if new-answers
		    (expr-match-helper (cadddr pat) (get-rh expr) new-answers)
		    #f))
	      #f)))
       ;; FUNCTION
       ((equal? (car pat) 'function)
	(helper-arglist function-t pat expr answers))
       ;; RELATION
       ((equal? (car pat) 'relation)
	(helper-arglist relation-t pat expr answers))
       ;; EXISTENTIAL
       ((equal? (car pat) 'existential)
	(helper-quantifier existential-t pat expr answers))
       ;; UNIVERSAL
       ((equal? (car pat) 'universal)
	(helper-quantifier universal-t pat expr answers))
       (else #f)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;           THE IMPORTANT STUFF                ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;returns a map of
;; ( ... (pattern-variable . <expression> )  ... (pattern-variable . <symbol>) ... )
;; 
;; We match expressions where the patvar is syntactically where an expression should go,
;; and symbols if the patvar is syntactically where a symbol should go. Use symbols
;; where the names of things must go: names of functions, variables, constants, relations...
;;
;;Will return '() if no substitutions need to be made,
;;or #f if the expression does not match the pattern.
(define expr-match?
  (lambda (pattern exp)
    (expr-match-helper pattern exp '())))

;;Prints an evaluable AST for an expression, as a string.
;;Use eval-string.
(define print-expression-evaluable
  (lambda (in)
    (apply string-append
	   (append
	    (list "(")
	    (cond
	     ;;Base
	     ((true? in) (list "true"))
	     ((false? in) (list "false"))
	     ((constant? in) (list "constant '" (symbol->string (get-name in))))
	     ((variable? in) (list "variable '" (symbol->string (get-variable in))))
	     ;;Recursion
	     ((is-type? in not-t) (list "neg " (print-expression-evaluable (get-sh in))))
	     ((universal? in) (list "universal '" (symbol->string (get-variable in)) " " (print-expression-evaluable (get-sh in)) " " ))
	     ((existential? in) (list "existential '" (symbol->string (get-variable in)) " " (print-expression-evaluable (get-sh in)) " " ))
	     ((function? in)
	      (append (list "function '" (symbol->string (get-name in)) " ")
		      (map print-expression-evaluable (get-args in))))
	     ((relation? in)
	      (append (list "relation '" (symbol->string (get-name in)) " ")
		      (map print-expression-evaluable (get-args in))))
	     ;;Binary recursion
	     (else 
	      (list
	       "binary '"
	       (symbol->string (get-type in))
	       " "
	       (print-expression-evaluable (get-lh in))
	       " "
	       (print-expression-evaluable (get-rh in)))))
	    (list ")")))))


;;Takes a pattern, a substitution (one made with expr-match?, I'd hope),
;;and returns a pattern with all substitutions made. A symbol.
;;Will replace #<expression>s with their symbolic counterparts.
;;If all substitutions are filled, you can (eval result) into anX #<expression>!!
;;That should turn out to be an incredibly powerful procedure.
;;Basically taken entirely from Schematics of Computation ch 10. Really puts my code to shame :P
(define expr-pattern-substitute
  (lambda (pattern substitution)
    (letrec
	((replace
	  (lambda (item)
	    (cond
	     ((pattern-variable? item)
	      (let ((r (cdr (assv item substitution))))
		(if r
		    (if (symbol?  r)
			(string->true-symbol (string-append "(quote " (symbol->string  r) ")")) ;;otherwise it's an expression.
			(string->true-symbol (print-expression-evaluable r)))
		    item)))
	     ((list? item)
	      (map replace item)) ;;MAP!! :P Otherwise you'd enter an infinite loop:
	                          ;;        (list? item) => (replace item) : (list? item) => (replace item).....
	                          ;;Don't code tired ladies and gents
	     (else item)))))
      (let ((kludge (map replace pattern)))
	(if (list? kludge)
	    (if (= 1 (length kludge))
		(raise-list kludge)
		kludge)
	    kludge)))))

;;Returns the transformed expression or #f if failure to match
(define apply-pattern-rule
  (lambda (match-pattern replace-pattern expression)
    (let ((match (expr-match? match-pattern expression)))
      (if match
	  (eval (expr-pattern-substitute replace-pattern match))
	  #f))))

;;If the exprsesion matches, returns the substitution over each replace pattern in the list.
(define apply-pattern-rule-multi-result
  (lambda (match-pattern replace-pattern-list expression)
    (let ((match (expr-match? match-pattern expression)))
      (if match
	  (map (lambda (x)
		 (eval (expr-pattern-substitute x match)))
	       replace-pattern-list)
	  #f))))

;;Applies a single rule not only to the expression itself, but also checks all sub-expressions.
;;Returns e even if any match fails.
;;Not garaunteed to replace every instance of the pattern. Use apply-pattern-rule-deep-while.
;;DO YOU REGRET HOW YOU ARE REPRESENTING EXPRESSIONS YET?!
(define apply-pattern-rule-deep
  (lambda (match replace e)
    ;;or returns the first non-#f! :)
    (or
     ;;Does e itself satisfy the rule? This takes care of the base case.
     (let ((superbase (apply-pattern-rule match replace e)))
       (if superbase superbase #f))
     ;;Another base case: if e is basic.
     (if (basic? e)
	 (let ((nexp (apply-pattern-rule match replace e))) e) ;;NOT DEEP! infinite recursion, again. Don't code tired. Fuck.
	 #f)
     (if (unary? e)
	 (let ((nexp (apply-pattern-rule-deep match replace (get-sh e))))
	   (if nexp
	       (let ((newe (--expression-create (get-type e) nexp nil)))
		 (begin
		   (when (or (universal? e) (existential? e)) (set-variable newe (get-variable e)))
		   newe))
	       e))
	 #f)
     (if (binary? e)
	 (let ((lexp (apply-pattern-rule-deep match replace (get-lh e)))
	       (rexp (apply-pattern-rule-deep match replace (get-rh e))))
	   (if (or lexp rexp)
	       (let ((newe (--expression-create (get-type e) nil nil)))
		 (begin
		   (set-lh newe (if lexp lexp (get-lh e)))
		   (set-rh newe (if rexp rexp (get-rh e)))
		   newe))
	       e))
	 #f)
     ;;Function or Relation
     (if (or (function? e) (relation? e))
      (let ((nargs
	     (map (lambda (x)
		    (let  ((newx (apply-pattern-rule-deep match replace x)))
		      (if newx newx x)))
		  (get-args e))))
	(let ((newe (--expression-create (get-type e) nil nil)))
	  (begin
	    (set-name newe (get-name e))
	    (set-args newe nargs)
	    newe)))
      #f)
     e))) ;;Nothing worked; so no changes.

;;Continuously applies match/replace to e, deeply, until e no longer changes.
(define apply-pattern-rule-deep-while
  (lambda (match replace e)
    (apply-until-stasis
     (lambda (arg) (apply-pattern-rule-deep match replace arg))
     e)))

;;Takes a (<pattern1> <pattern2> <pattern1> <pattern2>...) list and an expression.
;;Acts like a cond. If the expression matches any pattern 1, we return the substitution of that match on pattern 2.
;;Applies every rule deeply continuously until the expression no longer changes, IN SEQUENCE.
;;It will apply rule1 until it no longer changes e, then rule 2, etc.
(define apply-pattern-rules-deep-while-sequence
  (lambda (rules exp)
    (if (null? rules)
	exp
	(apply-pattern-rules-deep-while
	 (cddr rules)
	 (apply-until-stasis
	  (lambda (e) (apply-pattern-rule-deep (car rules) (cadr rules) e)) exp)))))

;;applies surface-level rules until one doesn't return #f, and returns the result of that rule.
(define apply-pattern-rules-condy
  (lambda (rules exp)
    (if (null? rules)
	#f 
	(let ((res (apply-pattern-rule (car rules) (cadr rules) exp)))
	  (if res
	      res
	      (apply-pattern-rules-condy (cddr rules) exp))))))

;;applies surface-level rules until one doesn't return #f, and returns the result of that rule.
(define apply-pattern-rules-condy-multi-result
  (lambda (rules exp)
    (if (null? rules)
	#f
	(let ((res (apply-pattern-rule-multi-result (car rules) (cadr rules) exp)))
	  (if res
	      res
	      (apply-pattern-rules-condy-multi-result (cddr rules) exp))))))

;;Repeatedly applies every rule in sequence until the expression no longer changes.
(define apply-pattern-rules-deep-while
  (lambda (rules exp)
    (apply-until-stasis
     (lambda (e)
       (apply-pattern-rules-deep-while-sequence rules e))
     exp)))
