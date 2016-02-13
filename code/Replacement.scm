;;Special thanks to The Schematics of Computation (1995), chapter 10.

(load "ExprUtil.scm")

(define pattern-variable?
  (lambda (x)
    (and
     (symbol? x)
     (char=? (string-ref (symbol->string x) 0) #\?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;   REPLACEMENT/MATCHING PROCEDURES    ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Does the matching of pat-var with targ-exp agree with
;;the substitution so far, answers?
(define agrees-with?
  (lambda (patvar target-expression answers)
    (let ((x (assv patvar answers)))
      (if x
	  (equal? (cdr x) target-expression)
	  #t))))

;;Add (patvar.targexp) to the substitution so far.
;;Make sure it agrees with answers before adding it.
(define add-answer
  (lambda (patvar targexp answers)
    (if (assv patvar answers)
	answers ;;This patvar is already included in answers.
	(cons (cons patvar targexp) answers))))

(define attempt-add-answer
  (lambda (patvar targexp answers)
    (if (agrees-with? patvar targexp answers)
	(add-answer patvar targexp answers)
	#f)))

(define helper-basic-named
 (lambda (named-t name-getter pat expr answers)
   (and (is-type? expr named-t)
	(if (pattern-variable? (cadr pat))
	    (attempt-add-answer (cadr pat) (name-getter expr) answers)
	    (if (equal? (cadr pat) (name-getter expr)) answers #f)))))

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
       ;; ANYTHING AT ALL
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
       ((equal? (car pat) 'not)
	(and (is-type? expr not-t)
	     (expr-match-helper (cadr pat) (get-sh expr) answers))) ;;Don't forget the cadr! not the cdr! Yeesh.
       ;; BINARIES : We won't strictly check if the pattern has a true binary connective symbol...
       ((equal? (car pat) 'binary)
	(and (is-type? expr (cadr pat))
	     (let ((new-answers (expr-match-helper (caddr pat) (get-lh expr) answers)))
	       (if new-answers
		   (expr-match-helper (cadddr pat) (get-rh expr) new-answers)
		   #f))))
       ;; FUNCTION
       ((equal? (car pat) 'function)
	(helper-arglist function-t pat expr answers))
       ;; RELATION
       ((equal? (car pat) 'relation)
	(helper-arglist relation-t pat expr answers))
       ;; EXISTENTIAL
       ((equal? (car pat) 'universal)
	(helper-quantifier universal-t pat expr answers))
       ;; UNIVERSAL
       ((equal? (car pat) 'universal)
	(helper-quantifier universal-t pat expr answers))
       (else #f)))))

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

;;Takes a pattern, a substitution (one made with expr-match?, I'd hope),
;;and returns a pattern with all substitutions made.
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
	      (let ((r (assv item substitution)))
		(if r
		    (if (symbol? (cdr r))
			(string->true-symbol (string-append "'" (symbol->string (cdr r)))) ;;otherwise it's an expression.
			(string->true-symbol (print-expression-evaluable (cdr r))))
		    item)))
	     ((list? item)
	      (replace item))
	     (else item)))))
      (map replace pattern))))
