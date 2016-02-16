(load "ExprForm.scm")

;;A HOF used to list components of a FOL expression.
;;This can't do anything involving the structure the expression is contained in.
;;See its usage.
;;Func is a function of a SINGLE expression that returns either #f or <value>,
;;where <value> is the thing you want strung into the listtttt......
(define list-excom-by-func
  (lambda (e func)
    (let* ((res (func e))
	   (next-item (if res (list res) '())))
      (append
       next-item
       (cond
	((basic? e)   '())
	((unary? e)   (list-excom-by-func (get-sh e) func))
	((binary? e)  (append (list-excom-by-func (get-rh e) func)
			      (list-excom-by-func (get-lh e) func)))
	((or (function? e) (relation? e))
	 (raise-list
	  (append
	   (map (lambda (x) (list-excom-by-func x func)) (get-args e))))))))))

;;A simplified version of the above.
(define list-excom-by-querget
  (lambda (e e-query e-getter)
    (list-excom-by-func e (lambda (x) (if (e-query x) (e-getter x) #f)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     BOOLEAN PROCEDURES               ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Is the expression a term?
(define term?
  (lambda (e)
    (or
     (is-type? e variable-t)
     (is-type? e constant-t)
     (and (is-type? e function-t)
	  ;;Macros aren't first-order!!!! :(
	  (eval (cons 'and
		      (map (lambda (x) (term? x)) (get-args e))))))))

;;A literal is an atomic formula or its negation. (or true or false...)
(define literal?
  (lambda (p)
    (or
     (equal? p true)
     (equal? p false)
     (is-type? p not-t relation-t) ;;Assuming that the relation is well-formed.
     (is-type? p relation-t))))

(define non-literal?
  (lambda (p)
    (not (literal? p))))

;;Does expression 1 occur in expression 2?
(define occurs-in
  (lambda (x1 x2)
    (if (equal? x1 x2)
	#t
	(cond
	 ((basic? x2) #f)
	 ((unary? x2) (occurs-in x1 (get-sh x2)))
	 ((binary? x2) (or (occurs-in x1 (get-lh x2))
			   (occurs-in x1 (get-rh x2))))
	 ((or (function? x2) (relation? x2))
	     ;;Why aren't macros first-order?!
	     (eval (cons 'or (map (lambda (le) (occurs-in x1 le)) (get-args x2)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     DESTRUCTURING PROCEDURES         ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The list of variables that actually occur in an expression.
;;EG: All[X](Loves(Mary,Y)) will return (Y)
;;The list of variables that quantifiers scope over in an expression.
;;EG: All[X]Exists[Z](Loves(M,Y)) will return (X Z)
;;WARNING: If a variable occurs both free and bound in the expresion,
;;this algorithm has no way of differentiating between them.
;;Make variable names unique before applying this.
(define list-variables-instantiated
  (lambda (e)
    (list-excom-by-querget e variable? get-variable)))

;;The list of variables that quantifiers scope over in an expression.
;;EG: All[X]Exists[Z](Loves(M,Y)) will return (X Z)
;;WARNING: If a variable occurs both free and bound in the expresion,
;;this algorithm has no way of differentiating between them.
;;Make variable names unique before applying this.
(define list-variables-scoped
  (lambda (e)
    (list-excom-by-querget e quantifier? get-variable)))

;;Returns a list of the free variables in e.
;;WARNING: If a variable occurs both free and bound in the expresion,
;;this algorithm has no way of differentiating between them.
;;Make variable names unique before applying this.
(define list-free-variables
  (lambda (e)
    (list-difference
     (list-variables-instantiated e)
     (list-variables-scoped e))))

(define list-variables
  (lambda (e)
    (list-excom-by-querget e variable? get-variable)))

(define list-constants
  (lambda (e)
    (list-excom-by-querget e constant? get-name)))

(define list-function-names
  (lambda (e)
    (list-excom-by-querget e function? get-name)))

(define list-relation-names
  (lambda (e)
    (list-excom-by-querget e relation? get-name)))

(define strip-quantifiers
  (lambda (e)
    (if (quantifier? e)
	(strip-quantifiers (get-sh e))
	e)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     CONSTRUCTIVE PROCEDURES          ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;Strings a list of expressions by a binary sig.
(define string-proposition-list
  (lambda (sig list)
    (if (= (length list) 1)
	(car list)
	(if (= (length list) 2)
	    (binary sig (car list) (cadr list))
	    (binary sig (car list) (apply string-propositions (cons sig (cdr list))))))))

;;Takes a list of premises and a conclusion and conjuncts them together.
;; P1 & P2 & ... & PN & C
;;The idea is to derive a contradiction.
(define argument-to-sentence
  (lambda (conc . premises)
    (let ((negonc (make-negation conc)))
      (if (null? premises)
	  negonc
	  (apply string-propositions
		 (cons negonc premises))))))

(define list-function-symbols
  (lambda (e)
    (cond
     ((basic? e) '())
     ((unary? e) (list-function-symbols (get-sh e)))
     ((binary? e) (append (list-function-symbols (get-lh e))
			  (list-function-symbols (get-rh e))))
     ((relation? e) (apply append (map list-function-symbols (get-args e))))
     ((function? e) (cons (get-name e)
			  (apply append (map list-function-symbols (get-args e))))))))

;;Finds the replacement for a single variable expression.
(define substitute-variable
  (lambda (variable substitution)
    (let ((rep (assv (get-variable variable) substitution)))
      (if rep (cdr rep) variable))))

;;Removes a variable from a substitutions's support.
(define substitution-unsupport
  (lambda (sub var)
    (remove-if (lambda (x) (equal? (car x) var)) sub)))

;;Adds a variable-expression pair to a substitution.
(define substitution-support
  (lambda (var exp sub)
    (let ((sym (if (symbol? var) var (get-variable var)))) ;;Doesn't matter if you pass a symbol or a variable.
      (cons (cons sym exp) sub))))

;;Applies a substitution to an expression.
(define apply-substitution
  (lambda (s sub)
    (cond
     ((or
       (true? s)
       (false? s)
       (constant? s)) s)
     ((variable? s) (substitute-variable s sub)) ;;The important Line
     ((negation? s)
      (negation (apply-substitution (get-sh s) sub)))
     ((universal? s)
      (universal (get-variable s)
		 (apply-substitution (get-sh s)
				     (substitution-unsupport sub (get-variable s)))))
     ((existential? s)
      (existential (get-variable s)
		   (apply-substitution (get-sh s)
				       (substitution-unsupport sub (get-variable s)))))
     ((binary? s)
      (binary (get-type s)
	      (apply-substitution (get-lh s) sub)
	      (apply-substitution (get-rh s) sub)))
    ((relation? s)
      (apply relation
	     (cons (get-name s)
		   (map
		    (lambda (s) (apply-substitution s sub))
		    (get-args s)))))
     ((function? s)
      (apply function
	     (cons (get-name s)
		   (map
		    (lambda (s) (apply-substitution s sub))
		    (get-args s))))))))

;;For easily mapping a substitution over terms.
(define substitution-applier
  (lambda (sub . exprs)
    (map (lambda (x) (apply-substitution x sub)) exprs)))

;;Returns a function that substitutes one expression.
(define substitutor
  (lambda (substitution)
    (lambda (expression) (apply-substitution expression substitution))))

(define list-substitution-support
  (lambda (sub)
    (map (lambda (x) (car x)) sub)))

;;Combines substitutions:
;;Specifically, d1d2 is:
;;   { x1/(t1d2) x2/(t2d2) ... xn/(tnd2), z1/(z1d2) .... zn/(znd2) }, where z are variables suporrted by d2 and not d1.
(define compose-substitutions
  (lambda (d1 d2) 
    (let  ((d1-support (list-substitution-support d1))) 
      ;;3. Add those substitutions of d2 whose variables are not in the support of d1
      (append
       (remove-if (lambda (x) (member? (car x) d1-support)) d2)
       ;;2. Remove any substitution that has degenerated into x/x
       (remove-if
	(lambda (single-sub)
	  (equal? (variable (car single-sub)) (cdr single-sub))) ;;(car is always a variable symbol, cdr is always an expression)
	;;1. Apply d2 to all of d1's replacement terms
	(map (lambda (single-sub)
	       (cons
		(car single-sub)
		(apply-substitution (cdr single-sub) d2)))
	     d1))))))

;;Returns the location of the disagreement pair between two ``terms``.
;;If there is no disagreement, returns #f.
;;A term location is a list (n1 n2 n3 ... nn) of numbers, where each
;;  number is which index to descend in while traversing the terms.
;;[terms = variables, constants, and functions of other terms.
;; NOT... RELATIONS...!!!!!]
(define disagreement-pair
  (letrec ((recur
	    (lambda (t1 t2 location-so-far)
	      (if (not (equal? (get-type t1) (get-type t2)))
		  ;;If t1 and t2 differ in type, we have reached disagreement.
		  location-so-far
		  ;;If t1 and t2 are the same type...
		  (cond
		   ((is-type? t1 constant-t)
		    (if (equal? (get-name t1) (get-name t2))
			#f              ;;Agreement on constant
			location-so-far));;Disagreement on constant
		   ((is-type? t1 variable-t)
		    (if (equal? (get-variable t1)
				(get-variable t2))
			#f                ;;Agreement on variable
			location-so-far)) ;;Disagreement on variable
		   ((is-type? t1 function-t)
		    (if (or
			 (not (equal? (get-name t1) (get-name t2)))
			 (not (equal? (get-arity t1) (get-arity t2))))
			location-so-far ;;Disagreement on function arity/name.
			(let ((disagreements
			       (map (lambda (one two) (disagreement-pair one two))
				    (get-args t1) (get-args t2) )))
			  (let ((numbered-disagreements (add-counters disagreements)))
			    (let ((first-disagreement ;;Choose the first disagreement
				   (first-member
				    (lambda (x) (not (equal? (car x) #f)))
				    numbered-disagreements)))
			      (if (null? first-disagreement)
				  #f ;;Agreement on function
				     ;;Disagreement on function
				  (append location-so-far
					  (list (cdr first-disagreement)) ;;its term number
					  (car first-disagreement)))))))))))));;its disagreement path
    (lambda (term1 term2)
      (recur term1 term2 '()))))


;;A new function symbol for a single expression.
(define new-function-symbol
  (lambda (e)
    (unique-symbol 'FOOFUNCTION (list-function-names e))))

;;A new variable symbol for a single expression.
(define new-variable-symbol
  (lambda (e)
    (unique-symbol 'FOOVARIABLE (list-variables e))))

;;A new variable symbol for a single expression.
(define new-constant-symbol
  (lambda (e)
    (unique-symbol 'FOOCONSTANT (list-constants e))))

;;Strings any series of propositions together by a single binary connective.
(define string-propositions
  (lambda (sig prop1 prop2 . rest)
    (if (null? rest)
	(binary sig prop1 prop2)
	(apply string-propositions sig
	       (append (list (binary sig prop1 prop2) (car rest))
		       (cdr rest))))))

;;Creates a substitution that unifies two sentences.
;;[see fitting, 156]
(define unify-2
  (letrec ((recur
	    (lambda (s1 s2 csub) ;;sentence 1, sentence 2, current substitution
	      (let ((ss1 (apply-substitution s1 csub)) ;;"substituted s1"
		    (ss2 (apply-substitution s2 csub)))
		(if (equal? ss1 ss2)
		    csub
		    (let* ((disagreement-loc (disagreement-pair ss1 ss2))
			   (s1d (descend-term ss1 disagreement-loc));;"s1 disagreement term"
			   (s2d (descend-term ss2 disagreement-loc)))
		      (if (not (or (is-type? s1d variable-t)
				   (is-type? s2d variable-t)))
			  ;;If two terms disagree at non-variables, unification is impossible.
			  "Two nonvar failure"
			  (let ((var-to-sub  (get-variable (if (is-type? s1d variable-t) s1d s2d)))
				(term-to-rep (if (is-type? s1d variable-t) s2d s1d)))
			    (if (occurs-in (variable var-to-sub) term-to-rep)
				"Variable Reoccurrence Failure" ;;Failure; would result in infinite replacement(?)
				(recur s1 s2 (cons (cons var-to-sub term-to-rep) csub)))))))))))
    (lambda (s1 s2)
      (if (and (term? s1) (term? s2))
	  (recur s1 s2 '())
	  "ATTEMPT TO UNIFY TWO NON-TERMS"))))

(define substitution?
  (lambda (s)
    (and
     (list? s)
     (eval (cons 'and
		 (map (lambda (x)
			(and (pair? x) (symbol? (car x)) (expression? (cdr x))))
		      s))))))

;;Creates a substitution that unifies n sentences.
;;Garaunteed to result in the most general unifier, if it unifies at all.
;;[see fitting, 158]
(define unify
  (letrec  ((recur
	     (lambda (csub first second . rest) ;;current substitution, first term, second term, rest of the terms.
	       (let ((nsub (unify-2 first second)))
		 (if (not (substitution? nsub)) ;;unify-2 returns an error string if it fails.
		     (string-append nsub " ->" (print-pf first) ":" (print-pf second) " [" (print-sub csub) "]") ;;Describe the error
		     (let  ((cnsub (compose-substitutions csub nsub)))
		       (if (null? rest)
			   cnsub                                        ;;Success!
			   (apply recur                                 ;;Add a unification that encompasses the next term.
				  (append (list cnsub
						(apply-substitution first nsub ) ;;first has already been substituted with csub
						(apply-substitution (car rest) cnsub));;We apply the full changes to the next term.
					  (cdr rest))))))))))
    (lambda (first second . rest)
      (apply recur (append (list '() first second) rest)))))
  
;;A string represerntation of a propositional formula.
(define print-pf
  (lambda (in)
    (apply string-append 
	   (cond
	    ;;Base
	    ((true? in) (list "!True!"))
	    ((false? in) (list "!False!"))
	    ((constant? in) (list (symbol->string (get-name in))))
	    ((variable? in) (list "$" (symbol->string (get-variable in))))
	    ;;Recursion
	    ((is-type? in not-t) (list "~(" (print-pf (get-sh in)) ")"))
	    ((universal? in) (list "All $" (symbol->string (get-variable in)) " [" (print-pf (get-sh in)) "]" ))
	    ((existential? in) (list "Some $" (symbol->string (get-variable in)) " [" (print-pf (get-sh in)) "]" ))
	    ((or (function? in)
		 (relation? in)) (list  (if (function? in) "f" "r")
					(symbol->string (get-name in)) "("
					(recurse-string print-pf (get-args in) ",") ")"))
	    (else ;;Binary recursion
	     (list
	      "(" (print-pf (get-lh in))
	      " " (symbol->string (get-type in)) " "
	          (print-pf (get-rh in))")"))))))

;;A textual representation of a substitution
(define print-sub
  (lambda (sub)
    (map
     (lambda (u)
       (cons (car u) (print-pf (cdr u))))
     sub)))

(define pe print-pf) ;;I type this too much
(define ps print-sub) 
