;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   FOLUtil.scm
;;;;
;;;; Workhorse utilities for FOL expressions.
;;;;
;;;; For a new basic library, just load this file - it depends on
;;;; both the representation file and the list utility file.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module basic-fol *
  (import chicken scheme)
  (reexport utility)
  (reexport expressions)
    
    ;;======================================;;
    ;;     HOFS                             ;;
    ;;======================================;;

    ;;Given a term location (n1 n2 n3 ... nn),
    ;;return the expression that results by diving into a term like it was a tree.
    (define descend-term
      (lambda (term location)
	(if (null? location)
	    term
	    (descend-term
	     (list-ref (get-args term) (car location))
	     (cdr location)))))

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

  ;;======================================;;
  ;;     DESTRUCTURING PROCEDURES         ;;
  ;;======================================;;

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

  (define list-variables-in-list
    (lambda (l)
      (remove-duplicates (apply append (map list-variables l)))))

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


  
  ;;Two expressions agree surface-structurally if they are identical but for
  ;;any place where a term must occur.
  ;;Terms occur inside relations and nowhere else.
  (define agree-term-locations?
    (lambda (e1 e2)
      (cond
       ;;Two terms agree structurally. A term and a non-term do not agree.
       ((term? e1) (term? e2))
       ;;Two non-terms of different types do not agree.
       ((not (equal? (get-type e1) (get-type e2))) #f)
       ;;Two negations agree if their expressions agree.
       ((negation? e1) (agree-term-locations? (get-sh e1) (get-sh e2)))
       ;;Quantifiers agree if they have the same variable and their expressions agree. 
       ((or (existential? e1) (universal? e1)) (and (equal? (get-variable e1) (get-variable e2))
						    (agree-term-locations? (get-sh e1) (get-sh e2))))
       ;;Two relations agree if they have the same name and arity. (We assume both are well-formed; i.e., they consist of terms.)
       ((relation? e1) (and (relation? e2)
			    (equal? (get-name e1) (get-name e2))
			    (equal? (get-arity e1) (get-arity e2))))
       ;;Two binaries agree if they are of the same type (checked above) and their expressions agree.
       ((binary? e1) (and
		      (agree-term-locations? (get-lh e1) (get-lh e2))
		      (agree-term-locations? (get-rh e1) (get-rh e2))))
       (else #f))))

  (define list-surface-terms
    (lambda (e)
      (cond
       ((term? e) e)
       ((relation? e) (get-args e))
       ((unary? e) (list-surface-terms (get-sh e)))
       ((binary? e) (append (list-surface-terms (get-lh e))
			    (list-surface-terms (get-rh e)))))))



  ;;======================================;;
  ;;     CONSTRUCTIVE PROCEDURES          ;;
  ;;======================================;;

  ;;A new function symbol for a single expression.
  (define new-function-symbol
    (lambda (e)
      (unique-symbol 'F (list-function-names e))))

  ;;A new variable symbol for a single expression.
  (define new-variable-symbol
    (lambda (e)
      (unique-symbol 'X (list-variables e))))

  ;;A new variable symbol for a single expression.
  (define new-constant-symbol
    (lambda (e)
      (unique-symbol 'C (list-constants e))))

  ;;Strings any series of propositions together by a single binary connective.
  (define string-propositions
    (lambda (sig prop1 prop2 . rest)
      (if (null? rest)
	  (binary sig prop1 prop2)
	  (apply string-propositions sig
		 (append (list (binary sig prop1 prop2) (car rest))
			 (cdr rest))))))

  ;;Strings a list of expressions by a binary sig and just sort of works nicer than string-propositions...
  (define string-proposition-list
    (lambda (sig list)
      (if (= (length list) 1)
	  (car list)
	  (if (= (length list) 2)
	      (binary sig (car list) (cadr list))
	      (binary sig (car list) (apply string-propositions (cons sig (cdr list))))))))


  ;;======================================;;
  ;;     VARIABLE SUBSTITUTION            ;;
  ;;======================================;;

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

  (define substitution?
    (lambda (s)
      (and
       (list? s)
       (eval (cons 'and
		   (map (lambda (x)
			  (and (pair? x) (symbol? (car x)) (expression? (cdr x))))
			s))))))

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



  ;;This substitution will also replace the quantifier variables.
  ;;Requires a list of (symbol . variable-exp) pairs.
  (define apply-variable-renaming
    (lambda (s sub)
      (cond
       ((or
	 (true? s)
	 (false? s)
	 (constant? s)) s)
       ((variable? s) (substitute-variable s sub)) ;;The important Line
       ((negation? s)
	(negation (apply-variable-renaming (get-sh s) sub)))
       ((universal? s)
	(universal (get-variable (apply-variable-renaming (variable (get-variable s)) sub))
		   (apply-variable-renaming (get-sh s)
					    sub)))
       ((existential? s)
	(existential (get-variable (apply-variable-renaming (variable (get-variable s)) sub))
		     (apply-variable-renaming (get-sh s)
					      sub)))
       ((binary? s)
	(binary (get-type s)
		(apply-variable-renaming (get-lh s) sub)
		(apply-variable-renaming (get-rh s) sub)))
       ((relation? s)
	(apply relation
	       (cons (get-name s)
		     (map
		      (lambda (s) (apply-variable-renaming s sub))
		      (get-args s)))))
       ((function? s)
	(apply function
	       (cons (get-name s)
		     (map
		      (lambda (s) (apply-variable-renaming s sub))
		      (get-args s))))))))

  ;;Renames the variables in an expression that occur in the forbidden-list.
  ;;Forbid-variables is a list of SYMBOLS.
  (define rename-variables
    (lambda (e forbid-vars)
      (let* ((e-vars                (set-union (list-variables-instantiated e) (list-variables-scoped e)))
	     (forbidden-new-symbols (append forbid-vars e-vars))
	     (offending-vars (list-intersect e-vars forbid-vars)))
	(letrec ((recursive-make-renaming-substitution
		  (lambda (varlist forbid)
		    (if (null? varlist)
			null
			(let ((newsym (unique-symbol 'X forbid)))
			  (cons
			   (cons (car varlist) (variable newsym) )
			   (recursive-make-renaming-substitution (cdr varlist) (cons newsym forbid))))))))
	  (apply-variable-renaming e (recursive-make-renaming-substitution offending-vars forbidden-new-symbols))))))

  ;;Ensures no variable in the list of expressions e has any variable occurences in forbid-vars.
  ;;does NOT add the variables of previous expressions to the forbid list.
  (define rename-variables-in-list
    (lambda (e forbid-vars)
      (if (null? e)
	  '()
	  (let ((newe (rename-variables (car e) forbid-vars)))
	    (cons
	     newe
	     (rename-variables-in-list (cdr e) forbid-vars))))))

  ;;Ensures no variable in the list of expressions e has any variable occurences in forbid-vars.
  ;;DOES add the variables of previous expressions to the forbid list.
  (define completely-rename-variables-in-list
    (lambda (e forbid-vars)
      (if (null? e)
	  '()
	  (let ((newe (rename-variables (car e) forbid-vars)))
	    (cons
	     newe
	     (rename-variables-in-list (cdr e) (append (list-variables newe) forbid-vars)))))))

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

  ;;======================================;;
  ;;     PRINTING......                   ;;
  ;;======================================;;

  ;;A string represerntation of a propositional formula.
  (define print-pf
    (lambda (in)
      (apply string-append 
	     (cond
	      ;;Base
	      ((true? in) (list "True"))
	      ((false? in) (list "False"))
	      ((constant? in) (list (symbol->string (get-name in))))
	      ((variable? in) (list (symbol->string (get-variable in))))
	      ;;Recursion
	      ((is-type? in not-t) (list "(not " (print-pf (get-sh in)) ")"))
	      ((universal? in) (list "All " (symbol->string (get-variable in)) " (" (print-pf (get-sh in)) ")" ))
	      ((existential? in) (list "Some " (symbol->string (get-variable in)) " (" (print-pf (get-sh in)) ")" ))
	      ((or (function? in) (relation? in))
	       (list (symbol->string (get-name in))
		     "[" (recurse-string print-pf (get-args in) ",") "]"))
	      ;;Binary
	      (else
	       (list "(" (print-pf (get-lh in)) " "
		     (cdr (assv (get-type in) bin-sym-string-assoc)) " "
		     (print-pf (get-rh in))")"))
	      ))))

  (define pe print-pf)

  (define print-clause
    (lambda (clause) (string-append "[" (recurse-string pe clause " | ") "]")))
  
  (define substitution->string
    (lambda (s)
      (if (null? s)
	  " "
	  (string-append
	   "["
	   (symbol->string (caar s))
	   " -> "
	   (pe (cdar s))
	   "] "
	   (substitution->string (cdr s))))))
  )

;;hooray
