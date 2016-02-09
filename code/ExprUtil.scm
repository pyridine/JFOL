(load "ExprForm.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     BOOLEAN PROCEDURES               ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;A literal is a propositional letter or its negation, or a constant, T or F.
(define literal?
  (lambda (pform)
    (or
     (equal? pform true)
     (equal? pform false)
     (if (is-type? pform constant-t)
	 #t
	 (if (is-type? pform not-t)
	     (if (is-type? (get-sh pform) constant-t)
		 #t
		 #f)
	     #f))
     #f)))

;;Does expression 1 occur in expression 2?
(define occurs-in
  (lambda (x1 x2)
    (if (equal? x1 x2)
	#t
	(cond
	 ((basic? x2) #f)
	 ((unary? x2) (occurs-in x1 (get-sh x2)))
	 ((binary? x2) (or (occurs-in x1 (get-lh x2))
			   (occurs-in x1 (get-rh x2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     DESTRUCTURING PROCEDURES         ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Return a list of the Alpha/Beta (Conjunctive/Disjunctive) components,
;;or the empty list if the expression is not an alph or beta expression.
(define --internal-components
  (lambda (in want-conjunctive)
    (cond
     ;;X,Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in and-t)
	   (is-type? in not-t nand-t))
	  (or ;;disjunctive conditions
	   (is-type? in or-t)
	   (is-type? in not-t nor-t)))
      (let ((fin  (if (is-type? in not-t) (get-sh in)in))) 
	(list (get-lh fin) (get-rh fin))))
     ;;~X,~Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in nor-t)
	   (is-type? in not-t or-t))
	  (or ;;disjunctive conditions
	   (is-type? in nand-t)
	   (is-type? in not-t and-t)))
      (let ((fin  (if (is-type? in not-t) (get-sh in) in))) 
	(list (negation (get-lh fin)) (negation (get-rh fin)))))
     ;;X,~Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in notimp-t)
	   (is-type? in not-t imp-t))
	  (or ;;disjunctive conditions
	   (is-type? in revimp-t)
	   (is-type? in not-t notrevimp-t)))
      (let ((fin  (if (is-type? in not-t) (get-sh in)in))) 
	(list (get-lh fin) (negation (get-rh fin)))))
     ;;~X,Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in notrevimp-t)
	   (is-type? in not-t revimp-t))
	  (or ;;disjunctive conditions
	   (is-type? in imp-t)
	   (is-type? in not-t notimp-t)))
      (let ((fin  (if (is-type? in not-t) (get-sh in)in))) 
	(list (negation (get-lh fin))  (get-rh fin))))
     ;;Not an Alpha or Beta
     (else nil))))

;;Alpha formula components.
(define conjunctive-components
  (lambda (formula)
    (--internal-components formula #t)))

;;Beta formula components.
(define disjunctive-components
  (lambda (formula)
    (--internal-components formula #f)))

;;The list of variables that actually occur in an expression.
;;EG: All[X](Loves(Mary,Y)) will return (Y)
(define list-variables-instantiated
  (lambda (e)
    (cond
     ((variable? e) (list (get-variable e)))
     ((basic? e) '())
     ((or (existential? e) (universal? e))
      (list-variables-instantiated (get-sh e)))
     ((binary? e)
      (append (list-variables-instantiated (get-rh e))
	      (list-variables-instantiated (get-lh e))))
     ((negation? e)
      (list-variables-instantiated (get-sh e)))
     ((or (function? e) (relation? e))
      (raise-list (append
		  (map list-variables-instantiated (get-args e))))))))

;;The list of variables that quantifiers scope over in an expression.
;;EG: All[X]Exists[Z](Loves(M,Y)) will return (X Z)
(define list-variables-scoped
  (lambda (e)
    (cond
     ((basic? e) '())
     ((or (existential? e) (universal? e))
      (cons (get-variable e)
	    (list-variables-scoped (get-sh e))))
     ((binary? e)
      (append (list-variables-scoped (get-rh e))
	      (list-variables-scoped (get-lh e))))
     ((negation? e)
      (list-variables-scoped (get-sh e)))
     ((or (function? e) (relation? e))
      (raise-list(append
	(map list-variables-scoped (get-args e))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     CONSTRUCTIVE PROCEDURES          ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Given a list of forbidden symbols, returns a symbol that is different from each of them.
(define new-unique-variable-symbol
  (lambda (forbidden)
    (letrec ((sym-iterator
	      (lambda (symbol count)
		(letrec ((new-sym (string->symbol
				   (string-append
				    (symbol->string symbol)
				    (number->string count)))))
		  (if (member? new-sym forbidden)
			     (sym-iterator symbol (+ count 1))
			     new-sym
			     )))))
      (sym-iterator 'X 1))))

(define substitute-variable
  (lambda (variable substitution)
    (let ((rep (assv (get-variable variable) substitution)))
      (if rep (cdr rep) variable))))

;;Removes a variable from a substitutions's support.
(define substitution-unsupport
  (lambda (sub var)
    (remove-if (lambda (x) (equal? (car x) var)) sub)))

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
				     (substitution-unsupport (get-variable s) sub))))
     ((existential? s)
      (existential (get-variable s)
		   (apply-substitution (get-sh s)
				       (substitution-unsupport (get-variable s) sub))))
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


;;Returns the location of the disagreement pair between two ``terms``.
;;If there is no disagreement, returns #f.
;;A term location is a list (n1 n2 n3 ... nn) of numbers, where each
;;  number is which index to descend in while traversing the terms.
;;[terms = variables, constants, and functions of other terms.]
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
			location-so-far);;Disagreement on constant
		    )
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
			;;Otherwise, choose the first disagreement.
			(let ((disagreements
			       (map (lambda (one two) (disagreement-pair one two))
				    (get-args t1) (get-args t2) )))
			  (let ((numbered-disagreements (add-counters disagreements)))
			    (let ((first-disagreement
				   (first-member
				    (lambda (x) (not (equal? (car x) #f)))
				    numbered-disagreements)))
			      (if (null? first-disagreement)
				  #f ;;Agreement on function
				     ;;Disagreement on function
				  (append location-so-far
					  (list (cdr first-disagreement)) ;;its term number
					  (car first-disagreement) ;;its disagreement path
					  ))))))))))))
    (lambda (term1 term2)
      (recur term1 term2 '()))))

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
				"Infrep Failure" ;;Failure; would result in infinite replacement(?)
				(recur s1 s2 (cons (cons var-to-sub term-to-rep) csub)))))))))))
    (lambda (s1 s2)
      (recur s1 s2 '())
      )))
  

;;A string represerntation of a propositional formula.
(define print-pf
  (lambda (in)
    (apply string-append 
	   (cond
	    ;;Base
	    ((true? in) (list "TRUE"))
	    ((false? in) (list "FALSE"))
	    ((constant? in) (list (symbol->string (get-name in))))
	    ((variable? in) (list (symbol->string (get-variable in))))
	    ;;Recursion
	    ((is-type? in not-t) (list "~" (print-pf (get-sh in))))
	    ((universal? in) (list "ALL " (symbol->string (get-variable in)) ":[" (print-pf (get-sh in)) "]" ))
	    ((existential? in) (list "SOME " (symbol->string (get-variable in)) ":[" (print-pf (get-sh in)) "]" ))
	    ((or (function? in)
		 (relation? in)) (list (symbol->string (get-name in)) "("
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
