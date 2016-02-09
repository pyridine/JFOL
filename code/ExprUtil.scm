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
      (list-variables (get-sh e)))
     ((binary? e)
      (append (list-variables (get-rh e))
	      (list-variables (get-lh e))))
     ((negation? e)
      (list-variables (get-sh e)))
     ((or (function? e) (relation? e))
      (raise-list (append
		  (map list-variables (get-args e))))))))

;;The list of variables that quantifiers scope over in an expression.
;;EG: All[X]Exists[Z](Loves(M,Y)) will return (X Z)
(define list-variables-scoped
  (lambda (e)
    (cond
     ((basic? e) '())
     ((or (existential? e) (universal? e))
      (cons (get-variable e)
	    (list-variables (get-sh e))))
     ((binary? e)
      (append (list-variables (get-rh e))
	      (list-variables (get-lh e))))
     ((negation? e)
      (list-variables (get-sh e)))
     ((or (function? e) (relation? e))
      (raise-list(append
	(map list-variables (get-args e))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     CONSTRUCTIVE PROCEDURES          ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define substitute-variable
  (lambda (variable substitution)
    (let ((rep (assv (get-variable variable) substitution)))
      (if rep (cdr rep) variable))))

;;Removes a variable from a substitutions's support.
(define unsupport
  (lambda (var sub)
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
				     (unsupport (get-variable s) sub))))
     ((existential? s)
      (existential (get-variable s)
		   (apply-substitution (get-sh s)
				       (unsupport (get-variable s) sub))))
     ((binary? s)
      (binary (get-type s)
	      (apply-substitution (get-lh s) sub)
	      (apply-substitution (get-rh s) sub)))
     ((relation? s)
      (relation (get-name s)
		(map
		 (lambda (s) (apply-substitution s sub))
		 (get-args s))))
     ((function? s)
      (function (get-name s)
		(map
		 (lambda (s) (apply-substitution s sub))
		 (get-args s)))))))

;;Strings any series of propositions together by a single binary connective.
(define string-propositions
  (lambda (sig prop1 prop2 . rest)
    (if (null? rest)
	(binary sig prop1 prop2)
	(apply string-propositions sig
	       (append (list (binary sig prop1 prop2) (car rest))
		       (cdr rest))))))

;;Returns 
(define disagreement-pair
  9
  )

;;Creates a substitution that unifies two sentences.
(define 2nify
  (lambda (s1 s2)
    4
    )
  )



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
	    ((universal? in) (list "ALL " (symbol->string (get-variable in)) ": " (print-pf (get-sh in)) ))
	    ((existential? in) (list "SOME " (symbol->string (get-variable in)) ": " (print-pf (get-sh in)) ))
	    ((or (function? in)
		 (relation? in)) (list (symbol->string (get-name in)) "("
				       (recurse-string print-pf (get-args in) ",") ")"))
	    (else ;;Binary recursion
	     (list
	      "(" (print-pf (get-lh in))
	      " " (symbol->string (get-type in)) " "
	          (print-pf (get-rh in))")"))))))

(define pe print-pf) ;;I type this too much
