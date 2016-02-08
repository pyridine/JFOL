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
     (if (is-type? pform letter-t)
	 #t
	 (if (is-type? pform not-t)
	     (if (is-type? (get-single-expression pform) letter-t)
		 #t
		 #f)
	     #f))
     #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     DESTRUCTURING PROCEDURES         ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Return a list of the Alpha/Beta (Conjunctive/Disjunctive) components, or the empty list if the expression is not an alph or beta expression.
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
      (let ((fin  (if (is-type? in not-t) (get-single-expression in)in))) 
	(list (get-lh-expression fin) (get-rh-expression fin))))
     ;;~X,~Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in nor-t)
	   (is-type? in not-t or-t))
	  (or ;;disjunctive conditions
	   (is-type? in nand-t)
	   (is-type? in not-t and-t)))
      (let ((fin  (if (is-type? in not-t) (get-single-expression in) in))) 
	(list (negation (get-lh-expression fin)) (negation (get-rh-expression fin)))))
     ;;X,~Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in notimp-t)
	   (is-type? in not-t imp-t))
	  (or ;;disjunctive conditions
	   (is-type? in revimp-t)
	   (is-type? in not-t notrevimp-t)))
      (let ((fin  (if (is-type? in not-t) (get-single-expression in)in))) 
	(list (get-lh-expression fin) (negation (get-rh-expression fin)))))
     ;;~X,Y
     ((if want-conjunctive
	  (or ;;conjunctive conditions
	   (is-type? in notrevimp-t)
	   (is-type? in not-t revimp-t))
	  (or ;;disjunctive conditions
	   (is-type? in imp-t)
	   (is-type? in not-t notimp-t)))
      (let ((fin  (if (is-type? in not-t) (get-single-expression in)in))) 
	(list (negation (get-lh-expression fin))  (get-rh-expression fin))))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;======================================;;
;;     CONSTRUCTIVE PROCEDURES          ;;
;;======================================;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Strings any series of propositions together by a single binary connective.
(define string-propositions
  (lambda (sig prop1 prop2 . rest)
    (if (null? rest)
	(binary sig prop1 prop2)
	(apply string-propositions sig
	       (append (list (binary sig prop1 prop2) (car rest))
		       (cdr rest))))))

;;A string represerntation of a propositional formula.
(define print-pf
  (lambda (in)
    (apply string-append 
	   (cond
	    ;;Base
	    ((true? in) (list "TRUE"))
	    ((false? in) (list "FALSE"))
	    ((letter? in) (list (symbol->string (get-propositional-letter in))))
	    ((constant? in) (list (symbol->string (get-name in))))
	    ((variable? in) (list (symbol->string (get-variable in))))
	    ;;Recursion
	    ((is-type? in not-t) (list "~" (print-pf (get-single-expression in))))
	    ((universal? in) (list "ALL " (symbol->string (get-variable in)) ": " (print-pf (get-single-expression in)) ))
	    ((existential? in) (list "SOME " (symbol->string (get-variable in)) ": " (print-pf (get-single-expression in)) ))
	    ((or (function? in)
		 (relation? in)) (list (symbol->string (get-name in)) "("
				       (recurse-string print-pf (get-expr-list in) ",") ")"))
	    (else ;;Binary recursion
	     (list
	      "(" (print-pf (get-lh-expression in))
	      " " (symbol->string (get-type in)) " "
	          (print-pf (get-rh-expression in))")"))))))
