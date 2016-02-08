;;     This file includes an abstract representation for propositional formulas,
;;     As well as some formal utilities for them.

;;Load utilities
(load "ListStuff.scm")

;;define-record type is specified in SRFI-9, here:
;;http://srfi.schemers.org/srfi-9/srfi-9.html
(define-record-type pf-expression
  (--pf-expression-create signifier lh-expression rh-expression)
  pf-expression?
  (signifier  get-signifier set-signifier)
  (lh-expression get-lh-expression set-lh-expression)
  (lh-expression get-single-expression set-single-expression) ;;for unary preds (negation)
  (lh-expression get-propositional-letter set-propositional-letter) ;;for propletters
  (rh-expression get-rh-expression set-rh-expression)
  )

(begin
  (define pf-letter-sig 'LETTER)
  (define pf-not-sig 'NOT)
  (define pf-and-sig 'AND)
  (define pf-or-sig  'OR)
  (define pf-imp-sig 'IMP)
  (define pf-revimp-sig 'REVIMP)
  (define pf-nand-sig 'NAND)         ;;NAND IS UP-ARROW!!!
  (define pf-nor-sig 'NOR)           ;;NOR IS DOWN-ARROW!!!
  (define pf-notimp-sig 'NOTIMP)
  (define pf-notrevimp-sig 'NOTREVIMP)
  (define pf-equiv-sig 'EQUIV)
  (define pf-inequiv-sig 'INEQUIV)
  (define pf-atomic-true-sym '-PFATOMICTRUE)
  (define pf-atomic-false-sym '-PFATOMICFALSE))

;;Whether pfexp is a binary expression.
(define pf-binary?
  (lambda (pfexp)
    (let ((sig (get-signifier pfexp)))
      (if
       (or
	(equal? sig pf-atomic-true-sym)
	(equal? sig pf-atomic-false-sym)
	(equal? sig pf-letter-sig)
	(equal? sig pf-not-sig))
       #f
       #t)))) ;;could be more elegant but WHAT EVER NOT NOW

(define atomic-true
  (--pf-expression-create pf-atomic-true-sym nil nil))

(define atomic-false
   (--pf-expression-create pf-atomic-false-sym nil nil))

(define make-propositional-letter
  (lambda (sym)
    (--pf-expression-create pf-letter-sig sym nil)))

(define make-negation
  (lambda (pf-expression)
    (--pf-expression-create pf-not-sig pf-expression nil)))

(define make-binary
  (lambda (sig-connective lh-expression rh-expression)
    (--pf-expression-create sig-connective lh-expression rh-expression)))

;;A recursive type predicate.
;;Can be used like (pf-is-type? expr pf-equiv-sig)
;;         or even (pf-is-type? expr pf-not-sig pf-and-sig)
;;Pass arguments in order of descending major connective.
;;When asked for a deeper predicate after a binary predicate, only the LH expression will be checked.
(define pf-is-type?
  (lambda (expression sig . rest-sigs)
    (if (equal? (get-signifier expression) sig)
	(if (not (null? rest-sigs))
	    (apply pf-is-type? (cons (get-single-expression expression) rest-sigs))
      	    #t)
	#f)))
	
;;Fitting 28: A literal is a propositional letter or its negation, or a constant, T or F.
(define pf-literal?
  (lambda (pform)
    (or
     (equal? pform atomic-true)
     (equal? pform atomic-false)
     (if (pf-is-type? pform pf-letter-sig)
	 #t
	 (if (pf-is-type? pform pf-not-sig)
	     (if (pf-is-type? (get-single-expression pform) pf-letter-sig)
		 #t
		 #f)
	     #f))
     #f)))

;;Return a list of the Alpha/Beta (Conjunctive/Disjunctive) components, or the empty list if the expression is not an alph or beta expression.
(define --internal-components
  (lambda (in want-conjunctive)
      (cond
	;;X,Y
	((if want-conjunctive
	     (or ;;conjunctive conditions
	      (pf-is-type? in pf-and-sig)
	      (pf-is-type? in pf-not-sig pf-nand-sig))
	     (or ;;disjunctive conditions
	      (pf-is-type? in pf-or-sig)
	      (pf-is-type? in pf-not-sig pf-nor-sig)))
	 (let ((fin  (if (pf-is-type? in pf-not-sig) (get-single-expression in)in))) 
	   (list (get-lh-expression fin) (get-rh-expression fin))))
	;;~X,~Y
	((if want-conjunctive
	     (or ;;conjunctive conditions
	      (pf-is-type? in pf-nor-sig)
	      (pf-is-type? in pf-not-sig pf-or-sig))
	     (or ;;disjunctive conditions
	      (pf-is-type? in pf-nand-sig)
	      (pf-is-type? in pf-not-sig pf-and-sig)))
	 (let ((fin  (if (pf-is-type? in pf-not-sig) (get-single-expression in) in))) 
	   (list (make-negation (get-lh-expression fin)) (make-negation (get-rh-expression fin)))))
	;;X,~Y
	((if want-conjunctive
	     (or ;;conjunctive conditions
	      (pf-is-type? in pf-notimp-sig)
	      (pf-is-type? in pf-not-sig pf-imp-sig))
	     (or ;;disjunctive conditions
	      (pf-is-type? in pf-revimp-sig)
	      (pf-is-type? in pf-not-sig pf-notrevimp-sig)))
	 (let ((fin  (if (pf-is-type? in pf-not-sig) (get-single-expression in)in))) 
	   (list (get-lh-expression fin) (make-negation (get-rh-expression fin)))))
	;;~X,Y
	((if want-conjunctive
	     (or ;;conjunctive conditions
	      (pf-is-type? in pf-notrevimp-sig)
	      (pf-is-type? in pf-not-sig pf-revimp-sig))
	     (or ;;disjunctive conditions
	      (pf-is-type? in pf-imp-sig)
	      (pf-is-type? in pf-not-sig pf-notimp-sig)))
	 (let ((fin  (if (pf-is-type? in pf-not-sig) (get-single-expression in)in))) 
	   (list (make-negation (get-lh-expression fin))  (get-rh-expression fin))))
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

;;Strings any series of propositions together by a single binary connective.
(define string-propositions
  (lambda (sig prop1 prop2 . rest)
    (if (null? rest)
	(make-binary sig prop1 prop2)
	(apply string-propositions sig
	       (append (list (make-binary sig prop1 prop2) (car rest))
		       (cdr rest))))))

;;A string represerntation of a propositional formula.
(define print-pf
  (lambda (in)
    (apply string-append 
	   (cond
	    ((equal? in atomic-true) (list "TRUE"))
	    ((equal? in atomic-false) (list "FALSE"))
	    ((pf-is-type? in pf-letter-sig) (list (symbol->string (get-propositional-letter in))))
	    ((pf-is-type? in pf-not-sig) (list "~" (print-pf (get-single-expression in))))
	    (else
	     (list
	      "("
	      (print-pf (get-lh-expression in))
	      " " (symbol->string (get-signifier in)) " "
	      (print-pf (get-rh-expression in))
	      ")"
	      ))))))

(define test1 (make-binary pf-and-sig (make-propositional-letter 'CBC)  (make-negation (make-propositional-letter 'ABA))))
(define test2 (make-binary pf-or-sig (make-propositional-letter 'CBC)  (make-negation (make-propositional-letter 'ABA))))
(define test3 (make-binary pf-and-sig test1 test2))

(define ta (make-propositional-letter 'A))
(define tnota (make-negation ta))
(define tb (make-propositional-letter 'B))
(define tc (make-propositional-letter 'C))

;;not (A and not A)
(define tautology1
  (make-negation
   (make-binary
    'AND
    ta
    (make-negation ta))))

;;proof by cases
(define tautology2
  (make-binary
   'IMP
   (string-propositions
    'AND
    (make-binary 'OR ta tb)
    (make-binary 'IMP ta tc)
    (make-binary 'IMP tb tc))
   tc))

;;Modus ponens
(define tautology3
  (make-binary
   'IMP
   (make-binary
    'AND
    ta
    (make-binary 'IMP ta tb))
   tb))

;;Modus tollens
(define tautology4
  (make-binary
   'IMP
   (make-binary
    'AND
    (make-binary 'IMP ta tb)
    (make-negation tb))
   (make-negation ta)))

;;Transitivity
(define tautology5
  (make-binary
   'IMP
   (make-binary
    'AND
    (make-binary 'IMP ta tb)
    (make-binary 'IMP tb tc))
   (make-binary 'IMP ta tc)))
