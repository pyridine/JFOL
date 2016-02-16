;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   Unification.scm
;;;;
;;;; Defines a procedure which finds the Most General Unifier
;;;; variable substitution for a list of terms.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "ExprUtil.scm")
(load "VariableSubstitution.scm")

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
  
;;A textual representation of a substitution
(define print-sub
  (lambda (sub)
    (map
     (lambda (u)
       (cons (car u) (print-pf (cdr u))))
     sub)))

(define ps print-sub) 
