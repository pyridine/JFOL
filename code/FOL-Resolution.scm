;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   FOL-Resolution.scm
;;;;
;;;; Implements FOL Resolution,
;;;; on expressions in Prenex, Skolemized, Clause Form (CNF)
;;;; including only the connectives AND, NOT, and OR.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "Unification.scm")
(load "Simplification")

;;The Y rule: from Ax{e(x)}, conclude e(c) for ANY closed term c.
;;151: We replace Y with Y(x), for x being a free variable whose value we will determine later.
;;
;;The idea is: can values for free variables be found that result in closed branches?
;; For instance, if we have  P(t1) and ~P(t2), can we satisfy t1=t2?

;;211: we can drop the quantifiers altogether, and work with the list C1, C2, ... CK of clauses containing free variables.
;;     But remember the quantifiers are implicitly present. So we never work with any clause directly, but rather with
;;     the result of renaming variables, replacing them with new free variables, effectively applicating Y rule.
;;     So we apply the Resolution rule to two clauses C1 and C2 containing free variables. 

;;If it is possible that two expressions can be unified into P and ~P.
(define potentially-unifiable-to-contradiction?
  (lambda (e1 e2)
    (letrec ((is-reverse-of-maybe-unifiable?
	      (lambda (e1 e2)
		(and
		 (negation? e1)
		 (agree-term-locations? (get-sh e1) e2)))))
      (or
       (is-reverse-of-maybe-unifiable? e1 e2)
       (is-reverse-of-maybe-unifiable? e2 e1)))))

;;Renames the variables in a list of expressions so that no variable name repeats per each expression.
(define uniquify-variables-in-expr-list
  (lambda (list)
    (letrec ((recur (lambda (list forbidden-vars)
		      (if (null? list)
			  '()
			  (let* ((nexpr (car list))
				 (nexprvars (remove-duplicates (list-variables nexpr)))
				 (new-forbidden (append nexprvars forbidden-vars))
				 (var-renaming (map (lambda (var) ;;WARNING: FAILURE!!!! YOU NEED TO APPLY THIS RECURSIVELY,
						      (let ((newsym (unique-symbol 'V new-forbidden)))
							(begin
							  (set! new-forbidden (cons newsym new-forbidden))
							  (cons var ;;BECAUSE IT JUST USES THE NEXT AVAILABLE SYMBOL OVER AND OVER!!
								;;You might consider using a letrec'd function which set!s the forbidden list.
								;;I.e. the forbidden list would no longer be passed as an arg.
								(variable (unique-symbol 'V new-forbidden))))))
						    nexprvars)))
			    (cons (apply-variable-renaming nexpr var-renaming)
				  (recur (cdr list) new-forbidden)))))))
      (recur list '()))))

;;Ensure only that each individual sentence is named apart.
;;We will take care of the rest.
(define create-FOL-resolution-premise
  (lambda (conclusion . premises)
    (strip-quantifiers
     (skolemize
      (prenex
       (reduce-connectives
	(string-proposition-list
	 'AND
	 (uniquify-variables-in-expr-list (cons (neg conclusion) premises)))))))))

;;A record for an application of the General Literal Resolution rule (the unification-applying one).
(define-record-type  GLR-record
  (new-GLR-record)
  GLR-record?
  ;;The list of "X" literals
  (true-literals get-true-literals set-true-literals)
  ;;The list of "~Z" literals. STORED WITH THE NEGATION.
  (neg-literals get-neg-literals set-neg-literals)
  ;;The unifier that makes each of these literals equal.
  (unifier  get-unifier set-unifier)
  ;;The line you need to add to the resolution. REMEMBER: BECAUSE THE VARIABLES ARE CHANGED UPON COMPARING CLAUSES, WE ONLY KNOW THE NEW LINE
  ;;WHILE CONSTRUCTING THE GLR.
  (result-line get-result-line set-result-line)
  ;;Book-Keeping: line numbers, not the actual lines.
  (true-parent-line get-true-parent-line set-true-parent-line)
  (neg-parent-line  get-neg-parent-line set-neg-parent-line))

;;Takes a list of atomics and a list of negated atomics.
;;Returns a list of ( ( (T1 ... Tn)  (N1 ... Nm) )* ) such that
;;each T appears in trus, each N appears in negs, and {T1...Tn,(get-sh N1)...(get-sh Nm)} all agree on term locations (are potentially unifiable).
;;No item appears twice.
(define potential-GLR-lists-finder
  (lambda (trus negs)
    (if (null? trus)
	null
	(let ((first (car trus)))
	  (let* ((tru-counterparts (filter (lambda (e) (agree-term-locations? first e)) trus)) ;;Will include first
		 (neg-counterparts (filter (lambda (e) (agree-term-locations? first (get-sh e))) negs ))
		 (unused-trus      (list-difference trus tru-counterparts))
		 (unused-negs      (list-difference negs neg-counterparts)))
	    (append
	     (if (> (+ (length tru-counterparts) (length neg-counterparts)) 1)
		 (list (list tru-counterparts neg-counterparts))
		 '()) ;;If only one term, not potentially an application of GLR.
	     (potential-GLR-lists-finder unused-trus unused-negs)))))))

;;Returns a list of ((<substitution> (t..t) (n..n) )*), for each valid GLR given the output of the above function "potential-GLR-lists-finder"....
;;So, you'll end up with... ( ( <substitution> (t...t) (n...n) )* )
(define find-unifications-for-potential-GLRs
  (lambda (potential-list)
    (if (null? potential-list)
	'()
	(let* ((next (car potential-list))
	       (trul (car next))
	       (negl (cadr next))
	       (mnegl (map get-sh negl))
	       (unification (apply unify-n-expressions (append trul mnegl))))
	  (cons
	   (if unification
	       (cons unification
		     (cons trul
			   (list negl)))
	       '())
	   (find-unifications-for-potential-GLRs (cdr potential-list))))))) 

;;Turns each item of find-unifications-for-potential-GLRs into GLR-records.
;;You will have to construct their new-lines yourself...?
(define but-into-GLRs
  (lambda (list true-parent neg-parent)
    (if (null? list)
	null
	(let ((newglr (new-GLR-record))
	      (data (car list)))
	  (begin
	    (set-unifier       newglr (car data))
	    (set-true-literals newglr (cadr data))
	    (set-neg-literals  newglr (caddr data))
	    (set-result-line newglr
			     (append
			      (list-difference true-parent (get-true-literals newglr))
			      (list-difference neg-parent (get-neg-literals newglr))))
	    (cons newglr (but-into-GLRs (cdr list) true-parent neg-parent)))))))

(define list-variables-in-list
  (lambda (l)
    (remove-duplicates (apply append (map list-variables l)))))

;; find-general-literal-resolution
;;Returns the most general GLR-record for a valid application of the General Literal Resolution rule on these two lines.
;;Returns #f if there is no possible GLR for these two lines.
;;Remember, after you use GLR on two lines, those lines are stricken from the proof (stricken from further GLR?)
;;INPUT:
;;    true-list is a list of expressions from which we will look for X literals.
;;    neg-list is a list of expressions from which we will look for ~Z literals.
;;
;; Because of the asymmetric nature of this function, if it doesn't work for one order of arguments, try the other.
;;
(define find-general-literal-resolution
  (lambda (true-list neg-list) ;;The list of expressions we will look for X and ~Z in. Call with args in different order if none was found.
    ;;For the neg list, we ensure no free variables match any in true-list.
    ;;So we need to not only make sure the neg list shares none with the true list, but that the true list's clauses share none too.
    ;;Renaming EVERY variable is implicitly an application of the Y rule.
    (let* ((original-true-vars (list-variables-in-list true-list))
	   (original-neg-vars  (list-variables-in-list neg-list))
	   (original-all-vars  (set-union original-true-vars original-neg-vars))
	   (renamed-neg-list   (rename-variables-in-list neg-list original-all-vars))
	   (renamed-neg-vars   (list-variables-in-list renamed-neg-list))
	   ;;Will rename repeating variables
	   (renamed-true-list (rename-variables-in-list true-list (append original-all-vars renamed-neg-vars))) 
	  ;;The ~Z
	  (negs (filter (lambda (e) (and (negation? e) (atomic? (get-sh e)))) renamed-neg-list))
	  ;;The X
	  (trus (filter atomic? renamed-true-list)))
      (if (or (null? negs) (null? trus))
	  #f ;;"No atomics in g1 or negatomics in g2" ;;FAILURE: Nothing to even potentially unify.;;A list of pairs of surface-term-agreeing terms.
	  (let* ((potential-GLRs  (potential-GLR-lists-finder trus negs)))
	    (if (null? potential-GLRs)
		#f ;;(list "No potentials" trus negs)
		(let ((real-GLRs (but-into-GLRs (find-unifications-for-potential-GLRs potential-GLRs) renamed-true-list renamed-neg-list)))
		  (if (null? real-GLRs)
		      #f;; "No GLRs."
		      (car (sort real-GLRs (lambda (a b) (< (length (get-result-line a) (get-result-line b))))))))))))))
