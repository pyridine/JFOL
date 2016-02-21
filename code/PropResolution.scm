;;Load Propositional Formula stuff
(load "ExprUtil.scm")
(load "Simplification.scm")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  STRUCTS AND DEFINITIONS
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-record-type proof-location
  (make-proof-location line-no disjunct-no)
  proof-location?
  (line-no get-line-no)             ;;Line number of proof
  (disjunct-no get-disjunct-no))    ;;Which disjunct of that line

;;expansion types
(begin
  (define expansion-type-a '-ALPHAEXPANSION)
  (define expansion-type-b '-BETAEXPANSION)
  (define expansion-type-nn '-DOUBLENEGEXPANSION)
  (define expansion-type-nttf '-NEGTRUETOFALSEEXPANSION)
  (define expansion-type-nftt '-NEGFALSETOTRUEEXPANSION))

(define-record-type resolution-step
  (make-step formula-list line-justification justification-string)
  resolution-step?
  (formula-list get-formulas)            ;;A list of pforms
  (line-justification get-justification-lines) ;;A (possibly empty) list of line numbers
  (justification-string get-justification-string))  ;;The type of justification... Make it a string.

(define-record-type resolution-proof
  (make-resolution-proof steps rule-application-records)
  resolution-proof?
  (steps get-steps set-steps)                ;;A list of resolution-steps
  ;;Rules record their appplication records here. Each rule shall have its own record list here,
  ;;                                              stored under a unique symbol with the almighty 'assv'.
  (rule-application-records get-rule-records set-rule-records) 
  )

;;A list of resolution-records

(define-record-type proof-location
  (make-proof-location line-no disjunct-no)
  proof-location?
  (line-no get-line-no)             ;;Line number of proof
  (disjunct-no get-disjunct-no))    ;;Which disjunct of that line

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  PROOF UTILITIES
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-resolution-proof
  (lambda (step1)
    (make-resolution-proof
     (list (make-step (list step1) '() "Premise"))
     '() ;;We start having made no rule applications, so no records.
     )))

(define locate-proof-line
  (lambda (proof line-no)
    (list-ref (get-steps proof) line-no)))

(define locate-proof-formula
  (lambda (proof location)
    (list-ref (locate-proof-line proof (get-line-no location)) (get-disjunct-no location))))

;;The number of lines (steps) in the proof.
;;Silly. But who cares.
(define proof-num-lines
  (lambda (proof)
    (apply + (map (lambda (x) 1 ) (get-steps proof)))))

(define add-to-rule-record
  (lambda (proof record-symbol list-of-items-to-add)
    (let* ((old-record   (assv record-symbol (get-rule-records proof)))
	   (new-items    (if old-record
			    (append list-of-items-to-add (cdr old-record))
			    list-of-items-to-add)))
      (set-rule-records proof (replace-assv record-symbol new-items (get-rule-records proof))))))

(define add-to-proof-steps
  (lambda (proof step-list)
    (set-steps proof (append (get-steps proof) step-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  ALPHA AND BETA EXPANSION
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-record-type expansion-record
  (make-expansion-record my-proof-location expansion-type)
  expansion-record?
  (my-proof-location get-expansion-location) ;;a 'proof-location' record. The line this expansion is due to.
  (expansion-type get-expansion-type)) ;;see the list of expansion tpye definitions

(define EXPANSION-SYMBOL 'EXPANSION)

(define get-expansions
  (lambda (proof)
    (let ((res (assv EXPANSION-SYMBOL (get-rule-records proof))))
      (if res (cdr res) nil))))

;;Alpha formula components. My old code depends on this returning nil for failure.
(define conjunctive-components
  (lambda (formula)
    (let ((a (alpha-components formula)))
      (if a a nil))))

;;Beta formula components. My old code depends on this returning nil for failure.
(define disjunctive-components
  (lambda (formula)
    (let ((b (beta-components formula)))
      (if b b nil))))

(define expansion-type-to-string
  (lambda (expansion-type)
    (cond
     ((equal? expansion-type expansion-type-nn) "~~A => A")
     ((equal? expansion-type expansion-type-nttf) "~T => F")
     ((equal? expansion-type expansion-type-nftt) "~F => T")
     ((equal? expansion-type expansion-type-a) "Alpha Expansion")
     ((equal? expansion-type expansion-type-b) "Beta Expansion")
     (else "Unknown Expansion Type Error"))))

(define expandable? 
  (lambda (pform)
    (or
     (not (null? (conjunctive-components pform)))  ;;expansion 1: alpha formulas
     (not (null? (disjunctive-components pform)))  ;;expansion 2: beta 
     (is-type? pform not-t not-t)    ;;trivial expansion 1: not not
     (and
      (is-type? pform not-t)
      (or                                      ;;trivial expansions 2 and 2: not T, not F.
       (equal? true  (get-sh pform))
       (equal? false  (get-sh pform)))))))

;;Returns '() or the expansion of the pform as a list of pforms. use `expandable?` first.
(define get-expansion
  (lambda (pform)
    (let ((disj (disjunctive-components pform))
	  (conj (conjunctive-components pform)))
      (if (null? disj)
	  (if (null? conj)
	      (if (is-type? pform not-t)
		  (let ((pform2 (get-sh pform)))
		    (cond
		     ((is-type? pform2 not-t) (get-sh pform2))
		     ((true? true pform2) false)
		     ((false? pform2) true)
		     (else nil)))
		  nil)
	      conj)
	  disj))))
;;Whether the resolution proof is closed. If one of its steps is empty.
(define proof-closed?
  (lambda (proof)
    ((a-member-is
      (lambda (step)
	(null? (get-formulas step))))
     (get-steps proof))))

;;Returns what type of expansion this pform has...
(define determine-expansion-type
  (lambda (pform)
    (cond
     ((is-type? pform not-t not-t) expansion-type-nn)
     ((and
       (is-type? pform not-t)
       (false? (get-sh pform)) expansion-type-nftt ))
     ((and
       (is-type? pform not-t)
       (equal? true (get-sh pform)) expansion-type-nttf ))
     ((not (null? (disjunctive-components pform))) expansion-type-b)
     ((not (null? (conjunctive-components pform))) expansion-type-a)
     (else 'ERRROOORRRRRR))))

;;Returns a single expansion record signifying the first expandable pform
;;occuring in this line. (or '() if no expansion is possible)
;;Line is a resolution-step, itsnumber is the number of the line in the proof..........
(define get-line-expansion
  (lambda (line itsnumber)
    (let
	((mapped-line (map expandable? (get-formulas line))))
      (let
	  ((expandable-ref (member-ref #t mapped-line)))
      (if (> expandable-ref -1)
	  (make-expansion-record
	   (make-proof-location itsnumber expandable-ref)
	   (determine-expansion-type (list-ref (get-formulas line) expandable-ref)))
	  '())))))

;;OUT: A list of line references of the proof to which expansion
;;has not yet been applied.
(define get-expandable-lines-refs
  (lambda (proof)
    (let ((expanded-lines (map get-line-no (map get-expansion-location (get-expansions proof))))
	  (total-lines (range-exclusive (proof-num-lines proof))))
      (list-difference total-lines expanded-lines))))

;;Returns an expansion-record of the next available expansion.
;;Returns '() if there is no expansion possible.
(define next-expansion
  (lambda (proof)
    (let ((expandable-lines (get-expandable-lines-refs proof)))
      ;;THIS MAKES EVERY POSSIBLE EXPANSION THEN TAKES THE FIRST NOT NULL!!!!! oh well
      (first-member
       not-null?
       (map
	get-line-expansion
	(map (lambda (n)
	       (locate-proof-line proof n))
	     expandable-lines)
	expandable-lines)))))



;;INPUT:
;;exptype is an expansion-type symbol
;;parent-line is a list of propositional formulas
;;expanding-ref is the ref into parent-line of the propositional formula we are expanding
;;OUTPUT:
;;A list of new lines of propositional-formulas to add.
;;(All expansion types result in a single new line... except for alpha expansion.)
(define construct-expansion-lines
  (lambda (exptype parent-line expanding-ref)
    (map remove-duplicates
	 (let (
	       ;;The base of the new line is the parent line missing its expanding formula.
	       (new-line (list-remove-ref parent-line expanding-ref))
	       ;;The pform we're expanding about.
	       (expander (list-ref parent-line expanding-ref)))
	   (if (equal? exptype expansion-type-a)
	       ;;If we're type a, we need to add two lines...
	       (list
		(cons (car (conjunctive-components expander))
		      new-line)
		(cons (cadr (conjunctive-components expander))
		      new-line))
	       ;;Otherwise, only one line needs to be added, which is the appension to new-line of...
	       (list (append
		      (if (equal? exptype expansion-type-b)
			  ;;Append the list of B components
			  (disjunctive-components expander)
			  ;;Append the list of the single needed component
			  (list (cond
				 ;;~~X -> X
				 ((equal? exptype expansion-type-nn)
				  (get-sh (get-sh expander)))
				 ;;~T -> F
				 ((equal? exptype expansion-type-nttf)  false)
				 ;;~F -> T
				 ((equal? exptype expansion-type-nftt)  true))))
		      new-line)))))))

;;This takes a proof, applies the specified expansion to it, and adds it to the proof's expansion record list.
(define apply-expansion!
  (lambda (proof expansion)
    (let(
	 ;;Parent expansion line-no
	 (expansion-line-no (get-line-no (get-expansion-location expansion)))
	 ;;Parent expansion line disjunct ref
	 (expansion-line-ref (get-disjunct-no (get-expansion-location expansion))))
      (let
	  ;;The parent line L
	  ((parent-line (locate-proof-line proof expansion-line-no)))
	(let (;;The string denoting the sort of expansion this is
	      (justification-string (expansion-type-to-string (get-expansion-type expansion)))
	      ;;A list of lists of propositional forms to add to the proof.
	      (lines-to-add  (construct-expansion-lines
			      (get-expansion-type expansion)
			      (get-formulas parent-line)
			      expansion-line-ref)))
	  (begin
	    ;;Add the expansion rule record to the list.
	    (add-to-rule-record proof EXPANSION-SYMBOL (list expansion))
	    ;;Add the steps to the proof
	    (add-to-proof-steps proof (map (lambda (x)
					     (make-step x (list expansion-line-no) justification-string))
					   lines-to-add))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  RESOLUTION
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-record-type resolution-record
  (make-resolution-record line1 line2 pivot)
  resolution-record?
  (line1 get-line-1) ;;a ref into a proof's steps
  (line2 get-line-2) ;;also a ref into a proof's steps
  (pivot get-pivot)) ;;The propositional formula about which the resolution occurred.

(define RESOLUTION-SYMBOL 'RESOLUTION)

(define get-resolutions
  (lambda (proof)
    (let ((res (assv RESOLUTION-SYMBOL (get-rule-records proof))))
      (if res (cdr res) nil))))

;;Returns a list of every X such that ~X is in lefts and X is in rights.
;;Left and right must be lists of propositional sentences.
;;Forbidden is a list of possible pivots X (not ~X) you want to skip over. (in terms of
;;          (resolution, this means pivots we already used).
(define get-resolution-pivots-unidirectional
  (lambda (lefts rights forbid)
    ;;for some reason, letrec makes this fuck up completely. I suppose because the order matters.
    (let ((leftnegs (elements-satisfying (lambda (p) (is-type? p not-t)) lefts)))
      (let ((negateds (map get-sh leftnegs)))
	(let ((searchterms  (list-difference negateds forbid)))
	  (list-intersect searchterms rights))))))

;;Returns '() or all X such that X is in A (or B) and ~X is in B (or A).
;;Forbidden is the list of propositional formulas X cannot be.
(define get-resolution-pivots
  (lambda (listA listB forbidden)
    (set-union
     (get-resolution-pivots-unidirectional listA listB forbidden)
     (get-resolution-pivots-unidirectional listB listA forbidden))))

;;IN: a list of lists of propositional formulas (i.e., the lines, brah)
;;OUT: a list of resolution-records 
(define permute-possible-resolutions
  (lambda (lines)
    (let ((numbered-pairs (all-unique-pairs (add-counters lines))))
      (raise-list
       (filter not-null?
	       (map (lambda (pair)
		      (let ((line1    (caar pair))
			    (line1-no (cdar pair))
			    (line2    (cadr pair))
			    (line2-no (cddr pair)))
			(let ((pivots (get-resolution-pivots line1 line2 nil)))
			  (if (null? pivots)
			      '()
			      (map  (lambda (p)
				      (make-resolution-record line1-no line2-no p))
				    pivots)))))
		    numbered-pairs))))))

;;Returns a resolution-record of the next available resolution.
;;Returns '() if there is no resolution possible.
(define next-resolution
  (lambda (proof)
    ;;Find every resolution
    (let ((every-resolution (permute-possible-resolutions (map get-formulas (get-steps proof)))))
      ;;Remove the ones that have already been done
      (let ((new-resolutions (filter
			      (lambda (x)
				(not (member? x (get-resolutions proof))))
			      every-resolution)))
	;;Return the first non-null
	(first-member not-null? new-resolutions)))))

;;IN: a proof and a resolution.
;;(Modifies the proof...)
(define apply-resolution!
  (lambda (proof resolution)
    ;;First we actually need to figure out which line had the X and which line had the ~X.
    ;;But what if both have both?????????
    (let ((line1 (get-formulas (locate-proof-line proof (get-line-1 resolution))))
	  (line2 (get-formulas (locate-proof-line proof (get-line-2 resolution))))
	  (pivot (get-pivot resolution))
	  (~pivot (neg (get-pivot resolution))))
      (let
	  ((lineP-ref (if (member? pivot line1) (get-line-1 resolution) (get-line-2 resolution)))
	   (line~P-ref (if (member? pivot line1) (get-line-2 resolution) (get-line-1 resolution))))
	(let ((new-line (remove-if
			 (lambda (m) (or (equal? m pivot) (equal? m ~pivot)))
			 (remove-duplicates
			  (append
			   (get-formulas (locate-proof-line proof lineP-ref))
			   (get-formulas (locate-proof-line proof line~P-ref)))))))
	  (begin
	    (add-to-rule-record proof RESOLUTION-SYMBOL (list resolution))
	    (add-to-proof-steps (list (make-step new-line (list lineP-ref line~P-ref) "Resolution")))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  UNIMPORTANT PRINTING BULLSHIT
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-all-justification-lines
  (lambda (step proof)
    (let ((lines (get-justification-lines step)))
      (if (null? lines)
	  '()
	  (append lines
		  (raise-list
		   (map (lambda (s) (get-all-justification-lines s proof))
			(map (lambda (sn) (locate-proof-line proof sn)) lines ))))))))

(define get-wasted-lines
  (lambda (proof)
    (list-difference (range-exclusive (proof-num-lines proof))
		     (get-all-justification-lines (car (reverse (get-steps proof))) proof) )))

(define print-wasted-lines
  (lambda (proof)
    (print "Wasted lines:")
    (recurse-string number->string (cdr (get-wasted-lines proof)) ",")))

(define print-step
  (lambda (step number)
    (printf "~S. [~S] ::: ~S on ~S\n"
	    number
	    (recurse-string print-pf (get-formulas step) " | ")
	    (get-justification-string step)
	    (recurse-string number->string (get-justification-lines step) ","))))

(define print-resolution-proof
  (lambda (proof)
    (begin
      (map (lambda (x y) (print-step x y))
	   (get-steps proof)
	   (reverse (range-exclusive (proof-num-lines proof))))
      (print-wasted-lines proof))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  GENERAL LITERAL RESOLUTION RULE
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define GLR-SYMBOL 'GENERAL-LITERAL-RESOLUTION)

;;grab a list of all the GLR records so far...... nil if none.
(define get-GLRs
  (lambda (proof)
    (let ((res (assv GLR-SYMBOL (get-rule-records proof))))
      (if res (cdr res) nil))))

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

(define line-refs-used-by-GLRs
  (lambda (GLRs)
    (if (null? GLRs)
	'()
	(cons
	 (get-true-parent-line (car GLRs))
	 (cons
	  (get-neg-parent-line (car GLRs))
	  (line-refs-used-by-GLRs (cdr GLRs)))))))

;;Finds the first valid GLR record given a proof and a list of lineref pairs (strictly, car is true line, cdr is neg line).
;;#f for failure.
(define find-first-GLR
  (lambda (proof lineref-pairs)
    (if (null? lineref-pairs)
	#f
	(let* ((trueline  (get-formulas (locate-proof-line proof (caar lineref-pairs))))
	       (negline   (get-formulas (locate-proof-line proof (cdar lineref-pairs))))
	       (GLR (find-general-literal-resolution trueline negline)))
	  (if GLR
	      (begin
		(set-true-parent-line GLR (caar lineref-pairs))
		(set-neg-parent-line  GLR (cdar lineref-pairs))
		GLR)
	      (find-first-GLR proof (cdr lineref-pairs)))))))

;;NEXT GLR
;;Sort of difficult...
;;1. List every line of the proof (just references).
;;2. Remove references that have already been GLR'd (determine by iterating through the GLR records.
;;3. Construct a list of every possible ordered pair of line references, prioritizing pairs of lines towards the end of the proof.
;;   ->note: due to the way all-ordered-pairs works, you can't do this lol. But it might help to try to have the last line refs at the car.
;;4. With find-general-literal-resolution, keep trying to find a pair that has a GLR unification. It will return a #<GLR-record>.
;;   Stop at the first pair to have a GLR.
;;5. If one was found, this is the next GLR.
;;6. If one was not found, #f for failure... Oh, shit, actually for "legacy reasons" we have to return nil.
(define next-GLR
  (lambda (proof)
    (let* ((all-line-refs (range-exclusive (length (get-steps proof))))
	   (forbidden-line-refs (line-refs-used-by-GLRs (get-GLRs proof)))
	   (usable-line-refs (list-difference all-line-refs forbidden-line-refs))
	   (possible-GLR-pairs (all-ordered-pairs usable-line-refs))
	   (first-GLR (find-first-GLR proof possible-GLR-pairs)))
      (if first-GLR first-GLR nil))))

;;APPLY GLR:
;;not difficult. GLR records come with the result line, so simply add the result line to the proof.
;; .... the annoying bit is printing them. Do I supply a textual representation of the whole substitution?
;; Well, why don't we start with that... :P
;; Don't forget to also add the GLR ot the GLR records.
;; Takes a GLR record, of course.
(define apply-GLR!
  (lambda (proof GLR)
    (let ((justification-string  (string-append "General Literal Resolution with "
						"T: " (number->string (get-true-parent-line GLR)) " "
						"N: " (number->string (get-neg-parent-line GLR)) " "
						"with substitution: " (substitution->string (get-unifier GLR)))))
      (begin
	(add-to-proof-steps proof
			    (list (make-step
				   (get-result-line GLR)
				   (list (get-true-parent-line GLR) (get-neg-parent-line GLR) )
				   justification-string)))
	(add-to-rule-record proof GLR-SYMBOL (list GLR))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  PROOFING BY RULESET.
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;The rules.
(define resolution-rule                  (cons next-resolution apply-resolution!))
(define expansion-rule                   (cons next-expansion apply-expansion!))
(define general-literal-resolution-rule  (cons next-GLR apply-GLR!) )
(define FOL-resolution-rules
  (list expansion-rule resolution-rule general-literal-resolution-rule))

;;Returns #f if no rule applied,
;; or (apply-func . apply-func-input) of the applied rule.
(define next-step-by-ruleset
  (lambda (proof rules)
    (if (null? rules)
	#f
	(let* ((next-rule   (car rules))
	       (rule-result ((car next-rule) proof)))
	  (if (not (null? rule-result)) 
	      (cons (cdr next-rule) rule-result)
	      (next-step-by-ruleset proof (cdr rules)))))))

;;Earlier (closer to car) members of ruleset are applied until failure before later ones.
(define proof-ruleset-resolve
  (lambda (proof rules)
    (let* ((next-step  (next-step-by-ruleset proof rules))
	   (next-func  (if next-step (car next-step) #f))
	   (next-input (if next-step (cdr next-step) #f)))
      (cond
       ((proof-closed? proof)    (begin (print "Proof closed!") proof))
       (next-step                (begin (next-func proof next-input) (proof-ruleset-resolve proof rules)))
       (else                    (begin (print "Exhausted all options. Proof failure :(") proof))))))

(define ruleset-resolve
  (lambda (step1)
    (let ((proof (init-resolution-proof step1)))
      (begin
	(proof-ruleset-resolve proof FOL-resolution-rules)
	(print-resolution-proof proof)))))

;;Ensure only that each individual sentence is named apart.
;;We will take care of the rest.
(define create-resolution-premise
  (lambda (conclusion . premises)
    (strip-quantifiers
     (skolemize
      (prenex
       (reduce-connectives
	(string-proposition-list
	 'AND
	 (uniquify-variables-in-expr-list (cons (neg conclusion) premises)))))))))
