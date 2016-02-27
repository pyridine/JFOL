(load "Resolution-Base.scm")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    (get-rule-record-assv proof EXPANSION-SYMBOL)))

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
     ((equal? expansion-type expansion-type-nn) "~~A -> A")
     ((equal? expansion-type expansion-type-nttf) "~T -> F")
     ((equal? expansion-type expansion-type-nftt) "~F -> T")
     ((equal? expansion-type expansion-type-a) "Conjunctive Expansion")
     ((equal? expansion-type expansion-type-b) "Disjunctive Expansion")
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

