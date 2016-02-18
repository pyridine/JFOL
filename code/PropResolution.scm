;;Load Propositional Formula stuff
(load "ExprUtil.scm")

;;Alpha formula components.
(define conjunctive-components
  (lambda (formula)
    (let ((a (alpha-components formula)))
      (if a a nil))))

;;Beta formula components.
(define disjunctive-components
  (lambda (formula)
    (let ((b (beta-components formula)))
      (if b b nil))))
;;The code that was already here depends in a very strange way on these returning nil, not #f, if failure.
;;I haven't yet worked on this file enough to remove this dependency.
;;I should be using #f throughout to indicate failure. It makes things easier.

(define-record-type proof-location
  (make-proof-location line-no disjunct-no)
  proof-location?
  (line-no get-line-no)             ;;Line number of proof
  (disjunct-no get-disjunct-no))    ;;Which disjunct of that line

(define-record-type expansion-record
  (make-expansion-record my-proof-location expansion-type)
  expansion-record?
  (my-proof-location get-expansion-location) ;;a 'proof-location' record. The line this expansion is due to.
  (expansion-type get-expansion-type)) ;;see the list of expansion tpye definitions

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
  
(define-record-type resolution-record
  (make-resolution-record line1 line2 pivot)
  resolution-record?
  (line1 get-line-1) ;;a ref into a proof's steps
  (line2 get-line-2) ;;also a ref into a proof's steps
  (pivot get-pivot)) ;;The propositional formula about which the resolution occurred.

(define-record-type resolution-proof
  (make-resolution-proof steps expansions resolutions)
  resolution-proof?
  (steps get-steps set-steps)                ;;A list of resolution-steps
  (expansions get-expansions set-expansions)      ;;A list of expansion-records. (Although the full location is specified, expanding any part of a line removes that whole line from expandable lines.
  (resolutions get-resolutions set-resolutions))   ;;A list of resolution-records

(define init-resolution-proof
  (lambda (step1)
    (make-resolution-proof
     (list (make-step (list step1) '() "Premise"))
     '() ;;We start having made no expansions. Thus, no records.
     '() ;;We start having made no resolutions. Thus, no resolutions
     )))

(define locate-proof-line
  (lambda (proof line-no)
    (list-ref (get-steps proof) line-no)))

(define locate-proof-formula
  (lambda (proof location)
    (list-ref (locate-proof-line proof (get-line-no location)) (get-disjunct-no location))))

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

;;The number of lines (steps) in the proof.
;;Silly. But who cares.
(define proof-num-lines
  (lambda (proof)
    (apply + (map (lambda (x) 1 ) (get-steps proof)))))

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

;;INPUT
;;A list of expansion-records to add
;;A list of resolution-records to add
;;A list of resolution-steps to add
;;OUTPUT
;;(This method changes the input proof itself.)
(define proof-add-steps!
  (lambda (proof expan-records resolv-records steps)
    (begin      
      ;;Add the expansion records
      (set-expansions proof (append expan-records (get-expansions proof)))
      ;;Add  the resolution records
      (set-resolutions proof (append resolv-records (get-resolutions proof)))
       ;;Add the steps (NOTE THE ORDER!!!!! Steps are added to the end. Otherwise, the
       ;;line references in expansions and resolutions are totally wrong!)
       (set-steps proof (append (get-steps proof) steps)))))

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

(define expansion-type-to-string
  (lambda (expansion-type)
    (cond
     ((equal? expansion-type expansion-type-nn) "~~A => A")
     ((equal? expansion-type expansion-type-nttf) "~T => F")
     ((equal? expansion-type expansion-type-nftt) "~F => T")
     ((equal? expansion-type expansion-type-a) "Alpha Expansion")
     ((equal? expansion-type expansion-type-b) "Beta Expansion")
     (else "Unknown Expansion Type Error"))))

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
	  (proof-add-steps!
	   proof
	   (list expansion)
	   '()
	   (map (lambda (x)
		  (make-step x (list expansion-line-no) justification-string))
		lines-to-add)))))))


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
	  (proof-add-steps!
	   proof
	   '()
	   (list resolution)
	   (list (make-step new-line (list lineP-ref line~P-ref) "Resolution"))))))))


(define get-all-justification-lines
  (lambda (step proof)
    (let ((lines (get-justification-lines step)))
      (if (null? lines)
	  '()
	  (append lines
		  (raise-list
		   (map (lambda (s) (get-all-justification-lines s proof))
			(map (lambda (sn) (locate-proof-line proof sn)) lines )
			)))))))


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
	    (recurse-string print-pf (get-formulas step) ", ")
	    (get-justification-string step)
	    (recurse-string number->string (get-justification-lines step) ","))))

(define print-resolution-proof
  (lambda (proof)
    (begin
      (map (lambda (x y) (print-step x y))
	   (get-steps proof)
	   (reverse (range-exclusive (proof-num-lines proof))))
      (print-wasted-lines proof))))

(define proof-resolve
  (lambda (proof)
    (let ((resolution (next-resolution proof))
	  (expansion (next-expansion proof))
	  (proof-complete #f))
      (if (proof-closed? proof)
	  (begin
	    (print "Proof closed!")
	    proof)
	  (if (not-null? resolution)
	      (begin
		(apply-resolution! proof resolution)
		(proof-resolve proof))
	      (if (not-null? expansion)
		  (begin
		    (apply-expansion! proof expansion)
		    (proof-resolve proof))
		  (begin
		    (print "Exhausted all expansions/resolutions. Proof failed. :(")
		    proof)))))))


;;resolves a single sentence......
(define resolve
  (lambda (step1)
    (let ((proof (init-resolution-proof step1)))
      (begin
	(proof-resolve proof)
	(print-resolution-proof proof)))))

;;Prove that a sentence is true
(define prove
 (lambda (step1)
   (resolve (neg step1))))
