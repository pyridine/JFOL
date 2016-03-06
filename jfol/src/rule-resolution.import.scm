;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  RESOLUTION
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module rule-resolution (next-resolution apply-resolution!)
  (import chicken scheme)
(import srfi-1)
  (reexport resolution-base)

  (define-record-type resolution-record
    (make-resolution-record line1 line2 pivot)
    resolution-record?
    (line1 get-line-1) ;;a ref into a proof's steps
    (line2 get-line-2) ;;also a ref into a proof's steps
    (pivot get-pivot)) ;;The propositional formula about which the resolution occurred.

  (define RESOLUTION-SYMBOL 'RESOLUTION)

  (define get-resolutions
    (lambda (proof)
      (get-rule-record-assv proof RESOLUTION-SYMBOL)))

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
	;;And the ones whose resultant lines already exist in the proof.
	(let ((new-resolutions (filter
				(lambda (x)
				  (and (not (member? x (get-resolutions proof)))
				       (not (member? (resolution-result-line proof x) (map get-formulas (get-steps proof))))))
				every-resolution)))
	  ;;Return the first non-null
	  (first-member not-null? new-resolutions)))))

  (define resolution-result-line
    (lambda (proof resolution)
      (let* ((line1 (get-formulas (locate-proof-line proof (get-line-1 resolution))))
	     (line2 (get-formulas (locate-proof-line proof (get-line-2 resolution))))
	     (pivot (get-pivot resolution))
	     (~pivot (neg (get-pivot resolution)))
	     (lineP-ref (if (member? pivot line1) (get-line-1 resolution) (get-line-2 resolution)))
	     (line~P-ref (if (member? pivot line1) (get-line-2 resolution) (get-line-1 resolution)))
	     (new-line (remove-if
			(lambda (m) (or (equal? m pivot) (equal? m ~pivot)))
			(remove-duplicates
			 (append
			  (get-formulas (locate-proof-line proof lineP-ref))
			  (get-formulas (locate-proof-line proof line~P-ref)))))))
	new-line)))

  ;;IN: a proof and a resolution.
  ;;(Modifies the proof...)
  (define apply-resolution!
    (lambda (proof resolution)
      ;;First we actually need to figure out which line had the X and which line had the ~X.
      ;;But what if both have both?????????
      (begin
	(add-to-rule-record proof RESOLUTION-SYMBOL (list resolution))
	(add-to-proof-steps proof (list (make-step
					 (resolution-result-line proof resolution)
					 (list (get-line-1 resolution) (get-line-2 resolution))
					 "Resolution"))))))
  )
