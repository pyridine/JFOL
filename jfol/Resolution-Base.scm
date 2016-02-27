(load "ExprUtil.scm")
(load "Simplification.scm")
(load "Unification.scm")
(load "TestExpressions.scm")

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
  (justification-string get-justification-string set-justification-string))  ;;The type of justification... Make it a string.

(define-record-type resolution-proof
  (make-resolution-proof steps rule-application-records)
  resolution-proof?
  (steps get-steps set-steps)                ;;A list of resolution-steps
  ;;Rules record their appplication records here. Each rule shall have its own record list here,
  ;;                                              stored under a unique symbol with the almighty 'assv'.
  (rule-application-records get-rule-records set-rule-records) 
  ;;We store the index of the last premise for ease of use
  (last-premise-ref get-last-premise-ref set-last-premise-ref)
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

  ;;Whether the resolution proof is closed. If one of its steps is empty.
  (define proof-closed?
    (lambda (proof)
      ((a-member-is
	(lambda (step)
	  (null? (get-formulas step))))
       (get-steps proof))))

(define init-resolution-proof
  (lambda (step1)
    (let ((proof (make-resolution-proof
	    (list (make-step (list step1) '() "Premise"))
	    '() ;;We start having made no rule applications, so no records.
	    )))
      (begin
	(set-last-premise-ref proof 0)
	proof))))

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

;;Gets the rule record associated list for some symbol.
;;If nothing is there yet, returns '().
(define get-rule-record-assv 
  (lambda (proof symbol)
    (let ((res (assv symbol (get-rule-records proof))))
      (if res (cdr res) nil))))

(define separate-premises-init-resolution-proof
  (lambda (steps)
    (let* ((proof (make-resolution-proof '() '()))
       	   (premises (reverse (map (lambda (x) (make-step (list x) '()  "Simplified Premise" )) steps)))
 	   (conclusion (car (reverse premises))))
      (begin
	(set-justification-string conclusion "Simplified Negated Conclusion")
	(set! premises (reverse (cons conclusion (cdr (reverse premises)))))
	(add-to-proof-steps proof premises)
	(set-last-premise-ref proof (- (length steps) 1))
	proof))))


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
    (let ((waste (get-wasted-lines proof)))
      (if (not-null? (cdr waste))
	  (begin  
	    (display "Wasted lines:\n")
	    (display (recurse-string number->string (map (lambda (x) (+ x 1)) (cdr waste)) ","))
	    (display "\n")
	    #t)
	  #f))))

(define print-step
  (lambda (step number)
    (printf "~S. [~S] ::: ~S on ~S\n"
	    number
	    (recurse-string print-pf (get-formulas step) " | ")
	    (get-justification-string step)
	    (recurse-string number->string (get-justification-lines step) ","))))

(define print-latest-step
  (lambda (proooooooooooooooof)
    (print-step  (car (reverse (get-steps proooooooooooooooof))) (- (length (get-steps proooooooooooooooof)) 1))))

(define print-proof-epilogue
  (lambda (proof)
    (if (proof-closed? proof)
	(display "Proof closed!\n")
	(display "Proof failed... :(\n")
	)
    (print-wasted-lines proof)))

(define success-emoticons
  (list "-><-")
  ;;(list ":D" ":3" "^_^" "8^y" "TvT" "^w^" "^3^" "=]" "B^D" "8D" "=D" "=-3" ":-)" "<3")
  )

(define step-to-formula-string
  (lambda (step-rec)
    (if (null? (get-formulas step-rec))
	(list-ref success-emoticons (random (length success-emoticons)))
	(recurse-string print-pf (get-formulas step-rec) " | "))))

(define step-to-justification-string
  (lambda (step-rec)
    (get-justification-string step-rec)))

(define step-to-justification-line-list
  (lambda (step-rec)
    (recurse-string number->string (map (lambda (x) (+ x 1)) (get-justification-lines step-rec)) ",")))

(define _ayyy-lmao_ 0)
(define reset-counter
  (lambda ()
    (set! _ayyy-lmao_ 0)))
(define next-counter-str
  (lambda ()
    (set! _ayyy-lmao_ (+ 1 _ayyy-lmao_))
    (string-append
     (number->string _ayyy-lmao_)
     ". ")))

;;Creates a set of strings for nicely formatting the proof's output.
(define proof-to-format-list
  (lambda (proof)
    (let ((steps (get-steps proof)))
      (begin
	(reset-counter)
       (map list
	    (map (lambda (x) (string-append (pad-string (next-counter-str)
							(+ 2(string-length (number->string (length (get-steps proof))  )    ))   ) x "    "))
		 (pad-string-list (map step-to-formula-string steps))) ;;1. Step
	    (map (lambda (x) (string-append x (if (equal? x "") "   " " : ")))
		 (pad-string-list (map step-to-justification-line-list steps))) ;;2. Lines due
	    (map (lambda (x) (string-append x "\n"))
		 (map step-to-justification-string steps))))))) ;;3. Justification
