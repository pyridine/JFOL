(declare (unit resolution))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;
;;;;;  THE FINAL MODULE.
;;;;;  PROVING BY RULESET!
;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module resolution *
  (import chicken scheme timer)
  (reexport resolution-base)
  (import simplification)
  (import rule-resolution rule-glr rule-expansion)

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
      (begin
	(if (proof-closed? proof)   ;;Check proof closed before trying to apply a rule! Saves a LOT of time!
	    proof
	    (let* ((next-step  (next-step-by-ruleset proof rules))
		   (next-func  (if next-step (car next-step) #f))
		   (next-input (if next-step (cdr next-step) #f)))
	      (cond
	       (next-step                (begin (next-func proof next-input) (proof-ruleset-resolve proof rules)))
	       (else                     proof)))))))

  ;;Puts all premises as separate lines. Conclusion must still appear first.
  (define separate-premises-ruleset-resolve
    (lambda (first-steps)
      (let* ((conc  (neg (car first-steps)))
	     (proof (separate-premises-init-resolution-proof (completely-rename-variables-in-list (cons conc (cdr first-steps)) '()))))
	(begin
	  (proof-ruleset-resolve proof FOL-resolution-rules)
	  proof))))

  (define resolution-form
    (lambda (expression)
      (strip-quantifiers (skolemize (prenex (reduce-connectives expression))))))

  (define prove-argument
    (lambda (explist)
      (let ((time1 0.0) (time2 0.0) (proof #f))
	(begin
	  (start-timer 'Poof)
	  (set! proof (separate-premises-ruleset-resolve (map resolution-form explist)))
	  (let ((format (proof-to-format-list proof)))
	    (map
	     (lambda (f)
	       (begin
		 (display (car f))
		 (display (cadr f))
		 (display (caddr f))))
	     format))
	  (print-proof-epilogue proof)
	  (display-timer 'Poof "Proof time (seconds): ")))))
  )
