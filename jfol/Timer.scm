;;A little timer utility for measuring lengths of time.
;;
;;start-timer records the start time for a unique symbol you supply.
;;display-timer takes that same symbol and `display`s the time difference from the start, converted to seconds.

(define __time__list__ (list))

(define start-timer
  (lambda (symbol)
    (set!
	__time__list__ (cons  (cons symbol (current-milliseconds))
			      (filter (lambda (x) (not (equal? (car x) symbol))) __time__list__)))))

(define display-timer
  (lambda (symbol display-string)
    (display display-string)
    (display
     (* .001
	(- (current-milliseconds) (cdr (assv symbol __time__list__)))))
    (display "\n")))



