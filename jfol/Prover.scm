(load "Resolution.scm")

;;=====================;;
;;     PARSE INPUT     ;;
;;=====================;;

;;(require-extension pyffi) ;;This is done by the compiler, but just so you remember......
;;(py-start)
;;(py-import "FOL-Parse")
;;(define input (py-eval "parse_input()")) 
;;(display input)
;;(py-stop)

(define parse-premises
  (lambda (list)
    (if (not-null? list)
	(begin
	  (set! premises (cons (eval-string (car list)) premises))
	  (parse-premises (cdr list)))
	#f)))

;;;Main...... no definition :P
(if (null? (command-line-arguments))
    (begin
      (display "The solver requires arguments as JFOL scheme expressions.\nThe output of the parser is just the format of the arguments I need.\n")
      (exit))
      (prove-argument (map eval-string (command-line-arguments))))
