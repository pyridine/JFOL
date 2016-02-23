(load "Resolution.scm")
;;This is all global and static because it's run over every time the executable is used.

;;=====================;;
;;     PARSE INPUT     ;;
;;=====================;;

;;(require-extension pyffi) ;;This is done by the compiler, but just so you remember......
;;(py-start)
;;(py-import "FOL-Parse")
;;(define input (py-eval "parse_input()")) 
;;(display input)
;;(py-stop)


(define args (command-line-arguments))

(define conclusion "ayyylmao")
(define premises '())
	
(define num-args 0)

(define parse-premises
  (lambda (list)
    (if (not-null? list)
	(set! premises (cons (eval-string (car list)) premises))
	#f)))

;;;Main...... no definition :P
(if (null? args)
    (begin
      (display "The solver requires arguments as JFOL scheme expressions.\nThe output of the parser is just the format of the arguments I need.\n")
      (exit)
      )
    (begin
      (display (length args))
      (map display  args)
      (set! conclusion (eval-string (car args)))
      (parse-premises (cdr args))
      (prove-argument (cons conclusion premises))))
