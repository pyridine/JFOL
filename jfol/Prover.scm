;;This won't compile in the interpreter: it's only for the compiler.
(load "Resolution.scm")

;;=====================;;
;;     PARSE INPUT     ;;
;;=====================;;

;;;Main...... no definition :P
(if (null? (command-line-arguments))
    (begin
      (display "The solver requires arguments as JFOL scheme expressions.\nThe output of the parser is just the format of the arguments I need.\n")
      (exit))
    (separate-premises-prove-argument (map eval-string (command-line-arguments))))
