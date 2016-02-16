;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   VariableSubstitution.scm
;;;;
;;;; Defines variable substitutions for FOL expresions,
;;;; as well as functions to use them and combine them.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "ExprUtil.scm")

(define substitution?
  (lambda (s)
    (and
     (list? s)
     (eval (cons 'and
		 (map (lambda (x)
			(and (pair? x) (symbol? (car x)) (expression? (cdr x))))
		      s))))))

;;Finds the replacement for a single variable expression.
(define substitute-variable
  (lambda (variable substitution)
    (let ((rep (assv (get-variable variable) substitution)))
      (if rep (cdr rep) variable))))

;;Removes a variable from a substitutions's support.
(define substitution-unsupport
  (lambda (sub var)
    (remove-if (lambda (x) (equal? (car x) var)) sub)))

;;Adds a variable-expression pair to a substitution.
(define substitution-support
  (lambda (var exp sub)
    (let ((sym (if (symbol? var) var (get-variable var)))) ;;Doesn't matter if you pass a symbol or a variable.
      (cons (cons sym exp) sub))))

;;Applies a substitution to an expression.
(define apply-substitution
  (lambda (s sub)
    (cond
     ((or
       (true? s)
       (false? s)
       (constant? s)) s)
     ((variable? s) (substitute-variable s sub)) ;;The important Line
     ((negation? s)
      (negation (apply-substitution (get-sh s) sub)))
     ((universal? s)
      (universal (get-variable s)
		 (apply-substitution (get-sh s)
				     (substitution-unsupport sub (get-variable s)))))
     ((existential? s)
      (existential (get-variable s)
		   (apply-substitution (get-sh s)
				       (substitution-unsupport sub (get-variable s)))))
     ((binary? s)
      (binary (get-type s)
	      (apply-substitution (get-lh s) sub)
	      (apply-substitution (get-rh s) sub)))
    ((relation? s)
      (apply relation
	     (cons (get-name s)
		   (map
		    (lambda (s) (apply-substitution s sub))
		    (get-args s)))))
     ((function? s)
      (apply function
	     (cons (get-name s)
		   (map
		    (lambda (s) (apply-substitution s sub))
		    (get-args s))))))))

;;For easily mapping a substitution over terms.
(define substitution-applier
  (lambda (sub . exprs)
    (map (lambda (x) (apply-substitution x sub)) exprs)))

;;Returns a function that substitutes one expression.
(define substitutor
  (lambda (substitution)
    (lambda (expression) (apply-substitution expression substitution))))

(define list-substitution-support
  (lambda (sub)
    (map (lambda (x) (car x)) sub)))

;;Combines substitutions:
;;Specifically, d1d2 is:
;;   { x1/(t1d2) x2/(t2d2) ... xn/(tnd2), z1/(z1d2) .... zn/(znd2) }, where z are variables suporrted by d2 and not d1.
(define compose-substitutions
  (lambda (d1 d2) 
    (let  ((d1-support (list-substitution-support d1))) 
      ;;3. Add those substitutions of d2 whose variables are not in the support of d1
      (append
       (remove-if (lambda (x) (member? (car x) d1-support)) d2)
       ;;2. Remove any substitution that has degenerated into x/x
       (remove-if
	(lambda (single-sub)
	  (equal? (variable (car single-sub)) (cdr single-sub))) ;;(car is always a variable symbol, cdr is always an expression)
	;;1. Apply d2 to all of d1's replacement terms
	(map (lambda (single-sub)
	       (cons
		(car single-sub)
		(apply-substitution (cdr single-sub) d2)))
	     d1))))))
