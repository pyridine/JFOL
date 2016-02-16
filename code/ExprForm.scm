;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;   ExprForm.scm
;;;;
;;;; The abstract representation for propositional formulas,
;;;; as well as a few fundamental procedures and queries.
;;;;
;;;; I strongly dislike this representation and believe that
;;;; it abstracts FOL incredibly poorly. Not only that, but its
;;;; complicated nature has led to a complication of the codebase,
;;;; and in turn an increase in the number of bugs in development.
;;;;
;;;; But to change it, and to change everything that depends on
;;;; it, at this stage in the game, would be more work than it's
;;;; worth. Unfortunately.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(load "ListStuff.scm")

;;define-record type is specified in SRFI-9, here:
;;http://srfi.schemers.org/srfi-9/srfi-9.html
(define-record-type expression
  (--expression-create type lh-expression rh-expression)
  expression?
  ;;See type list, below. The type of expression.
  (type get-type)
  ;;PF features
  (lh-expression get-lh set-lh)
  (lh-expression get-sh set-sh) ;;for unary preds and quantifiers.
  (rh-expression get-rh set-rh)
  ;;FOL features
  (variable get-variable set-variable)    ;;used to track the variable of quantifiers AND plain variables. JUST A SYMBOL!!!!!
  (name get-name set-name) ;;for functions and relations and constants
  ;;for functions and relations
  (args get-args set-args)
 )

;;Every type of expression has an associated symbol.
;;These symbols are considered reserved words, but this is not enforced.
(begin
;;First Order Logic types
  (define universal-t 'ALL)
  (define existential-t 'EXISTS)
  (define relation-t 'RELATION)
  (define function-t 'FUNCTION)
  (define constant-t 'CONSTANT) ;;Substitute for Sentential "Letter"s.
  (define variable-t 'VARIABLE)
;;Sentential Calculus inherited types
  (define not-t 'NOT)
  (define and-t 'AND)
  (define or-t  'OR)
  (define imp-t 'IMP)
  (define revimp-t 'REVIMP)
  (define nand-t 'NAND)         ;;NAND IS UP-ARROW!!!
  (define nor-t 'NOR)           ;;NOR IS DOWN-ARROW!!!
  (define notimp-t 'NOTIMP)
  (define notrevimp-t 'NOTREVIMP)
  (define equiv-t 'EQUIV)
  (define inequiv-t 'INEQUIV)
  (define atomic-true-sym '-PFATOMICTRUE)
  (define atomic-false-sym '-PFATOMICFALSE))
;;(define letter-t 'LETTER) ;;This is unused in FOL.

;;Eval this to remind yourself of the major types of expressions
(define major-types '(Universal Existential Relation Function Constant Variable Negation (Binaries) True False))

;; A listing of each binary expression type.
(define binary-types
  (list and-t or-t imp-t revimp-t nand-t nor-t
	notimp-t notrevimp-t equiv-t inequiv-t))

;;A recursive type predicate.
;;Unless you are asking for a multiple-type expression or a specific
;;binary expression, it is better to use a type's type? predicate,
;;which are all defined below.
;;
;;usage:
;;        * (is-type? expr or-t)
;;             #t for `a or b`
;;
;;        * (is-type? expr not-t and-t)
;;             #t for `not (a or b)`
;;
;;Pass arguments in order of descending major connective.
;;When asked for a deeper predicate after a binary predicate, only the LH expression will be checked.
;;
(define is-type?
  (lambda (expression type . rest-types)
    (if (equal? (get-type expression) type)
	(if (null? rest-types)
      	    #t
	    (apply is-type? (cons (get-sh expression) rest-types)))
	#f
	)))

(define true
  (--expression-create atomic-true-sym nil nil))

(define true?
  (lambda (x) (equal? x true)))

(define false
   (--expression-create atomic-false-sym nil nil))

(define false?
  (lambda (x) (equal? x false)))

;; Functions for creating and querying expressions follow.
(define negation
  (lambda (pf-expression)
    (--expression-create not-t pf-expression nil)))

(define negation?
  (lambda (expr)
    (is-type? expr not-t)))

(define binary
  (lambda (connective-type lh-expression rh-expression)
    (--expression-create connective-type lh-expression rh-expression)))

(define universal
  (lambda (variable expression)
    (let ((expr  (--expression-create universal-t expression nil)))
      (begin
	(set-variable expr variable)
	expr))))

(define universal?
  (lambda (expr)
    (is-type? expr universal-t)))

(define existential
  (lambda (variable expression)
    (let ((expr  (--expression-create existential-t expression nil)))
      (begin
	(set-variable expr variable)
	expr))))

(define existential?
  (lambda (expr)
    (is-type? expr existential-t)))

(define quantifier?
  (lambda (e)
    (or (existential? e) (universal? e))))

(define variable
  (lambda (variable)
    (let ((expr (--expression-create variable-t nil nil)))
      (begin
	(set-variable expr variable)
	expr))))

(define variable?
  (lambda (expr)
    (is-type? expr variable-t)))

(define constant
  (lambda (name)
    (let ((expr  (--expression-create constant-t nil nil)))
      (begin
	(set-name expr name)
	expr))))

(define constant?
  (lambda (expr)
    (is-type? expr constant-t)))

;;Don't use this.
;;Because creating a function and a relation is essentially the same thing,
;;I provide this higher function...
(define --function-or-relation
  (lambda (type name first . rest)
    (let ((newfunc (--expression-create type nil nil)))
      (letrec ((recurse-arguments
		(lambda (first . rest)
		  ;;recursively append expressions to newfunc's arguements.
		  (begin
		    (set-args newfunc (cons first (get-args newfunc)))
		    (if (null? rest)
			newfunc
			(apply recurse-arguments rest))))))
	(begin
	  (set-name newfunc name)
	  (set-args newfunc '())
	  (apply recurse-arguments (cons first rest))
	  (set-args newfunc (reverse (get-args newfunc))) ;; :P
	  newfunc)))))

(define function
  (lambda (name first . rest)
    (apply --function-or-relation (cons function-t
					(cons name
					      (cons first rest))))))
(define relation
  (lambda (name first . rest)
    (apply --function-or-relation (cons relation-t
					(cons name
					      (cons first rest))))))
(define function?
  (lambda (expr)
    (is-type? expr function-t)))

(define relation?
  (lambda (expr)
    (is-type? expr relation-t)))

;;The arity of a function or relation is not stored separately.
;;Be cautious when you modify a function or relation's
;;expression list (expr-list).
(define get-arity
  (lambda (func-or-rel)
    (length (get-args func-or-rel))))

;;Binary expressions are those combined via some binary connective.
;;Specific functions: lh-expr, rh-expr
(define binary?
  (lambda (expr)
    ;;For some fucking reason you can't apply `or`
    (eval (cons 'or
	   (map (lambda (x) (is-type? expr x)) binary-types)))))

;;Unary expressions are those with a single expression at their core.
;;Specific functions: single-expr
(define unary?
  (lambda (expr)
    (or (universal? expr) (existential? expr) (negation? expr))))

;;Expresions with names.
;;Relations, functions, and constants have names.
;;VARIABLES DO NOT HAVE NAMES...
(define named?
  (lambda (expr)
    (or
     (relation? expr)
     (function? expr)
     (constant? expr))))

;;If the expression is a base-case for structural recursion.
;;I.e., no expression is a part of it.
(define basic?
  (lambda (e)
    (or
     (constant? e)
     (variable? e)
     (false? e)
     (true? e))))

;;Is the expression a term?
(define term?
  (lambda (e)
    (or
     (is-type? e variable-t)
     (is-type? e constant-t)
     (and (is-type? e function-t)
	  ;;Macros aren't first-order!!!! :(
	  (eval (cons 'and
		      (map (lambda (x) (term? x)) (get-args e))))))))

;;A literal is an atomic formula or its negation. (or true or false...)
(define literal?
  (lambda (p)
    (or
     (equal? p true)
     (equal? p false)
     (is-type? p not-t relation-t) ;;Assuming that the relation is well-formed.
     (is-type? p relation-t))))

(define non-literal?
  (lambda (p)
    (not (literal? p))))

;; Synonyms
(define func function)
(define rel relation)

(define const constant)

(define var variable)

(define some existential)
(define exists existential)
(define there-is existential)

(define all universal)
(define for-all universal)

(define neg negation) ;;DON'T FUCKING DEFINE "not" AS NEGATION!!!!!!! YOU OVERRIDE BUILT-IN NOT!
