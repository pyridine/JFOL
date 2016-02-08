;;     This file includes an abstract representation for propositional formulas,
;;     As well as basic utilities for them.
;;     For the real workhorse utilities, see ExprUtils.scm.
;;Load utilities
(load "ListStuff.scm")

;;define-record type is specified in SRFI-9, here:
;;http://srfi.schemers.org/srfi-9/srfi-9.html
(define-record-type expression
  (--expression-create type lh-expression rh-expression)
  pf-expression?
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
;;Sentential Calculus types
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
	(if (not (null? rest-types))
	    (apply is-type? (cons (get-sh expression) rest-types))
      	    #t) #f)))

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

;;Synonyms for universal
(define all universal)
(define for-all universal)

(define universal?
  (lambda (expr)
    (is-type? expr universal-t)))

(define existential
  (lambda (variable expression)
    (let ((expr  (--expression-create existential-t expression nil)))
      (begin
	(set-variable expr variable)
	expr))))

;;Synonyms for existential
(define some existential)
(define exists existential)
(define there-is existential)

(define existential?
  (lambda (expr)
    (is-type? expr existential-t)))

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

;;takes a name and a list of expressions
(define function
  (lambda (name exprs)
    (let ((expr (--expression-create function-t nil nil)))
      (begin
	(set-name expr name)
	(set-args expr exprs)
	expr))))

(define function?
  (lambda (expr)
    (is-type? expr function-t)))

(define relation
  (lambda (name exprs)
    (let ((expr (--expression-create relation-t nil nil)))
      (begin
	(set-name expr name)
	(set-args expr exprs)
	expr))))

(define relation?
  (lambda (expr)
    (is-type? expr relation-t)))

;;The arity of a function or relation is not stored separately.
;;Be cautious when you modify a function or relation's
;;expression list (expr-list).
(define get-arity
  (lambda (func-or-rel)
    (length (get-args func-or-rel))))


;;
;; Major expression queries
;;

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
    (or
     (universal? expr)
     (existential? expr)
     (negation? expr))))

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
