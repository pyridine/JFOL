;; Preliminary stuff and list utilities I need.
(define nil '())

(define not-null?
  (lambda (a)
    (not (null? a))))

;;Whether item is equal to any surface member of list.
(define member?
  (lambda (item list)
    (if (null? list)
        #f
        (if (equal? item (car list))
            #t
            (member? item (cdr list))))))
 
;;Removes all occurence of item from the surface of the list.
(define remove-all
  (lambda (item list)
    (if (null? list)
        list
        (if (equal? item (car list))
            (remove-all item (cdr list))
            (cons (car list) (remove-all item (cdr list)))))))

;;Returns a list of elements from the list in that satisfy pred.
(define elements-satisfying
	(lambda (pred? in)
		(if (null? in)
			'()
			(if (pred? (car in))
				(cons (car in) (elements-satisfying pred? (cdr in)))
				(elements-satisfying pred? (cdr in))))))

;;Returns the first member of list satisfying pred, or '() if none found.
(define first-member
  (lambda (pred list)
    (if (null? list)
	'()
	(if (pred (car list))
	    (car list)
	    (first-member pred (cdr list))))))

;;Returns a func of a list. #t if the list contains any member satisfying pred.
(define a-member-is
  (lambda (predicate)
    (lambda (list)
      (if (null? list)
	  #f
	  (if (predicate (car list))
	      #t
	      ((a-member-is predicate) (cdr list)))))))
		  		  
;;Returns a range from 0 to n-1.
(define range-exclusive
  (lambda (n)
    (if (= n 0)
	'()
	(append (list (- n 1)) (range-exclusive (- n 1))))))

;;#t if the list contains a member satisfying pred
(define pred-member?
  (lambda (pred list)
    (if (null? list)
	#f
	(if (pred (car list))
	    #t
	    (pred-member? pred (cdr list))))))
		
;;Removes from A all elements also in B.	
;;uses equal? to test comparison.
(define list-difference 
  (lambda (A B)
    (filter 
     (lambda (A-MEMBER)
       (not (member? A-MEMBER B ))) A)))

;;Produces a list of only elements occuring in both A and B.
(define list-intersect
  (lambda (A B)
    (if (null? A)
	'()
	(if (member? (car A) B)
	    (cons (car A) (list-intersect (cdr A) B))
	    (list-intersect (cdr A) B)
	    ))))

(define remove-duplicates
  (lambda (A)
    (if (null? A)
	'()
	(if (member? (car A) (cdr A))
	    (remove-duplicates (cdr A))
	    (cons (car A) (remove-duplicates (cdr A)))))))

;Combines A and B and removes duplicates.
(define set-union
  (lambda (A B)
  (remove-duplicates (append A B))))

;;returns the index of member in li, or -1
(define member-ref
  (lambda (m l)
  (letrec ((memberrefaux
	    (lambda (mem li in)
	      (if (null? li)
		  -1
		  (if (equal? mem (car li))
		      in
		      (memberrefaux mem (cdr li) (+ 1 in)))))))
    (memberrefaux m l 0))))

(define list-remove-ref
  (lambda (list ref)
    (if (null? list)
	'()
	(if (= 0 ref)
	    (cdr list)
	    (cons (car list) (list-remove-ref (cdr list) (- ref 1)))))))

;;Inserts insert into list at position ref.
;;i.e., returned-list[ref] == insert.
(define list-insert-ref
  (lambda (list insert ref)
    (if (= 0 ref)
	(cons insert list)
	(cons (car list) (list-insert-ref (cdr list) insert (- ref 1))))))

;;Input: list1, a reference number "r" into list1, and list2 of size n.
;;Output: A list of n lists such that each list i is like list1, but with list1[r] removed and list2[i] added.
;;I add it in the rth position even though that's unnecessary.
(define list-ref-replacements
  (lambda (list1 r list2)
    (if (null? list2)
	'()
	(cons
	 (list-insert-ref (list-remove-ref list1 r) (car list2) r)
	 (list-ref-replacements list1 r (cdr list2))))))

;;Converts a bunch of Xs to strings and uses a separator.
;;You get f(x1) sep f(x2) sep ... sep f(xn)
(define recurse-string
  (lambda (stringfunc tostringlist separator)
    (if (null? tostringlist)
	""
	(let ((next-token (stringfunc (car tostringlist))))
	  (if (null? (cdr tostringlist))
	      next-token
	      (string-append
	       next-token
	       separator
	       (recurse-string stringfunc (cdr tostringlist) separator)))))))

;;Returns a list of all possible pairs of the elements of list.
;;Literally returns a list of pairs (x . y), not a list of lists!!
(define all-unique-pairs
  (lambda (list)
    (if (null? list)
	'()
	(append
	 (map (lambda (x) (cons (car list) x)) (cdr list))
	 (all-unique-pairs (cdr list))))))

;;Pairs up each element of each list with its reference in that list.
;;e.g. '(a b c) -> '((a . 0) (b . 1) (c . 2))
(define add-counters
  (lambda (list)
    (map
     (let ((n -1))
       (lambda (x)
	 (begin
	   (set! n (+ n 1))
	   (cons x n))))
     list)))

;;IN: a list of lists
;;OUT: The contents of each sublist have been raised to the surface
(define raise-list
  (lambda (llist)
    (if (null? llist)
	'()
	(append (car llist) (raise-list (cdr llist))))))

(define remove-if
  (lambda (pred list)
    (filter (lambda (m) (not (pred m))) list)))

;;Doesn't fuck with parens. Allows strings to be evaled.
(define string->true-symbol
 (lambda (str)
   (read (open-input-string str))))

;;Evals a string instead of a symbol.
;;Use with print-expression-evaluable.
(define eval-string
  (lambda (str)
    (eval (string->true-symbol str))))

;;Given a list of forbidden symbols, returns a symbol that is different from each of them.
;;The base-symbol will be appended with a number.
(define unique-symbol
  (lambda (base-symbol forbidden)
    (letrec ((sym-iterator
	      (lambda (symbol count)
		(letrec ((new-sym (string->symbol
				   (string-append
				    (symbol->string symbol)
				    (number->string count)))))
		  (if (member? new-sym forbidden)
			     (sym-iterator symbol (+ count 1))
			     new-sym)))))
      (sym-iterator base-symbol 1))))


;;Applies the given function onto the argument until the argument no longer changes.
;;If the function returns #f, this is taken to mean that the function failed to apply.
(define apply-until-stasis
  (lambda (function argument)
    (let ((previous argument)
	  (next argument))
      (letrec ((recurse (lambda ()
			  (begin
			    (set! previous next)
			    (set! next (let ((res (function previous))) (if res res previous)))
			    (if (equal? next previous)
				next
				(recurse))))))
	(recurse)))))
