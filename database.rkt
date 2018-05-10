#| Assignment 1 - Racket Query Language  


Sagar Suri
Ryan Mock
|#
#lang racket

(provide attributes
         tuples
         size
         SELECT
         FROM
         )

(define-syntax If
  (syntax-rules ()
  ((If cond conseq alter)
   (if cond
       conseq
       alter))))


(define-syntax And
  (syntax-rules ()
    ((And p q)
     (if p q #f))))

(define-syntax Or
  (syntax-rules ()
    ((Or p q)
     (if p #t q))))

(define (Inside? list item) ; Helper function to check if theres a value equal to item in the list
  (if (equal? list null)
      #f
      (if (equal? (first list) item)
          #t
          (Inside? (rest list) item))))

(define (cartesian-product lst-tables)
  (if (equal? (length lst-tables) 1)
      (first lst-tables)
      (if  (equal? (first lst-tables) null)
           '()
           (apply append (map (λ(x) (map (λ(y) (append x y)) (cartesian-product (rest lst-tables)))) (first lst-tables))))))

(define (gt-index list item)
  (if (equal? list null)
      '()
      (if (equal? (first list) item)
          0
          (let ((ind (gt-index (rest list) item)))
            (if (number? ind)
                (+ 1 ind)
                '()
                )))))
(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))
; Part 0: Semantic aliases

#|
(attributes table)
  table: a valid table (i.e., a list of lists as specified by assigment)

  Returns a list of the attributes in 'table', in the order they appear.
|#
(define (attributes table)
  (first table))

#|
(tuples table)
  table: a valid table

  Returns a list of all tuples in 'table', in the order they appear.
  Note: it is possible for 'table' to contain no tuples.
|#
(define (tuples table)
  (rest table))

#|
(size table)
  table: a valid table

  Returns the number of tuples in 'table'.
|#
(define (size table)
  (length (rest table)))


; Part I "WHERE" helpers

#|
A function that takes: 
  - a list of attributes
  - a string (representing an attribute)
  - a tuple

  and returns the value of the tuple corresponding to that attribute.
|#
(define (find-attribute lst attrbute tple)
    (list-ref tple (gt-index lst attrbute)))
#|
A function that takes:
  - f: a unary function that takes a tuple and returns a boolean value
  - table: a valid table

  and returns a new table containing only the tuples in 'table'
  that satisfy 'f'.
|#

;Function that takes a list of boolean and returns the list at the position that has boolean true
(define (filt-by-functn list table)
  (if (equal? list null)
      '()
      (if (eval (first list) ns)
          (cons (first table) (filt-by-functn (rest list) (rest table)))
          (filt-by-functn (rest list) (rest table)))))
  #|
A function 'replace-attr' that takes:
  - x 
  - a list of attributes

  and returns a function 'f' which takes a tuple and does the following:
    - If 'x' is in the list of attributes, return the corrresponding value 
      in the tuple.
    - Otherwise, just ignore the tuple and return 'x'.
|#
(define (replace-attr x list)
  (λ(y) (if (Inside? list x)
      (find-attribute list x y)
      x)))

;Part 1a Basic Selection

(define (filter-tuple lst-ind tuple);returns a tuple of elements from specific indexes
  ;lst-ind: list of indexes to filter
  ;tuple: tuple to filter
  
  (map (λ(x) (if (equal? x null) '() (list-ref tuple x) )) lst-ind))

(define (bsc-selection lst table)
  ;lst: list of attributes to find
  ;table: a table of values and attributes
  
  (if (equal? table null)
      '()
      (if (list? lst)
          (cons lst (map (λ(y) (filter-tuple (map (λ(x) (gt-index (first table) x)) lst) y)) (rest table)));maps the helper function on each tuple
          table)))

;Part 1b Selection from multiple tables

(define (duplicate-finder list); returns a list of items that appears more than once
  (if (equal? list null)
      '()
      (if (Inside? (rest list) (first list))
          (cons (first list) (duplicate-finder (rest list)))
          (duplicate-finder (rest list)))))

(define (prefix-helper lst-attr lst-table prefix)
  ;lst-attr: list of common attributes with other lst
  ;lst-table: list of attributes from a table
  (if (equal? lst-table null)
      '()
      (if (Inside? lst-attr (first lst-table))
          (cons (string-append prefix "." (first lst-table)) (prefix-helper lst-attr (rest lst-table) prefix)) 
          (cons (first lst-table)(prefix-helper lst-attr (rest lst-table) prefix)))))

(define (get-lst-tables lst);get list of tables from a list of list of tables
  (if (equal? lst null)
      '()
      (cons (cdar lst) (get-lst-tables (rest lst)))))

(define (cumulative-list lst-tables);gets the attributes of all of the tables in lst-tables
  (if (equal? lst-tables null)
      '()
      (append (caar lst-tables) (cumulative-list (rest lst-tables)))))


(define (combine-tables lst-lst-tables)
  ;lst: list of attributes to find
  ;lst-lst-tables: list of multiple tables as list with their respective names
  (let* ((lst-tables (get-lst-tables lst-lst-tables))
        (common-attr (duplicate-finder (cumulative-list lst-tables)))) 
        (cons (apply append (map (λ(x) (prefix-helper common-attr (cadr x) (first x))) lst-lst-tables))
                (cartesian-product (map (λ(x) (rest x)) lst-tables)))))


;Part 1c Filtering Tuples

(define (form-predicate arg list)
  ;arg: argument to turn into a pred
  ;table: the table to filter
  (if (list? arg)
      (map (λ(x) (form-predicate x list)) arg)
      (replace-attr arg list)))

(define (form-values list-args table)
  ;list-args: list of arguments that are part of a predicate
  ;table: list of lists that contains values to replace into the arguments
  (if (equal? list-args null)
      '()
      (if (list? (first list-args))
          (cons (form-values (first list-args) table) (form-values (rest list-args) table))
          (cons (map (form-predicate (first list-args) (first table)) (rest table)) (form-values (rest list-args) table)))))

(define (sorting-lists list [indx 0])
  ;takes a list of list and takes the first of every list and make it into a list
  (if (equal? (length (first list)) indx)
      '()
      (cons (map (λ(x) (if (list? (first x))
                           (list-ref (sorting-lists x indx) 0)
                           (list-ref x indx))) list)
            (sorting-lists list (+ indx 1)))))


(define (filt-t table args);Takes in a a table and filters out the tuples that does not satisfy the arguments
  (if (list? args)
      (cons (first table) (filt-by-functn (sorting-lists (form-values args table)) (rest table))) ;makes a list of all the values and compares them with each index in the table
      (cons (first table) (filter (replace-attr args (attributes table)) (rest table)))
      ))
      

;Part 1d Ordering

(define (ordering table args);Takes in a table and orders it based on the values substituted into the arguments
  (if (list? args)
      (cons (attributes table) (sort (tuples table) > #:key (λ(x) (list-ref (map (λ(y) (eval y ns)) (sorting-lists (form-values args table))) (gt-index (rest table) x)))))
                                                                                 ;makes a list of all the values and compares them with each index in the table

      (cons (attributes table) (sort (tuples table) > #:key (replace-attr args (attributes table)))))) 


; Syntax Definitions 

(define-syntax FROM ;takes care of queries of more than one lists and combines them into a list of list
  (syntax-rules()
    [(FROM [<table1> <name1>] [<table2> <name2>])
     (list (cons <name1> <table1>) (cons <name2> <table2>))]
    [(FROM [<table1> <name1>] [<table2> <name2>]  [<table3> <name3>] ...)
     (FROM (FROM [<table1> <name1>] [<table2> <name2>]) [<table3> <name3>] ...)]
    [(FROM <list> [<table3> <name3>] ...)
     (append <list> (list (cons <name3> <table3>)) ...)]
    ))


(define-syntax SELECT
  (syntax-rules()
    ;Only Select and from
    [(SELECT <attrs> FROM <table>)
     (bsc-selection <attrs> <table>)]
    [(SELECT <attrs> FROM [<table> <name>] ...)
     (bsc-selection <attrs> (combine-tables (FROM [<table> <name>] ...)))]
    ;only when WHERE is included
    [(SELECT <attrs> FROM <table> WHERE <condition>)
     (bsc-selection <attrs> (filt-t <table> (quote <condition>)))]
    [(SELECT <attrs> FROM [<table> <name>]... WHERE <condition>)
     (bsc-selection <attrs> (filt-t (combine-tables (FROM [<table> <name>] ...)) (quote <condition>)))]
    ;only when ORDER BY is included
    [(SELECT <attrs> FROM <table> ORDER BY <order-expr>)
     (bsc-selection <attrs> (ordering <table> (quote <order-expr>)))]
    [(SELECT <attrs> FROM [<table> <name>] ... ORDER BY <order-expr>)
     (bsc-selection <attrs> (ordering (combine-tables (FROM [<table> <name>] ...)) (quote <order-expr>)))]
    ;when both WHERE and ORDER BY are included
    [(SELECT <attrs> FROM <table> WHERE <condition> ORDER BY <order-expr>)
     (bsc-selection <attrs> (ordering (filt-t <table> (quote <condition>)) (quote <order-expr>)))]    
    [(SELECT <attrs> FROM [<table> <name>] ... WHERE <condition> ORDER BY <order-expr>)
     (bsc-selection <attrs> (ordering (filt-t (combine-tables (FROM [<table> <name>] ...)) (quote <condition>)) (quote <order-expr>)))]))



; This is suppossed to turn each element in to an expression
; into a function that takes in a tuple and returns either the value if the attribute is in, or the
; attribute itself
(define-syntax replace
  (syntax-rules ()
    ; The recursive step, when given a compound expression
    [(replace (expr ...) table)
     (let ((args (list expr ...)))
     (cons (replace-attr (first args) (first table)) (replace (rest args) table)))]
    ; The base case, when given just an atom. 
    [(replace atom table)
     (replace-attr atom (first table))]))