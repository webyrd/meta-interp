(load "mk.scm")
(load "meta.scm")
(load "testcheck.scm")

;;; Standard miniKanren relations for an evaluator of boolean
;;; expressions, based on fig 3-1 on p. 34 of Pierce's Types in
;;; Programming Languages (TAPL) (except I made the evaluator big-step
;;; instead of small-step).

(define termo
  (lambda (t)
    (conde
      [(== 'true t)]
      [(== 'false t)]
      [(fresh (t1 t2 t3)
         (== `(if ,t1 ,t2 ,t3) t))])))

(define valo
  (lambda (v)
    (conde
      [(== 'true v)]
      [(== 'false v)])))

(define not-valo
  (lambda (t)
    (fresh (t1 t2 t3)
      (== `(if ,t1 ,t2 ,t3) t))))

(define evalo
  (lambda (t v)
    (conde
      [(valo t) (== t v)]
      [(fresh (t2 t3)
         (== `(if true ,t2 ,t3) t)
         (evalo t2 v))]
      [(fresh (t2 t3)
         (== `(if false ,t2 ,t3) t)
         (evalo t3 v))]
      [(fresh (t1 t2 t3 t1^)
         (== `(if ,t1 ,t2 ,t3) t)
         (not-valo t1)
         (evalo t1 t1^)
         (evalo `(if ,t1^ ,t2 ,t3) v))])))

(test "evalo-1"
  (run* (q)
    (evalo '(if (if false true false) false true) q))
  '(true))

(test "evalo-2"
  (run 10 (q)
    (evalo q 'true))
  '(true
    (if true true _.0)
    (if false _.0 true)
    (if true (if true true _.0) _.1)
    (if true (if false _.0 true) _.1)
    (if false _.0 (if true true _.1))
    (if true (if true (if true true _.0) _.1) _.2)
    (if false _.0 (if false _.1 true))
    (if true (if true (if false _.0 true) _.1) _.2)
    (if true (if false _.0 (if true true _.1)) _.2)))


;;; meta-interpreter version of the evaluator

(define evalo-clause
  (lambda (c a b)
    (fresh (t v)
      (== `(evalo ,t ,v) a)
      (conde
        [(== 'Val c)
         (valo t)
         (== t v)
         (== '() b)]
        [(== 'If-True c)
         (fresh (t2 t3)
           (== `(if true ,t2 ,t3) t)
           (== `((evalo ,t2 ,v)) b))]
        [(== 'If-False c)
         (fresh (t2 t3)
           (== `(if false ,t2 ,t3) t)
           (== `((evalo ,t3 ,v)) b))]
        [(== 'If-Unknown c)
         (fresh (t1 t2 t3 t1^)
           (== `(if ,t1 ,t2 ,t3) t)
           (not-valo t1)
           (== b `((evalo ,t1 ,t1^)
                   (evalo (if ,t1^ ,t2 ,t3) ,v))))]))))

; run as normal
(define evalo-solve (solve-for evalo-clause))

; generate a derivation tree/proof true for the result
(define evalo-deriv (solve-proof-for evalo-clause))

; debugging variant
(define evalo-debug (debug-proof-for evalo-clause))



(test "evalo-solve-1"
  (run* (q)
    (evalo-solve `(evalo (if (if false true false) false true) ,q)))
  '(true))



(test "evalo-deriv-1"
  (run* (q)
    (fresh (v tree)
      (evalo-deriv `(evalo (if true false true) ,v) tree)
      (== `(,v ,tree) q)))
  '((false
     (((evalo (if true false true) false)
       <--
       If-True
       (((evalo false false) <-- Val ())))))))


(test "evalo-deriv-2"
  (run* (q)
    (fresh (v tree)
      (evalo-deriv `(evalo (if (if false true false) false true) ,v) tree)
      (== `(,v ,tree) q)))
  '((true
     (((evalo (if (if false true false) false true) true)
       <--
       If-Unknown
       (((evalo (if false true false) false)
         <--
         If-False
         (((evalo false false) <-- Val ())))
        ((evalo (if false false true) true)
         <--
         If-False
         (((evalo true true) <-- Val ())))))))))

(test "evalo-debug-1"
  (run* (q)
    (fresh (v tree ok)
      (evalo-debug `(evalo (if (if false true false) false true) ,v) tree ok)
      (== `(,v ,tree ,ok) q)))
  '((true
     (((evalo (if (if false true false) false true) true)
       <--
       If-Unknown
       (((evalo (if false true false) false)
         <--
         If-False
         (((evalo false false) <-- Val ())))
        ((evalo (if false false true) true)
         <--
         If-False
         (((evalo true true) <-- Val ()))))))
     #t)))

(test "evalo-debug-2"
  (run 3 (q)
    (fresh (v tree ok)
      (evalo-debug `(evalo (if (if bogus true false) false true) ,v) tree ok)
      (== `(,v ,tree ,ok) q)))
  '((false
     (((evalo (if (if bogus true false) false true) false)
       <--
       If-Unknown
       (((evalo (if bogus true false) true) error)
        ((evalo (if true false true) false)
         <--
         If-True
         (((evalo false false) <-- Val ()))))))
     #f)
    (true
     (((evalo (if (if bogus true false) false true) true)
       <--
       If-Unknown
       (((evalo (if bogus true false) false) error)
        ((evalo (if false false true) true)
         <--
         If-False
         (((evalo true true) <-- Val ()))))))
     #f)
    (false
     (((evalo (if (if bogus true false) false true) false)
       <--
       If-Unknown
       (((evalo (if bogus true false) (if true true _.0)) error)
        ((evalo (if (if true true _.0) false true) false)
         <--
         If-Unknown
         (((evalo (if true true _.0) true)
           <--
           If-True
           (((evalo true true) <-- Val ())))
          ((evalo (if true false true) false)
           <--
           If-True
           (((evalo false false) <-- Val ()))))))))
     #f)))
