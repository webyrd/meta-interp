(load "mk.scm")
(load "meta.scm")
(load "testcheck.scm")

;;; Vanilla miniKanren relational interpreter from
;;; https://github.com/webyrd/2012-scheme-workshop-quines-paper-code

(define lookupo
  (lambda (x env t)
    (fresh (y v rest)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))

(define proper-listo
  (lambda (exp env val)
    (conde
      ((== '() exp)
       (== '() val))
      ((fresh (a d v-a v-d)
         (== `(,a . ,d) exp)
         (== `(,v-a . ,v-d) val)
         (eval-expo a env v-a)
         (proper-listo d env v-d))))))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== v val)))
      ((fresh (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env val)))
      ((symbolo exp) (lookupo exp env val))
      ((fresh (rator rand x body env^ a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val))))))

;;; Our canonical quine
(define quinec 
  '((lambda (x)
      (list x (list (quote quote) x)))
    (quote
      (lambda (x)
        (list x (list (quote quote) x))))))

(test "eval-expo-1"
  (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
  '((closure x x ((quote . (closure y y ()))))))

(test "eval-expo-2"
  (run* (q) (eval-expo quinec '() q))
  '(((lambda (x) (list x (list 'quote x)))
     '(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-3"
  (run 1 (q) (eval-expo q '() quinec))
  '('((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-4"
  (run 1 (q) (eval-expo q '() q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))


;;;; Meta-interpreter version.

(define eval-expo-clause
  (lambda (c a b)
    (fresh (exp env val)
      (== `(eval-expo ,exp ,env ,val) a)
      (conde
        [(== 'Quote c)
         (fresh (v)
           (== `(quote ,v) exp)
           (not-in-envo 'quote env)
           (absento 'closure v)
           (== v val)
           (== '() b))]
        [(== 'List c)
         (fresh (a*)
           (== `(list . ,a*) exp)
           (not-in-envo 'list env)
           (absento 'closure a*)
           ;;; tricky!  Must pass in b
           (proper-listo2 a* env val b))]
        [(== 'Var c)
         (symbolo exp)
         (lookupo exp env val)
         (== '() b)]
        [(== 'App c)
         (fresh (rator rand x body env^ a)
           (== `(,rator ,rand) exp)
           (== b `((eval-expo ,rator ,env (closure ,x ,body ,env^))
                   (eval-expo ,rand ,env ,a)
                   (eval-expo ,body ((,x . ,a) . ,env^) ,val))))]
        [(== 'Abs c)
         (fresh (x body)
           (== `(lambda (,x) ,body) exp)
           (symbolo x)
           (not-in-envo 'lambda env)
           (== `(closure ,x ,body ,env) val)
           (== '() b))]))))

; proper-listo calls eval-expo, so we need to create a variant
; (proper-listo2) that accumulates the calls to eval-expo in the 'b'
; argument.
(define proper-listo2
  (lambda (exp env val b)
    (conde
      ((== '() exp)
       (== '() val)
       (== '() b))
      ((fresh (a d v-a v-d b^)
         (== `(,a . ,d) exp)
         (== `(,v-a . ,v-d) val)
         (== `((eval-expo ,a ,env ,v-a) . ,b^) b)         
         (proper-listo2 d env v-d b^))))))


; run as normal
(define eval-expo-solve (solve-for eval-expo-clause))

; generate a derivation tree/proof true for the result
(define eval-expo-deriv (solve-proof-for eval-expo-clause))

; debugging variant
(define eval-expo-debug (debug-proof-for eval-expo-clause))



(test "eval-expo-solve-1"
  (run* (q)
    (eval-expo-solve `(eval-expo (lambda (x) x) () ,q)))
  '((closure x x ())))

(test "eval-expo-solve-2"
  (run* (q)
    (eval-expo-solve `(eval-expo ((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) () ,q)))
  '((closure x x ((quote closure y y ())))))

(test "eval-expo-solve-3"
  (run 1 (q)
    (eval-expo-solve `(eval-expo ,quinec () ,q)))
  '(((lambda (x) (list x (list 'quote x)))
     '(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-solve-4"
  (run* (q)
    (eval-expo-solve `(eval-expo ,quinec () ,q)))
  '(((lambda (x) (list x (list 'quote x)))
     '(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-solve-5"
  (run 1 (q)
    (eval-expo-solve `(eval-expo ,q () ,quinec)))
  '('((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-solve-6"
  (run 2 (q)
    (eval-expo-solve `(eval-expo ,q () ,quinec)))
  '('((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))
    (list
     '(lambda (x) (list x (list 'quote x)))
     ''(lambda (x) (list x (list 'quote x))))))

(test "eval-expo-solve-7"
  (run* (q)
    (eval-expo-solve `(eval-expo ,quinec () ,quinec)))
  '(_.0))



(test "eval-expo-deriv-1"
  (run* (q)
    (fresh (v tree)
      (eval-expo-deriv `(eval-expo (lambda (x) x) () ,v) tree)
      (== `(,v ,tree) q)))
  '(((closure x x ())
     (((eval-expo (lambda (x) x) () (closure x x ()))
       <--
       Abs
       ())))))

(test "eval-expo-deriv-2"
  (run* (q)
    (fresh (v tree)
      (eval-expo-deriv `(eval-expo ,quinec () ,v) tree)
      (== `(,v ,tree) q)))
  '((((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))
     (((eval-expo
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x))))
        ()
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
       <--
       App
       (((eval-expo
          (lambda (x) (list x (list 'quote x)))
          ()
          (closure x (list x (list 'quote x)) ()))
         <--
         Abs
         ())
        ((eval-expo
          '(lambda (x) (list x (list 'quote x)))
          ()
          (lambda (x) (list x (list 'quote x))))
         <--
         Quote
         ())
        ((eval-expo
          (list x (list 'quote x))
          ((x lambda (x) (list x (list 'quote x))))
          ((lambda (x) (list x (list 'quote x)))
           '(lambda (x) (list x (list 'quote x)))))
         <--
         List
         (((eval-expo
            x
            ((x lambda (x) (list x (list 'quote x))))
            (lambda (x) (list x (list 'quote x))))
           <--
           Var
           ())
          ((eval-expo
            (list 'quote x)
            ((x lambda (x) (list x (list 'quote x))))
            '(lambda (x) (list x (list 'quote x))))
           <--
           List
           (((eval-expo
              'quote
              ((x lambda (x) (list x (list 'quote x))))
              quote)
             <--
             Quote
             ())
            ((eval-expo
              x
              ((x lambda (x) (list x (list 'quote x))))
              (lambda (x) (list x (list 'quote x))))
             <--
             Var
             ())))))))))))



(test "eval-expo-debug-1"
  (run 1 (q)
    (fresh (v tree ok)
      (eval-expo-debug `(eval-expo (lambda (x) x) () ,v) tree ok)
      (== `(,v ,tree ,ok) q)))
  '(((closure x x ())
     (((eval-expo (lambda (x) x) () (closure x x ()))
       <--
       Abs
       ()))
     #t)))

(test "eval-expo-debug-2"
  (run 1 (q)
    (fresh (v tree ok)
      (eval-expo-debug `(eval-expo ,quinec () ,v) tree ok)
      (== `(,v ,tree ,ok) q)))
  '((((lambda (x) (list x (list 'quote x)))
      '(lambda (x) (list x (list 'quote x))))
     (((eval-expo
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x))))
        ()
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
       <--
       App
       (((eval-expo
          (lambda (x) (list x (list 'quote x)))
          ()
          (closure x (list x (list 'quote x)) ()))
         <--
         Abs
         ())
        ((eval-expo
          '(lambda (x) (list x (list 'quote x)))
          ()
          (lambda (x) (list x (list 'quote x))))
         <--
         Quote
         ())
        ((eval-expo
          (list x (list 'quote x))
          ((x lambda (x) (list x (list 'quote x))))
          ((lambda (x) (list x (list 'quote x)))
           '(lambda (x) (list x (list 'quote x)))))
         <--
         List
         (((eval-expo
            x
            ((x lambda (x) (list x (list 'quote x))))
            (lambda (x) (list x (list 'quote x))))
           <--
           Var
           ())
          ((eval-expo
            (list 'quote x)
            ((x lambda (x) (list x (list 'quote x))))
            '(lambda (x) (list x (list 'quote x))))
           <--
           List
           (((eval-expo
              'quote
              ((x lambda (x) (list x (list 'quote x))))
              quote)
             <--
             Quote
             ())
            ((eval-expo
              x
              ((x lambda (x) (list x (list 'quote x))))
              (lambda (x) (list x (list 'quote x))))
             <--
             Var
             ()))))))))
     #t)))

(test "eval-expo-debug-3"
  (run 1 (q)
    (fresh (exp tree ok)
      (eval-expo-debug `(eval-expo ,exp () ,quinec) tree ok)
      (== `(,exp ,tree ,ok) q)))
  '(('((lambda (x) (list x (list 'quote x)))
       '(lambda (x) (list x (list 'quote x))))
     (((eval-expo
        '((lambda (x) (list x (list 'quote x)))
          '(lambda (x) (list x (list 'quote x))))
        ()
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
       <--
       Quote
       ()))
     #t)))

(test "eval-expo-debug-4"
  (run 1 (q)
    (fresh (tree ok)
      (eval-expo-debug `(eval-expo ,quinec () ,quinec) tree ok)
      (== `(,tree ,ok) q)))
  '(((((eval-expo
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x))))
        ()
        ((lambda (x) (list x (list 'quote x)))
         '(lambda (x) (list x (list 'quote x)))))
       <--
       App
       (((eval-expo
          (lambda (x) (list x (list 'quote x)))
          ()
          (closure x (list x (list 'quote x)) ()))
         <--
         Abs
         ())
        ((eval-expo
          '(lambda (x) (list x (list 'quote x)))
          ()
          (lambda (x) (list x (list 'quote x))))
         <--
         Quote
         ())
        ((eval-expo
          (list x (list 'quote x))
          ((x lambda (x) (list x (list 'quote x))))
          ((lambda (x) (list x (list 'quote x)))
           '(lambda (x) (list x (list 'quote x)))))
         <--
         List
         (((eval-expo
            x
            ((x lambda (x) (list x (list 'quote x))))
            (lambda (x) (list x (list 'quote x))))
           <--
           Var
           ())
          ((eval-expo
            (list 'quote x)
            ((x lambda (x) (list x (list 'quote x))))
            '(lambda (x) (list x (list 'quote x))))
           <--
           List
           (((eval-expo
              'quote
              ((x lambda (x) (list x (list 'quote x))))
              quote)
             <--
             Quote
             ())
            ((eval-expo
              x
              ((x lambda (x) (list x (list 'quote x))))
              (lambda (x) (list x (list 'quote x))))
             <--
             Var
             ()))))))))
     #t)))




#!eof  ;; remove eond-of-file marker to run the long (quine) tests

;; Long (quine-generating) tests!

(test "eval-expo-solve-quine-1"
  ;; takes a few minutes, but returns!
  (run 1 (q)
    (eval-expo-solve `(eval-expo ,q () ,q)))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "eval-expo-debug-quine-1"
  ;; takes a few minutes to return  
  (run 1 (q)
    (fresh (exp tree ok)
      (eval-expo-debug `(eval-expo ,exp () ,exp) tree ok)
      (== `(,exp ,tree ,ok) q)))
  '(((((lambda (_.0) (list _.0 (list 'quote _.0)))
       '(lambda (_.0) (list _.0 (list 'quote _.0))))
      (((eval-expo
         ((lambda (_.0) (list _.0 (list 'quote _.0)))
          '(lambda (_.0) (list _.0 (list 'quote _.0))))
         ()
         ((lambda (_.0) (list _.0 (list 'quote _.0)))
          '(lambda (_.0) (list _.0 (list 'quote _.0)))))
        <--
        App
        (((eval-expo
           (lambda (_.0) (list _.0 (list 'quote _.0)))
           ()
           (closure _.0 (list _.0 (list 'quote _.0)) ()))
          <--
          Abs
          ())
         ((eval-expo
           '(lambda (_.0) (list _.0 (list 'quote _.0)))
           ()
           (lambda (_.0) (list _.0 (list 'quote _.0))))
          <--
          Quote
          ())
         ((eval-expo
           (list _.0 (list 'quote _.0))
           ((_.0 lambda (_.0) (list _.0 (list 'quote _.0))))
           ((lambda (_.0) (list _.0 (list 'quote _.0)))
            '(lambda (_.0) (list _.0 (list 'quote _.0)))))
          <--
          List
          (((eval-expo
             _.0
             ((_.0 lambda (_.0) (list _.0 (list 'quote _.0))))
             (lambda (_.0) (list _.0 (list 'quote _.0))))
            <--
            Var
            ())
           ((eval-expo
             (list 'quote _.0)
             ((_.0 lambda (_.0) (list _.0 (list 'quote _.0))))
             '(lambda (_.0) (list _.0 (list 'quote _.0))))
            <--
            List
            (((eval-expo
               'quote
               ((_.0 lambda (_.0) (list _.0 (list 'quote _.0))))
               quote)
              <--
              Quote
              ())
             ((eval-expo
               _.0
               ((_.0 lambda (_.0) (list _.0 (list 'quote _.0))))
               (lambda (_.0) (list _.0 (list 'quote _.0))))
              <--
              Var
              ()))))))))
      #t)
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))
