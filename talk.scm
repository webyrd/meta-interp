(load "mk.scm")
(load "meta.scm")

;;; Understanding and Debugging via Meta-Interpreters

(define tio-clause
  (lambda (c a b)
    (fresh (g e t)
      (== `(tio ,g ,e ,t) a)
      (conde
        [(== 'T-Var c)
         (fresh (x)
           (nomo x) (== e x)
           (env-ino x t g)
           (== '() b))]
        [(== 'T-Abs c)
         (fresh (e0 tx t0 g0)
           (nom/fresh (x)
             (lamo x e0 e)
             (arro tx t0 t)
             (env-pluso x tx g g0)
             (== `((tio ,g0 ,e0 ,t0)) b)))]
        [(== 'T-App c)
         (fresh (e1 e2 t1 t2)
           (appo e1 e2 e)
           (arro t2 t t1)
           (== `((tio ,g ,e1 ,t1) (tio ,g ,e2 ,t2)) b))]))))

(define tio-deriv (solve-proof-for tio-clause))

; type-derivations
(run* (q)
  (fresh (ty tree)
    (nom/fresh (x)
      (tio-deriv `(tio ,empty-env ,(lam x x) ,ty) tree)
      (== `(,ty ,tree) q))))
;; ==>
;; '([[_0 -> _0]
;;    ([[tio [env () ()] (fn [a_1] a_1) [_0 -> _0]] <-- T-Abs
;;      ([[tio [env (a_2) ([a_2 _0])] a_2 _0] <-- T-Var ()])])])


(run* (q)
  (fresh (ty tree)
    (nom/fresh (x)
      (tio-deriv `(tio ,empty-env ,(lam x `(,x ,x)) ,ty) tree)
      (== `(,ty ,tree) q))))
;; ==> ()


(define tio-debug-clause
  (lambda (c a b)
    (conde
      [(fresh (x y)
         (== `(== ,x ,y) a)
         (== x y)
         (== '() b))]
      [(fresh (x t g)
         (== `(env-ino ,x ,t ,g) a)
         (env-ino x t g)
         (== '() b))]
      [(fresh (g e t)
         (== `(tio ,g ,e ,t) a)
         (conde
           [(== 'T-Var c)
            (fresh (x)
              (nomo x) (== e x)
              (== `((env-ino ,x ,t ,g)) b))]
           [(== 'T-Abs c)
            (fresh (e0 tx t0 g0)
              (nom/fresh (x)
                (lamo x e0 e)
                (env-pluso x tx g g0)
                (== `((tio ,g0 ,e0 ,t0) (== ,t ,(arr tx t0))) b)))]
           [(== 'T-App c)
            (fresh (e1 e2 t1 t2 t11 t12)
              (appo e1 e2 e)
              (== b `((tio ,g ,e1 ,t1)
                      (tio ,g ,e2 ,t2)
                      (== ,t1 ,(arr t11 t12))
                      (== ,t2 ,t11)
                      (== ,t ,t12))))]))])))

(define tio-debug (debug-proof-for tio-clause))

(run* (q)
  (fresh (ty tree ok)
    (nom/fresh (x)
      (tio-debug `(tio ,empty-env ,(lam x `(,x ,x)) ,ty) tree ok)
      (== `(,ty ,tree ,ok) q))))
;; ==>
;;     '([[[_0 -> _1] -> _1]
;;         ([[tio [env () ()] (fn [a_2] (a_2 a_2)) [[_0 -> _1] -> _1]] <-- T-Abs
;;            ([[tio [env (a_3) ([a_3 [_0 -> _1]])] (a_3 a_3) _1] <-- T-App
;;               ([[tio [env (a_3) ([a_3 [_0 -> _1]])] a_3 [_0 -> _1]] <-- T-Var ()]
;;                [[tio [env (a_3) ([a_3 [_0 -> _1]])] a_3 _0] error])])])
;;         false])
