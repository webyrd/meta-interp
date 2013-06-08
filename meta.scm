;;; Translated from Nada Amin's core.logic code from the miniKanren confo at Clojure/West:
;;;
;;; https://github.com/namin/minikanren-confo

(define solve-for*
  (lambda (clause)
    (letrec ([solve (lambda (goals)
                      (conde
                        [(== '() goals)]
                        [(fresh (c g gs b)
                           (== `(,g . ,gs) goals)
                           (clause c g b)
                           (solve b)
                           (solve gs))]))])
      solve)))
(define solve-for
  (lambda (clause)
    (let ([solver* (solve-for* clause)])
      (lambda (goal) (solver* `(,goal))))))

(define solve-proof-for
  (lambda (clause)
    (letrec ([solve0 (lambda (goal tree)
                       (solve `(,goal) tree))]
             [solve (lambda (goals tree)
                      (conde
                        [(== '() goals)
                         (== '() tree)]
                        [(fresh (c g gs ts b tb)
                           (== `(,g . ,gs) goals)
                           (clause c g b)
                           (== `((,g <-- ,c ,tb) . ,ts) tree)
                           (solve b tb)
                           (solve gs ts))]))])
      solve0)))

(define debug-proof-for
  (lambda (clause)
    (letrec ([solve0 (lambda (goal tree ok)
                       (fresh ()
                         (solve `(,goal) tree ok)
                         (conda
                           [(== #t ok)]
                           [(== #f ok)])))]
             [solve (lambda (goals tree ok)
                      (conde
                        [(== '() goals)
                         (== '() tree)]
                        [(fresh (c g gs ts b tb ehead etail)
                           (== `(,g . ,gs) goals)
                           (conda
                             [(clause c g b)
                              (== `((,g <-- ,c ,tb) . ,ts)  tree)
                              (solve b tb ok)]
                             [(== `((,g error) . ,ts) tree)
                              (== #f ok)])
                           (solve gs ts ok))]))])
      solve0)))
