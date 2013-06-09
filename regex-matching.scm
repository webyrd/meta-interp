(load "mk.scm")
(load "meta.scm")
(load "testcheck.scm")

;;; vanilla miniKanren code, taken from https://github.com/webyrd/relational-parsing-with-derivatives/blob/master/mK-empty-set-as-failure/mk-rd.scm

; <regex> ::= 
;          |  EPSILON                ; Empty/blank pattern (same as #t)
;          |  '<symbol>              ; Symbol
;          |  (alt <regex> <regex>)  ; Alternation
;          |  (seq <regex> <regex>)  ; Sequence
;          |  (rep <regex>)          ; Repetition

;; Special regular expression.
(define EPSILON #t)   ; the empty string

;; Simplifying regex constructors.
(define (valid-seqo exp)
  (fresh (pat1 pat2)
    (== `(seq ,pat1 ,pat2) exp)
    (=/= EPSILON pat1)
    (=/= EPSILON pat2)))

(define (seqo pat1 pat2 out)
  (conde    
    [(== EPSILON pat1) (== pat2 out)]
    [(== EPSILON pat2) (== pat1 out) (=/= EPSILON pat1)]
    [(=/= EPSILON pat1) (=/= EPSILON pat2) (== `(seq ,pat1 ,pat2) out)]))

(define (valid-alto exp)
  (fresh (pat1 pat2)
    (== `(alt ,pat1 ,pat2) exp)
    (=/= pat1 pat2)))

(define (alto pat1 pat2 out)
  (conde
    [(== pat1 pat2) (== pat1 out)]
    [(=/= pat1 pat2) (== `(alt ,pat1 ,pat2) out)]))

(define (valid-repo exp)
  (fresh (pat)
    (== `(rep ,pat) exp)
    (=/= EPSILON pat)
    (conde
      ((symbolo pat))
      ((fresh (re1 re2)
         (== `(seq ,re1 ,re2) pat)
         (valid-seqo pat)))
      ((fresh (re1 re2)
         (== `(alt ,re1 ,re2) pat)
         (valid-alto pat))))))

(define (repo pat out)
  (conde
    [(== EPSILON pat)
     (== EPSILON out)]
    [(conde
       ((symbolo pat) (== `(rep ,pat) out))
       ((fresh (re1 re2)
          (conde
            ((== `(rep ,re1) pat)
             ; remove nested reps
             (== pat out))
            ((== `(seq ,re1 ,re2) pat)
             (== `(rep ,pat) out)
             (valid-seqo pat))
            ((== `(alt ,re1 ,re2) pat)
             (== `(rep ,pat) out)
             (valid-alto pat))))))]))

;; Matching functions.

; deltao : regex
(define (deltao re)
  (conde
    [(== EPSILON re)]
    [(fresh (re1)
       (== `(rep ,re1) re)
       (valid-repo re))]
    [(fresh (re1 re2)
       (== `(alt ,re1 ,re2) re)
       (valid-alto re)
       (conde
         ((deltao re1))
         ((not-deltao re1) (deltao re2))))]
    [(fresh (re1 re2)
       (== `(seq ,re1 ,re2) re)
       (valid-seqo re)
       (deltao re1)
       (deltao re2))]))

(define (not-deltao re)
  (conde
    [(symbolo re)]
    [(fresh (re1 re2)       
       (== `(seq ,re1 ,re2) re)
       (valid-seqo re)
       (conde
         ((not-deltao re1))
         ((deltao re1) (not-deltao re2))))]
    [(fresh (re1 re2)
       (== `(alt ,re1 ,re2) re)
       (valid-alto re)
       (not-deltao re1)
       (not-deltao re2))]))

; d/dco : regex regex-atom regex
(define (d/dco re c out)
  (fresh ()
    (symbolo c)
    (conde
      [(== c re)
       (== EPSILON out)]
      [(fresh (re1 res1)
         (== `(rep ,re1) re)
         (valid-repo re)
         (seqo res1 re out)
         (d/dco re1 c res1))]
      [(fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (valid-alto re)
         (conde
           ((no-d/dco re2 c)
            (d/dco re1 c out))
           ((no-d/dco re1 c)
            (d/dco re2 c out))
           ((alto res1 res2 out)
            (d/dco re1 c res1)
            (d/dco re2 c res2))))]
      [(fresh (re1 re2 res1 res2 res3)
         (== `(seq ,re1 ,re2) re)
         (valid-seqo re)
         (seqo res1 re2 res2)
         (conde
           ((== res2 out) (not-deltao re1))
           ((alto res2 res3 out)
            (deltao re1)
            (d/dco re2 c res3)))
         (d/dco re1 c res1))])))

(define (no-d/dco re c)
  (fresh ()
    (symbolo c)
    (conde
      [(== EPSILON re)]
      [(symbolo re) (=/= c re)]
      [(fresh (re1 res1)
         (== `(rep ,re1) re)
         (valid-repo re)
         (no-d/dco re c))]
      [(fresh (re1 re2 res1 res2 res3)
         (== `(seq ,re1 ,re2) re)
         (valid-seqo re)
         (conde
           ((not-deltao re1))
           ((deltao re1) (no-d/dco re2 c)))
         (no-d/dco re1 c))]
      [(fresh (re1 re2 res1 res2)
         (== `(alt ,re1 ,re2) re)
         (valid-alto re)
         (no-d/dco re1 c)
         (no-d/dco re2 c))])))

; regex-matcho : regex list 
(define (regex-matcho pattern data)
  (conde
    [(== '() data) (deltao pattern)]
    [(fresh (a d res)
       (== `(,a . ,d) data)
       (d/dco pattern a res)
       (regex-matcho res d))]))

;;; new tests

(test "2"
  (run* (q) (repo EPSILON q))
  '(#t))

(test "3"
  (run* (q) (repo 'foo q))
  '((rep foo)))

(test "3-b"
  (run* (q)
    (fresh (res)
      (repo 'foo res)
      (repo res q)))
  '((rep foo)))

(test "3-c"
  (run* (q)
    (fresh (res)
      (repo EPSILON res)
      (repo res q)))
  '(#t))

(test "6"
  (run* (q) (alto 'foo 'bar q))
  '((alt foo bar)))

(test "6-b"
  (run* (q) (alto 'foo EPSILON q))
  '((alt foo #t)))

(test "6-c"
  (run* (q) (alto EPSILON 'foo q))
  '((alt #t foo)))

(test "9"
  (run* (q) (seqo EPSILON 'foo q))
  '(foo))

(test "10"
  (run* (q) (seqo 'foo EPSILON q))
  '(foo))

(test "11"
  (run* (q) (seqo 'foo 'bar q))
  '((seq foo bar)))

(test "12"
  (run 10 (q) (deltao q))
  '(#t
    ((rep _.0) (sym _.0))
    ((rep (seq _.0 _.1)) (=/= ((_.0 #t)) ((_.1 #t))))
    ((rep (alt _.0 _.1)) (=/= ((_.0 _.1))))
    ((alt #t _.0) (=/= ((_.0 #t))))
    ((alt _.0 #t) (sym _.0))
    ((alt (rep _.0) _.1) (=/= ((_.1 (rep _.0)))) (sym _.0))
    ((seq (rep _.0) (rep _.1)) (sym _.0 _.1))
    ((alt _.0 (rep _.1)) (sym _.0 _.1))
    ((alt (rep (seq _.0 _.1)) _.2)
     (=/= ((_.0 #t)) ((_.1 #t)) ((_.2 (rep (seq _.0 _.1))))))))

(test "12-b"
  (run 10 (q) (not-deltao q))
  '((_.0 (sym _.0)) ((seq _.0 _.1) (=/= ((_.1 #t))) (sym _.0))
    ((alt _.0 _.1) (=/= ((_.0 _.1))) (sym _.0 _.1))
    ((seq (rep _.0) _.1) (sym _.0 _.1))
    ((seq (seq _.0 _.1) _.2)
     (=/= ((_.1 #t)) ((_.2 #t)))
     (sym _.0))
    ((alt _.0 (seq _.1 _.2)) (=/= ((_.2 #t))) (sym _.0 _.1))
    ((alt (seq _.0 _.1) _.2) (=/= ((_.1 #t))) (sym _.0 _.2))
    ((seq (alt _.0 _.1) _.2)
     (=/= ((_.0 _.1)) ((_.2 #t)))
     (sym _.0 _.1))
    ((alt _.0 (alt _.1 _.2))
     (=/= ((_.1 _.2)))
     (sym _.0 _.1 _.2))
    ((alt (alt _.0 _.1) _.2)
     (=/= ((_.0 _.1)))
     (sym _.0 _.1 _.2))))

(test "13"
  (run 10 (q)
    (fresh (re c out)
      (d/dco re c out)
      (== `(,re ,c ,out) q)))
  '(((_.0 _.0 #t) (sym _.0)) (((rep _.0) _.0 (rep _.0)) (sym _.0))
    (((seq _.0 _.1) _.0 _.1) (=/= ((_.1 #t))) (sym _.0))
    (((alt _.0 #t) _.0 #t) (sym _.0))
    (((alt _.0 _.1) _.0 #t) (=/= ((_.0 _.1))) (sym _.0 _.1))
    (((alt #t _.0) _.0 #t) (sym _.0))
    (((rep (alt _.0 #t)) _.0 (rep (alt _.0 #t))) (sym _.0))
    (((rep (alt _.0 _.1)) _.0 (rep (alt _.0 _.1)))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))
    (((rep (alt #t _.0)) _.0 (rep (alt #t _.0))) (sym _.0))
    (((alt _.0 _.1) _.1 #t) (=/= ((_.0 _.1))) (sym _.0 _.1))))

(test "14"
  (run* (q) (regex-matcho '(seq foo (rep bar)) 
                          '(foo bar bar bar)))
  '(_.0))

(test "14-b"
  (run* (q) (regex-matcho '(seq foo (rep bar))
                          '(foo)))
  '(_.0))

(test "14-c"
  (run* (q) (d/dco '(seq foo (rep bar)) 'foo q))
  '((rep bar)))

(test "14-d"
  (run* (q) (valid-seqo '(seq foo (rep bar))))
  '(_.0))

(test "14-e"
  (run* (q) (d/dco 'foo 'foo q))
  '(#t))

(test "14-f"
  (run* (q) (d/dco '(rep bar) 'foo q))
  '())

(test "15"
  (run* (q) (regex-matcho '(seq foo (rep bar)) 
                          '(foo bar baz bar bar)))
  '())

(test "16"
  (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                          '(foo bar baz bar bar)))
  '(_.0))

;;; generate regex patterns that match the input string (!)
;;; (seq foo (rep bar)) was the original regex
;;; The #t's in the answer represent epsilons.  This seems to be okay, actually!
;;; The run expression can produce equivalent regex's; for example,
;;;    (rep (alt foo bar))
;;; and
;;;    (rep (alt bar foo))
;;; Is there a canonical representation of regex's that would avoid these
;;; essentially duplicate answers?

;;; WEB   wow--these answers are very different from the previous answers in the naive mk translation.
(test "20"
  (run 30 (q) (regex-matcho q '(foo bar bar bar)))
  '((seq foo (rep bar)) (seq foo (seq bar (rep bar))) (seq foo (seq bar (seq bar bar))) (seq foo (seq bar (seq bar (rep bar)))) ((seq foo (seq bar (seq bar (seq bar (rep _.0))))) (sym _.0)) (rep (alt foo bar)) (seq foo (seq bar (seq bar (alt bar #t)))) ((seq foo (seq bar (seq bar (seq bar (rep (seq _.0 _.1)))))) (=/= ((_.0 #t)) ((_.1 #t)))) ((seq foo (seq bar (seq bar (seq bar (rep (alt _.0 _.1)))))) (=/= ((_.0 _.1)))) ((seq foo (seq bar (seq bar (seq bar (alt #t _.0))))) (=/= ((_.0 #t)))) ((seq foo (seq bar (seq bar (seq bar (alt _.0 #t))))) (sym _.0)) (seq foo (rep (alt bar #t))) ((seq foo (seq bar (seq bar (seq bar (alt (rep _.0) _.1))))) (=/= ((_.1 (rep _.0)))) (sym _.0)) ((seq foo (seq bar (seq bar (alt bar _.0)))) (=/= ((_.0 bar))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep _.1)))))) (sym _.0 _.1)) (seq foo (seq bar (seq bar (alt #t bar)))) (seq foo (seq bar (rep (alt bar #t)))) ((seq foo (seq bar (seq bar (seq bar (alt _.0 (rep _.1)))))) (sym _.0 _.1)) ((seq foo (seq bar (seq bar (seq bar (alt (rep (seq _.0 _.1)) _.2))))) (=/= ((_.0 #t)) ((_.1 #t)) ((_.2 (rep (seq _.0 _.1)))))) ((seq foo (rep (alt bar _.0))) (=/= ((_.0 bar))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (alt (rep (alt _.0 _.1)) _.2))))) (=/= ((_.0 _.1)) ((_.2 (rep (alt _.0 _.1)))))) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep (seq _.1 _.2))))))) (=/= ((_.1 #t)) ((_.2 #t))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (alt (alt #t _.0) _.1))))) (=/= ((_.0 #t)) ((_.1 (alt #t _.0))))) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (rep (alt _.1 _.2))))))) (=/= ((_.1 _.2))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep _.0) (alt #t _.1)))))) (=/= ((_.1 #t))) (sym _.0)) (seq foo (seq bar (seq bar (rep (alt bar #t))))) ((seq foo (seq bar (seq bar (seq bar (alt (seq _.0 _.1) #t))))) (=/= ((_.1 #t))) (sym _.0)) ((seq foo (seq bar (seq bar (seq bar (seq (rep (seq _.0 _.1)) (rep _.2)))))) (=/= ((_.0 #t)) ((_.1 #t))) (sym _.2)) (rep (alt bar foo)) (seq foo (rep (alt #t bar))))
  )

(test "20-ab"
;;; takes around 10 seconds to generate 10,0000 answers under Petite
;;; Here's the 1,000th answer
  (car (reverse (run 1000 (q) (regex-matcho q '(foo bar bar bar)))))
  '((seq foo (seq bar (seq (seq bar bar) (alt (alt (rep (alt _.0 _.1)) _.2) _.3)))) (=/= ((_.0 _.1)) ((_.2 (rep (alt _.0 _.1)))) ((_.3 (alt (rep (alt _.0 _.1)) _.2))))))

(test "20-a"
  (run 1 (q) (regex-matcho '(alt #t (seq foo (rep bar))) '(foo bar bar bar)))
  '(_.0))

(test "20-aa"
  (run 1 (q) (regex-matcho '(alt (seq foo (rep bar)) #t) '(foo bar bar bar)))
  '(_.0))

(test "20-c"
  (run 1 (q) (d/dco '(alt #t (seq foo (rep bar))) 'foo q))
  '((rep bar)))

(test "20-cc"
  (run 1 (q) (d/dco '(alt (seq foo (rep bar)) #t) 'foo q))
  '((rep bar)))

(test "20-c1"
  (run 1 (q) (d/dco '#t 'foo q))
  '())

(test "20-c2"
  (run 1 (q) (d/dco '(seq foo (rep bar)) 'foo q))
  '((rep bar)))

(test "20-d"
  (run 1 (q) (d/dco '(alt (seq foo (rep bar)) #t) 'foo q))
  '((rep bar)))

(test "20-e"
;;; illegal alt with duplicate patterns
  (run 1 (q) (d/dco '(alt (seq foo (rep bar)) (seq foo (rep bar))) 'foo q))
  '())

(test "20-z"
  (run 1 (q) (fresh (e1 e2) (regex-matcho q '(foo bar bar bar)) (== `(alt ,e1 ,e2) q)))
  '((alt (seq foo (rep bar)) #t)))

;;; look for the literal match regex
;;; easy version
(test "21"
  (run 1 (q)
    (== `(seq foo (seq bar bar)) q)
    (regex-matcho q 
                  '(foo bar bar)))
  '((seq foo (seq bar bar))))

;;; look for the literal match regex
;;; hard version (generate and test)
(test "22"
  (run 1 (q)
    (regex-matcho q 
                  '(foo bar bar))
    (== `(seq foo (seq bar bar)) q))
  '((seq foo (seq bar bar))))

;;; look for the literal match regex (longer)
;;; easy version
(test "23"
  (run 1 (q)
    (== `(seq foo (seq bar (seq bar bar))) q)
    (regex-matcho q 
                  '(foo bar bar bar)))
  '((seq foo (seq bar (seq bar bar)))))

;;; look for the literal match regex (longer)
;;; hard version (generate and test)
(test "24"
  (run 1 (q)
    (regex-matcho q 
                  '(foo bar bar bar))
    (== `(seq foo (seq bar (seq bar bar))) q))
  '((seq foo (seq bar (seq bar bar)))))

;;; generate regex, and data that matches.
(test "25"
  (run 30 (q)
    (fresh (regex data)
      (regex-matcho regex 
                    data)
      (== `(,regex ,data) q)))
  '((#t ()) (((rep _.0) ()) (sym _.0)) ((_.0 (_.0)) (sym _.0)) (((rep (seq _.0 _.1)) ()) (=/= ((_.0 #t)) ((_.1 #t)))) (((rep (alt _.0 _.1)) ()) (=/= ((_.0 _.1)))) (((alt #t _.0) ()) (=/= ((_.0 #t)))) (((alt _.0 #t) ()) (sym _.0)) (((alt (rep _.0) _.1) ()) (=/= ((_.1 (rep _.0)))) (sym _.0)) (((seq (rep _.0) (rep _.1)) ()) (sym _.0 _.1)) (((rep _.0) (_.0)) (sym _.0)) (((alt _.0 (rep _.1)) ()) (sym _.0 _.1)) (((alt (rep (seq _.0 _.1)) _.2) ()) (=/= ((_.0 #t)) ((_.1 #t)) ((_.2 (rep (seq _.0 _.1)))))) (((alt (rep (alt _.0 _.1)) _.2) ()) (=/= ((_.0 _.1)) ((_.2 (rep (alt _.0 _.1)))))) (((seq (rep _.0) (rep (seq _.1 _.2))) ()) (=/= ((_.1 #t)) ((_.2 #t))) (sym _.0)) (((alt (alt #t _.0) _.1) ()) (=/= ((_.0 #t)) ((_.1 (alt #t _.0))))) (((seq (rep _.0) (rep (alt _.1 _.2))) ()) (=/= ((_.1 _.2))) (sym _.0)) (((seq (rep _.0) (alt #t _.1)) ()) (=/= ((_.1 #t))) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt (seq _.0 _.1) #t) ()) (=/= ((_.1 #t))) (sym _.0)) (((seq (rep (seq _.0 _.1)) (rep _.2)) ()) (=/= ((_.0 #t)) ((_.1 #t))) (sym _.2)) (((alt (alt _.0 #t) _.1) ()) (=/= ((_.1 (alt _.0 #t)))) (sym _.0)) (((alt (alt _.0 _.1) #t) ()) (=/= ((_.0 _.1))) (sym _.0 _.1)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq (rep _.0) (alt _.1 #t)) ()) (sym _.0 _.1)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((alt _.0 (rep (seq _.1 _.2))) ()) (=/= ((_.1 #t)) ((_.2 #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((alt _.0 (rep (alt _.1 _.2))) ()) (=/= ((_.1 _.2))) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((seq (rep (alt _.0 _.1)) (rep _.2)) ()) (=/= ((_.0 _.1))) (sym _.2))))

;;; generate regexs, and *non-empty* data, that match
;;; This test was *extremely* slow under the naive miniKanren translation:  even run 3 took a while.
;;; Now run 1000 takes 4.5 seconds under Petite.
(test "27"
  (run 20 (q)
    (fresh (regex data)
      (=/= '() data)
      (regex-matcho regex
                    data)
      (== `(,regex ,data) q)))
  '(((_.0 (_.0)) (sym _.0)) (((rep _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (rep (seq _.1 _.2))) (_.0)) (=/= ((_.1 #t)) ((_.2 #t))) (sym _.0)) (((seq _.0 (rep (alt _.1 _.2))) (_.0)) (=/= ((_.1 _.2))) (sym _.0)) (((seq _.0 (alt #t _.1)) (_.0)) (=/= ((_.1 #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt _.0 _.1) (_.0)) (=/= ((_.0 _.1))) (sym _.0 _.1)) (((seq _.0 (alt _.1 #t)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt #t _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt (rep _.1) _.2)) (_.0)) (=/= ((_.2 (rep _.1)))) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0))))

;;; generate regexs, and *non-null* data
;;; This test was problematic under the naive mk translation.
(test "28"
  (run 30 (q)
    (fresh (regex data)
      (=/= '() data)
      (regex-matcho regex 
                    data)
      (== `(,regex ,data) q)))
  '(((_.0 (_.0)) (sym _.0)) (((rep _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0)) (sym _.0)) (((alt _.0 #t) (_.0)) (sym _.0)) (((seq _.0 (rep _.1)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0)) (sym _.0)) (((seq _.0 _.1) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (rep (seq _.1 _.2))) (_.0)) (=/= ((_.1 #t)) ((_.2 #t))) (sym _.0)) (((seq _.0 (rep (alt _.1 _.2))) (_.0)) (=/= ((_.1 _.2))) (sym _.0)) (((seq _.0 (alt #t _.1)) (_.0)) (=/= ((_.1 #t))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt _.0 _.1) (_.0)) (=/= ((_.0 _.1))) (sym _.0 _.1)) (((seq _.0 (alt _.1 #t)) (_.0)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((alt #t _.0) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt (rep _.1) _.2)) (_.0)) (=/= ((_.2 (rep _.1)))) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (seq (rep _.1) (rep _.2))) (_.0)) (sym _.0 _.1 _.2)) (((seq _.0 (rep _.1)) (_.0 _.1)) (sym _.0 _.1)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep (alt _.0 #t)) (_.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0)) (((seq _.0 (alt _.1 (rep _.2))) (_.0)) (sym _.0 _.1 _.2)) (((seq _.0 (alt (rep (seq _.1 _.2)) _.3)) (_.0)) (=/= ((_.1 #t)) ((_.2 #t)) ((_.3 (rep (seq _.1 _.2))))) (sym _.0)) (((rep _.0) (_.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0 _.0)) (sym _.0))))

(test "28-b"
  (run 10 (q)
    (fresh (a b c d regex data)
      (== `(,a ,b ,b ,c ,c ,d) data)
      (=/= a b)
      (=/= b c)
      (=/= c d)
      (=/= d a)
      (regex-matcho regex 
                    data)
      (== `(,regex ,data) q)))
  '((((rep (alt _.0 _.1)) (_.0 _.1 _.1 _.0 _.0 _.1)) (=/= ((_.0 _.1))) (sym _.0 _.1)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 _.3))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (rep (alt _.1 _.2))) (_.0 _.1 _.1 _.2 _.2 _.1)) (=/= ((_.0 _.1)) ((_.1 _.2))) (sym _.0 _.1 _.2)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (rep _.3)))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3))) (sym _.0 _.1 _.2 _.3)) (((rep (alt _.0 _.1)) (_.1 _.0 _.0 _.1 _.1 _.0)) (=/= ((_.0 _.1))) (sym _.0 _.1)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep _.4))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3))) (sym _.0 _.1 _.2 _.3 _.4)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (alt _.3 #t)))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (seq _.1 (rep (alt _.1 _.2)))) (_.0 _.1 _.1 _.2 _.2 _.1)) (=/= ((_.0 _.1)) ((_.1 _.2))) (sym _.0 _.1 _.2)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep (seq _.4 _.5)))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3)) ((_.4 #t)) ((_.5 #t))) (sym _.0 _.1 _.2 _.3)) (((seq _.0 (seq _.1 (seq _.1 (seq _.2 (seq _.2 (seq _.3 (rep (alt _.4 _.5)))))))) (_.0 _.1 _.1 _.2 _.2 _.3)) (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.1 _.2)) ((_.2 _.3)) ((_.4 _.5))) (sym _.0 _.1 _.2 _.3))))

(test "29a"
  (run 10 (q)
    (fresh (regex data)
      (== '(rep #t) regex)
      (=/= '() data)
      (regex-matcho regex data)
      (== `(,regex ,data) q)))
  '())

(test "29b"
  (run 10 (q)
    (fresh (regex data out)
      (== '(rep #t) regex)
      (regex-matcho regex data)))
  '())

(test "29f"
  (run 10 (q)
    (fresh (regex data out)
      (== '(seq #t #t) regex)
      (regex-matcho regex data)))
  '())

(test "29z"
  (run* (q)
    (fresh (regex data)
      (== #t regex)
      (=/= '() data)
      (regex-matcho regex data)
      (== `(,regex ,data) q)))
  '())

(test "30"
  (run* (q) (repo EPSILON q))
  '(#t))


;;; generate strings that match a certain regex
(test "40"
  (run 30 (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                            q))
  '((foo)
    (foo bar)
    (foo baz)
    (foo bar bar)
    (foo baz bar)
    (foo bar baz)
    (foo baz baz)
    (foo bar bar bar)
    (foo baz bar bar)
    (foo bar baz bar)
    (foo baz baz bar)
    (foo bar bar baz)
    (foo baz bar baz)
    (foo bar baz baz)
    (foo baz baz baz)
    (foo bar bar bar bar)
    (foo baz bar bar bar)
    (foo bar baz bar bar)                
    (foo baz baz bar bar)
    (foo bar bar baz bar)
    (foo baz bar baz bar)
    (foo bar baz baz bar)
    (foo baz baz baz bar)
    (foo bar bar bar baz)
    (foo baz bar bar baz)
    (foo bar baz bar baz)
    (foo baz baz bar baz)
    (foo bar bar baz baz)
    (foo baz bar baz baz)
    (foo bar baz baz baz)))

(test "41"
  (run* (q)
    (fresh (re2)
      (regex-matcho `(seq foo ,re2) 
                    '(bar))))
  '())

;;; original tests

(test "31"
  (run* (q) (d/dco 'baz 'f q))
  '())

(test "32"
  (run* (q) (d/dco '(seq foo barn) 'foo q))
  '(barn))

(test "33"
  (run* (q) (d/dco '(alt (seq foo bar) (seq foo (rep baz))) 'foo q))
  '((alt bar (rep baz))))

(test "34"
  (run* (q) (regex-matcho '(seq foo (rep bar)) 
                          '(foo bar bar bar)))
  '(_.0))

(test "35"
  (run* (q) (regex-matcho '(seq foo (rep bar)) 
                          '(foo bar baz bar bar)))
  '())

(test "36"
  (run* (q) (regex-matcho '(seq foo (rep (alt bar baz))) 
                          '(foo bar baz bar bar)))
  '(_.0))




;;; meta-interpreter version

(define d/dco-clause
  (lambda (clause a b)
    (fresh (re c out)
      (== `(d/dco ,re ,c ,out) a)
      (symbolo c)
      (conde
        [(== 'C clause)
         (== c re)
         (== EPSILON out)
         (== '() b)]
        [(== 'Rep clause)
         (fresh (re1 res1)
           (== `(rep ,re1) re)
           (valid-repo re)
           (seqo res1 re out)
           (== `((d/dco ,re1 ,c ,res1)) b))]
        [(== 'Alt clause)
         (fresh (re1 re2 res1 res2)
           (== `(alt ,re1 ,re2) re)
           (valid-alto re)
           (conde
             ((no-d/dco re2 c)
              (== `((d/dco ,re1 ,c ,out)) b))
             ((no-d/dco re1 c)
              (== `((d/dco ,re2 ,c ,out)) b))
             ((alto res1 res2 out)
              (== b `((d/dco ,re1 ,c ,res1)
                      (d/dco ,re2 ,c ,res2))))))]
        [(== 'Seq clause)
         (fresh (re1 re2 res1 res2 res3)
           (== `(seq ,re1 ,re2) re)
           (valid-seqo re)
           (seqo res1 re2 res2)
           (conde
             ((== res2 out)
              (not-deltao re1)              
              (== `((d/dco ,re1 ,c ,res1)) b))
             ((alto res2 res3 out)
              (deltao re1)
              (== b `((d/dco ,re2 ,c ,res3)
                      (d/dco ,re1 ,c ,res1))))))]))))

; run as normal
(define d/dco-solve (solve-for d/dco-clause))

; generate a derivation tree/proof true for the result
(define d/dco-deriv (solve-proof-for d/dco-clause))

; debugging variant
(define d/dco-debug (debug-proof-for d/dco-clause))

(test "d/dco-solve-13"
  (run 10 (q)
    (fresh (re c out)
      (d/dco-solve `(d/dco ,re ,c ,out))      
      (== `(,re ,c ,out) q)))
  '(((_.0 _.0 #t) (sym _.0))
    (((rep _.0) _.0 (rep _.0)) (sym _.0))
    (((rep (alt _.0 #t)) _.0 (rep (alt _.0 #t))) (sym _.0))
    (((alt _.0 #t) _.0 #t) (sym _.0))
    (((rep (alt _.0 _.1)) _.0 (rep (alt _.0 _.1)))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))
    (((rep (seq _.0 _.1)) _.0 (seq _.1 (rep (seq _.0 _.1))))
     (=/= ((_.1 #t)))
     (sym _.0))
    (((rep (alt (alt _.0 #t) #t))
      _.0
      (rep (alt (alt _.0 #t) #t)))
     (sym _.0))
    (((alt (rep _.0) #t) _.0 (rep _.0)) (sym _.0))
    (((alt _.0 _.1) _.0 #t) (=/= ((_.0 _.1))) (sym _.0 _.1))
    (((rep (alt (alt _.0 _.1) #t))
      _.0
      (rep (alt (alt _.0 _.1) #t)))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))))

(test "d/dco-solve-14-c"
  (run* (q) (d/dco-solve `(d/dco (seq foo (rep bar)) foo ,q)))
  '((rep bar)))

(test "d/dco-solve-14-e"
  (run* (q) (d/dco-solve `(d/dco foo foo ,q)))
  '(#t))

(test "d/dco-solve-14-f"
  (run* (q) (d/dco-solve `(d/dco (rep bar) foo ,q)))
  '())

(test "d/dco-solve-20-c"
  (run 1 (q) (d/dco-solve `(d/dco (alt #t (seq foo (rep bar))) foo ,q)))
  '((rep bar)))

(test "d/dco-solve-20-cc"
  (run 1 (q) (d/dco-solve `(d/dco (alt (seq foo (rep bar)) #t) foo ,q)))
  '((rep bar)))

(test "d/dco-solve-20-c1"
  (run 1 (q) (d/dco-solve `(d/dco #t foo ,q)))
  '())

(test "d/dco-solve-20-c2"
  (run 1 (q) (d/dco-solve `(d/dco (seq foo (rep bar)) foo ,q)))
  '((rep bar)))

(test "d/dco-solve-20-d"
  (run 1 (q) (d/dco-solve `(d/dco (alt (seq foo (rep bar)) #t) foo ,q)))
  '((rep bar)))

(test "d/dco-solve-20-e"
;;; illegal alt with duplicate patterns
  (run 1 (q) (d/dco-solve `(d/dco (alt (seq foo (rep bar)) (seq foo (rep bar))) foo ,q)))
  '())

(test "d/dco-solve-31"
  (run* (q) (d/dco-solve `(d/dco baz f ,q)))
  '())

(test "d/dco-solve-32"
  (run* (q) (d/dco-solve `(d/dco (seq foo barn) foo ,q)))
  '(barn))

(test "d/dco-solve-33"
  (run* (q) (d/dco-solve `(d/dco (alt (seq foo bar) (seq foo (rep baz))) foo ,q)))
  '((alt bar (rep baz))))






(test "d/dco-deriv-14-c"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (seq foo (rep bar)) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((rep bar)
     (((d/dco (seq foo (rep bar)) foo (rep bar))
       <--
       Seq
       (((d/dco foo foo #t) <-- C ())))))))

(test "d/dco-deriv-14-e"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco foo foo ,v) tree)
      (== `(,v ,tree) q)))
  '((#t (((d/dco foo foo #t) <-- C ())))))

(test "d/dco-deriv-14-f"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (rep bar) foo ,v) tree)
      (== `(,v ,tree) q)))
  '())

(test "d/dco-deriv-20-c"
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (alt #t (seq foo (rep bar))) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((rep bar)
     (((d/dco (alt #t (seq foo (rep bar))) foo (rep bar))
       <--
       Alt
       (((d/dco (seq foo (rep bar)) foo (rep bar))
         <--
         Seq
         (((d/dco foo foo #t) <-- C ())))))))))

(test "d/dco-deriv-20-cc"
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (alt (seq foo (rep bar)) #t) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((rep bar)
     (((d/dco (alt (seq foo (rep bar)) #t) foo (rep bar))
       <--
       Alt
       (((d/dco (seq foo (rep bar)) foo (rep bar))
         <--
         Seq
         (((d/dco foo foo #t) <-- C ())))))))))

(test "d/dco-deriv-20-c1"
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco #t foo ,v) tree)
      (== `(,v ,tree) q)))
  '())

(test "d/dco-deriv-20-c2"
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (seq foo (rep bar)) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((rep bar)
     (((d/dco (seq foo (rep bar)) foo (rep bar))
       <--
       Seq
       (((d/dco foo foo #t) <-- C ())))))))

(test "d/dco-deriv-20-d"
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (alt (seq foo (rep bar)) #t) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((rep bar)
     (((d/dco (alt (seq foo (rep bar)) #t) foo (rep bar))
       <--
       Alt
       (((d/dco (seq foo (rep bar)) foo (rep bar))
         <--
         Seq
         (((d/dco foo foo #t) <-- C ())))))))))

(test "d/dco-deriv-20-e"
;;; illegal alt with duplicate patterns
  (run 1 (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (alt (seq foo (rep bar)) (seq foo (rep bar))) foo ,v) tree)
      (== `(,v ,tree) q)))
  '())

(test "d/dco-deriv-31"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco baz f ,v) tree)
      (== `(,v ,tree) q)))
  '())

(test "d/dco-deriv-32"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (seq foo barn) foo ,v) tree)
      (== `(,v ,tree) q)))
  '((barn
     (((d/dco (seq foo barn) foo barn)
       <--
       Seq
       (((d/dco foo foo #t) <-- C ())))))))

(test "d/dco-deriv-33"
  (run* (q)
    (fresh (v tree)
      (d/dco-deriv `(d/dco (alt (seq foo bar) (seq foo (rep baz))) foo ,v) tree)
      (== `(,v ,tree) q)))
  '(((alt bar (rep baz))
     (((d/dco
        (alt (seq foo bar) (seq foo (rep baz)))
        foo
        (alt bar (rep baz)))
       <--
       Alt
       (((d/dco (seq foo bar) foo bar)
         <--
         Seq
         (((d/dco foo foo #t) <-- C ())))
        ((d/dco (seq foo (rep baz)) foo (rep baz))
         <--
         Seq
         (((d/dco foo foo #t) <-- C ())))))))))
