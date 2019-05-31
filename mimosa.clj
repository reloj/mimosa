(define not-varo
  (lambda (out)
    (conde
      ((symbolo out))
      ((numbero out))
      ((== '() out))
      ((fresh (h r)
         (== `(,h . ,r) out)
         (=/= h 'variable))))))

(check-expect
  (run* (q) (not-varo '(variable x)))
(ns mimosa.mimosa
  (:refer-clojure :exclude [==]) ; Explicit exclusion for core.logic
  (:require [clojure.core.logic :refer :all]))


(defn listo [l]
  (conde
   [(== l '())]
   [(fresh [f r]
      (conso f r l))]))

(deftest test-listo
  (is (= (run* [q] (listo '()))
         '(_0)))
  (is (= (run* [q] (listo '(a b c)))
         '(_0))))

(defn varo* [x out]
  (== [:variable x] out))

(deftest test-varo*
  (is (= (run* [q] (varo* 'x q))
         '([:variable x])))
  (is (= (run* [q] (varo* q [:variable 'x]))
         '(x))))

(defn varo [out]
  (fresh [x]
    (varo* x out)))

(deftest test-varo
  (is (= (run* [q] (varo q))
         '([:variable _0]))))

  '())

(define paramo*
  (lambda (x out)
    (== `(param ,x) out)))

(check-expect
  (run* (q) (paramo* 'x q))
  '((param x)))

(check-expect
  (run* (q) (paramo* q '(param x)))
  '(x))

(define paramo
  (lambda (out)
    (fresh (x)
      (paramo* x out))))

(check-expect
  (run* (q) (paramo q))
  '((param _.0)))

(define not-paramo
  (lambda (out)
    (conde
      ((symbolo out))
      ((numbero out))
      ((== '() out))
      ((fresh (h r)
         (== `(,h . ,r) out)
         (=/= h 'param))))))

(check-expect
  (run* (q) (not-paramo '(param x)))
  '())

(define ext-so
  (lambda (x v s out)
    (== `((,x ,v) . ,s) out)))

(check-expect
  (run* (q) (ext-so 'x 1 '() q))
  '(((x 1))))

(check-expect
  (run* (q) (fresh (x y)
              (ext-so x y '() '((x 1)))
              (== `(,x ,y) q)))
  '((x 1)))

(define lookupo
  (lambda (u s out)
    (fresh (fkey fvalue rest)
      (== `((,fkey ,fvalue) . ,rest) s)
      (conde
        ((== u fkey)
         (== out fvalue))
        ((=/= u fkey)
         (lookupo u rest out))))))

(define lookup-failbacko
  (lambda (u s out)
    (conde
      ((lookupo u s out))
      ((not-in-assoco u s)
       (== u out)))))

(check-expect
  (run* (q) (lookupo 'x '((x 1) (x 2)) q))
  '(1))

(check-expect
  (run 1 (q) (lookupo 'x q 1))
  '(((x 1) . _.0)))

(define not-in-assoco
  (lambda (u s)
    (conde
      ((== '() s))
      ((fresh (fkey fvalue rest)
         (== `((,fkey ,fvalue) . ,rest) s)
         (=/= fkey u)
         (not-in-assoco u rest))))))

(check-expect
  (run* (q) (not-in-assoco 'x '((x 1))))
  '())

(define walko
  (lambda (u s out)
    (conde
      ((varo u)
       (conde
         ((fresh (val)
            (lookupo u s val)
            (walko val s out)))
         ((not-in-assoco u s)
          (== out u))))
      ((not-varo u)
       (== out u)))))

(check-expect
  (run* (q) (walko '(variable x) '(((variable x) (variable y))
                                   ((variable y) 1)) q))
  '(1))

(define unifyo*
  (lambda (u v s out)
    (fresh (uw vw)
      (walko u s uw)
      (walko v s vw)
      (conde
        ((== uw vw)
         (== s out))
        ((=/= uw vw)
         (conde
           ((varo uw)
            (ext-so uw vw s out))
           ((not-varo uw)
            (varo vw)
            (ext-so vw uw s out))
           ((not-varo uw)
            (not-varo vw)
            (conde
              ((conde
                 ((numbero uw)) ((numbero vw))
                 ((symbolo uw)) ((symbolo vw)))
               (== out #f))
              ((fresh (uwf uwr vwf vwr tmps)
                (== `(,uwf . ,uwr) uw)
                (== `(,vwf . ,vwr) vw)
                (unifyo uwf vwf s tmps)
                (unifyo uwr vwr tmps out)))))))))))

(define unifyo
  (lambda (u v s out)
    (conde
      ((== s #f) (== out #f))
      ((=/= s #f) (unifyo* u v s out)))))

(check-expect
  (run* (q) (unifyo '(variable x) 1 '() q))
  '((((variable x) 1))))

(check-expect
  (run* (q) (unifyo '(variable x) '(variable y)
                    '(((variable x) 1) ((variable y) 1))
                    q))
  '((((variable x) 1) ((variable y) 1))))

(check-expect
  (run* (q) (unifyo '(variable x) '(variable y) '() q))
  '((((variable x) (variable y)))))

(define zipo
  (lambda (a b out)
    (conde
      ((== '() a) (== '() b) (== '() out))
      ((fresh (af ar bf br outf outr)
         (== `(,af . ,ar) a)
         (== `(,bf . ,br) b)
         (== `(,outf . ,outr) out)
         (== `(,af ,bf) outf)
         (zipo ar br outr))))))

(check-expect
  (run* (q) (zipo '(a b c) '(1 2 3) q))
  '(((a 1) (b 2) (c 3))))

(define appendo
  (lambda (a b out)
    (conde
      ((== '() a) (== b out))
      ((fresh (af ar outf outr)
         (== `(,af . ,ar) a)
         (== `(,outf . ,outr) out)
         (== af outf)
         (appendo ar b outr))))))

(check-expect
  (run* (q) (appendo '(a b c) '(1 2 3) q))
  '((a b c 1 2 3)))

(define patterno
  (lambda (vars predicate out)
    (== `(pattern ,vars ,predicate) out)))

(check-expect
  (run* (q) (patterno '((param x)) '(== (param x) 1) q))
  '((pattern ((param x)) (== (param x) 1))))

(define apply-listo
  (lambda (value params out)
    (conde
     ((== '() value) (== '() out))
     ((fresh (f r outf outr)
        (== `(,f . ,r) value)
        (apply-atomo f params outf)
        (apply-listo r params outr)
        (== `(,outf . ,outr) out))))))

(define apply-atomo
  (lambda (value params out)
    (conde
     ((not-paramo value)
      (== value out))
     ((paramo value)
      (lookup-failbacko value params out)))))

(define apply-valueo
  (lambda (value params out)
    (conde
     ((paramo value) (apply-atomo value params out))
     ((not-paramo value) (symbolo value) (apply-atomo value params out))
     ((not-paramo value) (numbero value) (apply-atomo value params out))
     ((not-paramo value) (listo value) (apply-listo value params out)))))

(check-expect
  (run* (q) (apply-valueo '(param x) '(((param x) (variable x))) q))
  '((variable x)))

(check-expect
  (run* (q) (apply-valueo 'x '() q))
  '(x))

(define applyo
  (lambda (predicate pattern-assoc params fresh-next fresh-next-out out)
    (conde
      ((fresh (builtin s1 s2 o1 o2)
         (conde
          ((== 'disj builtin))
          ((== 'conj builtin))
          ((== '== builtin)))
         (== `(,builtin ,s1 ,s2) predicate)
         (== `(,builtin ,o1 ,o2) out)
         (apply-valueo s1 params o1)
         (apply-valueo s2 params o2)
         (== fresh-next fresh-next-out)))
      ((fresh (fvar fparam fpredicate new-params new-fresh-next)
         (== `(fresh ,fparam ,fpredicate) predicate)
         (varo* fresh-next fvar)
         (ext-so fparam fvar params new-params)
         (== `(fresh . ,fresh-next) new-fresh-next)
         (applyo fpredicate pattern-assoc new-params new-fresh-next
                 fresh-next-out out)))
      ((fresh (selbri args pattern pv pp a-params combined-params)
         (== `(,selbri . ,args) predicate)
         (=/= '== selbri)
         (=/= 'disj selbri)
         (=/= 'conj selbri)
         (=/= 'fresh selbri)
         (lookupo selbri pattern-assoc pattern)
         (patterno pv pp pattern)
         (predicateo pp pattern-assoc)
         (zipo pv args a-params)
         (appendo a-params params combined-params)
         (applyo pp pattern-assoc combined-params fresh-next fresh-next-out out))))))

(check-expect
  (run* (q) (fresh (fresh-next-out out)
              (applyo '(== 1 2) '() '() '(fresh) fresh-next-out out)
              (== `(,out ,fresh-next-out) q)))
  '(((== 1 2) (fresh))))

(check-expect
  (run* (q) (fresh (fresh-next-out out)
              (applyo '(fresh (param x) (== (param x) 1)) '()
                      '(((param x) 2)) '(fresh) fresh-next-out out)
              (== `(,out ,fresh-next-out) q)))
  '(((== (variable (fresh)) 1) (fresh fresh))))

(define predicateo
  (lambda (p pattern-assoc)
    (conde
     ((fresh (s1 s2)
        (== `(== ,s1 ,s2) p)))
     ((fresh (selbri s1 s2)
        (== `(,selbri ,s1 ,s2) p)
        (conde
          ((== 'disj selbri))
          ((== 'conj selbri)))
        (conde
          ((varo s1))
          ((predicateo s1 pattern-assoc)))
        (conde
          ((varo s2))
          ((predicateo s2 pattern-assoc)))))
     ((fresh (selbri args pattern pv pp a-params)
        (== `(,selbri . ,args) p)
        (=/= selbri '==)
        (=/= selbri 'conj)
        (=/= selbri 'disj)
        (=/= selbri 'fresh)
        (lookupo selbri pattern-assoc pattern)
        (patterno pv pp pattern)
        (predicateo pp pattern-assoc)
        (zipo pv args a-params))))))

(check-expect
 (run* (q) (predicateo '(== 1 1) '()))
 '(_.0))

(define predicatifyo
  (lambda (s pattern-assoc parent fresh-next fresh-next-out substitution)
    (fresh (tmp predicate)
      (conde
        ((varo s)
         (unifyo predicate s tmp substitution))
        ((not-varo s)
         (== predicate s)
         (== tmp substitution)))
      (predicateo predicate pattern-assoc)
      (runo* predicate pattern-assoc parent
             fresh-next fresh-next-out tmp))))

(define runo*
  (lambda (predicate pattern-assoc parent fresh-next fresh-next-out
                     out)
    (conde
      ((fresh (s1 s2)
         (== `(== ,s1 ,s2) predicate)
         (unifyo s1 s2 parent out)))
      ((fresh (s1 s2 out1 out2 fresh-next-out1 fresh-next-out2)
         (== `(disj ,s1 ,s2) predicate)
         (predicatifyo s1 pattern-assoc parent fresh-next
                          fresh-next-out1 out1)
         (predicatifyo s2 pattern-assoc parent fresh-next
                          fresh-next-out2 out2)
         (conde
           ((== out1 #f) (== out2 #f)
                       (== out #f) (== fresh-next-out fresh-next))
           ((=/= out1 #f) (== out2 #f)
                        (== out out1) (== fresh-next-out fresh-next-out1))
           ((== out1 #f) (=/= out2 #f)
                       (== out out2) (== fresh-next-out fresh-next-out2))
           ((=/= out1 #f) (=/= out2 #f)
                        (conde ((== out out1) (== fresh-next-out fresh-next-out1))
                               ((== out out2) (== fresh-next-out fresh-next-out2)))))))
      ((fresh (s1 s2 o1 o2 fresh-next-tmp tmp)
         (== `(conj ,s1 ,s2) predicate)
         (predicatifyo s1 pattern-assoc parent fresh-next
                       fresh-next-tmp tmp)
         (predicatifyo s2 pattern-assoc tmp fresh-next-tmp
                       fresh-next-out out)))
      ((fresh (selbri rest fresh-next-tmp applied)
         (== `(,selbri . ,rest) predicate)
         (=/= '== selbri)
         (=/= 'conj selbri)
         (=/= 'disj selbri)
         (applyo predicate pattern-assoc '() fresh-next
                 fresh-next-tmp applied)
         (runo* applied pattern-assoc parent fresh-next-tmp
                fresh-next-out out))))))

(define selecto*
  (lambda (queries s ss)
    (conde
      ((== '() queries) (== '() ss))
      ((fresh (qf qr ssf ssr)
         (== `(,qf . ,qr) queries)
         (== `(,ssf . ,ssr) ss)
         (selecto qr s ssr)
         (walko qf s ssf))))))

(define selecto
  (lambda (queries s ss)
    (conde
      ((== s #f) (== ss #f))
      ((=/= s #f) (selecto* queries s ss)))))

(define runo
  (lambda (queries predicate pattern-assoc ss)
    (fresh (s fresh-out)
      (runo* predicate pattern-assoc '() '(fresh) fresh-out s)
      (selecto queries s ss))))

;; (display
;;   (run 1 (patterns)
;;     (runo '() '(mother a b) patterns '())
;;     (runo '() '(mother b c) patterns '())
;;     (runo '() '(mother a c) patterns #f)
;;     (runo '() '(grandmother a c) patterns '())
;;     (runo '() '(grandmother a b) patterns #f)
;;     (runo '() '(grandmother b c) patterns #f)))

(test)

