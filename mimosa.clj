(ns mimosa.mimosa
  (:refer-clojure :exclude [==]) ; Explicit exclusion for core.logic
  (:require [clojure.core.logic :refer :all :exclude [is appendo]]
            [clojure.test :refer :all]))


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

(defn symbolo [v]
  (when (symbol? v) succeed))

(defn numbero [v]
  (when symbol? v) succeed)

(defn not-varo [out]
  (conde
    [(symbolo out)]
    [(numbero out)]
    [(== '() out)]
    [(fresh [h r]
       (== [h r] out)
       (!= h :variable))]))

(deftest test-not-varo
  (is (= (run* [q] (not-varo [:variable 'x]))
         '())))

(defn paramo* [x out]
    (== [:param x] out))

(deftest test-paramo*
  (is (= (run* [q] (paramo* 'x q))
         '([:param x])))
  (is (= (run* [q] (paramo* q [:param 'x]))
         '(x))))

(defn paramo [out]
  (fresh [x]
    (paramo* x out)))

(deftest test-paramo
  (is (= (run* [q] (paramo q))
         '([:param _0]))))

(defn not-paramo [out]
  (conde
    [(symbolo out)]
    [(numbero out)]
    [(== '() out)]
    [(fresh [h r]
       (== [h r] out)
       (!= h :param))]))

(deftest test-not-paramo
  (is (= (run* [q] (not-paramo [:param 'x]))
         '())))

(defn lookupo [u s out]
  (fresh [fkey fvalue rest]
    (conso [fkey fvalue] rest s)
    (conde
      [(== [u out] [fkey fvalue])]
      [(!= u fkey)
       (lookupo u rest out)])))

(deftest test-lookupo
  (is (= (run* [q] (lookupo 'x '([x 1] [x 2]) q))
         '(1)))
  (is (= (run 1 [q] (lookupo 'x q 1))
         '(([x 1] . _0)))))

(defn not-in-assoco [u s]
  (conde
    [(== '() s)]
    [(fresh [fkey fvalue rest]
       (conso [fkey fvalue] rest s)
       (!= fkey u)
       (not-in-assoco u rest))]))

(deftest test-not-in-assoco
  (is (= (run* [q] (not-in-assoco 'x '([x 1])))
         '())))

(defn lookup-failbacko [u s out]
  (conde
    [(lookupo u s out)]
    [(not-in-assoco u s)
     (== u out)]))

(defn walko [u s out]
  (conde
    [(varo u)
     (conde
       [(fresh [val]
          (lookupo u s val)
          (walko val s out))]
       [(not-in-assoco u s)
        (== out u)])]
    [(not-varo u)
     (== out u)]))

(deftest test-walko
  (is (= (run* [q] (walko '[:variable x]
                          '(([:variable x] [:variable y])
                            ([:variable y] 1))
                          q))
         '(1))))

(declare unifyo)
(defn unifyo* [u v s out]
  (fresh [uw vw]
    (walko u s uw)
    (walko v s vw)
    (conde
      [(== uw vw)
       (== s out)]
      [(!= uw vw)
       (conde
         [(varo uw)
          (conso [uw vw] s out)]
         [(not-varo uw)
          (varo vw)
          (conso [vw uw] s out)]
         [(not-varo uw)
          (not-varo vw)
          (conde
            [(conde
               [(numbero uw)] [(numbero vw)]
               [(symbolo uw)] [(symbolo vw)])
             (== out fail)]
            [(fresh [uwf uwr vwf vwr tmps]
              (== [uwf uwr] uw)
              (== [vwf vwr] vw)
              (unifyo uwf vwf s tmps)
              (unifyo uwr vwr tmps out))])])])))

(defn unifyo [u v s out]
  (conde
    [(== s fail) (== out fail)]
    [(!= s fail) (unifyo* u v s out)]))

(deftest test-unifyo
  (is (= (run* [q] (unifyo [:variable 'x] 1 '() q))
         '((([:variable x] 1)))))
  (is (= (run* [q] (unifyo [:variable 'x] [:variable 'y]
                           '([[:variable x] 1] [[:variable y] 1])
                           q))
         '(([[:variable x] 1] [[:variable y] 1]))))
  (is (= (run* [q] (unifyo [:variable 'x] [:variable 'y] '() q))
         '(([[:variable x] [:variable y]])))))

(defn zipo [a b out]
  (conde
    [(== '() a) (== '() b) (== '() out)]
    [(fresh [af ar bf br outf outr]
       (conso af ar a)
       (conso bf br b)
       (conso outf outr out)
       (== [af bf] outf)
       (zipo ar br outr))]))

(deftest test-zipo
  (is (= (run* [q] (zipo '(a b c) '(1 2 3) q))
         '(([a 1] [b 2] [c 3])))))

(defn appendo [a b out]
  (conde
    [(== '() a) (== b out)]
    [(fresh [af ar outf outr]
       (== [af ar] a)
       (== [outf outr] out)
       (== af outf)
       (appendo ar b outr))]))

(deftest test-appendo
  (is (= (run* [q] (appendo '(a b c) '(1 2 3) q))
         '((a b c 1 2 3)))))

(defn patterno [vars predicate out]
    (== [:pattern vars predicate] out))

(deftest test-patterno
  (is (= (run* [q] (patterno '([:param x]) '(== [:param x] 1) q))
         '([:pattern ([:param 'x]) (== [:param x] 1)]))))

(defn apply-atomo [value params out]
  (conde
   [(not-paramo value)
    (== value out)]
   [(paramo value)
    (lookup-failbacko value params out)]))

(defn apply-listo [value params out]
  (conde
   [(== '() value) (== '() out)]
   [(fresh [f r outf outr]
      (conso f r value)
      (apply-atomo f params outf)
      (apply-listo r params outr)
      (conso outf outr out))]))

(defn apply-valueo [value params out]
  (conde
   [(paramo value) (apply-atomo value params out)]
   [(not-paramo value) (symbolo value) (apply-atomo value params out)]
   [(not-paramo value) (numbero value) (apply-atomo value params out)]
   [(not-paramo value) (listo value) (apply-listo value params out)]))

(deftest test-apply-valueo
  (is (= (run* [q] (apply-valueo '[:param x] '(([:param x] [:variable x])) q))
         '([:variable x])))
  (is (= (run* [q] (apply-valueo 'x '() q))
         '(x))))

(defn predicateo [p pattern-assoc]
  (conde
   [(fresh [s1 s2]
      (== (list '== s1 s2) p))]
   [(fresh [verb s1 s2]
      (== (list verb s1 s2) p)
      (conde
        [(== 'disj verb)]
        [(== 'conj verb)]
        [(varo s1)]
        [(predicateo s1 pattern-assoc)]
        [(varo s2)]
        [(predicateo s2 pattern-assoc)]))]
   [(fresh [verb args pattern pv pp a-params]
      (conso verb args p)
      (!= verb '==)
      (!= verb 'conj)
      (!= verb 'disj)
      (!= verb 'fresh)
      (lookupo verb pattern-assoc pattern)
      (patterno pv pp pattern)
      (predicateo pp pattern-assoc)
      (zipo pv args a-params))]))

(deftest test-predicateo
 (is (= (run* [q] (predicateo '(== 1 1) '()))
        '(_0))))

(declare runo*)
(defn predicatifyo [s pattern-assoc parent fresh-next fresh-next-out substitution]
  (fresh [tmp predicate]
    (conde
      [(varo s)
       (unifyo predicate s tmp substitution)]
      [(not-varo s)
       (== predicate s)
       (== tmp substitution)])
    (predicateo predicate pattern-assoc)
    (runo* predicate pattern-assoc parent
           fresh-next fresh-next-out tmp)))

(defn applyo [predicate pattern-assoc params fresh-next fresh-next-out out]
  (conde
    [(fresh [builtin s1 s2 o1 o2]
       (membero builtin ['== 'disj 'conj])
       (== (list builtin s1 s2) predicate)
       (== (list builtin o1 o2) out)
       (apply-valueo s1 params o1)
       (apply-valueo s2 params o2)
       (== fresh-next fresh-next-out))]
    [(fresh [fvar fparam fpredicate new-params new-fresh-next]
       (== (list 'fresh fparam fpredicate) predicate)
       (varo* fresh-next fvar)
       (conso [fparam fvar] params new-params)
       (conso 'fresh fresh-next new-fresh-next)
       (applyo fpredicate pattern-assoc new-params new-fresh-next
               fresh-next-out out))]
    [(fresh [verb args pattern pv pp a-params combined-params]
       (== (list verb args) predicate)
       (!= '== verb)
       (!= 'disj verb)
       (!= 'conj verb)
       (!= 'fresh verb)
       (lookupo verb pattern-assoc pattern)
       (patterno pv pp pattern)
       (predicateo pp pattern-assoc)
       (zipo pv args a-params)
       (appendo a-params params combined-params)
       (applyo pp pattern-assoc combined-params fresh-next fresh-next-out out))]))

(deftest test-applyo
  (is (= (run* [q] (fresh [fresh-next-out out]
                     (applyo '(== 1 2) '() '() '(fresh) fresh-next-out out)
                     (== (list out fresh-next-out) q)))
         '(((== 1 2) (fresh)))))
  (is (= (run* [q] (fresh [fresh-next-out out]
                     (applyo '(fresh [:param x] (== [:param x] 1)) '()
                             '(([:param x] 2)) '(fresh) fresh-next-out out)
                     (== `(~out ~fresh-next-out) q)))
         '(((== (:variable (fresh)) 1) (fresh fresh))))))

(defn runo* [predicate pattern-assoc parent fresh-next fresh-next-out
                     out]
    (conde
      [(fresh [s1 s2]
         (== (list '== s1 s2) predicate)
         (unifyo s1 s2 parent out))]
      [(fresh [s1 s2 out1 out2 fresh-next-out1 fresh-next-out2]
         (== (list 'disj s1 s2) predicate)
         (predicatifyo s1 pattern-assoc parent fresh-next
                          fresh-next-out1 out1)
         (predicatifyo s2 pattern-assoc parent fresh-next
                          fresh-next-out2 out2)
         (conde
           [(== out1 fail) (== out2 fail)
                       (== out fail) (== fresh-next-out fresh-next)]
           [(!= out1 fail) (== out2 fail)
                        (== out out1) (== fresh-next-out fresh-next-out1)]
           [(== out1 fail) (!= out2 fail)
                       (== out out2) (== fresh-next-out fresh-next-out2)]
           [(!= out1 fail) (!= out2 fail)
                        (conde ((== out out1) (== fresh-next-out fresh-next-out1))
                               ((== out out2) (== fresh-next-out fresh-next-out2)))]))]
      [(fresh [s1 s2 o1 o2 fresh-next-tmp tmp]
         (== (list 'conj s1 s2) predicate)
         (predicatifyo s1 pattern-assoc parent fresh-next
                       fresh-next-tmp tmp)
         (predicatifyo s2 pattern-assoc tmp fresh-next-tmp
                       fresh-next-out out))]
      [(fresh [verb rest fresh-next-tmp applied]
         (conso verb rest predicate)
         (!= '== verb)
         (!= 'conj verb)
         (!= 'disj verb)
         (applyo predicate pattern-assoc '() fresh-next
                 fresh-next-tmp applied)
         (runo* applied pattern-assoc parent fresh-next-tmp
                fresh-next-out out))]))

(declare selecto)
(defn selecto* [queries s ss]
    (conde
      [(== '() queries) (== '() ss)]
      [(fresh [qf qr ssf ssr]
         (conso qf qr queries)
         (conso ssf ssr ss)
         (selecto qr s ssr)
         (walko qf s ssf))]))

(defn selecto [queries s ss]
    (conde
      [(== s fail) (== ss fail)]
      [(!= s fail) (selecto* queries s ss)]))

(defn runo [queries predicate pattern-assoc ss]
    (fresh [s fresh-out]
      (runo* predicate pattern-assoc '() '(fresh) fresh-out s)
      (selecto queries s ss)))

;; (display
;;   (run 1 (patterns)
;;     (runo '() '(mother a b) patterns '())
;;     (runo '() '(mother b c) patterns '())
;;     (runo '() '(mother a c) patterns fail)
;;     (runo '() '(grandmother a c) patterns '())
;;     (runo '() '(grandmother a b) patterns fail)
;;     (runo '() '(grandmother b c) patterns fail)))


