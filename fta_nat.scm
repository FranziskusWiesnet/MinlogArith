;; 2025-04-02.  fta_nat.scm.  Based on Franziskus Wiesnet's
;; div_nat.scm gcd_nat.scm prime_nat.scm and FTA_nat.scm

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (exload "arith/gcd_nat.scm")
;; (exload "arith/prime_nat.scm")
;; (set! COMMENT-FLAG #t)

;; Fundamental theorem of arithmetic
;; =================================

;; NatExPrimeFactorisation
(set-goal "all n(
 Zero<n -> exd ns exl m NatPrimes ns m andb NatProd 0 m ns=n)")
(assert "all l,n(
n<l -> Zero<n -> exi ns exi m((NatPrimes ns m) andb NatProd Zero m ns = n))")
(ind)
(assume "n" 1 2)
(intro 0 (pt "[n]Zero"))
(intro 0 (pt "Zero"))
(use "EfAtom")
(use 1)
(assume "l10" 1)
(cases)
(assume 2 3)
(intro 0 (pt "[n] Zero"))
(intro 0 (pt "Zero"))
(use "EfAtom")
(use 3)
(cases)
(assume 2 3)
(intro 0 (pt "[n]Zero"))
(intro 0 (pt "Zero"))
(use "Truth")
(assume "n" 2 3)
(use
 "ExBNatElim"
 (pt "[l]l*cNatLeastFac(Succ(Succ n))=Succ(Succ n)")
 (pt "Succ(Succ(Succ n))"))
(simp "NatLeastFacExFree")
(use "NatLeastFactorProp1")
(use "Truth")
(assume "l" 4 5)
(inst-with 1 (pt "NatLeast (Succ(Succ(Succ n)))
 ([l0]l0*cNatLeastFac(Succ(Succ n))=Succ(Succ n)) ") "?" "?")
(by-assume 6 "ns" 7)
(by-assume 7 "m" 8)
(intro 0 (pt "[n0][if (n0<m) (ns n0) (cNatLeastFac (Succ(Succ n)))]"))
(intro 0 (pt "Succ m"))
(split)
(simp "NatPrimes1CompRule")
(split)
(simp (pf "([n0][if (n0<m) (ns n0) (cNatLeastFac(Succ(Succ n)))])m=
                                    cNatLeastFac(Succ(Succ n))"))
(simp "NatLeastFacExFree")
(use "NatLeastFactorPrime")
(use "Truth")
(use "Truth")
(simp "NatPrimesCompat" (pt "ns"))
(use 8)
(assume "n0" 9)
(ng #t)
(simp 9)
(use "Truth")
(use "NatEqTrans" (pt "NatLeast(Succ(Succ(Succ n)))
 ([l]l*cNatLeastFac(Succ(Succ n))=Succ(Succ n))*cNatLeastFac(Succ(Succ n))"))
(simp "NatProd1CompRule")
(simp "NatProdCompat" (pt "ns"))
(simp (pf "NatProd 0 m ns=NatLeast(Succ(Succ(Succ n)))
            ([l]l*cNatLeastFac(Succ(Succ n))=Succ(Succ n))"))
(use "Truth")
(use 8)
(assume "l1" 7 8)
(ng #t)
(simp 10)
(use "Truth")
(use-with "PropNatLeast"
	  (pt "Succ(Succ (Succ n))")
	  (pt "l")
	  (pt "[l]l*cNatLeastFac(Succ(Succ n))=Succ(Succ n)")
	  "?"
	  "?")
(use "NatLtToLe")
(use 4)
(use 5)
(use "NatLeLtTrans" (pt "Succ n"))
(use "NatLeTrans" (pt "l"))
(use "NatLeastLeIntro")
(use 5)
(use "NatLtSuccToLe")
(simp "<-" (pf "l*cNatLeastFac(Succ(Succ n))=Succ(Succ n)"))
(use "NatLtPosToLtTimes")
(simp "NatLeastFacExFree")
(use "Truth")
(cases (pt "l"))
(assume 6)
(simphyp 5 6)
(use 7)
(assume "l1" 6)
(use "Truth")
(use 5)
(use 2)
(cases (pt "l"))
(assume 6)
(simphyp 5 6)
(use "EfAtom")
(use 7)
(search)
(assume 1 "n" 2)
(use 1 (pt "n+1"))
(use "Truth")
(use 2)
;; (cp)
(save "NatExPrimeFactorisation")

;; Permutation pairs Pms
;; =====================

;; (add-var-name "f" "g" (py "nat=>nat"))

(add-ids
 (list (list "Pms"
	     (make-arity (py "nat")
			 (py "nat=>nat") (py "nat=>nat"))))
 '("all m,ns,ms(
  all n ms(ns n)=n  ->
  all n ns(ms n)=n  ->
  all n(m<=n -> ns n=n) ->
  Pms m ns ms)" "PmsIntro"))

;; EfPms
(set-goal "all m,ns,ms(F -> Pms m ns ms)")
(assume "m" "ns" "ms" 1)
(intro 0)
(assume "n")
(use "EfAtom")
(use 1)
(assume "n")
(use "EfAtom")
(use 1)
(strip)
(use "EfAtom")
(use 1)
;; (cp)
(save "EfPms")

;; PmsCirc
(set-goal "all m,ns,ns0(Pms m ns ns0 -> all n ns0(ns n)=n)")
(assume "m" "ns" "ns0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsCirc")

;; PmsCircInv
(set-goal "all m,ns,ns0(Pms m ns ns0 -> all n ns(ns0 n)=n)")
(assume "m" "ns" "ns0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsCircInv")

;; PmsIdOut
(set-goal "all m,ns,ns0(Pms m ns ns0 -> all n(m<=n -> ns n=n))")
(assume "m" "ns" "ns0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsIdOut")

;; PmsSucc
(set-goal "all m,ns,ns0(Pms m ns ns0 -> Pms(Succ m)ns ns0)")
(assume "m" "ns" "ns0" 1)
(intro 0)
;; 3-6
(use "PmsCirc" (pt "m"))
(use 1)
;; 4
(use "PmsCircInv" (pt "m"))
(use 1)
;; 5
(assume "n" 2)
(use "PmsIdOut" (pt "m") (pt "ns0"))
(use 1)
(use "NatLeTrans" (pt "Succ m"))
(use "Truth")
(use 2)
;; Proof finished.
;; (cp)
(save "PmsSucc")

;; PmsSuccInv
(set-goal
 "all m,ns,ms(Pms(Succ m)ns ms -> ns m = m -> Pms m ns ms)")
(assume "m" "ns" "ms" 1 2)
(intro 0)
(use "PmsCirc" (pt "Succ m"))
(use 1)
(use "PmsCircInv" (pt "Succ m"))
(use 1)
(assume "n" 3)
(cases (pt "n=m"))
(assume 4)
(simp 4)
(use 2)
(assume 4)
(use "PmsIdOut" (pt "Succ m") (pt "ms"))
(use 1)
(use "NatLtToSuccLe")
(use "NatLeNotEqToLt")
(use 3)
(assume 5)
(use 4)
(use "NatEqSym")
(use 5)
;; (cp)
(save "PmsSuccInv")

;; PmsIdOutInv
(set-goal "all m,ns,ms(Pms m ns ms -> all n (m<=n -> ms n=n))")
(assume "m" "ns" "ms" 1 "n" 2)
(assert "n = ns n")
(use "NatEqSym")
(use "PmsIdOut" (pt "m") (pt "ms"))
(use 1)
(use 2)
(assume 3)
(use "NatEqTrans" (pt "ms(ns n)"))
(simp "<-" 3)
(use "Truth")
(use "PmsCirc" (pt "m"))
(use 1)
;; (cp)
(save "PmsIdOutInv")

;; PmsSym
(set-goal "all m,ns,ms(Pms m ns ms -> Pms m ms ns)")
(strip)
(intro 0)
(use "PmsCircInv" (pt "m"))
(use 1)
(use "PmsCirc" (pt "m"))
(use 1)
(use "PmsIdOutInv" (pt "ns"))
(use 1)
;; (cp)
(save "PmsSym")

;; PmsConcat
(set-goal "all m,ns,ns0,ms,ms0(
 Pms m ns ns0 -> Pms m ms ms0 -> Pms m([n]ns(ms n))([n]ms0(ns0 n)))")
(strip)
(intro 0)
(ng)
(assume "n")
(simp (pf "ns0(ns(ms n))=ms n"))
(use "PmsCirc" (pt "m"))
(use 2)
(use-with "PmsCirc" (pt "m") (pt "ns") (pt "ns0") 1 (pt "ms n"))
(ng)
(assume "n")
(simp (pf "ms(ms0(ns0 n))=ns0 n"))
(use "PmsCircInv" (pt "m"))
(use 1)
(use-with "PmsCircInv" (pt "m") (pt "ms") (pt "ms0") 2 (pt "ns0 n"))
(assume "n" 3)
(ng)
(simp (pf "ms n = n"))
(use "PmsIdOut" (pt "m") (pt "ns0"))
(use 1)
(use 3)
(use "PmsIdOut" (pt "m") (pt "ms0"))
(use 2)
(use 3)
;; (cp)
(save "PmsConcat")

(add-program-constant "Transp" (py "nat=>nat=>nat=>nat"))
(add-computation-rules
 "Transp n m l" "[if (l=n) m [if (l=m) n l]]")

(set-totality-goal "Transp")
(strip)
(use "BooleIfTotal")
(use "NatEqTotal")
(auto)
(use "BooleIfTotal")
(use "NatEqTotal")
(auto)
;; (cp)
(save-totality)

;;Pms Transp
(set-goal "n0 max n1 < m -> Pms m(Transp n0 n1)(Transp n0 n1)")
(strip)
(intro 0)
(assume "l")
(ng)
(cases (pt "l=n0"))
(assume 2)
(ng)
(cases (pt "n1=n0"))
(simp 2)
(search)
(simp 2)
(search)
(assume 2)
(ng)
(cases (pt "l=n1"))
(use "NatEqSym")
(ng)
(simp 2)
(assume 3)
(simp 3)
(search)
(assume "l")
(ng)
(cases (pt "l=n0"))
(assume "2")
(ng)
(cases (pt "n1=n0"))
(simp 2)
(search)
(simp 2)
(search)
(assume 2)
(ng)
(cases (pt "l=n1"))
(assume 3)
(simp 3)
(search)
(assume 3)
(ng)
(simp 2)
(simp 3)
(search)
(assume "n" 2)
(ng)
(assert "n=n0 -> m<m")
(assume 3)
(use "NatLeLtTrans" (pt "n"))
(use 2)
(simp 3)
(use "NatLeLtTrans" (pt "n0 max n1"))
(use "NatMaxUB1")
(use 1)
(assume 3)
(simp 3)
(assert "n=n1 -> m<m")
(assume 4)
(use "NatLeLtTrans" (pt "n"))
(use 2)
(use "NatLeLtTrans" (pt "n0 max n1"))
(simp 4)
(use "NatMaxUB2")
(use 1)
(assume 4)
(simp 4)
(use "Truth")
;; (cp)
(save "PmsTransp")

;; NatProdInvTranspAux
(set-goal "all m,n,ns(
     n<m -> NatProd Zero(Succ m) ns=
            NatProd Zero(Succ m)([l]ns(Transp n m l)))")
(ind)
;; Case 0
 (assume "n" "ns" 1)
 (use "EfAtom")
 (use 1)
;; Case Succ n
 (assume "m" 1 "n" "ns" 2)
 (ng)
 (assert "Succ m=n->F")
  (assume 3)
  (simphyp 2 3)
  (use 4)
 (assume 3)
 (simp 3)
 (ng)
 (cases (pt "m=n"))
 ;; Case m=n
  (assume 4)
  (simp 4)
  (ng)
(simp (pf "NatProd Zero n
 ([l]ns[if (l=n) (Succ n) [if (l=Succ n) n l]])=NatProd Zero n ns"))
  (simp "<-" "NatTimesAssoc")
  (simp (pf "ns n*ns(Succ n) =ns(Succ n)*ns n"))
  (use "Truth")
  (use "NatTimesComm")
  (use "NatProdCompat")
  (strip)
  (ng)
  (assert "l=n-> F")
   (assume 7)
   (simphyp 6 7)
   (use 8)
  (assume 7)
  (simp 7)
  (assert "l=Succ n -> F")
   (assume 8)
   (simphyp 6 8)
   (use 9)
  (assume 8)
  (simp 8)
  (use "Truth")
 ;; Case m=n->F
  (assume 4)
  (ng)
  (simp (pf "m=Succ m -> F"))
  (simp "<-" "NatTimesAssoc")
  (simp "<-" "NatTimesAssoc")
  (simp (pf "ns m*ns(Succ m)=ns(Succ m)*ns m"))
  (simp (pf "ns[if False n m]*ns n=ns n *ns m"))
  (ng)
  (inst-with 1 (pt "n") (pt "[l]ns([if (l=m) (Succ m) l])") "?")
  (ng)
(simphyp 5
  (pf "NatProd Zero m([n0]ns[if (n0=m) (Succ m) n0])=NatProd Zero m ns"))
  (drop 5)
  (simphyp 6 4)
  (ng)
  (simphyp 7 (pf "n=m -> F"))
  (drop 6 7)
  (ng)
  (simphyp 8 (pf "NatProd Zero m
      ([n0]
        ns
        [if ([if (n0=n) m [if (n0=m) n n0]]=m)
          (Succ m)
          [if (n0=n) m
          [if (n0=m) n n0]]])=
  NatProd Zero m([n0]ns[if (n0=n) (Succ m) [if (n0=Succ m) n n0]])"))
  (simp 9)
  (use "Truth")
  (use "NatProdCompat")
   (strip)
   (ng)
   (assert "l=m -> F")
    (assume 11)
    (simphyp 10 11)
    (use 12)
   (assume 11)
   (simp 11)
   (ng)
   (cases (pt "l=n"))
   ;; Case l=n
    (assume 12)
    (use "Truth")
    (assume 12)
    (ng)
    (simp 11)
    (ng)
    (simp (pf "l=Succ m -> F"))
    (use "Truth")
    (assume 13)
    (simphyp 10 13)
    (use 14)
   (assume 8)
   (use 4)
   (use "NatEqSym")
   (use 8)
  (use "NatProdCompat")
   (assume "l" 6 7)
   (ng)
   (simp (pf "l=m -> F"))
   (use "Truth")
   (assume 8)
   (simphyp 7 8)
   (use 9)
   (use "NatLtSuccNotEqToLt")
   (use 2)
   (assume 5)
   (use 4)
   (use "NatEqSym")
   (use 5)
   (use "NatTimesComm")
   (use "NatTimesComm")
   (assume 5)
   (assert "m<m")
   (use "NatLtLeTrans" (pt "Succ m"))
   (use "Truth")
   (simp "<-" 5)
   (use "Truth")
   (search)
;; (cp)
(save "NatProdInvTranspAux")

(add-var-name "ls" (py "nat=>nat"))

;; NatProdInvPms
(set-goal "all n,ns,ms,ls(
 Pms n ns ms -> NatProd Zero n ls=NatProd Zero n ([l]ls(ns l)))")
(ind)
;; Case 0
 (strip)
 (use "Truth")
;; Succ n
 (assume "n" 1 "ns" "ms" "ls" 2)
 (cases (pt "ns n<n"))
 ;; Case ns n<n
  (assume 3)
  (simp "NatProdInvTranspAux" (pt "ns n"))
  (simp "NatProd1CompRule")
  (simp "NatProd1CompRule")
  (simp 1 (pt "[l]Transp(ns n)n (ns l)") (pt "[l]ms(Transp(ns n)n l)"))
(simp (pf
 "NatProd Zero n([l]([l0]ls(Transp(ns n)n l0))(([l0]Transp(ns n)n(ns l0))l))=
  NatProd Zero n([l]ls(ns l))"))
  (ng #t)
  (cases (pt "n=ns n"))
   (assume 4)
   (simp "<-" 4)
   (use "Truth")
   (assume 4)
   (use "Truth")
  (use "NatProdCompat")
   (strip)
   (ng)
   (cases (pt "ns l=ns n"))
   ;; Case ns l=ns n
    (assume 6)
    (simp 6)
    (ng)
    (cases (pt "n=ns n"))
    ;; Case n=ns n
     (assume 7)
     (simp "<-" 7)
     (use "Truth")
    ;; Case n=ns n -> F
     (assume 7)
     (use "Truth")
   ;; Case ns l=ns n -> F
    (assume 6)
    (ng)
    (cases (pt "ns l=n"))
    ;; Case ns l=n
     (assume 7)
     (simp 7)
     (use "Truth")
    ;; Case ns l=n -> F
     (assume 7)
     (ng)
     (simp 6)
     (simp 7)
     (use "Truth")
  (use "PmsSuccInv")
  (use "PmsConcat")
  (use "PmsTransp")
  (use "NatLeToLtSucc")
  (use "NatMaxLUB")
  (use "NatNotLtToLe")
  (assume 4)
(inst-with
 "PmsIdOutInv" (pt "Succ n") (pt "ns") (pt "ms") 2 (pt "ns n") "?")
  (simphyp 5 "PmsCirc" (pt "Succ n"))
  (assert "ns n<ns n")
   (use "NatLeLtTrans" (pt "n"))
   (simp "<-" 6)
   (auto)
   (use "NatLtToSuccLe")
   (auto)
 ;; Case ns n<n -> F
  (assume 3)
  (simp "NatProd1CompRule")
  (simp "NatProd1CompRule")
  (assert "ns n=n")
   (use "NatLeAntiSym")
   (use "NatNotLtToLe")
   (assume "4")
   (inst-with
    "PmsIdOutInv" (pt "Succ n") (pt "ns") (pt "ms") 2 (pt "ns n") "?")
   (simphyp 5 "PmsCirc" (pt "Succ n"))
   (assert "ns n<ns n")
   (use "NatLeLtTrans" (pt "n"))
   (simp "<-" 6)
   (use "Truth")
   (use 4)
   (search)
   (use 2)
   (use "NatLtToSuccLe")
   (use 4)
   (use "NatNotLtToLe")
   (use 3)
  (assume 4)
  (ng)
  (simp 4)
  (simp 1 (pt "ns") (pt "ms"))
  (use "Truth")
  (use "PmsSuccInv")
  (use 2)
  (use 4)
;; (cp)
(save "NatProdInvPms")

;; PrimesConstInvTranspAux
(set-goal "all m,n,ns(
 n<m -> NatPrimes ns(Succ m)=NatPrimes ([l]ns(Transp n m l)) (Succ m))")
(ind)
(assume "n" "ns" 1)
(use "EfAtom")
(use 1)
(assume "m" 1 "n" "ns" 1)
(simp "NatPrimes1CompRule")
(simp "NatPrimes1CompRule")
(simp "NatPrimes1CompRule")
(simp "NatPrimes1CompRule")
(assert "Succ m=n->F")
(assume 3)
(simphyp 2 3)
(use 4)
(assume 3)
(simp 3)
(cases (pt "m=n"))
(assume 4)
(simp 4)
(ng #t)
(simp (pf "NatPrimes([n0]ns[if (n0=n) (Succ n) [if (n0=Succ n) n n0]])n=
           NatPrimes ns n"))
(cases (pt "Succ Zero<ns(Succ n)"))
(cases (pt "negb(ExBNat(ns n)
            ([n0]
              (Succ Zero)<n0 andb
              [if (ns n*n0=ns n) True (ExBNat(ns n)([n1]n1*n0=ns n))]))andb 
       (Succ Zero)<ns n"))
(strip)
(use "Truth")
(strip)
(use "Truth")
(cases (pt "negb(ExBNat(ns n)
            ([n0]
              (Succ Zero)<n0 andb
              [if (ns n*n0=ns n) True (ExBNat(ns n)([n1]n1*n0=ns n))]))andb 
       (Succ Zero)<ns n"))
(strip)
(use "Truth")
(strip)
(use "Truth")
(use "NatPrimesCompat")
(assume "l" 5)
(ng)
(assert "l=n->F")
(assume 5)
(simphyp 5 6)
(use 7)
(assume 6)
(simp 6)
(assert "l=Succ n -> F")
(assume 7)
(simphyp 5 7)
(use 8)
(assume 7)
(simp 7)
(use "Truth")
(assume 4)
(ng)
(simp (pf "m=Succ m -> F"))
(ng)
(cases (pt "negb(ExBNat(ns m)
            ([n0]
              (Succ Zero)<n0 andb
              [if (ns m*n0=ns m) True (ExBNat(ns m)([n1]n1*n0=ns m))]))andb 
       (Succ Zero)<ns m"))
(ng)
(assume 15)
(inst-with 1 (pt "n") (pt "[l]ns([if (l=m) (Succ m) l])") "?")
(ng)
(simphyp 6 4)
(drop 6)
(ng)
(simphyp 7 (pf "n=m -> F"))
(drop 7)
(ng)
(simp (pf "NatPrimes ns m=NatPrimes([n0]ns[if (n0=m) (Succ m) n0])m"))
(drop 7)
(simp 8)
(ng)
(cases (pt "negb(ExBNat(ns n)
            ([n0]
              (Succ Zero)<n0 andb
              [if (ns n*n0=ns n) True (ExBNat(ns n)([n1]n1*n0=ns n))]))andb 
       (Succ Zero)<ns n"))
(ng)
(assume 9)
(use "NatPrimesCompat")
(assume "l" 10)
(ng)
(assert "l=m -> F")
(assume 11)
(simphyp 10 11)
(use 12)
(assume 11)
(simp 11)
(simp (pf "l=Succ m -> F"))
(ng)
(cases (pt "l=n"))
(search)
(assume 12)
(ng)
(simp 11)
(use "Truth")
(assume 12)
(simphyp 10 12)
(use 13)
(search)
(use "NatPrimesCompat")
(assume "l" 9)
(ng)
(simp (pf "l=m->F"))
(use "Truth")
(assume 10)
(simphyp 9 10)
(use 11)
(assume 8)
(use 4)
(use "NatEqSym")
(use 8)
(use "NatLtSuccNotEqToLt")
(use 2)
(assume 6)
(use 4)
(use "NatEqSym")
(use 6)
(search)
(assume 5)
(assert "m<m")
(use "NatLtLeTrans" (pt "Succ m"))
(use "Truth")
(simp "<-" 5)
(use "Truth")
(search)
;; (cp)
(save "NatPrimesInvTranspAux")

;; Uniqueness of prime factorisation
;; =================================

;; (add-var-name "ls" (py "nat=>nat"))

;; NatPrimeFactorisationsToPms
(set-goal "all n,m,ns,ms(
 NatPrimes ns n -> 
 NatPrimes ms m -> 
 NatProd Zero n ns=NatProd Zero m ms -> 
 n=m andr exd ls exl ls0 (Pms n ls ls0 andnc all l(l<n -> ns(ls l)=ms l)))")
(ind)
(cases)
(strip)
(split)
(use "Truth")
(intro 0 (pt "[n]n"))
(intro 0 (pt "[n]n"))
(split)
(intro 0)
(auto)
(assume "l" 4)
(use "EfAtom")
(use 4)
(assume "m" "ns" "ms" 1 2 3)
(ng 3)
(ng 2)
(assert "Succ Zero<NatProd Zero m ms*ms m")
(use "NatLeLtTrans" (pt "NatProd Zero m ms"))
(use "NatLtToSuccLe")
(use "NatPrimesToProdNotZero")
(use 2)
(use "NatLtPosToLtTimes")
(use 2)
(use "NatPrimesToProdNotZero")
(use 2)
(assume 4)
(simphyp 4 3)
(split)
(use "EfAtom")
(use 5)
(intro 0 (pt "[n]n"))
(intro 0 (pt "[n]n"))
(split)
(use "EfPms")
(use 5)
(strip)
(use "EfAtom")
(use 5)
(assume "n" 1)
(cases)
(strip)
(ng 4)
(assert "ns n=Succ Zero")
(use "NatTimesEqualOneToOne" (pt "NatProd Zero n ns"))
(simp "NatTimesComm")
(use 4)
(assume 5)
(ng 2)
(simphyp 2 5)
(split)
(use 6)
(intro 0 (pt "[n]n"))
(intro 0 (pt "[n]n"))
(split)
(use "EfPms")
(use 6)
(strip)
(use "EfAtom")
(use 6)
(assume "m" "ns" "ms" 2 3 4)
(inst-with "NatPrimeToIrred"
 (pt "ms m") (pt "NatProd Zero n ns") (pt "ns n") "?" "?")
(elim 5)
(assume 6)
(inst-with "NatPrimeDivProdPrimesToInPrimes"
 (pt "ns") (pt "ms m") (pt "n") "?" "?" 6)
(by-assume 7 "l" 8)
(inst-with 1 (pt "m") (pt "[l0]ns(Transp l n l0)") (pt "ms") "?" "?" "?")
(elim 9)
(drop 9)
(assume 10 11)
(by-assume 11 "ls" 12)
(by-assume 12 "ls0" 13)
(split)
(use 10)
(intro 0 (pt "[l1](Transp l n (ls l1))"))
(intro 0 (pt "[l1]ls0(Transp l n l1)"))
(split)
(use-with "PmsConcat" (pt "Succ n")
   (pt "Transp l n") (pt "Transp l n")(pt "ls")(pt "ls0") "?" "?")
(use "PmsTransp")
(use "NatLeToLtSucc")
(use "NatMaxLUB")
(use "NatLtToLe")
(use 8)
(use "Truth")
(use "PmsSucc")
(use 13)
(assume "l0" 14)
(cases (pt "l0=n"))
(assume 15)
(simp 15)
(ng)
(assert "ls n =n")
(use "PmsIdOut" (pt "n") (pt "ls0"))
(use 13)
(use "Truth")
(assume "16")
(simp 16)
(assert "ls n=l -> F")
(simp 16)
(assume 17)
(simphyp 8 17)
(use 18)
(assume 17)
(simp 17)
(ng)
(simp 10)
(use 8)
(assume 15)
(use 13)
(use "NatLtSuccNotEqToLt")
(use 14)
(use 15)
(simphyp 2 "NatPrimesInvTranspAux" (pt "l"))
(simphyp 9 "NatPrimes1CompRule")
(use 10)
(use 8)
(simphyp 3 "NatPrimes1CompRule")
(use 9)
(simphyp 4 "NatProdInvTranspAux" (pt "l"))
(simphyp 9 "NatProd1CompRule")
(simphyp 10 "NatProd1CompRule")
(simphyp 11 (pf "([l0]ns(Transp l n l0))(0+n)=ns l"))
(simphyp 12 (pf "ns l=ms m"))
(use "NatTimesCancelR" (pt "ms m"))
(use "NatLtTrans" (pt "1"))
(use "Truth")
(ng 3)
(use 3)
(use 13)
(use 8)
(ng)
(cases (pt "n=l"))
(assume 12)
(simp 12)
(use "Truth")
(assume 13)
(use "Truth")
(use 8)
(ng 3)
(use 3)
(ng 2)
(use 2)
(assume 6)
(inst-with "NatDivPrimeToEq" (pt "ms m") (pt "ns n") "?" "?" 6)
(inst-with 1 (pt "m") (pt "ns") (pt "ms") "?" "?" "?")
(elim 8)
(assume 9 10)
(drop 8)
(split)
(use 9)
(by-assume 10 "ls" 11)
(by-assume 11 "ls0" 12)
(intro 0 (pt "ls"))
(intro 0 (pt "ls0"))
(split)
(use "PmsSucc")
(use 12)
(assume "l" 13)
(cases (pt "l=n"))
(assume 14)
(simp 14)
(simp (pf "ls n=n"))
(simp 9)
(simp 7)
(simp 9)
(use "Truth")
(use "PmsIdOut" (pt "n") (pt "ls0"))
(use 12)
(use "Truth")
(assume 14)
(use 12)
(use "NatLtSuccNotEqToLt")
(use 13)
(use 14)
(simphyp 2 "NatPrimes1CompRule")
(use 8)
(simphyp 3 "NatPrimes1CompRule")
(use 8)
(ng 4)
(simphyp 4 7)
(use "NatTimesCancelR" (pt "ns n"))
(use "NatLtTrans" (pt "1"))
(use "Truth")
(ng 2)
(use 2)
(use 8)
(ng 3)
(use 3)
(ng 2)
(use 2)
(ng 3)
(use 3)
(simp 4)
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "NatProd Zero m ms"))
(use "NatLeToLtSucc")
(simp (pf "NatProd Zero m ms=NatProd Zero m ms *1"))
(use "NatLeMonTimes")
(use "Truth")
(simphyp 3 "NatPrimes1CompRule")
(simphyp 5 "NatPrime0CompRule")
(use "NatLtToLe")
(use 6)
(use "Truth")
(use "Truth")
;; (cp)
(save "NatPrimeFactorisationsToPms")

;; Application
;; ===========

(add-program-constant "NatSeqConcat"
		      (py "nat=>nat=>(nat=>nat)=>(nat=>nat)=>nat=>nat"))
(add-computation-rules
 "NatSeqConcat n m ns ms l" "[if (l<n) (ns l) (ms(l--n))]")

(set-totality-goal "NatSeqConcat")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "n0")
(fold-alltotal)
(assume "ns")
(fold-alltotal)
(assume "ns0")
(fold-alltotal)
(assume "n1")
(use "TotalVar")
(save-totality)

;; NatPrimeFactorSeqConcat
(set-goal "all n,m,ns,ms(
     NatPrimes ns n -> 
     NatPrimes ms m -> NatPrimes(NatSeqConcat n m ns ms)(n+m))")
(ind)
(assume "m" "ns" "ms" 1 2)
(use 2)
(assume "n" 1)
(ind)
(assume "ns" "ms " 1 2)
(simp "NatPrimesCompat" (pt "ns"))
(use 2)
(assume "n0" 4)
(ng #t)
(simp 4)
(use "Truth")
(assume "m" 2 "ns" "ms" 3 4)
(simp (pf "Succ n+Succ m=Succ(Succ n + m)"))
(simp "NatPrimes1CompRule")
(split)
(simp "NatSeqConcat0CompRule")
(simp (pf "Succ n+m<Succ n -> F"))
(ng)
(use 4)
(search)
(use 2)
(use 3)
(ng)
(use 4)
(use "Truth")
;; (cp)
(save "NatPrimeFactorSeqConcat")

;; NatProdSeqConcat
(set-goal "all n,m,ns,ms 
     NatProd Zero n ns*NatProd Zero m ms=
     NatProd Zero(n+m)(NatSeqConcat n m ns ms)")
(assume "n")
(ind)
(strip)
(use "NatProdCompat")
(strip)
(ng #t)
(simp 2)
(use "Truth")
(assume "m" 1  "ns" "ms")
(ng #t)
(simp 1)
(use "Truth")
;; (cp)
(save "NatProdSeqConcat")

;; NatProdSeqConcatSplit0
(set-goal "all n,m,ns,ms
 NatProd Zero n ns=NatProd Zero n(NatSeqConcat n m ns ms)")
(ind)
(strip)
(use "Truth")
(assume "n" 1 "m" "ns" "ms")
(ng)
(simp (pf "NatProd Zero n ns=
           NatProd Zero n([n0][if (n0<Succ n) (ns n0) (ms(Pred(n0--n)))])"))
(use "Truth")
(use "NatProdCompat")
(strip)
(ng)
(simp (pf "l<Succ n"))
(use "Truth")
(use "NatLtTrans" (pt "n"))
(use 3)
(use "Truth")
;; (cp)
(save "NatProdSeqConcatSplit0")

;; NatProdSeqConcatSplit1
(set-goal "all m,n,ns,ms NatProd Zero m ms=
                         NatProd n m(NatSeqConcat n m ns ms)")
(ind)
(strip)
(use "Truth")
(assume "m" 1 "n" "ns" "ms")
(ng)
(simp (pf "NatProd Zero m ms=
           NatProd n m([n0][if (n0<n) (ns n0) (ms(n0--n))])"))
(use "Truth")
(use "NatEqTrans" (pt "NatProd n m ([l]ms(l--n))"))
(use "NatProdShiftZero")
(use "NatProdCompat")
(strip)
(ng)
(simp (pf "l<n -> F"))
(use "Truth")
(assume 4)
(assert "l<l")
(use "NatLtLeTrans" (pt "n"))
(use 4)
(use 2)
(search)
;; (cp)
(save "NatProdSeqConcatSplit1")

(add-program-constant "NatSeqFilter"
 (py "(nat=>nat)=>(nat=>boole)=>nat=>nat"))
(add-computation-rules
 "NatSeqFilter ns ws n" "[if (ws n) (ns n) 1]")

(set-totality-goal "NatSeqFilter")
(fold-alltotal)
(assume "ns")
(fold-alltotal)
(assume "ws")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; (cp)
(save-totality)

;; NatSeqFilterNegbTimes
(set-goal "all ns,ws,n
 NatSeqFilter ns ws n*(NatSeqFilter ns ([l](negb (ws l)))n)=ns n")
(strip)
(ng)
(cases (pt "ws n"))
(auto)
;; (cp)
(save "NatSeqFilterNegbTimes")

;; NatSeqFilterSucc
(set-goal
 "all n,m,ns,ms 
     NatSeqFilter ns([l0]ms l0<Succ n)m=
     NatSeqFilter ns([l0]ms l0<n)m*(NatSeqFilter ns([l0]ms l0=n)m)")
(strip)
(ng)
(cases (pt "ms m=n"))
(assume 1)
(simp 1)
(use "Truth")
(assume 1)
(cases (pt "ms m<n"))
(assume 2)
(simp (pf "ms m<Succ n"))
(use "Truth")
(use "NatLtTrans" (pt "n"))
(auto)
(assume 2)
(simp (pf "ms m<Succ n -> F"))
(use "Truth")
(assume 3)
(use 2)
(use "NatLeNotEqToLt")
(use "NatLtSuccToLe")
(use 3)
(use 1)
;; (cp)
(save "NatSeqFilterSucc")

;; NatProdSeqFilterSucc
(set-goal "all l,ns,n,ms,ls 
     NatProd Zero l([m]NatSeqFilter ms([l0]ls l0<Succ n)(ns m))=
     NatProd Zero l
     ([m]NatSeqFilter ms([l0]ls l0<n)(ns m)*
     NatSeqFilter ms([l0]ls l0=n)(ns m))")
(strip)
(use "NatProdCompat")
(strip)
(use "NatSeqFilterSucc")
;; (cp)
(save "NatProdSeqFilterSucc")

;; NatProdSeqFilterProp0
(set-goal "all n0,n1,ns,ns0,ms(
     Pms(n0+n1)ns ns0 -> 
     NatProd 0(n0+n1)(NatSeqFilter ms([l]ns0 l<n0))=
     NatProd 0 n0 ([l]ms (ns l)))")
(assume "n0")
(ind)
(strip)
(use "NatEqTrans" (pt "NatProd Zero(n0+Zero)ms"))
(use "NatProdCompat")
(strip)
(ng)
(simp (pf "ns0 l<n0"))
(use "Truth")
(use "NatNotLeToLt")
(assume 4)
(inst-with "PmsIdOut" (pt "n0") (pt "ns") (pt "ns0") 1 (pt "ns0 l") 4)
(simphyp 5 "PmsCircInv" (pt "n0"))
(assert "ns0 l<ns0 l")
(use "NatLeLtTrans" (pt "l"))
(simp "<-" 6)
(use "Truth")
(use "NatLtLeTrans" (pt "n0"))
(use 3)
(use 4)
(search)
(use 1)
(use "NatProdInvPms" (pt "ns0"))
(use 1)
(assume "n1" 1 "ns" "ns0" "ms" 2)
(simp (pf "n0+Succ n1=Succ(n0+n1)"))
(cases (pt "ns (n0+n1)< n0+n1"))
(assume 3)
(simp "NatProdInvTranspAux" (pt "ns (n0+n1)"))
(simp "NatProd1CompRule")
(simp (pf "([l]NatSeqFilter ms
 ([l0]ns0 l0<n0)(Transp(ns (n0+n1))(n0+n1)l))(Zero+(n0+n1))=Succ Zero"))
(inst-with 1
	   (pt "[l]Transp(ns(n0+n1))(n0+n1)(ns l)")
	   (pt "[l]ns0(Transp(ns(n0+n1))(n0+n1)l)")
	   (pt "[l]ms (Transp(ns(n0+n1))(n0+n1)l)")
	   "?")
(use "NatEqTrans" (pt "NatProd Zero(n0+n1)
    (NatSeqFilter([l]ms(Transp(ns(n0+n1))(n0+n1)l))
     ([l]([l0]ns0(Transp(ns(n0+n1))(n0+n1)l0))l<n0))"))
(use "Truth")
(simp 4)
(use "NatProdCompat")
(strip)
(ng #t)
(cases (pt "ns l=ns(n0+n1)"))
(assume 7)
(ng #t)
(simp 7)
(cases (pt "n0+n1=ns(n0+n1)"))
(assume 8)
(simp "<-" 8)
(use "Truth")
(search)
(assume 7)
(ng #t)
(cases (pt "ns l=n0+n1"))
(assume 8)
(ng #t)
(simp 8)
(use "Truth")
(assume 8)
(ng #t)
(simp 7)
(simp 8)
(use "Truth")
(use "PmsSuccInv")
(use "PmsConcat")
(use "PmsTransp")
(use "NatLeToLtSucc")
(use "NatMaxLUB")
(use "NatLtToLe")
(use 3)
(use "Truth")
(use 2)
(use "Truth")
(ng)
(simp (pf "n0+n1=ns(n0+n1)->F"))
(ng)
(simp "PmsCirc" (pt "Succ(n0+n1)"))
(use "Truth")
(use 2)
(assume 4)
(assert "ns(n0+n1)<ns(n0+n1)")
(use "NatLtLeTrans" (pt "n0+n1"))
(use 3)
(simp "<-" 4)
(use "Truth")
(search)
(use 3)
(assume 3)
(assert "ns(n0+n1)=n0+n1")
(use "NatLeAntiSym")
(use "NatNotLtToLe")
(assume 4)
(inst-with "PmsIdOutInv" (pt "n0+Succ n1") (pt "ns") (pt "ns0") 2 (pt "ns(n0+n1)") "?")
(simphyp 5 "PmsCirc" (pt "n0+Succ n1"))
(assert "n0+n1<n0+n1")
(use "NatLtLeTrans" (pt "ns(n0+n1)"))
(use 4)
(simp "<-" 6)
(use "Truth")
(search)
(use 2)
(use "NatLtToSuccLe")
(use 4)
(use "NatNotLtToLe")
(use 3)
(assume "4")
(simp "NatProd1CompRule")
(simp 1 (pt "ns"))
(ng)
(simp (pf "ns0(n0+n1)<n0 -> F"))
(use "Truth")
(simp "<-" 4)
(simp "PmsCirc" (pt "Succ(n0+n1)"))
(search)
(use 2)
(use "PmsSuccInv")
(use 2)
(use 4)
(use "Truth")
;; (cp)
(save "NatProdSeqFilterProp0")

;; NatProdSeqFilterProp1
(set-goal "all n0,n1,ns,ns0,ms(
     Pms(n0+n1)ns ns0 -> 
     NatProd Zero(n0+n1)(NatSeqFilter ms([l]negb(ns0 l<n0)))=
     NatProd n0 n1([l]ms(ns l)))")
(assume "n0")
(ind)
(strip)
(use "NatEqTrans" (pt "NatProd 0 n0([l]1)"))
(use "NatProdCompat")
(strip)
(ng)
(cases (pt "ns0 l<n0"))
(assume 4)
(use "Truth")
(assume 4)
(use "EfAtom")
(inst-with "PmsIdOut" (pt "n0") (pt "ns") (pt "ns0") 1 (pt "ns0 l") "?")
(use 4)
(simphyp 5 "PmsCircInv" (pt "n0"))
(simp "<-" 6)
(use 3)
(use 1)
(use "NatNotLtToLe")
(use 4)
(use "NatProdOne")
(assume "n1" 1 "ns" "ns0" "ms" 2)
(simp (pf "n0+Succ n1=Succ(n0+n1)"))
(cases (pt "ns (n0+n1)< n0+n1"))
(assume 3)
(simp "NatProdInvTranspAux" (pt "ns (n0+n1)"))
(simp "NatProd1CompRule")
(simp "NatProd1CompRule")
(simp (pf "([l]NatSeqFilter ms
 ([l0]negb(ns0 l0<n0))(Transp(ns (n0+n1))(n0+n1)l))(Zero+(n0+n1))=
 ([l]ms(ns l))(n0+n1)"))
(inst-with 1
	   (pt "[l]Transp(ns (n0+n1))(n0+n1)(ns l)")
	   (pt "[l]ns0(Transp(ns (n0+n1))(n0+n1)l)")
	   (pt "[l]ms (Transp(ns (n0+n1))(n0+n1)l)")
	   "?")
(use "NatEqTrans" (pt "NatProd 0(n0+n1)
    (NatSeqFilter([l]ms(Transp(ns(n0+n1))(n0+n1)l))
     ([l]negb(([l0]ns0(Transp(ns(n0+n1))(n0+n1)l0))l<n0)))*
     ([l]ms(ns l))(n0+n1)"))
(use "Truth")
(simp 4)
(simp (pf "NatProd n0 n1
       ([l]
        ([l0]ms(Transp(ns(n0+n1))(n0+n1)l0))
        (([l0]Transp(ns(n0+n1))(n0+n1)(ns l0))l))=
       NatProd n0 n1([l]ms(ns l))"))
(use "Truth")
(use "NatProdCompat")
(strip)
(ng #t)
(cases (pt "ns l=ns (n0+n1)"))
(assume 7)
(ng #t)
(simp 7)
(cases (pt "n0+n1=ns (n0+n1)"))
(assume 8)
(simp "<-" 8)
(use "Truth")
(search)
(assume 7)
(ng #t)
(cases (pt "ns l=n0+n1"))
(assume 8)
(ng #t)
(simp 8)
(use "Truth")
(assume 8)
(ng #t)
(simp 7)
(simp 8)
(use "Truth")
(use "PmsSuccInv")
(use "PmsConcat")
(use "PmsTransp")
(use "NatLeToLtSucc")
(use "NatMaxLUB")
(use "NatLtToLe")
(use 3)
(use "Truth")
(use 2)
(use "Truth")
(ng)
(simp (pf "n0+n1=ns(n0+n1)->F"))
(ng)
(simp "PmsCirc" (pt "Succ(n0+n1)"))
(use "Truth")
(use 2)
(assume 4)
(assert "ns(n0+n1)<ns(n0+n1)")
(use "NatLtLeTrans" (pt "n0+n1"))
(use 3)
(simp "<-" 4)
(use "Truth")
(search)
(use 3)
(assume 3)
(assert "ns(n0+n1)=n0+n1")
(use "NatLeAntiSym")
(use "NatNotLtToLe")
(assume 4)
(inst-with "PmsIdOutInv"
 (pt "n0+Succ n1") (pt "ns") (pt "ns0") 2 (pt "ns(n0+n1)") "?")
(simphyp 5 "PmsCirc" (pt "n0+Succ n1"))
(assert "n0+n1<n0+n1")
(use "NatLtLeTrans" (pt "ns(n0+n1)"))
(use 4)
(simp "<-" 6)
(use "Truth")
(search)
(use 2)
(use "NatLtToSuccLe")
(use 4)
(use "NatNotLtToLe")
(use 3)
(assume 4)
(simp "NatProd1CompRule")
(simp 1 (pt "ns"))
(ng)
(simp (pf "ns0(n0+n1)<n0 -> F"))
(simp 4)
(use "Truth")
(simp "<-" 4)
(simp "PmsCirc" (pt "Succ(n0+n1)"))
(search)
(use 2)
(use "PmsSuccInv")
(use 2)
(use 4)
(use "Truth")
;; (cp)
(save "NatProdSeqFilterProp1")

;; NatProdEqProdSplit
(set-goal "all m0,m1,n0,n1(
     Zero<m0 -> 
     Zero<m1 -> 
     Zero<n0 -> 
     Zero<n1 -> 
     m0*m1=n0*n1 -> 
     exd l0,l1,l2 
     exl l3(m0=l0*l1 andnc m1=l2*l3 andnc n0=l0*l2 andnc n1=l1*l3))")
(strip)
(inst-with "NatExPrimeFactorisation" (pt "m0") 1)
(inst-with "NatExPrimeFactorisation" (pt "m1") 2)
(inst-with "NatExPrimeFactorisation" (pt "n0") 3)
(inst-with "NatExPrimeFactorisation" (pt "n1") 4)
(by-assume 6 "ms0" 10)
(by-assume 7 "ms1" 11)
(by-assume 8 "ns0" 12)
(by-assume 9 "ns1" 13)
(by-assume 10 "m10" 14)
(by-assume 11 "m11" 15)
(by-assume 12 "n10" 16)
(by-assume 13 "n11" 17)
(inst-with "NatProdSeqConcat" (pt "m10") (pt "m11") (pt "ms0") (pt "ms1"))
(inst-with "NatProdSeqConcat" (pt "n10") (pt "n11") (pt "ns0") (pt "ns1"))
(simphyp 18 (pf "NatProd Zero m10 ms0=m0"))
(drop 18)
(simphyp 20 (pf "NatProd Zero m11 ms1=m1"))
(drop 20)
(simphyp 19 (pf "NatProd Zero n10 ns0=n0"))
(drop 19)
(simphyp 22 (pf "NatProd Zero n11 ns1=n1"))
(drop 21 22)
(drop 22)
(simphyp 21 5)
(simphyp 24 23)
(drop 23 24)
(inst-with "NatPrimeFactorisationsToPms"
	   (pt "m10+m11") (pt "n10+n11")
	   (pt "NatSeqConcat m10 m11 ms0 ms1")
	   (pt "NatSeqConcat n10 n11 ns0 ns1")
	   "?"
	   "?"
	   "?")
(elim 26)
(drop 26)
(assume 27)
(elim)
(assume "ns")
(elim)
(assume "ms")
(elim)
(assume 31 32)
(drop 28 29 30)
;; Now we define the required l,l0,l1,l2
(intro 0 (pt "NatProd Zero m10
 (NatSeqFilter(NatSeqConcat m10 m11 ms0 ms1)([l]ms l<n10))"))
(intro 0 (pt "NatProd Zero m10
 (NatSeqFilter(NatSeqConcat m10 m11 ms0 ms1)([l]negb(ms l<n10)))"))
(intro 0 (pt "NatProd m10 m11
 (NatSeqFilter(NatSeqConcat m10 m11 ms0 ms1)([l]ms l<n10))"))
(intro 0 (pt "NatProd m10 m11(NatSeqFilter
 (NatSeqConcat m10 m11 ms0 ms1)([l]negb(ms l<n10)))"))
(simp "NatTimesProd")
(simp "NatTimesProd")
(simp "NatProdSplitZero")
(simp "NatProdSplitZero")
;; why not for n1= conjunct as well?   Why split here?
(split)
(use "NatEqTrans" (pt "NatProd 0 m10(NatSeqConcat m10 m11 ms0 ms1)"))
(use "NatEqTrans" (pt "NatProd 0 m10 ms0"))
(use "NatEqSym")
(use 14)
(simp "NatProdSeqConcatSplit0" (pt "m11") (pt "ms1"))
(use "Truth")
(use "NatProdCompat")
(strip)
(ng #t)
(cases (pt "ms l<n10"))
(auto)
(split)
(use "NatEqTrans" (pt "NatProd m10 m11(NatSeqConcat m10 m11 ms0 ms1)"))
(use "NatEqTrans" (pt "NatProd Zero m11 ms1"))
(use "NatEqSym")
(use 15)
(simp "NatProdSeqConcatSplit1" (pt "m10") (pt "ms0"))
(use "Truth")
(use "NatProdCompat")
(strip)
(ng #t)
(cases (pt "ms l<n10"))
(auto)
;; 84
(split)
;; 96,97
(simp 27)
(simp "NatProdSeqFilterProp0" (pt "ns"))
(use "NatEqTrans" (pt "NatProd Zero n10 ns0"))
(use "NatEqSym")
(use 16)
(use "NatEqTrans" (pt "NatProd Zero n10(NatSeqConcat n10 n11 ns0 ns1)"))
(use "NatProdSeqConcatSplit0")
(use "NatProdCompat")
(strip)
(use "NatEqSym")
(use 32)
(simp 27)
(use "NatLtLeTrans" (pt "n10"))
(use 34)
(use "Truth")
(simp "<-" 27)
(use 31)

;;   27:m10+m11=n10+n11
;; ----------------------
;; ?^97:n1=
;;      NatProd 0 m10
;;      (NatSeqFilter(NatSeqConcat m10 m11 ms0 ms1)([l]negb(ms l<n10)))*
;;      NatProd m10 m11
;;      (NatSeqFilter(NatSeqConcat m10 m11 ms0 ms1)([l]negb(ms l<n10)))

(simp 27)
(simp "NatProdSeqFilterProp1" (pt "ns"))
(use "NatEqTrans" (pt "NatProd Zero n11 ns1"))
(use "NatEqSym")
(use 17)
(use "NatEqTrans" (pt "NatProd n10 n11(NatSeqConcat n10 n11 ns0 ns1)"))
(use "NatProdSeqConcatSplit1")
(use "NatProdCompat")
(strip)
(use "NatEqSym")
(use 32)
(simp 27)
(use 34)
(simp "<-" 27)
(use 31)
(use "NatPrimeFactorSeqConcat")
(use 14)
(use 15)
(use "NatPrimeFactorSeqConcat")
(use 16)
(use 17)
(use "NatEqSym")
(use 25)
(use 17)
(use 16)
(use 15)
(use 14)
;; (cp)
(save "NatProdEqProdSplit")

;; NatGcdEqOneDivProdToDiv
(set-goal "all l,n,m(
 Zero<l -> Zero<n -> Zero<m -> NatGcd l n=1 -> NatDiv l(n*m) -> NatDiv l m)")
(strip)
(inst-with "NatDivToProd" (pt "l") (pt "n*m") 5)
(by-assume 6 "l0" 7)
(inst-with "NatProdEqProdSplit"
	   (pt "l0") (pt "l") (pt "n") (pt "m") "?" 1 2 3 7)
(by-assume 8 "l1" 9)
(by-assume 9 "l2" 10)
(by-assume 10 "l3" 11)
(by-assume 11 "l4" 12)
(elim 12)
(assume 13)
(elim)
(assume 14)
(elim)
(assume 17 18)
(drop 12 14 16)
(simp 18)
(simp 15)
(simphyp 4 15)
(simphyp 19 17)
(assert "l3=1")
(use "NatDivAntiSym")
(use "Truth")
(use "NatDivTrans" (pt "NatGcd(l3*l4)(l1*l3)"))
(use "NatDivGcd")
(use "NatProdToDiv" (pt "l4"))
(use "NatTimesComm")
(use "NatProdToDiv" (pt "l1"))
(use "Truth")
(simp 20)
(use "Truth")
(assume 21)
(simp 21)
(use "NatProdToDiv" (pt "l2"))
(use "Truth")
(use "NatNotLeToLt")
(assume 8)
(simphyp 7 8)
(assert "Zero<n*m")
(use "NatLtTimesPos")
(use 2)
(use 3)
(simp "<-" 9)
(search)
;; (cp)
(save "NatGcdEqOneDivProdToDiv")

