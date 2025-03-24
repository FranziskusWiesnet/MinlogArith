;; 2025-02-17.  examplesarithprime_nat.scm.  Based on Franziskus Wiesnet's
;; div_nat.scm and gcd_nat.scm

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (load "~/temp/libnat2502.scm")
;; (load "~/temp/examplesarithgcd_nat.scm")
;; (set! COMMENT-FLAG #t)

;; Prime numbers
;; =============

(add-program-constant "NatComposed" (py "nat=>boole"))
(add-computation-rules
 "NatComposed n" "ExBNat n([m]1<m andb NatDiv m n)")

(set-totality-goal "NatComposed")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; (cp)
(save-totality)

(add-program-constant "NatPrime" (py "nat=>boole"))
(add-computation-rules
 "NatPrime n" "negb(NatComposed n) andb 1<n")

(set-totality-goal "NatPrime")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; (cp)
(save-totality)

;; NatPrimeProd
(set-goal "all n,l0,l1(NatPrime n -> l0*l1=n -> l0=1 orb l1=1)")
(assume "n")
(cases)
(strip)
(use "EfAtom")
(simphyp 1 (pf "n=0"))
(use 3)
(use "NatEqSym")
(use 2)
(cases)
(search)
(assume "l0")
(cases)
(strip)
(ng 2)
(simphyp 1 (pf "n=0"))
(use "EfAtom")
(use 3)
(use "NatEqSym")
(use 2)
(cases)
(search)
(assume "l1")
(strip)
(ng 1)
(assert "ExBNat n([n0]1<n0 andb[if (n*n0=n) True (ExBNat n([n1]n1*n0=n))])")
(use "ExBNatIntro" (pt "Succ(Succ l1)"))
(simp "<-" 2)
(simp "NatTimesComm")
(use "NatLtPosToLtTimes")
(use "Truth")
(use "Truth")
(ng #t)
(cases (pt "n*l1+n+n=n"))
(assume 3)
(use "Truth")
(assume 4)
(use "ExBNatIntro" (pt "Succ(Succ l0)"))
(simp "<-" 2)
(use "NatLtPosToLtTimes")
(use "Truth")
(use "Truth")
(use 2)
(assume 3)
(simphyp 1 3)
(use "EfAtom")
(use 4)
;; (cp)
(save "NatPrimeProd")

;; NatProdToPrime
(set-goal "all n(1<n -> all l0,l1(l0*l1=n -> l0=1 orb l1=1) -> NatPrime n)")
(assume "n" 1 2)
(ng #t)
(split)
(assert
 "ExBNat n([n0]1<n0 andb[if (n*n0=n) True (ExBNat n([n1]n1*n0=n))]) -> F")
(assume 3)
(use
 "ExBNatElim"
 (pt "([n0]1<n0 andb [if (n*n0=n) True (ExBNat n([n1]n1*n0=n))])") (pt "n"))
(use 3)
(assume "m" 4 5)
(ng 5)
(cases (pt "n*m=n"))
(assume 6)
(inst-with "NatLtPosToLtTimes" (pt "m") (pt "n") "?" "?")
(simphyp 7 6)
(use 8)
(use 5)
(use "NatLtTrans" (pt "1"))
(use "Truth")
(use 1)
(assume 6)
(simphyp 5 6)
(use "ExBNatElim" (pt "[n0]n0*m=n") (pt "n"))
(use 7)
(cases)
(assume 8 9)
(ng 9)
(simphyp 8 9)
(use 10)
(assume "l" 8 9)
(inst-with 2 (pt "Succ l") (pt "m") 9)
(ng 10)
(cases (pt "l=0"))
(assume 11)
(simphyp 9 11)
(ng 12)
(simphyp 4 12)
(use 13)
(assume 11)
(cases (pt "m=1"))
(assume 12)
(use 6)
(simp 12)
(use "Truth")
(assume 13)
(simphyp 10 12)
(simphyp 13 11)
(use 14)
(assume 3)
(simp 3)
(use "Truth")
(use 1)
;; (cp)
(save "NatProdToPrime")

;; NatLeastFactor
(add-program-constant "NatLeastFactor" (py "nat=>nat"))
(add-computation-rules
 "NatLeastFactor n" "NatLeast n([m]1<m andb ExBNat(Succ n)([l]l*m=n))")

(set-totality-goal "NatLeastFactor")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; (cp)
(save-totality)

;;NatLeastFactorProp
(set-goal "all n(
 1<n -> 1<NatLeastFactor n andb ExBNat (Succ n)([l]l*(NatLeastFactor n)=n))")
(assume "n" 1)
(use-with "PropNatLeast" (pt "n") (pt "n")
	  (pt "[m]1<m andb ExBNat(Succ n)([l]l*m=n)") "?" "?")
(use "Truth")
(ng)
(split)
(use 1)
(cases (pt "n*n=n"))
(search)
(assume 2)
(use "ExBNatIntro" (pt "1"))
(use 1)
(use "Truth")
;; (cp)
(save "NatLeastFactorProp")

;; LeastFactorProp0
(set-goal "all n(1<n -> 1<NatLeastFactor n)")
(strip)
(use "NatLeastFactorProp")
(use 1)
;; (cp)
(save "NatLeastFactorProp0")

;; LeastFactorProp1
(set-goal "all n(1<n -> ExBNat(Succ n)([l]l*(NatLeastFactor n)=n))")
(assume "n" 1)
(use "NatLeastFactorProp")
(use 1)
;; (cp)
(save "NatLeastFactorProp1")

;; NatLeastFactorToLe
(set-goal "all n(
 1<n -> all m(1<m -> ExBNat(Succ n)([l]l*m=n) -> NatLeastFactor n <= m))")
(strip)
(use "NatLeastLeIntro")
(ng)
(split)
(use 2)
(use 3)
;; (cp)
(save "NatLeastFactorToLe")

;; NatLeastFactorBound
(set-goal "all n(1<n -> NatLeastFactor n<=n)")
(assume "n" 1)
(use "NatLeastFactorToLe")
(use 1)
(use 1)
(use "ExBNatIntro" (pt "1"))
(use "NatLtTrans" (pt "n"))
(use 1)
(use "Truth")
(use "Truth")
;; (cp)
(save "NatLeastFactorBound")

;; NatLeastFactorPrime
(set-goal "all n(1<n -> NatPrime(NatLeastFactor n))")
(assume "n" 1)
(simp "NatPrime0CompRule")
(simp "NatComposed0CompRule")
(assert "ExBNat(NatLeastFactor n)
          ([m]1<m andb NatDiv m(NatLeastFactor n)) -> F")
(assume 2)
(use "ExBNatElim"
     (pt "[m]1<m andb NatDiv m(NatLeastFactor n)") (pt "NatLeastFactor n"))
(use 2)
(assume "m" 1 2)
(assert "1<m andb NatDiv m(NatLeastFactor n)")
(use 4)
(assume 5)
(inst-with "NatLeastFactorToLe" (pt "n") 1 (pt "m") "?" "?")
(assert "m<m")
(use "NatLtLeTrans" (pt "NatLeastFactor n"))
(use 3)
(use 6)
(search)
(use 5)
(simphyp 5 "NatDiv0CompRule")
(use "ExBNatElim"
     (pt "[l]l*m=NatLeastFactor n") (pt "Succ(NatLeastFactor n)"))
(use 6)
(assume "l" 7 8)
(use "ExBNatElim" (pt "[l]l*NatLeastFactor n=n") (pt "Succ n"))
(use "NatLeastFactorProp1")
(use 1)
(assume "l0" 9 10)
(use "ExBNatIntro" (pt "l0*l"))
(use "NatLeToLtSucc")
(simp (pf "n=l0*NatLeastFactor n"))
(use "NatLeMonTimes")
(use "Truth")
(use "NatLtSuccToLe")
(use 7)
(use "NatEqSym")
(use 10)
(ng #t)
(simp "<-" "NatTimesAssoc")
(simp (pf "l*m= NatLeastFactor n"))
(use 10)
(use 8)
(assume 2)
(simp 2)
(split)
(use "Truth")
(use "NatLeastFactorProp0")
(use 1)
;; (cp)
(save "NatLeastFactorPrime")

;; NatLeastFac
(set-goal "all n exl m m=NatLeastFactor n")
(assume "n")
(intro 0 (pt "NatLeastFactor n"))
(use "Truth")
;; (cp)
(save "NatLeastFac")

(animate "NatLeastFac")

;; NatLeastFacExFree
(set-goal "all n cNatLeastFac n=NatLeastFactor n")
(assume "n")
(use "Truth")
;; (cp)
(save "NatLeastFacExFree")

(deanimate "NatLeastFac")

;; NatDivPrime
(set-goal "all n,m(NatPrime n -> NatDiv m n -> m=1 oru m=n)")
(strip)
(inst-with "NatDivToProd" (pt "m") (pt "n") 2)
(by-assume 3 "l" 4)
(inst-with "NatPrimeProd" (pt "n") (pt "l") (pt "m") 1 4)
(cases (pt "l=1"))
(assume 6)
(simphyp 4 6)
(intro 1)
(use 7)
(assume 6)
(cases (pt "m=1"))
(assume 7)
(intro 0)
(use "Truth")
(assume 7)
(simphyp 5 6)
(simphyp 8 7)
(intro 0)
(use 9)
;; (cp)
(save "NatDivPrime")

;; NatDivPrimeToEq
(set-goal "all n,m(NatPrime n -> NatPrime m -> NatDiv n m -> n=m)")
(assume "n" "m" 1 2 3)
(inst-with "NatDivPrime" (pt "m") (pt "n") 2 3)
(elim 4)
(assume 5)
(simphyp 1 "NatPrime0CompRule")
(simphyp 6 5)
(use "EfAtom")
(use 7)
(search)
;; (cp)
(save "NatDivPrimeToEq")

;; NatGcdPrime
(set-goal "all n, m(NatPrime n -> NatGcd n m=1 oru NatGcd n m=n)")
(assume "n" "m" 1)
(use "NatDivPrime")
(use 1)
(use "NatGcdDiv0")
;; (cp)
(save "NatGcdPrime")


;; Lists of prime numbers
;;=======================

(add-program-constant "NatPrimes" (py "(nat=>nat)=>nat=>boole"))
(add-computation-rules
 "NatPrimes ns Zero" "True"
 "NatPrimes ns(Succ n)" "NatPrime(ns n) andb NatPrimes ns n")

(set-totality-goal "NatPrimes")
(fold-alltotal)
(assume "ns")
(fold-alltotal)
(ind)
(use "TotalBooleTrue")
(strip)
(use "AndConstTotal")
(use "TotalVar")
(use 1)
;; (cp)
(save-totality)

;; NatPrimesCompat
(set-goal "all ns,ms,m(
 all n(n<m -> ns n=ms n) -> NatPrimes ns m=NatPrimes ms m)")
(assume "ns" "ms")
(ind)
(search)
(assume "m" 1 2)
(simp "NatPrimes1CompRule")
(simp "NatPrimes1CompRule")
(simp 2)
(simp 1)
(use "Truth")
(assume "n" 4)
(use 2)
(use "NatLtTrans" (pt "m"))
(use 3)
(use "Truth")
(use "Truth")
;; (cp)
(save "NatPrimesCompat")

;; NatPrimesToPrime
(set-goal "all m,n,ns(NatPrimes ns m -> n<m -> NatPrime(ns n))")
(ind)
(assume "n" "ns" 1 2)
(use "EfAtom")
(use 2)
(assume "m" 1 "n" "ns" 2 3)
(simphyp 2 "NatPrimes1CompRule")
(cases (pt "n=m"))
(assume 1)
(simp 5)
(use 4)
(assume 5)
(use 1)
(use 4)
(use "NatLtSuccNotEqToLt")
(use 3)
(use 5)
;;(cp)
(save "NatPrimesToPrime")

;;NatPrimesToProdNotZero
(set-goal "all ns,m(NatPrimes ns m -> 0<NatProd 0 m ns)")
(assume "ns")
(ind)
(search)
(assume "n" 1 2)
(ng 2)
(use "NatPosTimes")
(use 1)
(use 2)
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(use 2)
;; (cp)
(save "NatPrimesToProdNotZero")

;; New number of a list
;;=====================

(add-ids (list (list "NatNewNumber"
		     (make-arity (py "nat") (py "nat=>nat") (py "nat")) ))
	 '("NatNewNumber m ns Zero" "NatNewNumberInit")
	 '("all m, n, ns(NatNewNumber m ns n -> (ns n=m -> F) ->
                         NatNewNumber m ns(Succ n))" "NatNewNumberCons"))
					
;; EfNewNumber
(set-goal "all m,ns,n(F -> NatNewNumber m ns n)")
(assume "m" "ns" "n")
(assume 1)
(simp (pf "n=Zero"))
(intro 0)
(use "EfAtom")
(use 1)
;; (cp)
(save "EfNatNewNumber")

;; NatNewNumberConsRev
(set-goal "all n,ns,m(
 NatNewNumber m ns(Succ n) -> NatNewNumber m ns n andnc (ns n=m -> F))")
(assert "all n,ns,m(
  NatNewNumber m ns n -> all n0(Succ n0=n ->
  NatNewNumber m ns n0 andnc (ns n0=m -> F)))")
(assume "n" "ns" "m")
(elim)
(assume "n1" 1)
(split)
(use "EfNatNewNumber")
(use 2)
(assume 3)
(use 2)
(assume "m0" "n0" "ns0" 2 3 4 "n1" 5)
(simp 5)
(split)
(use 2)
(use 4)
(assume 1)
(strip)
(use 1 (pt "Succ n"))
(use 2)
(use "Truth")
;; (cp)
(save "NatNewNumberConsRev")

;; NatNewNumberDecidable
(set-goal "all n,m,ns(NatNewNumber m ns n ori (NatNewNumber m ns n -> F))")
(ind)
(assume "m" "ns")
(intro 0)
(intro 0)
(assume "n" 1 "m" "ns")
(inst-with 1 (pt "m") (pt "ns"))
(elim 2)
(assume 3)
(cases (pt "ns n=m"))
(assume 4)
(intro 1)
(assume 5)
(inst-with "NatNewNumberConsRev" (pt "n") (pt "ns") (pt "m") 5)
(use 6)
(use 4)
(assume 4)
(intro 0)
(intro 1 (pt "m") (pt "ns"))
(use 3)
(use 4)
(assume 3)
(intro 1)
(assume 4)
(use 3)
(inst-with "NatNewNumberConsRev" (pt "n") (pt "ns") (pt "m") 4)
(use 5)
;; (cp)
(save "NatNewNumberDecidable")

;; NatProd
;; =======

;; NatNotDivProdToNewNumber
(set-goal "all n,ns,m(
 (NatDiv n(NatProd 0 m ns) -> F) -> NatNewNumber n ns m)")
(assume "n" "ns")
(ind)
(assume 1)
(intro 0)
(assume "m" 1 2)
(intro 1 (pt "n") (pt "ns"))
(use 1)
(assume 3)
(use 2)
(simphyp 3 "NatDiv0CompRule")
(use "ExBNatElim" (pt "[l]l*n=NatProd 0 m ns") (pt "Succ(NatProd 0 m ns)"))
(use 4)
(assume "l" 5 6)
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "(ns m)*l"))
(simp "NatProd1CompRule")
(ng #t)
(simp "NatTimesComm")
(use "NatLeToLtSucc")
(use "NatLeMonTimes")
(use "NatLtSuccToLe")
(use 5)
(use "Truth")
(ng #t)
(ng 6)
(simp 6)
(simp "<-" "NatTimesAssoc")
(simp 6)
(use "NatTimesComm")
(assume 3)
(use 2)
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "NatProd 0 m ns"))
(simp "NatProd1CompRule")
(ng #t)
(simp 3)
(use "NatLeToLtSucc")
(cases (pt "n"))
(assume 4)
(simphyp 3 4)
(simphyp 2 "NatProd1CompRule")
(ng 6)
(simphyp 6 5)
(ng 7)
(use "EfAtom")
(use 7)
(use "Truth")
(assume "n0" 4)
(use "NatLeTrans" (pt "NatProd 0 m ns * 1"))
(use "Truth")
(use "NatLeMonTimes")
(use "Truth")
(use "Truth")
(ng #t)
(simp 3)
(use "Truth")
;; (cp)
(save "NatNotDivProdToNewNumber")

;; NatNotNewNumberToDivProd
(set-goal "all n,ns,m(
 (NatNewNumber n ns m -> F) -> NatDiv n(NatProd Zero m ns))")
(strip)
(cases (pt "NatDiv n (NatProd Zero m ns)"))
(assume 2)
(use "Truth")
(assume 2)
(use 1)
(use "NatNotDivProdToNewNumber")
(assume 3)
(use 2)
(use 3)
;; (cp)
(save "NatNotNewNumberToDivProd")

;; NatDivProdPlusOneToNewNumber
(set-goal "all ns,n,m(
 1<n -> NatDiv n(NatProd Zero m ns+1)  -> NatNewNumber n ns m)")
(strip)
(use "NatNotDivProdToNewNumber")
(assume 3)
(assert "n=1")
(use "NatDivAntiSym")
(use "Truth")
(use "NatDivPlusRev" (pt "NatProd Zero m ns"))
(use 3)
(use 2)
(assume 4)
(simphyp 1 4)
(use 5)
;; (cp)
(save "NatDivProdPlusOneToNewNumber")

;; Euclid's proof of the infinitude of prime numbers

;; NatPrimesToNewPrime
(set-goal "all m,ns(
 NatPrimes ns m -> exl n(NatPrime n andnc NatNewNumber n ns m))")
(assume "m" "ns" 1)
(intro 0 (pt "NatLeastFactor(NatProd Zero m ns+1)"))
(split)
(use "NatLeastFactorPrime")
(use "NatLeLtTrans" (pt "Zero+(Succ Zero)"))
(use "Truth")
(use "NatLtMonPlus1")
(use "NatPrimesToProdNotZero")
(use 1)
(use "Truth")
(use "NatDivProdPlusOneToNewNumber")
(use "NatLeastFactorProp0")
(use "NatPrimesToProdNotZero")
(use 1)
(simp "NatDiv0CompRule")
(use "NatLeastFactorProp1")
(use "NatLeLtTrans" (pt "0+1"))
(use "Truth")
(use "NatLtMonPlus1")
(use "NatPrimesToProdNotZero")
(use 1)
(use "Truth")
;; (cp)
(save "NatPrimesToNewPrime")

;; NatPrimeToIrred (Euclid's lemma)
(set-goal "all l,n,m(
 NatPrime l -> NatDiv l(n*m) -> NatDiv l n oru NatDiv l m)")
(assume "l" "n" "m" 1 2)
(inst-with "NatGcdPrime" (pt "l") (pt "n") 1)
(elim 3)
(assume 4)
(inst-with "NatGcdToLinComp" (pt "l") (pt "n"))
(by-assume 5 "l0" 6)
(by-assume 6 "l1" 7)
(inst-with "NatDivToProd" (pt "l") (pt "n*m") 2)
(by-assume 8 "l2" 9)
(simphyp 7 4)
(elim 10)
(assume 11)
(intro 1)
(use "NatDivPlusRev" (pt "m*l0*l"))
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "m*l0"))
(use "NatLeToLtSucc")
(simp (pf "m*l0*l=l*(m*l0)"))
(use "NatLeTimesPos")
(simphyp 1 "NatPrime0CompRule")
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(use 12)
(use "Truth")
(use "NatTimesComm")
(use "Truth")
(simp (pf "m*l0*l+m= m*((Succ Zero)+l0*l)"))
(simp 11)
(simp "NatTimesComm")
(simp "<-" "NatTimesAssoc")
(simp "<-" 9)
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "l1*l2"))
(use "NatLeToLtSucc")
(use "NatLeMonTimes")
(use "Truth")
(use "NatLeTrans" (pt "l2*1"))
(use "Truth")
(use "NatLeMonTimes")
(use "Truth")
(simphyp 1 "NatPrime0CompRule")
(use "NatLtToLe")
(use 12)
(use "Truth")
(simp (pf "(Succ Zero)+l0*l=l0*l+(Succ Zero)"))
(use "Truth")
(use "NatPlusComm")
(assume 11)
(intro 1)
(use "NatDivPlusRev" (pt "l0*l2*l"))
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "l0*l2"))
(use "NatLeToLtSucc")
(simp (pf "l0*l2*l=l*(l0*l2)"))
(use "NatLeTimesPos")
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(simphyp 1 "NatPrime0CompRule")
(use 12)
(use "Truth")
(use "NatTimesComm")
(use "Truth")
(simp "<-" "NatTimesAssoc")
(simp 9)
(simp (pf "l0*(n*m)+m=(l0*n +(Succ Zero))*m"))
(simp (pf "l0*n+(Succ Zero)=(Succ Zero)+l0*n"))
(simp 11)
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "l1*m"))
(use "NatLeToLtSucc")
(simp (pf "l1*l=l*l1"))
(simp "<-" "NatTimesAssoc")
(use "NatLeTimesPos")
(simphyp 1 "NatPrime0CompRule")
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(use 12)
(use "Truth")
(use "NatTimesComm")
(ng #t)
(simp "<-" "NatTimesAssoc")
(simp (pf "m*l=l*m"))
(use "Truth")
(use "NatTimesComm")
(use "NatPlusComm")
(use "Truth")
(assume 4)
(intro 0)
(simp "<-" 4)
(use "NatGcdDiv1")
;; (cp)
(save "NatPrimeToIrred")

;; NatPrimeToIrredRev
(set-goal "all l,m,n(
  NatPrime l -> NatDiv m(l*n) -> NatDiv l m oru NatDiv m n)")
(strip)
(inst-with "NatDivToProd" (pt "m") (pt "l*n") 2)
(by-assume 3 "m0" 4)
(inst-with "NatPrimeToIrred" (pt "l") (pt "m0") (pt "m") 1 "?")
(elim 5)
(assume 6)
(inst-with "NatDivToProd" (pt "l") (pt "m0") 6)
(by-assume 7 "n0" 8)
(intro 1)
(use "NatProdToDiv" (pt "n0"))
(use "NatTimesCancelL" (pt "l"))
(use "NatLtTrans" (pt "Succ Zero"))
(use "Truth")
(ng 1)
(use 1)
(ng #t)
(simp "<-" 4)
(simp "<-" 8)
(simp (pf "l*n0=n0*l"))
(use "Truth")
(use "NatTimesComm")
(assume 6)
(intro 0)
(use 6)
(use "NatProdToDiv" (pt "n"))
(use "NatEqSym")
(use "NatEqTrans" (pt "l*n"))
(use 4)
(use "NatTimesComm")
;; (cp)
(save "NatPrimeToIrredRev")

;; NatPrimeDivProdToDiv
(set-goal "all ns,n,m(
 NatPrime n -> NatDiv n(NatProd 0 m ns) -> exi l(l<m andi NatDiv n(ns l)))")
(assume "ns" "n")
(ind)
(assume 1 2)
(assert "n=1")
(use "NatDivAntiSym")
(simp "NatDiv0CompRule")
(use "ExBNatIntro" (pt "n"))
(use "Truth")
(use "Truth")
(use 2)
(assume 3)
(simphyp 1 3)
(intro 0 (pt "Zero"))
(split)
(use 4)
(use "EfAtom")
(use 4)
(assume "m" 1 2 3)
(ng 3)
(inst-with
 "NatPrimeToIrred" (pt "n") (pt "NatProd Zero m ns") (pt "ns m") 2 3)
(elim 4)
(assume 5)
(inst-with 1 2 5)
(by-assume 6 "l1" 7)
(intro 0 (pt "l1"))
(split)
(use "NatLtTrans" (pt "m"))
(use 7)
(use "Truth")
(use 7)
(assume 5)
(intro 0 (pt "m"))
(split)
(use "Truth")
(use 5)
;; (cp)
(save "NatPrimeDivProdToDiv")

;; NatPrimeDivProdPrimesToInPrimes
(set-goal "all ns,n,m(
     NatPrime n -> 
     NatPrimes ns m -> NatDiv n(NatProd 0 m ns) -> exl l(l<m andnc ns l=n))")
(strip)
(inst-with "NatPrimeDivProdToDiv" (pt "ns") (pt "n") (pt "m") 1 3)
(by-assume 4 "l" 5)
(intro 0 (pt "l"))
(split)
(use 5)
(use "NatDivAntiSym")
(use 5)
(inst-with "NatDivToProd" (pt "n") (pt "ns l") "?")
(by-assume 6 "l0" 7)
(inst-with "NatPrimeProd" (pt "ns l") (pt "l0") (pt "n") "?" 7)
(cases (pt "l0=1"))
(assume 9)
(simphyp 7 9)
(simp 10)
(use "NatDivRefl")
(assume 9)
(simphyp 8 9)
(cases (pt "n=1"))
(assume 11)
(ng 1)
(simphyp 1 11)
(use "EfAtom")
(use 12)
(assume "11")
(simphyp 10 11)
(use "EfAtom")
(use 12)
(use "NatPrimesToPrime" (pt "m"))
(use 2)
(use 5)
(use 5)
;; (cp)
(save "NatPrimeDivProdPrimesToInPrimes")
