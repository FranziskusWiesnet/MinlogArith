;; 2025-03-23.  examplesarithfactor_pos.scm.  Based on Franziskus Wiesnet's
;; div_nat.scm gcd_nat.scm prime_nat.scm FTA_nat.scm and Factor_nat.scm

;; Revised by Franziskus Wiesnet 

;; (load "/home/fwiesnet/Minlog/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "libnat2503.scm")
;; (exload "arith/FTA/examplesarithgcd_nat.scm")
;; (exload "arith/FTA/examplesarithprime_nat.scm")
;; (exload "arith/FTA/examplesarithfta_nat.scm")
;; (libload "libpos.scm")
;; (exload "arith/FTA/examplesarithgcd_pos.scm")
;; (exload "arith/FTA/examplesarithprime_pos.scm")
;; (exload "arith/FTA/examplesarithfta_pos.scm")
;; (set! COMMENT-FLAG #t)

;; PosSqrtSOneBound
(set-goal "all p (2<p->PosSqrt(SOne p)<p)")
(assume "p" 1)
(cases (pt "p=3"))
(assume 2)
(simp 2)
(use "Truth")
(assume 2)
(use "PosNotLeToLt")
(assume 3)
(inst-with "PosLeMonSquare" (pt "p") (pt "PosSqrt(SOne p)") 3)
(assert "3*p<3*p")
(use "PosLtLeTrans" (pt "p*p"))
(use "PosLtLeMonTimes")
(cases (pt "p"))
(assume 5)
(simphyp 1 5)
(use 6)
(cases)
(assume 5)
(simphyp 1 5)
(auto)
(cases)
(auto)
(use "PosLeTrans" (pt "PosSquare(PosSqrt(SOne p))"))
(use 4)
(use "PosLeTrans" (pt "SOne p"))
(use "PosSquareSqrtUpBound")
(ng #t)
(use "PosLeTrans" (pt "SZero p +1"))
(use "Truth")
(use "PosLeMonPlus")
(auto)
;; (cp)
(save "PosSqrtSOneBound")

;; PosOddProdToDiffSq
(set-goal "all p,q0,q1(
     SOne p=q0*q1 -> 
     1<q0 ->
     1<q1 ->
     (q0=q1 -> F)->
     exnc p0,p1(
      p0<p1 andnc 
      p1<p andnc SOne p=p1*p1--p0*p0))")
;;We first add the assumption q0<q1 and do the general proof later.
(assert "all p,q0,q1(
     SOne p=q0*q1 -> 
     1<q0 ->
     1<q1 ->
     q0<q1 ->
     exnc p0,p1(
      p0<p1 andnc 
      p1<p andnc SOne p=p1*p1--p0*p0))")
(assume "p")
(cases)
;;Case q0 = 1
 (strip)
 (intro 0 (pt "1"))
 (intro 0 (pt "1"))
 (split)
 (use 2)
 (split)
 (use "EfAtom")
 (use 2)
 (use 2)
;;Case q0 = SZero...
 (strip)
 (intro 0 (pt "1"))
 (intro 0 (pt "1"))
 (ng 1)
 (split)
 (use 1)
 (split)
 (use "EfAtom")
 (use 1)
 (use 1)
;;Case q0 = SOne...
 (assume "q0")
 (cases)
 ;;Case q1 = 1
  (strip)
  (intro 0 (pt "1"))
  (intro 0 (pt "1"))
  (split)
  (use 3)
  (split)
  (use "EfAtom")
  (use 3)
  (use 3)
 ;;Case q1 = SZero...
  (strip)
  (intro 0 (pt "1"))
  (intro 0 (pt "1"))
  (ng 1)
  (split)
  (use 1)
  (split)
  (use "EfAtom")
  (use 1)
  (use 1)
 ;;Case q1 = SOne...
  (assume "q1")
  (strip)
  (ng 2 3 4)
  (drop 2 3)
  (intro 0 (pt "PosHalf(SOne q1--SOne q0)"))
  (intro 0 (pt "PosHalf(SOne q1+SOne q0)"))
  ;; Proof of the first part of the conjuction:
  (split)
   (ng #t)
   (use "PosLeLtTrans" (pt "q1+q0"))
   (use "PosLeTrans" (pt "q1"))
   (use "Truth")
   (use "Truth")
   (use "Truth")
  ;; Proof of the secound part of the conjuction:
  (split)
   (ng #t)
   (ng 1)
   (simp 1)
   (simp (pf "PosS(q1+q0)=1+q1+q0"))
   (simp "SZeroPosPlus")
   (use "PosLeLtTrans" (pt "q0*q1+q1+q0"))
   (use "PosLeMonPlus")
   (use "PosLeMonPlus")
   (use "Truth")
   (use "Truth")
   (use "Truth")
   (use "Truth")
   (use "Truth")
  ;; Proof of the last part of the conjuction:
   (ng #t)
   (simp "PosThirdBinom")
   (simp (pf "PosS(q1+q0)+(q1--q0)=SOne q1"))
   (simp (pf "PosS(q1+q0)--(q1--q0)=SOne q0"))
   (simp "PosTimesComm")
   (use 1)
   (simp "PosMinusMinus")
   (simp "PosPlusComm")
   (simp (pf "q0+PosS(q1+q0)=SOne q0 +q1"))
   (use "Truth")
   (ng #t)
   (simp "PosPlusComm")
   (use "PosEqTrans" (pt "PosS(q0+q0)+q1"))
   (use "Truth")
   (simp "<-" "SZeroPosPlus")
   (use "Truth")
   (use "PosLtTrans" (pt "PosS(q1+q0)"))
   (use "PosLeLtTrans" (pt "q1+q0"))
   (use "Truth")
   (use "Truth")
   (use "Truth")
   (use 4)
   (simp "PosPlusComm")
   (simp (pf "PosS(q1+q0)=q0+q1+1"))
   (ng #t)
   (simp "PosMinusPlusEq")
   (simp "<-" "SZeroPosPlus")
   (use "Truth")
   (use 4)
   (simp "PosPlusComm")
   (use "Truth")
   (use "PosLeLtTrans" (pt "q1"))
   (use "Truth")
   (use "PosLtTrans" (pt "q1+q0"))
   (use "Truth")
   (use "Truth")
;; General Proof
(strip)
(cases (pt "q0<q1"))
(assume 5)
(use 1 (pt "q0") (pt "q1"))
(auto)
(assume 5)
(assert "q1<q0")
(use "PosLeNotEqToLt")
(use "PosNotLtToLe")
(use 6)
(assume 7)
(use 5)
(use "PosEqSym")
(use 7)
(assume 7)
(use 1 (pt "q1") (pt "q0"))
(simp "PosTimesComm")
(auto)
;; (cp)
(save "PosOddProdToDiffSq")

(add-program-constant "PosSquareNumber" (py "pos=>boole"))
(add-computation-rules
 "PosSquareNumber p" "([q]q*q = p)(PosSqrt p)")

(set-totality-goal "PosSquareNumber")
(fold-alltotal)
(assume "p")
(ng)
(use "TotalVar")
(save-totality)

;; PosSquareNumberSquare
(set-goal "all p PosSquareNumber(PosSquare p)")
(assume "p")
(simp "PosSquareNumber0CompRule")
(bpe-ng)
(simp "PosSqrtSquareId")
(use "Truth")
;; (cp)
(save "PosSquareNumberSquare")

;; NatLtMinusZero
(set-goal "all n,m (n<m)=(Zero<m--n)")
(ind)
;; 2,3
(assume "m")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(use "Truth")
(assume "m")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtMinusZero")

;; PosPrimeOrComposedFermat
(set-goal "all p(
     1<p -> 
     PosPrime p orr exd q0 exl q1(1<q0 andnc 1<q1 andnc p=q0*q1))")
(cases)
;; Case 1 
 (assume 1)
 (intro 0)
 (use "EfAtom")
 (use 1)
;;Case SZero p
 (cases)
 (assume 1)
 (intro 0)
 (use "Truth")
 (assume "p" 1)
 (intro 1)
 (intro 0 (pt "2"))
 (intro 0 (pt "SZero p"))
 (split)
 (use "Truth")
 (split)
 (use "Truth")
 (use "Truth")
 (assume "p" 1)
 (intro 1)
 (intro 0 (pt "2"))
 (intro 0 (pt "SOne p"))
 (split)
 (use "Truth")
 (split)
 (use "Truth")
 (use "Truth")
 (assume "p" 1)
;;Case SOne p
 (cases (pt "PosSquareNumber (SOne p)"))
  ;;Case "PosSquareNumber (SOne p)"
  (assume 2)
  (intro 1)
  (intro 0 (pt "PosSqrt (SOne p)"))
  (intro 0 (pt "PosSqrt (SOne p)"))
  (assert "1<PosSqrt(SOne p)")
  (use "PosNotLeToLt")
  (assume 1)
  (inst-with "PosEqSqrtToOne" (pt "SOne p") "?")
  (use 4)
  (simphyp 2 "PosSquareNumber0CompRule")
  (bpe-ng)
  (simp "<-" 4)
  (use "PosLeTrans" (pt "PosSqrt(SOne p)*PosSqrt(SOne p)"))
  (simp 4)
  (use "Truth")
  (simp (pf "PosSqrt(SOne p)=1"))
  (use "Truth")
  (use 3)
  (assume 3)
  (split)
  (use 3)
  (split)
  (use 3)
  (use "PosEqSym")
  (use 2)
 ;; C;; Case "PosSquareNumber (SOne p) -> F"
  (assume 2)
  (cases (pt "p<=2"))
  ;; Case p<=2
   (assume 3)
   (cases (pt "p"))
   (assume 4)
   (intro 0)
   (use "Truth")
   (cases)
   (assume 4)
   (intro 0)
   (use "Truth")
   (assume "q" 4)
   (simphyp 3 4)
   (intro 0)
   (use "EfAtom")
   (use 5)
   (assume "q" 4)
   (simphyp 3 4)
   (intro 0)
   (use "EfAtom")
   (use 5)
   (assume "q" 4)
   (intro 0)
   (use "EfAtom")
   (simphyp 3 4)
   (use 5)
  ;; Case 2<p
   (assume 3)
   (assert
    "exi l(l=NatLeastUp(PosToNat (cPosSqr (SOne p) +1)) 
          (PosToNat p)
          ([l]PosSquareNumber ((cNatPos l)*(cNatPos l)--(SOne p))))")
   (intro 0 (pt "NatLeastUp(PosToNat(cPosSqr (SOne p) +1)) 
                (PosToNat p)
                ([l]PosSquareNumber ((cNatPos l)*(cNatPos l)--(SOne p)))"))
   (use "Truth")
   (assume 4)
   (by-assume 4 "l" 5)
   (cases (pt "l=PosToNat p"))
   ;; Case l=PosToNat p
    (assume 6)
    (intro 0)
    (use "PosProdToPrime")
    (use 1)
    (assume "q0" "q1" 7)
    (assert "1<q0->1<q1 -> F")
    (assume 8 9)
    (inst-with "PosEqSym" (pt "q0*q1") (pt "SOne p") 7)
    (inst-with "PosOddProdToDiffSq" (pt "p") (pt "q0") (pt "q1") 10 8 9 "?")
    (by-assume 11 "p0" 12)
    (by-assume 12 "p1" 13)
    (inst-with "NatLeastUpLeIntro"
    	       (pt "PosToNat (cPosSqr (SOne p) +1)")
	       (pt "PosToNat p")
	       (pt "PosToNat p1")
	       (pt "[l0]PosSquareNumber(cNatPos l0*cNatPos l0--SOne p)")
	       "?"
	       "?")
    (assert "p1<p1")
    (use "PosLtLeTrans" (pt "p"))
    (use 13)
    (simp "<-" "PosToNatLe")
    (simp "<-" 6)
    (simp 5)
    (use 14)
    (assume 15)
    (use 15)
    (simp "PosToNatPlus")
    (simp (pf "NatPlus(PosToNat(cPosSqr(SOne p)))
                      (PosToNat 1)=Succ(PosToNat(cPosSqr(SOne p)))"))
    (use "NatLtToSuccLe")
    (simp "PosToNatLt")
    (simp (pf "SOne p=p1*p1--p0*p0"))
    (use "PosLtLeTrans" (pt "cPosSqr(PosSquare p1)"))
    (use "PosNotLeToLt")
    (assume 11)
    (inst-with "PosLeMonSquare"
	       (pt "cPosSqr(PosSquare p1)")
	       (pt "cPosSqr(p1*p1--p0*p0)")
	       14)
    (simphyp 15 "PosSqrExFree")
    (simphyp 16 "PosSqrExFree")
    (simphyp 17 "PosSqrtSquareId")
    (assert "p1*p1<=p1*p1--p0*p0")
    (use "PosLeTrans" (pt "PosSquare(PosSqrt(p1*p1--p0*p0))"))
    (use 18)
    (use "PosSquareSqrtUpBound")
    (assume 19)
    (assert "p1*p1<p1*p1")
    (use "PosLeLtTrans" (pt "p1*p1--p0*p0"))
    (use 19)
    (simp "<-" "PosToNatLt")
    (simp "PosToNatMinus")
    (simp "PosToNatTimes")
    (use "NatLtPlusMinus1")
    (simp "<-""PosToNatTimes")
    (simp "PosToNatLe")
    (use "PosLeMonSquare")
    (use "PosLtToLe")
    (use 13)
    (simp "<-" "PosToNatTimes")
    (simp "<-" "PosToNatPlus")
    (simp "PosToNatLt")
    (use "Truth")
    (use "PosLtMonTimes")
    (use 13)
    (use 13)
    (assume 20)
    (use 20)
    (simp "PosSqrExFree")
    (simp "PosSqrtSquareId")
    (use "Truth")
    (use 13)
    (use "Truth")
    (bpe-ng)
    (simp "NatPosExFree")
    (simp (pf "SOne p=p1*p1--p0*p0"))
    (simp "NatToPosToNatId")
    (simp (pf "p1*p1--(p1*p1--p0*p0)=p0*p0"))
    (use "PosSquareNumberSquare")
    (simp "PosMinusMinus")
    (use "Truth")
    (use "Truth")
    (use "PosLtMonSquare")
    (use 13)
    (use 13)
    (assume 10)
    (use 2)
    (simp "<-" 7)
    (simp 11)
    (use "PosSquareNumberSquare")
    (assume 8)
    (cases (pt "q0"))
    (assume 9)
    (use "Truth")
    (assume "q10" 1)
    (simphyp 8 9)
    (ng 10 #t)
    (cases (pt "q1"))
    (assume 10)
    (use "Truth")
    (assume "q11" 11)
    (use "EfAtom")
    (use 10)
    (use "Truth")
    (simp 11)
    (use "Truth")
    (assume "q11" 11)
    (use 10)
    (use "Truth")
    (simp 11)
    (use "Truth")
    (assume "p10" 9)
    (simphyp 8 9)
    (ng #t 10)
    (cases (pt "q1"))
    (assume 11)
    (use "Truth")
    (assume "q11" 11)
    (use 10)
    (use "Truth")
    (simp 11)
    (use "Truth")
    (assume "q11" 11)
    (use 10)
    (use "Truth")
    (simp 11)
    (use "Truth")
   ;; Case l=PosToNat p -> F
    (assume 6)
    ;;In this case SOne p is a composed number.
    (intro 1)
;; l will be used later as part of the prime factors.
;; Hence, we need a few properties about l.
     (assert "cPosSqr(SOne p)+1<=l")
     (simp 5)
     (use "NatLeastUpLBound")
     (simp "PosToNatPlus")
     (simp (pf "NatPlus(PosToNat(cPosSqr(SOne p)))
                       (PosToNat 1)=Succ(PosToNat(cPosSqr(SOne p)))"))
     (use "NatLtToSuccLe")
     (simp "PosToNatLt")
     (simp "PosSqrExFree")
     (use "PosSqrtSOneBound")
     (use "PosNotLeToLt")
     (use 3)
     (use "Truth")
     (assume 7)
    ;; Zero<l
     (assert "Zero<l")
     (use "NatLtLeTrans" (pt "PosToNat(cPosSqr(SOne p)+1)"))
     (use "NatLtZeroPos")
     (use 7)
     (assume 8)
    ;; PosSquareNumber(cNatPos l*cNatPos l--SOne p)
     (assert "PosSquareNumber(cNatPos l*cNatPos l--SOne p)")
     (simp 5)
     (use-with "NatLeastUpLtElim"
	        (pt "PosToNat (cPosSqr (SOne p) + 1)")
	        (pt "PosToNat p")
	        (pt "[l0]PosSquareNumber(cNatPos l0*cNatPos l0--SOne p)")
	        "?"
	        "?")
     (simp "<-" 5)
     (use 7)
     (use "NatLeNotEqToLt")
     (use "NatLeastUpBound")
     (simp "<-" 5)
     (use 6)
     (assume 9)
    ;; SOne < l*l
     (assert "SOne p < l*l")
     (use "NatLtLeTrans"
           (pt "PosToNat(cPosSqr(SOne p)+1)*PosToNat(cPosSqr(SOne p)+1)"))
     (simp "<-" "PosToNatTimes")
     (simp "PosToNatLt")
     (simp "<-" "PosSquare0CompRule")
     (use "PosSquareSqrtLowBound")
     (simp "PosSqrExFree")
     (use "Truth")
     (use "NatLeMonTimes")
     (use 7)
     (use 7)
     (assume 10)
    ;;Abreviation q
     (assert "exl q q=cPosSqr(cNatPos l*cNatPos l--SOne p)")
     (intro 0 (pt "cPosSqr(cNatPos l*cNatPos l--SOne p)"))
     (use "Truth")
     (assume 10)
     (by-assume 11 "q" 12)
    ;;q<l
     (assert "q<l")
     (simp 12)
     (simp "<-" "NatToPosLt")
     (simp "NatToPosToNatId")
     (use "PosLtMonSquareInv")
     (simphyp 9 "PosSquareNumber0CompRule")
     (bpe-ng)
     (simp "PosSquare0CompRule")
     (simp "PosSqrExFree")
     (simp 13)
     (simp "PosSquare0CompRule")
     (simp "<-" "NatToPosTimes")
     (simp "<-" "PosToNatLt")
     (simp (pf "SOne p=NatToPos(PosToNat(SOne p))"))
     (simp "NatPosExFree")
     (simp "<-" "NatToPosTimes")
     (simp "<-" "NatToPosMinus")
     (simp "PosToNatLt")
     (simp "NatToPosLt")
     (use "NatLtLeTrans" (pt "l*l--Zero"))
     (use "NatLtMonMinusRight")
     (use "Truth")
     (use "NatLtToLe")
     (use 10)
     (use "Truth")
     (use "NatLtTimesPos")
     (use 8)
     (use 8)
     (simp "<-" "NatLtMinusZero")

     (use 10)
     (use 10)
     (use "Truth")
     (use 8)
     (use 8)
     (use "PosEqSym")
     (use "NatToPosToNatId")
     (use 8)
     (use 8)
     (use 8)
     (use "NatLtZeroPos")
     (assume 13)
    ;;Main Proof
    (intro 0 (pt "cNatPos l +q"))
    (intro 0 (pt "cNatPos l --q"))
;; All three parts of the conjunction follow by the last one.
;; Hence, we proof it first.
     (assert "SOne p =(cNatPos l +q)*(cNatPos l --q)")
     (simp "<-" "PosThirdBinom")
     (simphyp 9 "PosSquareNumber0CompRule")
     (bpe-ng)
     (simp 12)
     (simp "PosSqrExFree")
     (simp 14)
     (simp "PosMinusMinus")
     (simp "PosPlusComm")
     (use "Truth")
     (use "Truth")
     (simp "NatPosExFree")
     (simp "<-" "NatToPosTimes")
     (simp "<-" "PosToNatLt")
     (simp "PosToNatToPosId")
     (use 10)
     (use "NatLtTimesPos")
     (use 8)
     (use 8)
     (use 8)
     (use 8)
     (simp "<-" "PosToNatLt")
     (simp "NatPosExFree")
     (simp "PosToNatToPosId")
     (use 13)
     (use 8)
     (assume 14)
    ;; Proof of the first part of the conjunction:
    (split)
    (use "PosLeLtTrans" (pt "cNatPos l"))
    (use "Truth")
    (use "Truth")
    ;; Proof of the secound part of the conjucntion
    (split)
    (cases (pt "l--q=1"))
    ;; Case l--q=1 (leeds to F)
     (assume 15)
     ;; Transformation to Pos
     (assert "cNatPos l--q=1")
      (use "PosToNatInj")
      (simp (pf "q=NatToPos(PosToNat q)"))
      (simp "NatPosExFree")
      (simp "<-" "NatToPosMinus")
      (simp "PosToNatToPosId")
      (use 15)
      (simp 15)
      (use "Truth")
      (use 13)
      (use "NatLtZeroPos")
      (use "PosEqSym")
      (use "NatToPosToNatId")
      (assume 16)
     ;; Proof of Falsum
     (assert "PosToNat q<PosToNat q")
      (use "NatLtLeTrans" (pt "l"))
      (use 13)
      (simp 5)
      (simphyp 14 16)
      (simp (pf "p=q")) 
      (use "NatLeastUpBound")
      (assert "SOne p=SOne q")
       (simp 17)
       (simp (pf "l=q+1"))
       (simp "PosToNatPlus")
       (simp "NatPosExFree")
       (simp "NatToPosPlus")
       (simp "NatToPosToNatId")
       (simp "NatToPosToNatId")
       (ng #t)
       (simp "<-" "SZeroPosPlus")
       (use "Truth")
       (use "Truth")
       (use "NatLtZeroPos")
       (simp "<-" 16)
       (simp "PosPlusComm")
       (simp "PosMinusPlusEq")
       (use "NatEqSym")
       (simp "NatPosExFree")
       (use "PosToNatToPosId")
       (use 8)
       (simp "<-" "PosToNatLt")
       (simp "NatPosExFree")
       (simp "PosToNatToPosId")
       (use 13)
       (use 8)
       (assume 18)
      (use 18)
     (assume 17)
     (use "EfAtom")
     (use 17)
    ;; Case l--q=PosToNat 1 -> F)
     (assume 1)
     (use "PosNotLeToLt")
     (assume 16)
     (use 15)
     (simp "<-" "PosToNatToPosId")
     (simp "NatToPosMinus")
     (simp "NatToPosToNatId")
     (simp (pf "NatToPos l--q=1"))
     (use "Truth")
     (simp "<-" "NatPosExFree")
     (use 16)
     (use 13)
     (use "NatLtZeroPos")
     (simp "<-" "NatLtMinusZero")
     (use 13)
    ;;The last part of the conjuction is already proven:
    (use 14)
;; (cp)
(save "PosPrimeOrComposedFermat")

(define eterm (proof-to-extracted-term))

;; (animate "PosSqr")
;; (animate "NatPos")

 (terms-to-haskell-program
   "/home/fwiesnet/Minlog/minlog/factor_pos.hs"
   (list (list eterm "fermat")))

;;(ppc (bpe-nt (rename-variables eterm)))

;; [p]
;;  [case p
;;    (1 -> DummyL)
;;    (SZero p0 -> 
;;    [case p0
;;      (1 -> DummyL)
;;      (SZero p1 -> Inr(2 pair SZero p1))
;;      (SOne p1 -> Inr(2 pair SOne p1))])
;;    (SOne p0 -> 
;;    [case (PosSquareNumber(SOne p0))
;;      (True -> Inr(PosSqrt(SOne p0)pair PosSqrt(SOne p0)))
;;      (False -> 
;;      [case (p0<=2)
;;        (True -> 
;;        [case p0
;;          (1 -> DummyL)
;;          (SZero p1 -> 
;;          [case p1 (1 -> DummyL) (SZero q -> DummyL) (SOne q -> DummyL)])
;;          (SOne q -> DummyL)])
;;        (False -> 
;;        [case (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;                ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0))=
;;                PosToNat p0)
;;          (True -> DummyL)
;;          (False -> 
;;          Inr(cNatPos
;;              (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;               ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))+
;;              cPosSqr
;;              (cNatPos
;;               (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;                ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))*
;;               cNatPos
;;               (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;                ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))--
;;               SOne p0)pair 
;;              cNatPos
;;              (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;               ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))--
;;              cPosSqr
;;              (cNatPos
;;               (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;                ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))*
;;               cNatPos
;;               (NatLeastUp(PosToNat(cPosSqr(SOne p0)+1))(PosToNat p0)
;;                ([l]PosSquareNumber(cNatPos l*cNatPos l--SOne p0)))--
;;               SOne p0)))])])])]

