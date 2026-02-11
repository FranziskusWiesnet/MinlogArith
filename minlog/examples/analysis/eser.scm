;; 2025-04-02.scm.  eser.scm.  The goal is an explicit proof of the
;; functional equation for the exponential function and positivity of
;; exponential function.  The idea is to employ different pair codings
;; to deal with double sums in the Cauchy product: root coding and
;; quadratic Gauss coding, as studied in lib/natpair.scm

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
(remove-var-name "k" "i" "j" "ml" "ij")
;; natpair.scm uses k,i,j as nat variables and ml, ij as pair variable
(libload "natpair.scm")
(libload "rsum.scm")
(libload "rseq.scm")
;; (set! COMMENT-FLAG #t)

;; Theorems in 1. Exponential series
;; (pp "RESeq")
;; (pp "RESeqExFree")
;; (pp "REModOne")
;; (pp "REModOneExFree")
;; (pp "REModTwo")
;; (pp "REModTwoExFree")
;; (pp "REMod")
;; (pp "REModExFree")
;; (pp "RealEModTwoProp")
;; (pp "RealEModOneProp")
;; (pp "RealEModProp")

;; (pp "RealEAbsConvAux")
;; (pp "MonConst")
;; (pp "RealConvLimConstRat")
;; (pp "RealEAbsConv")
;; (pp "RealEAbsConvCor")
;; (pp "RealLimESeqMod")
;; (pp "RealEReal")
;; (pp "RE")
;; (pp "REExFree")
;; (pp "cREReal")

;; Theorems in 2. Cauchy product
;; (pp "RealConvLimIncrToCauchy")
;; (pp "RealLeSumZeroAbs")
;; (pp "RealConvLimPStarToCauchy")

;; (pp "LeIdMaxToLeSquareC")
;; (pp "IntTimesChoosePosF")
;; (pp "RealTimesChoosePosF")
;; (pp "RatChoosePosF")
;; (pp "RealCauchyProdLimE")

;; Theorems in 3. Estimate of the rest
;; (pp "RealBinomPosF")
;; (pp "NatFPlusLB")
;; (pp "RealTimesExpDivPosFAux")
;; (pp "RealEEstRest")

;; Theorems in 4. Functional equation
;; (pp "RealSumPmsPair")
;; (pp "RealSumPmsPairCor")
;; (pp "RealSumPmsGq")
;; (pp "RealSumPmsGqCor")
;; (pp "RealSumSplitGs")
;; (pp "RealSumSplitGsCor")
;; (pp "RealSumDiagBinomAux")
;; (pp "RealSumDiagBinom")

;; (pp "RealEAbsConvCor1")
;; (pp "RealEConv")
;; (pp "RealEConvLim")
;; (pp "RealEModMon")
;; (pp "RealCauchyProdLimECor")
;; (pp "PmOdEqStep")
;; (pp "PmOdZero")
;; (pp "PmOdEqZero")
;; (pp "PmOdEqId")
;; (pp "PmOdInvEqZero")
;; (pp "PmOdInvEqStep")
;; (pp "PmOdAtZero")
;; (pp "PmOdBd")
;; (pp "PmOdId1")
;; (pp "PmOdInvBd")
;; (pp "PmOdId2")

;; (pp "IndTwo")
;; (pp "IndTwoCr")
;; (pp "RtToGsBd")
;; (pp "RtToGsId")
;; (pp "RtToGsUp")
;; (pp "RtToGsDn")
;; (pp "RtToGsMd")
;; (pp "GsToRtBd")
;; (pp "GsToRtId")
;; (pp "GsToRtUp")
;; (pp "GsToRtDn")
;; (pp "GsToRtMd")
;; (pp "GsToRtToGsId")
;; (pp "RtToGsToRtId")

;; (pp "RealSumSplitGsCor1")
;; (pp "RealSumEqDiagZero")
;; (pp "RealSumEqDiagSucc")
;; (pp "RealSumEqDiag")
;; (pp "RealSumEqDiagCor")
;; (pp "RealEFunEq")
;; (pp "RealECompat")
;; (pp "RealEFunEqZero")
;; (pp "RealELeZero")
;; (pp "RealEPos")
;; (pp "RealEInvEqMinus")
;; (pp "RealEToExpNat")
;; (pp "RealEToExpNeg")

;; 1.  Exponential series
;; ======================

(add-program-constant "RealESeq" (py "rea=>nat=>rea"))
(add-computation-rules "RealESeq x m" "cRSum Zero(Succ m)([n](1#PosF n)*x**n)")

(set-totality-goal "RealESeq")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; RESeq
(set-goal "all x exl xs xs eqd RealESeq x")
(assume "x")
(intro 0 (pt "RealESeq x"))
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "RESeq")

(animate "RESeq")

;; RESeqExFree
(set-goal "all x cRESeq x eqd RealESeq x")
(assume "x")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "RESeqExFree")

(deanimate "RESeq")

(set-totality-goal "cRESeq")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use the deanimated cRESeq x instead of RealESeq x

(add-program-constant "RealEModOne" (py "rea=>nat"))
(add-computation-rules
 "RealEModOne x" "PosToNat(2**Succ(cRBound x))")

(set-totality-goal "RealEModOne")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; REModOne
(set-goal "all x exl l l eqd RealEModOne x")
(assume "x")
(intro 0 (pt "RealEModOne x"))
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REModOne")

(animate "REModOne")

;; REModOneExFree
(set-goal "all x cREModOne x eqd RealEModOne x")
(assume "x")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REModOneExFree")

(deanimate "REModOne")

(set-totality-goal "cREModOne")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use cREModOne instead of RealEModOne

(add-program-constant "RealEModTwo" (py "rea=>pos"))
(add-computation-rules
 "RealEModTwo x"
 "cNatPos(cRBound((1#PosF(cREModOne x))*abs x**cREModOne x))")

(set-totality-goal "RealEModTwo")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; REModTwo
(set-goal "all x exl q q eqd RealEModTwo x")
(assume "x")
(intro 0 (pt "RealEModTwo x"))
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REModTwo")

(animate "REModTwo")

;; REModTwoExFree
(set-goal "all x cREModTwo x eqd RealEModTwo x")
(assume "x")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REModTwoExFree")

(deanimate "REModTwo")

(set-totality-goal "cREModTwo")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use cREModTwo instead of RealEModTwo

(add-program-constant "RealEMod" (py "rea=>pos=>nat"))
(add-computation-rules
 "RealEMod x p"
 "PosS(cREModTwo x+p)+cREModOne x")

(set-totality-goal "RealEMod")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; REMod
(set-goal "all x,p exl n n=RealEMod x p")
(assume "x" "p")
(intro 0 (pt "RealEMod x p"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "REMod")

(animate "REMod")
(animate "REModOne")
(animate "REModTwo")

;; REModExFree
(set-goal "all x cREMod x eqd RealEMod x")
(assume "x")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REModExFree")

(deanimate "REModTwo")
(deanimate "REModOne")
(deanimate "REMod")

(set-totality-goal "cREMod")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use cREMod instead of RealEMod

;; 2023-06-03
;; RealEModTwoProp
(set-goal "all x,l,q(Real x -> l=cREModOne x -> q=RealEModTwo x ->
 (1#PosF l)*abs x**l<<=2**q)")
(assume "x" "l" "q" "Rx" "lDef" "qDef")
(simp "qDef")
(ng #t)
;; ?^4:(1#PosF l)*abs x**l<<=
;;     2**cNatPos(cRBound((1#PosF(cREModOne x))*abs x**cREModOne x))
(simp "<-" "lDef")
(use "RealLeTrans" (pt "abs((1#PosF l)*abs x**l)"))
;; 6,7
(use "RealLeIdAbs")
(autoreal)
(simp "NatPosExFree")
(simp "PosToNatToPosId")
(use "RealBoundProp1")
(autoreal)
;; Zero<cRBound((1#PosF l)*abs x**l)
(simp "RBoundExFree")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealEModTwoProp")

;; RealEModOneProp
(set-goal "all x(Real x -> 2*abs x<<=Succ(RealEModOne x))")
(assume "x" "Rx")
(use "RealLeTrans" (pt "RealConstr([n]RealEModOne x)([p]Zero)"))
;; 3,4
;; ?^3:2*abs x<<=RealEModOne x
(use "RealLeTrans" (pt "RealTimes 2(2**cRBound x)"))
;; 5,6
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
;; ?^8:abs x<<=2**cRBound x
(use "RealBoundProp1")
(use "Rx")
;; ?^6:RealTimes 2(2**cRBound x)<<=RealEModOne x
(simp "RealEModOne0CompRule")
(use "RatLeToRealLe")
(simp "NatDoubleSZero")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "NatToPosToNatId")
(use "Truth")
;; ?^15:Zero<SZero(2**cRBound x)
(use "NatLtZeroPos")
;; 4
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEModOneProp")

;; RealEModProp
(set-goal "all x,p cREMod x p=PosToNat(PosS(cREModTwo x +p))+cREModOne x")
(assume "x" "p")
(simp "REModExFree")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEModProp")

;; 2023-10-13.

;; We prove that the exponential series is absolutely convergent, with
;; an explicitly given modulus.

;; RealEAbsConvAux (was Lemma5 or Q4) directly proved, with Q1-Q3
;; inlined via assert.  RealEAbsConv is essentially the same: the
;; only difference is the short conclusion (RealSerConv xs M) .

;; This will be the new RealEAbsConv
;; (set-goal "all x,l,q,xs,M(
;;  Real x -> 
;;  2*abs x<<=Succ l -> 
;;  xs l<<=2**q -> 
;;  all n xs n===(1#PosF n)*abs x**n -> 
;;  all p M p=PosS(q+p)+l -> RealSerConv xs M)")

;; RealEAbsConvAux
(set-goal "all x,xs,l,q,p,n,m(
 Real x -> 
 all n0 xs n0===(1#PosF n0)*abs x**n0 -> 
 2*abs x<<=Succ l -> 
 xs l<<=2**q -> PosS(q+p)+l<=n -> RealSum n m xs<<=(1#2)**p)")

;; We prove that the members of the exponential series for |x| are
;; non-negative, as Lemma1 (was Q13)

(assert "all x,n(Real x -> 0<<=(1#PosF n)*abs x**n)")
(assume "x" "n" "Rx")
(use "RealLeTrans" (pt "RealTimes 0 0"))
;; 5,6
(use "RatLeToRealLe")
(use "Truth")
;; 6
(use "RealLeMonTimesTwo")
;; 8-10
(use "RatLeToRealLe")
(use "Truth")
;; 0
(use "RatLeToRealLe")
(use "Truth")
;; 10
(use "RatLeToRealLe")
(use "Truth")
;; ?^11:0<<=abs x**l
(simpreal "<-" "RealAbsExp")
;; 15,16
(use "RealLeZeroAbs")
(autoreal)
;; Assertion proved.
(assume "Lemma1")

;; We prove that the members of the exponential series for |x|
;; decrease by 1/2, as Lemma2 (was Q12)

(assert "all x,n(
 Real x -> 
 abs x<<=RealTimes(1#2)(cNatPos(Succ n)) -> 
 (1#PosF(Succ n))*abs x**Succ n<<=(1#2)*((1#PosF n)*abs x**n))")
(assume "x" "n" "Rx" "nBd")
(simp "RealExp1CompRule")
(simpreal (pf "abs x**n*abs x===abs x*abs x**n"))
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(use "RealLeMonTimes")
(simpreal "<-" "RealAbsExp")
(use "RealLeZeroAbs")
(autoreal)
;; ?^34:(1#PosF(Succ n))*abs x<<=RealTimes(1#2)(1#PosF n)
(use "RealLeTrans" (pt "(1#PosF(Succ n))*RealTimes(1#2)(cNatPos(Succ n))"))
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "nBd")
;; ?^39:(1#PosF(Succ n))*RealTimes(1#2)(cNatPos(Succ n))<<=
;; RealTimes(1#2)(1#PosF n)
(simpreal "RealTimesComm")
(simpreal "<-" "RealTimesAssoc")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
;; ?^51:RealTimes(cNatPos(Succ n))(1#PosF(Succ n))<<=(1#PosF n)
(use "RatLeToRealLe")
(ng #t)
(simp "PosTimesComm")
(simp "NatPosExFree") ;added 2025-10-06
(use "Truth")
;; 49
(autoreal)
;; 24
(use "RealTimesComm")
(autoreal)
;; Assertion proved.
(assume "Lemma2")

;; We prove Lemma3 by induction from Lemma1 and Lemma2.  (Lemma3 was Q2)

(assert "all x,l(
 Real x -> 
 2*abs x<<=Succ l -> 
 all n (1#PosF(l+n))*abs x**(l+n)<<=(1#2)**n*((1#PosF l)*abs x**l))")
(assume "x" "l" "Rx" "lBd")
(ind)
;; 62,64
(ng #t)
;; 65
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
;; 64
(assume "n" "IH")
(simp "NatPlus1CompRule")
(use "RealLeTrans" (pt "(1#2)*((1#PosF(l+n))*abs x**(l+n))"))
;; 71,72
(use "Lemma2")
(use "Rx")
(use "RealLeTimesCancelL" (pt "RealConstr([n](2#1))([p]Zero)") (pt "1"))
;; 75-77
(autoreal)
;; 78
(ng #t)
(use "Truth")
;; ?^79:2*abs x<<=2*RealTimes(1#2)(cNatPos(Succ(l+n)))
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealLeTrans" (pt "RealConstr([n]Succ l)([p]Zero)"))
;; 86,87
(use "lBd")
;; ?^87:Succ l<<=cNatPos(Succ(l+n))
(use "RatLeToRealLe")
(simp "NatPosExFree")
(simp "<-" "PosToNatToIntId")
(simp "PosToNatToPosId")
(simp "RatLe0CompRule")
(ng #t)
;; ?^94:IntLe l(l+n)
(use "IntLeTrans" (pt "l+IntZero"))
;; 95,96
(use "Truth")
;; 96
(simp "<-" "NatToIntPlus")
(use "IntLeMonPlus")
(use "Truth")
(use "Truth")
(use "Truth")
(autoreal)
;; 72
(use "RealLeTrans" (pt "(1#2)*((1#2)**n*((1#PosF l)*abs x**l))"))
;; 100,101
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "IH")
;; 101
(simpreal "RealTimesAssoc")
(use "RealLeMonTimes")
;; 109,110
;; ?^109:0<<=(1#PosF l)*abs x**l
(use "Lemma1")
(use "Rx")
;; ?^110:RealTimes(1#2)((1#2)**n)<<=(1#2)**Succ n
(simpreal "<-" "RatTimesRealTimes")
(use "RatLeToRealLe")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
;; 108
(autoreal)
;; Assertion proved.
(assume "Lemma3")

;; We prove Lemma4 which essentially is the ratio test.  (Lemma4 was Q3)

(assert "all xs,n,m(
 all n0 0<<=xs n0 -> 
 all n0 xs(n+n0)<<=(1#2)**n0*xs n -> RealSum n m xs<<=2*xs n)")
(assume "xs" "n" "m" "0<=xs" "LeHyp")
(use "RealLeTrans" (pt "RealSum n m([n0](1#2)**(n0--n)*xs n)"))
;; 120,121
(use "RealLeMonSum")
(bpe-ng #t)
(assume "l" "n<=l" "Useless")
(inst-with-to "LeHyp" (pt "l--n") "Inst")
(simphyp-with-to "Inst" (pf "n+(l--n)=l") "SimpInst")
(use "SimpInst")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "n<=l")
;; ?^121:RealSum n m([n0](1#2)**(n0--n)*xs n)<<=2*xs n
(simpreal (pf "RealSum n m([n0](1#2)**(n0--n)*xs n)===
               RealSum Zero m([n0](1#2)**n0*xs n)"))
;; 132,133
(get 133)
(use "RealEqSym")
(use "RealSumZeroShiftUp")
(bpe-ng #t)
(assume "n0")
(autoreal)
;; ?^132:RealSum Zero m([n0](1#2)**n0*xs n)<<=2*xs n
(simpreal (pf "RealSum Zero m([n0](1#2)**n0*xs n)===
               (RealSum Zero m([n0](1#2)**n0))*xs n"))
;; 138,139
(get 139)
(use "RealEqSym")
(use "RealTimesSumDistrLeft")
(autoreal)
(bpe-ng #t)
(assume "n0")
(autoreal)
;; ?^138:RealSum Zero m([n0](1#2)**n0)*xs n<<=2*xs n
(use "RealLeMonTimes")
(use "0<=xs")
;; ?^146:RealSum Zero m([n](1#2)**n)<<=2
(simpreal "GeomSumOneHalfEqRat")
;; ?^147:2*(1+ ~((1#2)**m))<<=2
(use "RatLeToRealLe")
(simprat "RatTimesPlusDistr")
(ng #t)
;; ?^150:2+ ~(2*(1#2)**n)<=2
(use "RatLeTrans" (pt "2+RatUMinus Zero"))
(use "RatLeMonPlus")
(use "Truth")
(simp "RatLeUMinus")
;; ?^155:Zero<=2*(1#2)**m
(ind (pt "m"))
(use "Truth")
(assume "m0" "IH")
(ng #t)
(simprat (pf "0==0*(1#2)"))
(use "RatLeMonTimes")
(use "Truth")
(use "IH")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "Lemma4")

;; We can now prove the final goal, i.e., the absolute convergence of
;; the exponential function, with modulus.  (This was Q4).

(assume "x" "xs" "l" "q" "p" "n" "m" "Rx" "xsDef" "lBd" "qBd" "nBd")
(use "RealLeTrans" (pt "RealTimes 2((1#2)**(n--l))*xs l"))
;; 166,167
;; ?^166:RealSum n m xs<<=RealTimes 2((1#2)**(n--l))*xs l
(use "RealLeTrans" (pt "2*(xs n)"))
;; 168,169
(use "Lemma4")
;; 170,171
(assume "n0")
(simpreal "xsDef")
;; ?^173:0<<=(1#PosF n0)*abs x**n0
(use "Lemma1")
(use "Rx")
;; ?^171:all n0 xs(n+n0)<<=(1#2)**n0*xs n
(assume "n0")
(simpreal "xsDef")
(simpreal "xsDef")
(use "Lemma3")
(use "Rx")
;; ?^179:2*abs x<<=Succ n
(use "RealLeTrans" (pt "RealConstr([n]Succ l)([p]Zero)"))
(use "lBd")
(use "RatLeToRealLe")
(ng #t)
(simp "NatToIntLe")
(use "NatLeTrans" (pt "PosS(q+p)+l"))
(use "Truth")
(use "nBd")
;; ?^169:2*xs n<<=RealTimes 2((1#2)**(n--l))*xs l
(simpreal "<-" "RealTimesAssoc")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
;; ?^192:xs n<<=(1#2)**(n--l)*xs l
(simpreal "xsDef")
(simpreal "xsDef")
(inst-with-to "Lemma3" (pt "x") (pt "l") "Rx" "lBd" (pt "n--l") "Inst")
(simphyp-with-to "Inst" (pf "l+(n--l)=n") "SimpInst")
(drop "Inst")
(use "SimpInst")
(drop "Inst")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLeTrans" (pt "PosS(q+p)+l"))
(use "Truth")
(use "nBd")
(autoreal)
;; ?^167:RealTimes 2((1#2)**(n--l))*xs l<<=(1#2)**p
;; Now the rhs
(use "RealLeTrans" (pt "RealTimes 2((1#2)**(n--l))*2**q"))
;; 207,208
(use "RealLeMonTimesR")
(simpreal "<-" "RatTimesRealTimes")
(use "RatLeToRealLe")
(use "RatLeTrans" (pt "RatTimes 0 0"))
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "qBd")
;; ?^208:RealTimes 2((1#2)**(n--l))*2**q<<=(1#2)**p
(simpreal "<-" "RatTimesRealTimes")
(simpreal "<-" "RatTimesRealTimes")
(use "RatLeToRealLe")
;; ?^221:2*(1#2)**(n--l)*2**q<=(1#2)**p
(use "RatLeTrans" (pt "2*(1#2)**PosS(q+p)*2**q"))
(use "RatLeMonTimes")
(use "Truth")
(use "RatLeMonTimesR")
(use "Truth")
;; ?^227:(1#2)**(n--l)<=(1#2)**PosS(q+p)
(simp "<-" "PosToNatToIntId")
(simp "<-" "PosToNatToIntId")
(use "RatLeMonExpDecr")
(use "Truth")
(use "Truth")
;; ?^232:PosS(q+p)<=n--l
(use "NatLePlusCancelR" (pt "l"))
(simp "NatMinusPlusEq")
(use "nBd")
;; ?^235:l<=n
(use "NatLeTrans" (pt "PosS(q+p)+l"))
(use "Truth")
(use "nBd")
;; ?^223:2*(1#2)**PosS(q+p)*2**q<=(1#2)**p
(simp "RatExpPosS")
(simp (pf "((1#2)**(q+p)*(1#2))=((1#2)*(1#2)**(q+p))"))
(simp "RatTimesAssoc")
(simprat "RatExpPosPlus")
(ng #t)
(simp "PosTimesComm")
(use "Truth")
;; ?^240:(1#2)**(q+p)*(1#2)=(1#2)*(1#2)**(q+p)
(use "RatTimesComm")
;; Proof finished.
;; (cp)
(save "RealEAbsConvAux")

;; MonConst
(set-goal "all n Mon([p]n)")
(assume "n")
(intro 0)
(assume "p" "q" "p<=q")
(use "Truth")
;; Proof finished.
;; (cp)
(save "MonConst")

;; RealConvLimConstRat
(set-goal "all a, M (Real a -> Mon M -> RealConvLim ([n]a) a M)")
(assume "a" "M" "Ra" "Mon M")
(intro 0)

;; RealConvLimIntro 1
(assume "n")
(realproof)
;; RealConvLimIntro 2
(use "Ra")
;; RealConvLimIntro 3
(use "Mon M")
;; RealConvLimIntro 4
(intro 0)
(assume "p" " n" "nBd")
(use "RatLeToRealLe")
(simprat (pf "a+(~a)==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealConvLimConstRat")

;; RealEAbsConv
(set-goal "all x,l,q,xs,M(
 Real x -> 
 2*abs x<<=Succ l -> 
 xs l<<=2**q -> 
 all n xs n===(1#PosF n)*abs x**n -> 
 all p M p=PosS(q+p)+l -> RealSerConv xs M)")
(assume "x" "l" "q" "xs" "M" "Rx" "lBd" "qBd" "xsDef" "MDef")

(assert "all n Real(xs n)")
(assume "n")
(realproof)
;; Assertion proved.
(assume "Rxs")

;; ?^6:RealSerConv xs M
(intro 0)
;; 7-9
(use "Rxs")
;; ?^8:Mon M
(intro 0)
(assume "p0" "q0" "LeH")
(simp "MDef")
(simp "MDef")
(simp "NatLe5RewRule")
(simp "PosToNatLe")
(ng #t)
(use "LeH")
;; ?^9:RSerConv xs M
(intro 0)
(assume "p" "n" "m" "nBd")
(use "RealLeTrans" (pt "RealSum n m([l]abs(xs l))"))
;; 19,20
(use "RealLeAbsSum")
(use "Rxs")
;; 20
(use "RealEAbsConvAux" (pt "x") (pt "l") (pt "q"))
;; 22-26
(use "Rx")
;; ?^23:all n ([n0]abs(xs n0))n===(1#PosF n)*abs x**n
(assume "n0")
(bpe-ng #t)
(simpreal "xsDef") ; now works since we have RealCompat
(simpreal "RealAbsTimes")
(simpreal "<-" "RealAbsExp")
(simp "RealAbs0RewRule")
(use "RealEqRefl")
(autoreal)
;; 24
(use "lBd")
;; 25
(bpe-ng #t)
(simpreal (pf "abs(xs l)===xs l"))
;; 38,39
(use "qBd")
;; ?^39:abs(xs l)===xs l
(simpreal "xsDef")
(simpreal "RealAbsTimes")
(simpreal "<-" "RealAbsExp")
(simp "RealAbs0RewRule")
(use "RealEqRefl")
(autoreal)
;; ?^26:PosS(q+p)+l<=n
(simp "<-" "MDef")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RealEAbsConv")

;; We reformulate (pp "RealEAbsConv"), avoiding usage of xs and M.

;; all x,l,q,xs,M(
;;  Real x -> 
;;  2*abs x<<=Succ l -> 
;;  xs l<<=2**q -> 
;;  all n xs n===(1#PosF n)*abs x**n -> 
;;  all p M p=PosS(q+p)+l -> RealSerConv xs M)

;; RealEAbsConvCor
(set-goal "all x(Real x ->
 RealSerConv([n]((1#PosF n)*abs x**n))(RealEMod x))")
(assume "x" "Rx")
(use "RealEAbsConv" (pt "x") (pt "cREModOne x") (pt "cREModTwo x"))
(use "Rx")
(simp "REModOneExFree")
(use "RealEModOneProp")
(use "Rx")
;; 5
(bpe-ng #t)
(use "RealEModTwoProp")
(use "Rx")
(use "Truth")
(simp "REModTwoExFree")
(use "Truth")
;; 6
(assume "n")
(bpe-ng #t)
(use "RealEqRefl")
(realproof)
;; 7
(assume "p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEAbsConvCor")

;; RealLimESeqMod
(set-goal "all x(Real x -> Real(cRLim(cRESeq x)(cREMod x)))")

;; We first proof a Lemma (was Q4Cor)
(assert "all x,l,q,p,n,m(Real x ->
 2*abs x<<=Succ l ->
 (1#PosF l)*abs x**l<<=2**q ->
 PosS(q+p)+l<=n ->
 RealSum n m([n0](1#PosF n0)*abs x**n0)<<=(1#2)**p)")
(assume "x" "l" "q" "p" "n" "m" "Rx" "lBd" "qBd" "nBd")
(use "RealEAbsConvAux" (pt "x") (pt "l") (pt "q"))
(use "Rx")
(assume "n0")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "lBd")
(use "qBd")
(use "nBd")
;; Assertion proved.
(assume "Lemma")

;; Now we can prove the final goal.
(assume "x" "Rx")
(simp "RLimExFree")
(simp "<-" "RLimExFree")
(use "RealLimRealCor")
;; 17-19
;; ?^17:all n Real(cRESeq x n)
(assume "n")
(simp "RESeqExFree")
(ng #t)
(simp "RSumExFree")
(autoreal)
;; ?^18:all p,n,m(
;;      cREMod x p<=n -> n<=m -> abs(cRESeq x n+ ~(cRESeq x m))<<=(1#2**p))
(assume "p" "n" "m" "nBd" "n<=m")
(simp "RESeqExFree")
(ng #t)
(simp "RSumExFree")
(simp "RSumExFree")
;; ?^28:abs(RealSum Zero(Succ n)([n0](1#PosF n0)*x**n0)+ 
;;        ~(RealSum Zero(Succ m)([n0](1#PosF n0)*x**n0)))<<=
;;      (1#2**p)
(simpreal "RealAbsPlusUMinus")
(simpreal "RealSumZeroMinusMod")
;; ?^32:abs(RealSum(Succ n)(Succ m--Succ n)([n0](1#PosF n0)*x**n0))<<=(1#2**p)
(ng #t)
;; ?^35:abs(RealSum(Succ n)(m--n)([n0](1#PosF n0)*x**n0))<<=(1#2**p)
;; Move abs inside
(use "RealLeTrans" (pt "(RealSum(Succ n)(m--n)([n0](1#PosF n0)*abs x**n0))"))
;; 36,37
;; ?^36:abs(RealSum(Succ n)(m--n)([n0](1#PosF n0)*x**n0))<<=
;;          RealSum(Succ n)(m--n)([n0](1#PosF n0)*abs x**n0)
(use "RealLeTrans" (pt "RealSum(Succ n)(m--n)([n0]abs((1#PosF n0)*x**n0))"))
(use "RealLeAbsSum")
(assume "n0")
(autoreal)
;; ?^39:RealSum(Succ n)(m--n)([n0]abs((1#PosF n0)*x**n0))<<=
;;      RealSum(Succ n)(m--n)([n0](1#PosF n0)*abs x**n0)
(use "RealLeMonSum")
(assume "l" "Useless1" "Useless2")
(ng #t)
(simpreal "RealAbsTimes")
(use "RealLeMonTimesTwo")
;; 48-50
(use "RealLeZeroAbs")
(autoreal)
;; 49
(use "RealLeZeroAbs")
(autoreal)
;; 50
(use "RatLeToRealLe")
(use "Truth")
;; ?^51:abs(x**l)<<=abs x**l
(simpreal "RealAbsExp")
(use "RealLeRefl")
(autoreal)
;; ?^37:RealSum(Succ n)(m--n)([n0](1#PosF n0)*abs x**n0)<<=(1#2**p)
(use "Lemma" (pt "cREModOne x") (pt "cREModTwo x"))
;; 58-61
(use "Rx")
;; ?^49:2*abs x<<=Succ(cREModOne x)
(simp "REModOneExFree")
(use "RealEModOneProp")
(use "Rx")
;; ?^60:(1#PosF(cREModOne x))*abs x**cREModOne x<<=2**cREModTwo x
(defnc "l" "cREModOne x")
(simp "<-" "lDef")
(use "RealEModTwoProp")
(use "Rx")
(simp "lDef")
(use "Truth")
(simp "REModTwoExFree")
(use "Truth")
;; ?^61:PosS(cREModTwo x+p)+cREModOne x<=Succ n
(simp "<-" "RealEMod0CompRule")
(simp "<-" "REModExFree")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
;; ?^34:Succ n<=Succ m
(use "n<=m")
;; 33
(assume "n0")
(autoreal)
;; ?^19:all p,q(p<=q -> cREMod x p<=cREMod x q)
(assume "p" "q" "p<=q")
(simp "REModExFree")
(simp "REModExFree")
(simp "RealEMod0CompRule")
(simp "RealEMod0CompRule")
(ng #t)
(simp "PosToNatLe")
(ng #t)
(use "p<=q")
;; Proof finished.
;; (cp)
(save "RealLimESeqMod")

;; 2023-06-04

;; We use RealE (or cRE) for the real exponential function, by defining
;; (RealE x) to be cRLim(cRESeq x)(cREMod x)

(add-program-constant "RealE" (py "rea=>rea"))
(add-computation-rules "RealE x" "cRLim(cRESeq x)(cREMod x)")

(set-totality-goal "RealE")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; 2024-10-06

;; RealEReal
(set-goal "all x(Real x -> Real(RealE x)) ")
(assume "x" "Rx")
(simp "RealE0CompRule")
(use "RealLimESeqMod")
(use "Rx")
;; Proof finished.
;; (cp)
(save "RealEReal")

;; End 2024-10-06

;; RE
(set-goal "all x exl y y eqd cRLim(cRESeq x)(cREMod x)")
(assume "x")
(intro 0 (pt "cRLim(cRESeq x)(cREMod x)"))
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "RE")

(animate "RE")

;; REExFree
(set-goal "all x cRE x eqd RealE x")
(assume "x")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "REExFree")

;; 2024-10-06

;; cREReal
(set-goal "all x(Real x -> Real(cRE x))")
(assume "x" "Rx")
(use "RealEReal")
(use "Rx")
;; Proof finished.
;; (cp)
(save "cREReal")

;; End 2024-10-06

(deanimate "RE")

(set-totality-goal "cRE")
(fold-alltotal)
(assume "x")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use the deanimated cRE instead of RealE.

;; 2. Cauchy product
;; =================
;; We now aim at RealCauchyProdLim and RealCauchyProdLimAbs which are
;; needed for the functional equation of the exponential function.

;; 2021-01-14.  RealCauchyProduct, auxiliary lemma for both parts

;; We now aim at RealCauchyProdLim and RealCauchyProdLimAbs which are
;; needed for the functional equation of the exponential function.

;; 2021-01-14.  RealCauchyProduct, auxiliary lemma for both parts

;; RealConvLimIncrToCauchy (was ConvLimIncrToConv)
(set-goal "all xs,x,M,m,n,p(RealConvLim xs x M ->
 all m,n(m<=n -> xs m<<=xs n) ->
 all n xs n<<=x ->
 M p<=m ->
 m<=n ->
 xs n+ ~(xs m)<<=(1#2**p))")  
(assume "xs" "x" "M" "m" "n" "p" "CxsxM" "xsIncr" "xBd" "Mp<=m" "m<=n")
(use "RealLeTrans" (pt "x+ ~(xs m)"))
(use "RealLeMonPlus")
(autoreal)
(use "xBd")
(use "RealLeTrans" (pt "abs(xs m+ ~x)"))
(simpreal "RealAbsPlusUMinus")
(use "RealLeIdAbs")
(autoreal)
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "CxsxM")
(use "Mp<=m")
;; Proof finished.
;; (cp)
(save "RealConvLimIncrToCauchy")

;; RealLeSumZeroAbs
(set-goal "all xs,m,n(all n Real(xs n) -> m<=n ->
 RealSum Zero m([n0]abs(xs n0))<<=RealSum Zero n([n0]abs(xs n0)))")
(assume "xs" "m" "n" "Rxs" "m<=n")
(simpreal (pf "RealSum Zero n([n0]abs(xs n0))===
     RealSum Zero m([n0]abs(xs n0))+RealSum m(n--m)([n0]abs(xs n0))"))
(use "RealLeTrans" (pt "RealSum Zero m([n0]abs(xs n0))+0"))
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealLeMonPlusR")
(autoreal)
;; ?^11:0<<=RealSum m(n--m)([n0]abs(xs n0))
(simpreal (pf "0===RealSum m(n--m)([i]0)"))
(use "RealLeMonSum")
(ng #t)
(strip)
(use "RealLeZeroAbs")
(autoreal)
(simpreal "RealSumZeros")
(use "RatEqvToRealEq")
(use "Truth")
(assume "l0")
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(simpreal "RealSumZeroSplit")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "RealEqRefl")
(autoreal)
(use "m<=n")
(assume "n0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealLeSumZeroAbs")

;; RealConvLimPStarToCauchy (was RealConvLimPStarToConv)
(set-goal "all xs,x,ys,y,M,N,p,q,K(
     all n Real(xs n) -> 
     all n Real(ys n) -> 
     Real x -> 
     Real y -> 
     RealConvLim([n]RealSum Zero n([i]abs(xs i)))x M -> 
     RealConvLim([n]RealSum Zero n([j]abs(ys j)))y N -> 
     all n RealSum Zero n([j]abs(xs j))<<=x -> 
     all n RealSum Zero n([j]abs(ys j))<<=y -> 
     all n RealSum Zero n([i]abs(xs i))<<=2**p -> 
     all n RealSum Zero n([j]abs(ys j))<<=2**q -> 
     all r K r=N(p+r+1)max M(q+r+1) -> 
     all r,m,n(
      K r<=m -> 
      m<=n -> 
      RealSum Zero(n*n)([k]abs(xs lft(RtD k))*abs(ys rht(RtD k)))+ 
      ~(RealSum Zero(m*m)
        ([k]abs(xs lft(RtD k))*abs(ys rht(RtD k))))<<=
      (1#2**r)))")
(assume "xs" "x" "ys" "y" "M" "N" "p" "q" "K" "Rxs" "Rys" "Rx" "Ry"
"CxsxM" "CysyN" "xBd" "yBd" "xsBd" "ysBd" "KDef"
"r" "m" "n" "Kr<=m" "m<=n")
(def "zs" "[k]abs(xs lft(RtD k))*abs(ys rht(RtD k))")

(assert "all n0 Real(zs n0)")
(assume "k")
(simp "zsDef")
(autoreal)
(assume "Rzs")

(simp "<-" "zsDef")
;; ?^15:RealSum Zero(n*n)zs+ ~(RealSum Zero(m*m)zs)<<=(1#2**r)

(simpreal (pf "RealSum Zero(n*n)zs===
 (RealSum Zero n([i]abs(xs i)))*(RealSum Zero n([j]abs(ys j)))"))
(get 17)
(simpreal "RealSumTimes")
;; 18-20
(ng #t)
(simp "zsDef")
(use "RealEqRefl")
(autoreal)
(assume "n0")
(autoreal)
(assume "n0")
(autoreal)
;; 16

(simpreal (pf "RealSum Zero(m*m)zs===
(RealSum Zero m([i]abs(xs i)))*(RealSum Zero m([j]abs(ys j)))"))
(get 27)
(simpreal "RealSumTimes")
;; 28-30
(ng #t)
(simp "zsDef")
(use "RealEqRefl")
(autoreal)
(assume "n0")
(autoreal)
(assume "n0")
(autoreal)
;; 26
(use "RealLeTrans"
     (pt "RealSum Zero n([i]abs(xs i))*RealSum Zero n([j]abs(ys j))+
          (~(RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j)))+
            (RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j))))+
          ~(RealSum Zero m([i]abs(xs i))*RealSum Zero m([j]abs(ys j)))"))
(simpreal (pf "~(RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j)))+
            (RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j)))===
            RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j))+
            ~(RealSum Zero n([i]abs(xs i))*RealSum Zero m([j]abs(ys j)))"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; 37
(simpreal "RealPlusAssoc")
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
;; ?^65:RealSum Zero n([i]abs(xs i))*
;;      (RealSum Zero n([j]abs(ys j))+ ~(RealSum Zero m([j]abs(ys j))))+
;;      (RealSum Zero n([i]abs(xs i))+ ~(RealSum Zero m([i]abs(xs i))))*
;;      RealSum Zero m([j]abs(ys j))<<=
;;      (1#2**r)
(use "RealLeTrans"
     (pt "RealTimes(2**p)(1#2**(p+r+1))+RealTimes(1#2**(q+r+1))(2**q)"))
;; 69,70
(use "RealLeMonPlusTwo")
(use "RealLeMonTimesTwo")
;; ?^73:0<<=RealSum Zero n([i]abs(xs i))
(simpreal (pf "0===RealSum Zero n([i]0)"))
(use "RealLeMonSum")
(ng #t)
(strip)
(use "RealLeZeroAbs")
(autoreal)
(simpreal "RealSumZeros")
(use "RatEqvToRealEq")
(use "Truth")
(assume "l")
(use "RatEqvToRealEq")
(use "Truth")
;; ?^74:0<<=RealSum Zero n([j]abs(ys j))+ ~(RealSum Zero m([j]abs(ys j)))
(use "RealLePlusUMinusR")
(autoreal)
(ng #t)
(simpreal "RealPlusZero")
;;   m<=n:m<=n
;; -----------------------------------------------------------------------------
;; ?^92:RealSum Zero m([n0]abs(ys n0))<<=RealSum Zero n([n0]abs(ys n0))
(use "RealLeSumZeroAbs")
(use "Rys")
(use "m<=n")
(autoreal)
(use "xsBd")
;; ?^76:RealSum Zero n([j]abs(ys j))+ ~(RealSum Zero m([j]abs(ys j)))<<=
;;      (1#2**(p+r+1))
(assert "([n0]RealSum Zero n0([j]abs(ys j)))n+
 ~(([n0]RealSum Zero n0([j]abs(ys j)))m)<<=(1#2**(p+r+1))")
(use-with
 "RealConvLimIncrToCauchy"
 (pt "[n]RealSum Zero n([j]abs(ys j))")
 (pt "y") (pt "N") (pt "m") (pt "n") (pt "p+r+1") "?" "?" "?" "?" "?")
;; 98-102
(use "CysyN")
;; 99
(assume "m0" "n0" "m0<=n0")
(ng #t)
;; ?^104:RealSum Zero m0([n]abs(ys n))<<=RealSum Zero n0([n]abs(ys n))
(use "RealLeSumZeroAbs")
(use "Rys")
(use "m0<=n0")
;; ?^100:all n ([n0]RealSum Zero n0([j]abs(ys j)))n<<=y
(ng #t)
(use "yBd")
;; 101
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB1")
(use "Kr<=m")
;; 102
(use "m<=n")
;; 96
(ng #t)
(auto)
;;   m<=n:m<=n
;; -----------------------------------------------------------------------------
;; ?^72:(RealSum Zero n([i]abs(xs i))+ ~(RealSum Zero m([i]abs(xs i))))*
;;      RealSum Zero m([j]abs(ys j))<<=
;;      RealTimes(1#2**(q+r+1))(2**q)
(use "RealLeMonTimesTwo")
;; 112-115
;; ?^112:0<<=RealSum Zero n([i]abs(xs i))+ ~(RealSum Zero m([i]abs(xs i)))
(use "RealLePlusUMinusR")
(autoreal)
(ng #t)
(simpreal "RealPlusZero")
;;   m<=n:m<=n
;; -----------------------------------------------------------------------------
;; ?^120:RealSum Zero m([n0]abs(xs n0))<<=RealSum Zero n([n0]abs(xs n0))
(use "RealLeSumZeroAbs")
(use "Rxs")
(use "m<=n")
(autoreal)
;; ?^113:0<<=RealSum Zero m([j]abs(ys j))
(simpreal (pf "0===RealSum Zero m([i]0)"))
(use "RealLeMonSum")
(ng #t)
(strip)
(use "RealLeZeroAbs")
(autoreal)
(simpreal "RealSumZeros")
(use "RatEqvToRealEq")
(use "Truth")
(assume "l")
(use "RatEqvToRealEq")
(use "Truth")
;; ?^114:RealSum Zero n([i]abs(xs i))+ ~(RealSum Zero m([i]abs(xs i)))<<=
;;       (1#2**(q+r+1))
(assert "([n0]RealSum Zero n0([i]abs(xs i)))n+
 ~(([n0]RealSum Zero n0([i]abs(xs i)))m)<<=(1#2**(q+r+1))")
(use-with
 "RealConvLimIncrToCauchy"
 (pt "[n]RealSum Zero n([i]abs(xs i))")
 (pt "x") (pt "M") (pt "m") (pt "n") (pt "q+r+1") "?" "?" "?" "?" "?")
;; 137-141
(use "CxsxM")
;; 138
(assume "m0" "n0" "m0<=n0")
(ng #t)
(use "RealLeSumZeroAbs")
(use "Rxs")
(use "m0<=n0")
;; 139
(ng #t)
(assume "n0")
(use "xBd")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB2")
(use "NatLeTrans" (pt "m"))
(use "Kr<=m")
(use "Truth")
(use "m<=n")
;; 135
(auto)
;; ?^70:RealTimes(2**p)(1#2**(p+r+1))+RealTimes(1#2**(q+r+1))(2**q)<<=(1#2**r)
(use "RatLeToRealLe")
(simprat "<-" "RatPlusHalfExpPosS")
(ng #t)
(use "PosLeMonPlus")
;; 156,157
(simp "PosTimesComm")
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(use "PosLeMonTimes")
(use "Truth")
(simp (pf "2**PosS(q+r)*2**PosS r=2**PosS r*2**PosS(q+r)"))
(simp "PosTimesAssoc")
(use "PosLeMonTimes")
;; ?^166:2**p*2**PosS r<=2**PosS(p+r)
(simp "PosSSucc")
(simp "PosSSucc")
(ng #t)
(simp "PosToNatPlus")
(simp "PosExpTwoNatPlus")
(use "Truth")
;; 167
(use "Truth")
;; 164
(use "PosTimesComm")
;; 157
(simp "PosTimesComm")
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(use "PosLeMonTimes")
(use "Truth")
(simp (pf "2**PosS(p+r)*2**PosS r=2**PosS r*2**PosS(p+r)"))
(simp (pf "2**PosS(p+r)*2**PosS(q+r)=2**PosS(q+r)*2**PosS(p+r)"))
(simp "PosTimesAssoc")
(use "PosLeMonTimes")
(simp "PosSSucc")
(simp "PosSSucc")
(ng #t)
(simp "PosToNatPlus")
(simp "PosExpTwoNatPlus")
(use "Truth")
(use "Truth")
(use "PosTimesComm")
(use "PosTimesComm")
;; 68
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimPStarToCauchy")

;; Will need: RealSumDiags below.  For RealSumDiags we will also need
;; (pp "RealIfImpToIfIf")

;; LeIdMaxToLeSquareC
(set-goal "all n,i,j(n<=i max j -> n*n<=RtC(i pair j))")
(assume "n" "i" "j" "LeMaxHyp")
(use "NatLeTrans" (pt "i max j*(i max j)"))
(use "NatLeMonTimes")
(use "LeMaxHyp")
(use "LeMaxHyp")
(use "RtCProp2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "LeIdMaxToLeSquareC")

;; IntTimesChoosePosF
(set-goal "all n,m(m<=n -> IntTimes(Choose n m)(PosF(n--m))*PosF m=PosF n)")
(assume "n" "m" "m<=n")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "IntTimes2CompRule")
;; (simp "<-" "NatPosExFree") ;commented out 2025-10-06
(use "PosTimesChoosePosF")
(use "m<=n")
;; ?^4:Zero<Choose n m
(use "NatLeToLtZeroChoose")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "IntTimesChoosePosF")

;; RealTimesChoosePosF
(set-goal "all n,m(m<=n -> RealTimes(Choose n m)(PosF(n--m))*PosF m===PosF n)")
(assume "n" "m" "m<=n")
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(assume "n0" "Useless")
(ng #t)
(use "IntTimesChoosePosF")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "RealTimesChoosePosF")

;; RatChoosePosF
(set-goal "all n,m(m<=n -> Choose n m==PosF n*(1#PosF(n--m))*(1#PosF m))")
(assume "n" "m" "m<=n")
(simp "<-" "IntPNatToPosEqNatToInt")
;; (simp "<-" "NatPosExFree")
(use "PosTimesChoosePosF") ;commented out 2025-10-06
(use "m<=n")
;; ?^4:Zero<Choose n m
(use "NatLeToLtZeroChoose")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "RatChoosePosF")

;; We specialize RealCauchyProdLim to exponential functions

;; RealCauchyProdLimE (was RealCauchyProdLimExp)
(set-goal "all xs,ys,x,y,x0,M,y0,N,p,q,K,xs0,ys0,M0,N0,p0,q0,K0(
     Real x -> 
     Real y -> 
     all n xs n===(1#PosF n)*x**n -> 
     all n ys n===(1#PosF n)*y**n -> 
     RealConvLim([n]RealSum Zero n xs)x0 M -> 
     RealConvLim([n]RealSum Zero n ys)y0 N -> 
     all n abs(RealSum Zero n xs)<<=2**p -> 
     all n abs(RealSum Zero n ys)<<=2**q -> 
     all r K r=N(p+r+1)max M(q+r+1) -> 
     all n xs0 n===RealSum Zero n([i]abs(xs i)) -> 
     all n ys0 n===RealSum Zero n([j]abs(ys j)) -> 
     RealCauchy xs0 M0 -> 
     RealCauchy ys0 N0 -> 
     all n xs0 n<<=2**p0 -> 
     all n ys0 n<<=2**q0 -> 
     all r K0 r=N0(p0+r+1)max M0(q0+r+1) -> 
     all r,n(
      (K0(PosS r)+K0(PosS r))max K(PosS r)<=n -> 
      abs(RealSum Zero(Succ(n*n+n+n))
          ([k]
            [if (lft(RtD k)+rht(RtD k)<=n)
              (xs lft(RtD k)*ys rht(RtD k))
              0])+ 
          ~(x0*y0))<<=
      (1#2**r)))")
(assume
 "xs0" "ys0" "x" "y" "x0" "M0" "y0" "N0" "p0" "q0" "K0"	"xs1" "ys1" "M1" "N1"
"p1" "q1" "K1" "Rx" "Ry" "xs0Def" "ys0Def" "Cxs0x0M0" "Cys0y0N0"
 "xs0Bd" "ys0Bd" "K0Def" "xs1Def" "ys1Def" "Cxs1M1" "Cys1N1"
 "xs1Bd" "ys1Bd" "K1Def" "r" "n" "nBd")
(assert "all n Real(xs0 n)")
(assume "n0")
(autoreal)
(assume "Rxs0")
(assert "all n Real(ys0 n)")
(assume "n0")
(autoreal)
(assume "Rys0")
(assert "(K1(PosS r)+K1(PosS r))max K0(PosS r)<=Succ n")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(assume "SnBd")

;; (pp "RealCauchyProdLim")
(inst-with-to
 "RealCauchyProdLim"
 (pt "xs0") (pt "ys0") (pt "x0") (pt "y0") (pt "M0") (pt "N0")
 (pt "p0") (pt "q0") (pt "K0") (pt "xs1") (pt "ys1") (pt "M1") (pt "N1")
 (pt "p1") (pt "q1") (pt "K1") "Rxs0" "Rys0" "Cxs0x0M0" "Cys0y0N0"
 "xs0Bd" "ys0Bd" "K0Def" "xs1Def" "ys1Def"  "Cxs1M1" "Cys1N1"
 "xs1Bd" "ys1Bd" "K1Def" (pt "r") (pt "Succ n") "SnBd"
 "Inst")
(simpreal
 (pf "RealSum Zero(Succ(n*n+n+n))
      ([k][if (lft(RtD k)+rht(RtD k)<=n)
 (xs0(lft(RtD k))*ys0(rht(RtD k))) 0])===
      RealSum Zero(Succ n*Succ n)
      ([k][if (lft(RtD k)+rht(RtD k)<Succ n)
 (xs0(lft(RtD k))*ys0(rht(RtD k))) 0])"))
;; 18,19
(use "Inst")
;; 19
(simp (pf "Succ(n*n+n+n)=Succ n*Succ n"))
(use "RealSumCompat")
(assume "l" "Useless1" "Useless2")
(bpe-ng #t)
(simp (pf "(lft(RtD l)+rht(RtD l)<=n)=
           (lft(RtD l)+rht(RtD l)<Succ n)"))
(use "RealEqRefl")
(autoreal)
;; 26
(use "BooleAeqToEq")
(use "NatLeToLtSucc")
(use "NatLtSuccToLe")
;; ?^21:Succ(n*n+n+n)=Succ n*Succ n
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealCauchyProdLimE")

;; (pp "RealCauchyProdLimE")
;; (pp "RealSumDiags")
;; These two together will prove the equation for the functional equation.

;; 3. Estimate of the rest
;; =======================

;; We reformulate RealBinom with factorials rather than the binomial
;; coefficients (Choose n m)

;; RealBinomPosF
(set-goal "all x,y(Real x -> Real y -> all n((1#PosF n)*(x+y)**n===
 RealSum Zero(Succ n)([m](1#PosF(n--m))*x**(n--m)*(1#PosF m)*y**m)))")
(assume "x" "y" "Rx" "Ry" "n")
(simpreal "RealBinom")
(simpreal "RealTimesSumDistr")
(use "RealSumCompat")
(bpe-ng #t)
(assume "l" "Useless" "l<=n")
;; ?^11:(1#PosF n)*(x**(n--l)*y**l*Choose n l)===
;;      (1#PosF(n--l))*x**(n--l)*(1#PosF l)*y**l
(simpreal "RealTimesAssoc")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
(simpreal "RealTimesComm")
(simpreal (pf "(1#PosF(n--l))*x**(n--l)===x**(n--l)*(1#PosF(n--l))"))
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
(use "RatEqvToRealEq")
;; ?^41:(Choose n l#PosF n)==(1#PosF(n--l)*PosF l)
(simp "RatChoosePosF")
(use "Truth")
(use "NatLtSuccToLe")
(use "l<=n")
(autoreal)
;; ?^33:(1#PosF(n--l))*x**(n--l)===x**(n--l)*(1#PosF(n--l))
(use "RealTimesComm")
(autoreal)
;; 28
(use "RealEqRefl")
(autoreal)
;; 8
(assume "n0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealBinomPosF")

;; RealSumDiags says: The conditional sum of length (n+1)^2 of the
;; lower triangle equals the sum of length (n+1) of the conditional
;; sum of length (m+1)^2 of the diagonals.  The conditional sums have
;; many zeros.

;; Aim now: explicit estimate of the rest.  This requires some
;; auxiliary propositions.

;; NatFPlusLB
(set-goal "all m,n NatF m*Succ m**n<=NatF(m+n)")
(assume "m")
(ind)
(use "Truth")
(assume "n" "IH")
(simp "NatExp1CompRule")
(simp "NatPlus1CompRule")
(simp "NatF1CompRule")
(simp "NatTimesAssoc")
(use "NatLeMonTimes")
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatFPlusLB")

;; 2024-11-08

;; Reformulation of (pp "RealTimesExpDivPosFAux")

;; RealTimesExpDivPosFAux
(set-goal "all x(
 Real x -> 
 all m,n 
  (1#PosF(m+n))*abs x**(m+n)<<=
  (1#PosF m)*abs x**m*((1#NatToPos(Succ m**n))*abs x**n))")
(assume "x" "Rx" "m")
(ind)
;; 3,4
(ng #t)
(simpreal "RealTimesOne")
(use "RealLeRefl")
(autoreal)
;; 4
(assume "n" "IH")
;; ?^9:(1#PosF(m+Succ n))*abs x**(m+Succ n)<<=
;;     (1#PosF m)*abs x**m*((1#NatToPos(Succ m**Succ n))*abs x**Succ n)
(simpreal "RealExpPlus")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(use "RealLeMonTimes")
(use "RealExpZeroLe")
(use "RealLeZeroAbs")
(use "Rx")
;; ?^21:(1#PosF(m+Succ n))*abs x**m<<=
;;      (1#PosF m)*abs x**m*(1#NatToPos(Succ m**Succ n))
(simpreal "RealTimesComm")
(simpreal (pf "(1#PosF m)*abs x**m===abs x**m*(1#PosF m)"))
(simpreal "<-" "RealTimesAssoc")
(use "RealLeMonTimesR")
(use "RealExpZeroLe")
(use "RealLeZeroAbs")
(use "Rx")
;; ?^34:(1#PosF(m+Succ n))<<=RealTimes(1#PosF m)(1#NatToPos(Succ m**Succ n))
(simpreal "<-" "RatTimesRealTimes")
(use "RatLeToRealLe")
;; ?^38:(1#PosF(m+Succ n))<=(1#PosF m)*(1#NatToPos(Succ m**Succ n))
(simp "RatTimes0CompRule")
(simp "IntTimes2RewRule")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "<-" "PosToNatToIntId")
(simp "<-" "PosToNatToIntId")
(use "NatLeToIntLe")
(simp "PosToNatLe")
;; ?^47:PosF m*NatToPos(Succ m**Succ n)<=PosF(m+Succ n)
(simp "<-" "NatFToPosF")
(simp "<-" "NatFToPosF")
(simp "<-" "NatToPosTimes")
(use "PosLeMonNatToPos")
;; ?^53:NatF m*Succ m**Succ n<=NatF(m+Succ n)
(use "NatFPlusLB")
;; ?^52:Zero<Succ m**Succ n
(use "NatLtLeTrans" (pt "Succ m**Zero"))
(use "Truth")
(use "NatLeMonExpR")
(use "Truth")
(use "Truth")
;; ?^51:Zero<NatF m
(use "NatLtZeroNatF")
;; ?^32:Real(1#NatToPos(Succ m**Succ n))
(autoreal)
;; ?^28:(1#PosF m)*abs x**Succ n===abs x**Succ n*(1#PosF m)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealTimesExpDivPosFAux")

;; RealEEstRest
(set-goal "all x(
     Real x -> 
     all m(
      abs x<<=(1#2)*Succ m -> 
      all l 
       RealSum Zero l([n](1#PosF(m+n))*abs x**(m+n))<<=(1#PosF m)*abs x**m*2))")
(assume "x" "Rx" "m" "Bd" "l")
(use "RealLeTrans"
     (pt "RealSum Zero l
          ([n](1#PosF m)*abs x**m*
              ((1#NatToPos(Succ m**n))*abs x**n))"))
;; 3
(use "RealLeMonSum")
(bpe-ng #t)
(assume "n" "Useless" "n<l")
(use "RealTimesExpDivPosFAux")
(use "Rx")
;; 4
(inst-with-to
 "RealTimesSumDistr"
 (pt "(1#PosF m)*abs x**m") (pt "[n](1#NatToPos(Succ m**n))*abs x**n")
 "Inst1")
(bpe-ng "Inst1")
(assert "Real((1#PosF m)*abs x**m)")
(autoreal)
(assume "RH1")
(assert "all n Real((1#NatToPos(Succ m**n))*abs x**n)")
(assume "n")
(autoreal)
(assume "RH2")
(inst-with-to "Inst1" "RH1" "RH2" (pt "Zero") (pt "l") "Inst2")
(drop "Inst1" "RH1" "RH2")
(simpreal "<-" "Inst2")
;; ?^22:
;; (1#PosF m)*abs x**m*RealSum Zero l([n](1#NatToPos(Succ m**n))*abs x**n)<<=
;; (1#PosF m)*abs x**m*2
(drop "Inst2")
(simpreal "<-" "RealTimesAssoc")
(simpreal "<-" "RealTimesAssoc")
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
;; 33
(use "RealLeMonTimesR")
(use "RealExpZeroLe")
(use "RealLeZeroAbs")
(use "Rx")
;; ?^36:RealSum Zero l([n](1#NatToPos(Succ m**n))*abs x**n)<<=2
;; Here we need the geometric sum RealGeomSumEqvNoDivOneHalf
;; (pp "RealGeomSumEqvNoDivOneHalf")
;; all n,m (1#2)*RealSum n m([n0](1#2)**n0)===(1#2)**n*(1+ ~((1#2)**m))
(use "RealLeTrans" (pt "RealSum Zero l([n](1#2)**n)"))
;; 39,40
(use "RealLeMonSum")
(bpe-ng #t)
(assume "n" "Useless" "n<l")
;; ?^43:(1#NatToPos(Succ m**n))*abs x**n<<=(1#2)**n
(use "RealLeTrans" (pt "RealTimes(1#NatToPos(Succ m**n))(((1#2)*Succ m)**n)"))
;; 44,45
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "RatExpRealExp")
(use "RealLeMonExpBase")
(use "RealLeZeroAbs")
(use "Rx")
;; ?^51:abs x<<=(1#2)*Succ m
(use "Bd")
;; ?^45:RealTimes(((1#2)*Succ m)**n)(1#NatToPos(Succ m**n))<<=(1#2)**n
(simpreal "<-" "RatTimesRealTimes")
(use "RatLeToRealLe")
;; ?^54:(1#NatToPos(Succ m**n))*((1#2)*Succ m)**n<=(1#2)**n
(simp "NatToPosExp") ;new in pos.scm
(simp "<-" "RatExpNatOne") ;new in rat.scm
(simprat "RatTimesExp")
(use "RatLeMonExpBase")
(ng #t)
;; ?^61:0<=IntS m
(use "IntLeZeroIntS") ;new in int.scm
;; ?^60:(1#NatToPos(Succ m))*((1#2)*Succ m)<=(1#2)
(simp "RatTimesComm")
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesInvNat") ;new in rat.scm
(use "Truth")
;; ?^56:Zero<Succ m
(use "Truth")
;; ?^40:RealSum Zero l([n](1#2)**n)<<=2
(inst-with-to "RatSumRealSum" (pt "[n](1#2)**n") (pt "Zero") (pt "l") "Inst")
(bpe-ng "Inst")
(simpreal "<-" "Inst")
(drop "Inst")
(use "RatLeToRealLe")
;; ?^70:RatSum Zero l([n](1#2)**n)<=2

;; (pp "RatGeomSumEqvNoDivOneHalf")
;; all n,m (1#2)*RatSum n m([n0](1#2)**n0)==(1#2)**n*(1+ ~((1#2)**m))

(use "RatLeTimesCancelL" (pt "(1#2)"))
(use "Truth")
(simprat "RatGeomSumEqvNoDivOneHalf")
(ng #t)
(use "RatLePlusCancelR" (pt "(1#2)**l"))
(simprat "RatEqvPlusMinus")
(use "RatLeTrans" (pt "RatPlus 1 0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
;; ?^80:0<=(1#2)**l
(use "RatLeExpPosGen")
(use "Truth")
;; 31
(autoreal)
;; Proof finished.
;; (cp)
(save "RealEEstRest")

;; End 2024-11-08

;; 4. Functional equation
;; ======================

;; We now use knowledge on the Cauchy Product to prove the functional
;; equation of the exponential function.

;; We use the reordering theorem RealSumPmsAll to prove that the sum
;; of the Rt-ordered elements on a diagonal of the lower triangle
;; equals the sum of the Gq-ordered elements on the corresponding
;; diagonal of the square.  The Rt-order comes from RealSumTimes, and
;; the Gq-order is needed to make RealBinomPosF applicable.

;; We first specialize RealSumPmsAll.  n is a fixed parameter, and the
;; sums have lenths (n+1)^2.  The reals to be summed up are given by a
;; function zss: nat yprod nat=>nat, with the intended meaning (zss ij)
;; := x^i/i! * y^j/j!.  The functions f, f0 both depend on n and are
;; defined from the coding and decoding functions for Rt and Gq.  From
;; (n+1)^2 onwards they are identities.

(add-var-name "zss" (py "nat yprod nat=>rea"))

;; RealSumPmsPair
(set-goal "all zss(
     all ij Real(zss ij) -> 
     all n 
      RealSum Zero(Succ(n*n+n+n))([k]zss(RtD k))===
      RealSum Zero(Succ(n*n+n+n))([k]zss(RtD(RtCGqD n k))))")
(assume "zss" "Rzss" "n")
(use "RealSumPmsAll" (pt "GqCRtD n"))
;; 3,4
(assume "k")
(ng #t)
(use "Rzss")
;; ?^4:PmsAll(n*n+n+n)(RtCGqD n)(GqCRtD n)
(intro 0)
;; 7-9
(assume "k")
(use "GqCRtDRtCGqDId")
;; 8
(assume "k")
(use "RtCGqDGqCRtDId")
;; 9
(assume "k")
(assume "LtH")
(simp "RtCGqD0CompRule")
(simp (pf "k<=n*n+n+n -> F"))
(use "Truth")
(assume "LeH")
(assert "k<k")
(use "NatLeLtTrans" (pt "n*n+n+n"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "RealSumPmsPair")

;; 2024-09-01

;; (pp (nt (pt "lft(RtD 12)"))) ;Zero
;; (pp (nt (pt "NatToPos(lft(RtD 7))"))) ;1
;; (pp (nt (pt "NatToPos(lft(RtD 5))"))) ;2
;; (pp (nt (pt "NatToPos(lft(RtD 9))"))) ;3

;; (pp (nt (pt "NatToPos(GsC(RtD 12))"))) ;6
;; (pp (nt (pt "NatToPos(GsC(RtD 7))"))) ;7
;; (pp (nt (pt "NatToPos(GsC(RtD 5))"))) ;8
;; (pp (nt (pt "NatToPos(GsC(RtD 9))"))) ;9

;; (pp (nt (pt "GsC(RtD 12)--Gs 3"))) ;Zero
;; (pp (nt (pt "NatToPos(GsC(RtD 7)--Gs 3)"))) ;1
;; (pp (nt (pt "NatToPos(GsC(RtD 5)--Gs 3)"))) ;2
;; (pp (nt (pt "NatToPos(GsC(RtD 9)--Gs 3)"))) ;3

;; ;; Conversely

;; (pp (nt (pt "NatToPos(RtC(GsD(Zero+Gs 3)))"))) ;12
;; (pp (nt (pt "NatToPos(RtC(GsD(1+Gs 3)))"))) ;7
;; (pp (nt (pt "NatToPos(RtC(GsD(2+Gs 3)))"))) ;5
;; (pp (nt (pt "NatToPos(RtC(GsD(3+Gs 3)))"))) ;9

;; (pp "RealSumPmsPair")
;; all zss(
;;  all ij Real(zss ij) -> 
;;  all n 
;;   RealSum Zero(Succ(n*n+n+n))([k]zss(RtD k))===
;;   RealSum Zero(Succ(n*n+n+n))([k]zss(RtD(RtCGqD n k))))

;; RealSumPmsPairCor
(set-goal "all zss(
     all ij Real(zss ij) -> 
     all n 
      RealSum Zero(n*n)([k]zss(RtD k))===
      RealSum Zero(n*n)([k]zss(RtD(RtCGqD(Pred n)k))))")
(assume "zss" "Rzss")
(cases)
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; 4
(use "RealSumPmsPair")
(use "Rzss")
;; Proof finished.
;; (cp)
(save "RealSumPmsPairCor")

;; As a consequnce of RealSumPmsPair we show

;; RealSumPmsGq
(set-goal "all zss(
 all ij Real(zss ij) -> 
 all n 
  RealSum Zero(Succ(n*n+n+n))([k]zss(RtD k))===
  RealSum Zero(Succ(n*n+n+n))([k]zss(GqD n k)))")
(assume "zss" "Rzss" "n")
(use "RealEqTrans" (pt "RealSum Zero(Succ(n*n+n+n))([k]zss(RtD(RtCGqD n k)))"))
;; 3,4
(use "RealSumPmsPair")
(use "Rzss")
;; 4
(use "RealSumCompat")
(assume "k" "Useless" "kBd")
(bpe-ng #t)
(ng "kBd")
;; ?^9:zss(RtD k)===zss(RtD(RtCGqD n k))
(simp "RtCGqD0CompRule")
(simp (pf "k<=n*n+n+n"))
(simp "IfTrue")
(simp "RtDCId")
(use "RealEqRefl")
(autoreal)
(use "NatLtSuccToLe")
(use "kBd")
;; Proof finished.
;; (cp)
(save "RealSumPmsGq")

;; As a consequnce of RealSumPmsPairCor we show

;; RealSumPmsGqCor
(set-goal "all zss(
 all ij Real(zss ij) -> 
 all n 
  RealSum Zero(n*n)([k]zss(RtD k))===
  RealSum Zero(n*n)([k]zss(GqD(Pred n)k)))")
(assume "zss" "Rzss")
(cases)
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; 4
(use "RealSumPmsGq")
(use "Rzss")
;; Proof finshed.
;; (cp)
(save "RealSumPmsGqCor")

;; From RealSumSplit and properties of Gauss sums we obtain

;; RealSumSplitGs
(set-goal "all n,xs(all n Real(xs n) ->
     RealSum Zero(Gs n)xs+RealSum(Gs n)(Succ n)xs+
     RealSum(Gs(Succ n))(Gs n)xs===
     RealSum Zero(Succ(n*n+n+n))xs)")
(assume "n" "xs" "Rxs")
(simpreal (pf "RealSum Zero(Gs n)xs+RealSum(Gs n)(Succ n)xs===
               RealSum Zero(Gs(Succ n))xs"))
;; 3,4
;; ?^3:RealSum Zero(Gs(Succ n))xs+RealSum(Gs(Succ n))(Gs n)xs===
;;     RealSum Zero(Succ(n*n+n+n))xs
(inst-with-to "RealSumSplit" (pt "xs") "Rxs" (pt "Zero") (pt "Gs(Succ n)")
	      (pt "Gs n") "Inst")
(simphyp-with-to "Inst" (pf "Zero+Gs(Succ n)=Gs(Succ n)") "InstS")
;; 8,9
(simp (pf "Succ(n*n+n+n)=Gs(Succ n)+Gs n"))
(use "InstS")
;; ?^11:Succ(n*n+n+n)=Gs(Succ n)+Gs n
(simp "GsProp")
(use "Truth")
;; 8
(use "Truth")
;; ?^4:RealSum Zero(Gs n)xs+RealSum(Gs n)(Succ n)xs===RealSum Zero(Gs(Succ n))xs
(simpreal "RealSumZeroSplit")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumSplitGs")

;; RealSumSplitGsCor
(set-goal "all n,xs(all n Real(xs n) ->
     RealSum Zero(Gs(Pred n))xs+RealSum(Gs(Pred n))n xs+
     RealSum(Gs n)(Gs(Pred n))xs===
     RealSum Zero(n*n)xs)")
(cases)
;; 2,3
(assume "xs" "Rxs")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
;; 3
(assume "n" "xs" "Rxs")
(use "RealSumSplitGs")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumSplitGsCor")

;; 2024-10-06

;; Preparations for the functional equation of the exponential
;; function.  We will need RealEDiagSum (replaces RealBinomDiag).
;; Given n,x,y, it maps ij to (x**i/i!)*(y**j/!) if i+j=n and to 0
;; else.

(add-program-constant
 "RealEDiagSum" (py "nat=>rea=>rea=>nat yprod nat=>rea "))
(add-computation-rules
 "RealEDiagSum n x y ij"
 "[if (lft ij+rht ij=n)
      ((1#PosF rht ij)*x**rht ij*((1#PosF lft ij)*y**lft ij)) 0]")

(set-totality-goal "RealEDiagSum")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "x")
(fold-alltotal)
(assume "y")
(fold-alltotal)
(assume "ij")
(ng #t)
(use "BooleIfTotal")
;; 11-13
(use "TotalVar")
;; 12
(use "TotalVar")
;; 13
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; RealSumDiagBinomAux
(set-goal "all m,x,y,xs(Real x -> Real y ->
 xs eqd([k]RealEDiagSum m x y(GqD m k)) ->
 all k Real(xs k) ->
 RealSum(Gs m)(Succ m)xs===(1#PosF m)*(x+y)**m)")
(assume "m" "x" "y" "xs" "Rx" "Ry" "xsDef" "Rxs")
(simpreal "RealSumZeroShiftDown")
(simpreal "RealBinomPosF")
(use "RealSumCompat")
(ng #t)
(assume "l" "Useless" "l<m+1")
(simp "xsDef")
(bpe-ng #t)
(simp "RealEDiagSum0CompRule")
;; ?^13:[if (lft(GqD m(Gs m+l))+rht(GqD m(Gs m+l))=m)
;;        ((1#PosF rht(GqD m(Gs m+l)))*x**rht(GqD m(Gs m+l))*
;;        ((1#PosF lft(GqD m(Gs m+l)))*y**lft(GqD m(Gs m+l))))
;;        0]===
;;      (1#PosF(m--l))*x**(m--l)*(1#PosF l)*y**l
;; Need that GqD(Gs m+l) is on the diagonal.
;; (pp "GsCM2")
;; all n,i,j(Gs n<=GsC(i pair j) -> GsC(i pair j)<Gs(Succ n) -> i+j=n)
;; To use it, we must show GqD m(Gs m+l)=GsD(Gs m+l) for l<Succ m

(assert "GqD m(Gs m+l)=GsD(Gs m+l)")
(simp "GqD0CompRule")
(simp (pf "(Gs m+l<Gs(Succ m))"))
(use "Truth")
(simp "GsEq")
(simp "NatLt4RewRule")
(use "l<m+1")
;; Assertion proved.
(assume "A1")
(simp "A1")

(assert "(lft(GsD(Gs m+l))+rht(GsD(Gs m+l))=m)")
(use "GsCM2" (pt "Gs m+l"))
;; (use "GsEqDiag" (pt "Gs m+l"))
(simp "<-" "NatPairEq")
(simp "GsCDId")
(use "Truth")
(simp "GsEq")
(simp "<-" "NatPairEq")
(simp "GsCDId")
(simp "NatLt4RewRule")
(use "l<m+1")
;; Assertion proved.
(assume "A2")
(simp "A2")
(simp "IfTrue")

(def "i" "lft(GsD(Gs m+l))")
(def "j" "rht(GsD(Gs m+l))")
(simp "<-" "iDef")
(simp "<-" "jDef")
(simphyp-with-to "A2" "<-" "iDef" "A2S")
(simphyp-with-to "A2S" "<-" "jDef" "A2SS")
(simp "<-" "A2SS")
;; ?^56:(1#PosF j)*x**j*((1#PosF i)*y**i)===
;;      (1#PosF(i+j--l))*x**(i+j--l)*(1#PosF l)*y**l
(simp "A2SS")

(assert "(i pair j)=GsD(Gs m+l)")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "A4")

(inst-with-to "GsCEq" (pt "i") (pt "j") "Inst")
(simphyp-with-to "Inst" "A2SS" "InstS")
(simphyp-with-to "InstS" "A4" "InstSS")
;; 69

(assert "i=l")
(use "NatPlusCancelL" (pt "Gs m"))
(simp "<-" "InstSS")
(simp "GsCDId")
(use "Truth")
;; Assertion proved.
(assume "A5")

(assert "m--l=j")
(simp "<-" "A2SS")
(simp "<-" "A5")
(simp "NatPlusComm")
(use "Truth")
;; Assertion proved.
(assume "A6")
(simp "A6")
(simp "<-" "A5")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
;; 4
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumDiagBinomAux")

;; We split the long sum (RealSum Zero(Succ m*Succ m)xs) into 3 parts
;; of lengths (Gs m), (Succ m) and (Gs m) using (pp "RealSumZerosLR").
;; The first and the last part will be 0, by the definition of
;; (display-pconst "RealEDiagSum").  The claim follows, since the
;; middle part is (1#PosF m)*(x+y)**m) by (pp "RealSumDiagBinomAux").

;; RealSumDiagBinom
(set-goal "all m,x,y,xs(
 Real x -> Real y ->
 xs eqd([k]RealEDiagSum m x y(GqD m k)) ->
 RealSum Zero(Succ(m*m+m+m))xs===(1#PosF m)*(x+y)**m)")
(assume "m" "x" "y" "xs" "Rx" "Ry" "xsDef")

(assert "all k Real(xs k)")
(assume "k")
(simp "xsDef")
(bpe-ng #t)
(simp "RealEDiagSum0CompRule")
(use "RealIfReal")
(autoreal)
;; Assertion proved.
(assume "Rxs")

(simpreal "<-" "RealSumSplitGs")
;; ?^12:RealSum Zero(Gs m)xs+RealSum(Gs m)(Succ m)xs+
;;      RealSum(Gs(Succ m))(Gs m)xs===
;;      (1#PosF m)*(x+y)**m

(assert "RealSum Zero(Gs m)xs===0")
(simp "xsDef")
(use "RealEqTrans" (pt "RealSum Zero(Gs m)([k]0)"))
;; 17,18
(use "RealSumCompat")
(assume "k" "Useless" "kBd")
(bpe-ng #t)
(simp (pf "GqD m k=GsD k"))
;; 22,23
(simp "RealEDiagSum0CompRule")

(assert "lft(GsD k)+rht(GsD k)<m")
(use "GsCL2")
;; (use "GsLtDiag2")
(simp "<-" "NatPairEq")
(simp "GsCDId")
(use "kBd")
;; 25
(assume "LtH")
(simp (pf "lft(GsD k)+rht(GsD k)=m -> F"))
(use "RealEqRefl")
(autoreal)
(assume "EqH")
(simphyp-with-to "LtH" "EqH" "Absurd")
(use "Absurd")
;; ?^23:GqD m k=GsD k
(simp "GqD0CompRule")
(simp (pf "k<Gs(Succ m)"))
(use "Truth")
(use "NatLtLeTrans" (pt "Gs m"))
(use "kBd")
(use "GsMon")
(use "Truth")
;; 18
(use "RealSumZeros")
(assume "n")
(use "RealEqRefl")
(autoreal)
;; 14
(assume "ZeroH")
(simpreal "ZeroH")
(drop "ZeroH")
(simpreal "RealZeroPlus")

;;?^49:RealSum(Gs m)(Succ m)xs+RealSum(Gs(Succ m))(Gs m)xs===(1#PosF m)*(x+y)**m
;; We prove that the sum of the reals in the upper triangle is 0
;; This can be simplified using RealSumZerosLR -- postponed

(assert "RealSum(Gs(Succ m))(Gs m)xs===0")
;; 51,52
(simp "xsDef")

(use "RealEqTrans" (pt "RealSum(Gs(Succ m))(Gs m)([k]0)"))
;; 54,55
(use "RealSumCompat")
(assume "k" "kLBd" "kUBd")
(bpe-ng #t)
;; ?^58:RealEDiagSum m x y(GqD m k)===0

(def "ij" "GqD m k")
(def "i" "lft ij")
(def "j" "rht ij")
(simp "<-" "ijDef")

;; ?^80:RealEDiagSum m x y ij===0
(simp "RealEDiagSum0CompRule")
(simp "<-" "ijDef")
(simp "<-" "iDef")
(simp "<-" "jDef")

;; It suffices to show "m<i+j".  This is done by unfolding the
;; definitions of GqD and its parts GdsCToMl, GqMlToIj.

(def "k0" "k--Gs(Succ m)")
(def "ml0" "GdsCToMl m k0")
(def "m0" "lft ml0")
(def "l0" "rht ml0")

(assert "ml0=(m0 pair l0)")
(simp "m0Def")
(simp "l0Def")
(use "NatPairEq")
;; Assertion proved.
(assume "A1")
(simphyp-with-to "ml0Def" "A1" "ml0DefS")

(assert "GqD m k=(Succ(m0+l0) pair m--l0)")
(simp "GqD0CompRule")
(simp (pf "k<Gs(Succ m) -> F"))
(simp "IfFalse")
(simp "<-" "k0Def")
(simp "<-" "ml0DefS")
(simp "GqMlToIj0CompRule")
(use "Truth")
;; 123
(assume "k<Gs(m+1)")
(assert "k<k")
(use "NatLtLeTrans" (pt "Gs(Succ m)"))
(use "k<Gs(m+1)")
(use "kLBd")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
;; 119
(assume "A2")

(assert "k--Gs(Succ m)<Gs m")
(simp "<-" "NatLtPlusMinus")
;; (use "NatLtMinus")
(simp "NatPlusComm")
(use "kUBd")
(use "kLBd")
;; Assertion proved.
(assume "A3")
(simphyp-with-to "A3" "<-" "k0Def" "A3S")

(assert "(i pair j)=(Succ(m0+l0)pair m--l0)")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(simp "ijDef")
(simp "GqD0CompRule")
(simp (pf "k<Gs(Succ m) -> F"))
(simp "IfFalse")
(simp "<-" "k0Def")
(simp "<-" "ml0DefS")
(simp "GqMlToIj0CompRule")
(use "Truth")
(assume "kBd")
(assert "k<k")
(use "NatLtLeTrans" (pt "Gs(Succ m)"))
(use "kBd")
(use "kLBd")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "A4")
(ng "A4")
;; 163

(assert "i+j=m -> F")
(assume "i+j=m")
(inst-with-to "A4" 'left "iEq")
(inst-with-to "A4" 'right "jEq")
(simphyp-with-to "i+j=m" "iEq" "A5")
(simphyp-with-to "A5" "jEq" "A6")
(ng "A6")
;;   A5:Succ(m0+l0)+j=m
;;   A6:Succ(m0+l0+(m--l0))=m
;; -----------------------------------------------------------------------------
;; ?^175:F

(assert "l0<m--m0")
(inst-with-to "GdsCToMlProp" (pt "m") (pt "k0") "A3S" "Inst")
(simphyp-with-to "Inst" "<-" "ml0DefS" "InstS")
(use "InstS")
;; Assertion proved.
(assume "A7")

(assert "l0<m")
(use "NatLtLeTrans" (pt "m--m0"))
(use "A7")
(use "Truth")
;; Assertion proved.
(assume "l0<m")

(assert (pf "m0+l0+(m--l0)=m0+m"))
(simp "<-" "NatPlusAssoc")
(simp (pf "l0+(m--l0)=m"))
(use "Truth")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "l0<m")
;; Assertion proved.
(assume "A8")
(simphyp-with-to "A6" "A8" "A6S")
(assert "m<Succ(m0+m)")
(use "NatLeLtTrans" (pt "m0+m"))
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "A9")
(simphyp-with-to "A9" "A6S" "Absurd")
(use "Absurd")
;; 164
(assume "NegH")
(simp "NegH")
(use "RealEqRefl")
(autoreal)
;; ?^55:RealSum(Gs(Succ m))(Gs m)([n]0)===0
(use "RealSumZeros")
(assume "n")
(use "RealEqRefl")
(autoreal)

;; ?^51:RealSum(Gs(Succ m))(Gs m)xs===0 -> 
;;      RealSum(Gs m)(Succ m)xs+RealSum(Gs(Succ m))(Gs m)xs===
;;      (1#PosF m)*(x+y)**m

(assume "RZero")
(simpreal "RZero")
(simpreal "RealPlusZero")
;; ?^214:RealSum(Gs m)(Succ m)xs===(1#PosF m)*(x+y)**m

(use "RealSumDiagBinomAux")
(autoreal)
(use "xsDef")
(use "Rxs")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumDiagBinom")

;; End of the previous examplesanalysiseser2.scm
;; RealEAbsConvCor1 (was RealESerConv)
(set-goal "all x(Real x -> RealSerConv([n]abs((1#PosF n)*x**n))(cREMod x))")
(assume "x" "Rx")

;; Defs
(def "xs" "[n](1#PosF n)*x**n")
(def "l" "RealEModOne x") ; =PosToNat(2**cRBound(2*abs x))
(def "q" "RealEModTwo x") ; =NatToPos(Succ(cRBound(xs l)))
(def "M" "[p]PosS(q+p)+l")

;; (use "RealExpSerAbsConv" (pt "x") (pt "l") (pt "q")) ;missing
;; Was in examplesanalysiseser1.scm, with xs n eqd ... (stronger hypothesis)

(use "RealEAbsConv" (pt "x") (pt "l") (pt "q"))
;; RealEAbsConv 1
(use "Rx")

;; RealEAbsConv 2
(use "RealLeTrans" (pt "l"))
;; RealLeTrans 1
(simp "lDef")
(simp "RealEModOne0CompRule")
(use "RealLeTrans" (pt "RealTimes 2 (2**cRBound x)"))
;;; RealLeTrans 1
(use "RealLeMonTimesR")
;; RealLeMonTimesR 1
(use "RatLeToRealLe")
(use "Truth")
;; RealLeMonTimesR 2
(use "RealBoundProp1")
(use "Rx")
;; RealLeTrans 2
(simp "PosToNatToIntId")
(use "RatLeToRealLe")
(use "Truth")

;; RealLeTrans 2
(use "RatLeToRealLe")
(use "Truth")

;; RealEAbsConv 3
(ng #t)
(simp "qDef")
(use "RealLeTrans" (pt "2**cRBound((1#PosF l)*(abs x)**l)"))
;; RealLeTrans 1
(use "RealLeTrans" (pt "abs((1#PosF l)*(abs x)**l)"))
;; RealLeTrans 1
(simpreal "RealAbsTimes")
;; RealAbsTimes 1
(simpreal "RealAbsExp")
;; RealAbsExp 1
(ng #t)
(use "RealLeIdAbs")
(realproof)
;; RealAbsExp 2
(realproof)
;; RealAbsTimes 2
(realproof)
;; RealAbsTimes 3
(realproof)
;;; RealLeTrans 2
(use "RealBoundProp1")
(realproof)
;; RealLeTrans 2
(use "RatLeToRealLe")
(simp "RealEModTwo0CompRule")
(simp "REModOneExFree")
(simp "<-" "lDef")
(use "NatLeMonTwoExp")
(simp "NatPosExFree")

(simp "PosToNatToPosId")
(use "Truth")
(simp "RBoundExFree")
(use "Truth")
(autoreal)

;; (use "NatLePosToNatToPos")
;; (use "Truth")

;; RealEAbsConv 4
(assume "n")
(ng #t)
(simpreal "RealAbsTimes")
;; RealAbsTimes 1
(simpreal "RealAbsExp")
;; RealAbsExp 1
(use "RealEqRefl")
(realproof)
;; RealAbsExp 2
(realproof)
;; RealAbsTimes 2
(realproof)
;; RealAbsTimes 3
(realproof)

;; RealEAbsConv 5
(assume "p")
(simp "REModExFree")
(ng #t)
(simp "REModOneExFree")
(simp "REModTwoExFree")
(simp "<-" "lDef")
(simp "<-" "qDef")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEAbsConvCor1") ;was RealESerConv

;; RealEConv
(set-goal "all x(Real x -> RealSerConv([n](1#PosF n)*x**n)(RealEMod x))")
(assume "x" "Rx")
(use "RealSerAbsConvToConv")
;; 3,4
(assume "n")
(realproof)
 ;; 4
(bpe-ng #t)
;; ?^6:RealSerConv([n]abs((1#PosF n)*x**n))(RealEMod x)
(use "RealSerConvCompat" (pt "[n](1#PosF n)*abs x**n") (pt "RealEMod x"))
;; 7-9
(assume "n")
(bpe-ng #t)
(simpreal "RealAbsTimes")
(simpreal "RealAbsExp")
(use "RealEqRefl")
(autoreal)
;; 8
(assume "p")
(use "Truth")
;; ?^9:RealSerConv([n](1#PosF n)*abs x**n)(RealEMod x)
(use "RealEAbsConvCor")
(use "Rx")
;; Proof finished.
;; (cp)
(save "RealEConv")

;; Thus from the absolute convergence of the exponential series

;; (pp "RealEAbsConvCor")
;; all x(Real x -> RealSerConv([n](1#PosF n)*abs x**n)(RealEMod x))

;; and from the general fact that absolute convergence implies covergence

;; (pp "RealSerAbsConvToConv")
;; all xs,M(all n Real(xs n) -> RealSerConv([n]abs(xs n))M -> RealSerConv xs M)

;; we have proved the convergence of the exponential series, with the
;; same modulus (RealEMod x)

;; (pp "RealEConv")
;; all x(Real x -> RealSerConv([n](1#PosF n)*x**n)(RealEMod x))

;; RealEConvLim
(set-goal "all x(Real x -> RealConvLim(cRESeq x)(cRE x)(cREMod x))")
(assume "x" "Rx")
(simp "REExFree")
(use "RealCompleteCor")
(simp "RESeqExFree")
(ng #t)
(use-with "RealCauchyShiftUpWithoutMod"
	  (pt "([n0]cRSum Zero n0([n1](1#PosF n1)*x**n1))")
	  (pt "cREMod x") (pt "Succ Zero") "?")
(use "RealSerConvToCauchy")
(use "RealSerAbsConvToConv")
;; RealSerAbsConvToConv 1
(assume "n")
(realproof)
;; RealSerAbsConvToConv 2
(bpe-ng #t)
;; ?^12:RealSerConv([n]abs((1#PosF n)*x**n))(cREMod x)
(use "RealEAbsConvCor1")
(use "Rx")
;; Proof finished.
;; (cp)
(save "RealEConvLim")

;; RealEModMon
(set-goal "all x(Real x -> Mon(cREMod x))")
(assume "x" "Rx")
(intro 0)
(assume "p" "q" "p<=q")
(simp "REModExFree")
(ng #t)
(simp "PosToNatLe")
(ng #t)
(use "p<=q")
;; Proof finished.
;; (cp)
(save "RealEModMon")

;; RealCauchyProdLimECor (was RealCauchyProdLimExpCor)
(set-goal "all xs0,ys0,x,y(
 Real x ->
 Real y ->
 xs0 eqd [n](1#PosF n)*x**n ->
 ys0 eqd [n](1#PosF n)*y**n ->
 exl K(
   Mon K andnc
   all r,n(
     K r<=n -> 
     abs(RealSum Zero(Succ(n*n+n+n))
       ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs0(lft(RtD k))*ys0(rht(RtD k))) 0])+
       ~((cRE x)*(cRE y)))<<=
  (1#2**r))))")
(assume "xs0" "ys0" "x" "y" "Rx" "Ry" "xs0Def" "ys0Def")

;; Defs
(def "xs1" "[n]cRSum Zero n([i]abs(xs0 i))")
(def "ys1" "[n]cRSum Zero n([j]abs(ys0 j))")

(def "M0" "[p]Succ(cREMod x p)")
(defnc "x0" "cRE x")
(def "N0" "[p]Succ (cREMod y p)")
(defnc "y0" "cRE y")

(def "M1" "cREMod x")
(def "N1" "cREMod y")
(def "p0" "NatToPos (Succ (cRSeqBd xs1 M1))")
(def "q0" "NatToPos (Succ (cRSeqBd ys1 N1))")
(def "K0" "[r]N0(p0+r+1)max M0(q0+r+1)")
(def "K1" "[r]N1(p0+r+1)max M1(q0+r+1)")
(def "K"  "[r](K1(PosS r)+K1(PosS r))max K0(PosS r)")

;; Assertions

;; xs0SerLim
(assert "RealConvLim([n]RealSum Zero n xs0)x0 M0")
;; 94,95
(simp "M0Def")
(simp (pf "[p]Succ(cREMod x p) eqd [p]cREMod x p+1"))
;; Simp 1
(use "RealConvLimShiftDown")
;; RealConvLimShiftDown 1
(assume "n")
(simp "xs0Def")
(realproof)
;; RealConvLimShiftDown 2
(bpe-ng #t)
;; ?^103:RealConvLim([k]RealSum Zero(k+1)xs0)x0(cREMod x)
(simp (pf "([k]RealSum Zero(k+1)xs0)eqd cRESeq x"))
;; Simp 1
(simp "x0Def")
(use "RealEConvLim")
(use "Rx")
;; Simp 2
(simp "xs0Def")
(simp "RESeqExFree")
(ng #t)
(simp "cRSumEqDRealSum")
(use "InitEqD")
;; Simp 3
(ng #t)
(use "InitEqD")
;; Assertion proved.
(assume "xs0SerLim")

;; ys0SerLim
(assert "RealConvLim([n]RealSum Zero n ys0)y0 N0")
;; 115,116
(simp "N0Def")
(simp (pf "[p]Succ(cREMod y p) eqd [p]cREMod y p+1"))
;; Simp 1
(use "RealConvLimShiftDown")
;; RealConvLimShiftDown 1
(assume "n")
(simp "ys0Def")
(realproof)
;; RealConvLimShiftDown 2
(bpe-ng #t)
(simp (pf "([k]RealSum Zero(k+1)ys0)eqd cRESeq y"))
;;; Simp 1
(simp "y0Def")
(use "RealEConvLim")
(use "Ry")
;; Simp 2
(simp "ys0Def")
(simp "RESeqExFree")
(ng #t)
(simp "cRSumEqDRealSum")
(use "InitEqD")
;; Simp 3
(ng #t)
(use "InitEqD")
;; Assertion proved.
(assume "ys0SerLim")

;; RC xs1 M1
(assert "RealCauchy xs1 M1")
(simp "xs1Def")
(use "RealSerConvToCauchy")
(simp "xs0Def")
(simp "M1Def")
(ng #t)
(use "RealEAbsConvCor1")
(use "Rx")
;; Assertion proved.
(assume "RC xs1 M1")

;; RC ys1 N1
(assert "RealCauchy ys1 N1")
(simp "ys1Def")
(use "RealSerConvToCauchy")
(simp "ys0Def")
(simp "N1Def")
(ng #t)
(use "RealEAbsConvCor1")
(use "Ry")
;; Assertion proved.
(assume "RC ys1 N1")

;; xs1Bound
(assert "all n xs1 n<<=2**p0")
(assume "n")
(use "RealLeTrans" (pt "2**(cRSeqBd xs1 M1)"))
;; RealLeTrans 1
(use "RealAbsLe")
;; RealAbsLe 1
(simp "xs1Def")
(simp "xs0Def")
(ng #t)
(simp "RSumExFree")
(realproof)
;; RealAbsLe 2
(use "RealSeqBdPos")
(use "RC xs1 M1")
;; RealLeTrans 2
(use "RatLeToRealLe")
(use "NatLeMonTwoExp")
(simp "p0Def")
(simp "PosToNatToPosId")
;; PosToNatToPosId 1
(use "Truth")
;; PosToNatToPosId 2
(use "Truth")
;; Assertion proved.
(assume "xs1Bound")

;; ys1Bound
(assert "all n ys1 n<<=2**q0")
(assume "n")
(use "RealLeTrans" (pt "2**(cRSeqBd ys1 N1)"))
;; RealLeTrans 1
(use "RealAbsLe")
;; RealAbsLe 1
(simp "ys1Def")
(simp "ys0Def")
(ng #t)
(simp "RSumExFree")
(realproof)
;; RealAbsLe 2
(use "RealSeqBdPos")
(use "RC ys1 N1")
;; RealLeTrans 2
(use "RatLeToRealLe")
(use "NatLeMonTwoExp")
(simp "q0Def")
(simp "PosToNatToPosId")
;; PosToNatToPosId 1
(use "Truth")
;; PosToNatToPosId 2
(use "Truth")
;; Assertion proved.
(assume "ys1Bound")

;; Mon K0
(assert "Mon K0")
(intro 0)
(assume "p" "q" "p<=q")
(simp "K0Def")
(ng #t)
(use "NatLeMonMax")
;; NatLeMonMax 1
(simp "N0Def")
(ng #t)
(use "MonElim")
;; MonElim 1
(use "RealEModMon")
(use "Ry")
;; MonElim 2
(use "p<=q")
;; NatLeMonMax 2
(simp "M0Def")
(ng #t)
(use "MonElim")
;; MonElim 1
(use "RealEModMon")
(use "Rx")
;; MonElim 2
(use "p<=q")
;; Assumption proved.
(assume "Mon K0")

;; Mon K1
(assert "Mon K1")
(intro 0)
(assume "p" "q" "p<=q")
(simp "K1Def")
(ng #t)
(use "NatLeMonMax")
;; NatLeMonMax 1
(simp "N1Def")
(ng #t)
(use "MonElim")
;; MonElim 1
(use "RealEModMon")
(use "Ry")
;; MonElim 2
(use "p<=q")
;; NatLeMonMax 2
(simp "M1Def")
(ng #t)
(use "MonElim")
;; MonElim 1
(use "RealEModMon")
(use "Rx")
;; MonElim 2
(use "p<=q")
;; Asserion proved.
(assume "Mon K1")

;; Mon K
(assert "Mon K")
(intro 0)
(assume "p" "q" "p<=q")
(simp "KDef")
(use "NatLeMonMax")
;; NatLeMonMax 1
(use "NatLeMonPlus")
;; NatLeMonPlus 1
(use "MonElim")
;; MonElim 1
(use "Mon K1")
;; MonElim 2
(use "p<=q")
;; NatLeMonPlus 2
(use "MonElim")
;; MonElim 1
(use "Mon K1")
;; MonElim 2
(use "p<=q")
;; NatLeMonMax 2
(use "MonElim")
;; MonElim 1
(use "Mon K0")
;; MonElim 2
(use "p<=q")
;; Assertion proved.
(assume "Mon K")

;; Proof
(intro 0 (pt "K"))

(split)

;; Split 1
(use "Mon K")
(assume "r" "n")
(assume "ModBound")
;; Split 2

;;   xs0  ys0  x  y  Rx:Real x
;;   Ry:Real y
;;   xs0Def:xs0 eqd([n](1#PosF n)*x**n)
;;   ys0Def:ys0 eqd([n](1#PosF n)*y**n)
;;   xs1  xs1Def:xs1 eqd([n]cRSum Zero n([i]abs(xs0 i)))
;;   ys1  ys1Def:ys1 eqd([n]cRSum Zero n([j]abs(ys0 j)))
;;   M0  M0Def:M0 eqd([p]Succ(cREMod x p))
;;   {x0}  x0Def:x0 eqd cRE x
;;   N0  N0Def:N0 eqd([p]Succ(cREMod y p))
;;   {y0}  y0Def:y0 eqd cRE y
;;   M1  M1Def:M1 eqd cREMod x
;;   N1  N1Def:N1 eqd cREMod y
;;   p0  p0Def:p0 eqd NatToPos(Succ(cRSeqBd xs1 M1))
;;   q0  q0Def:q0 eqd NatToPos(Succ(cRSeqBd ys1 N1))
;;   K0  K0Def:K0 eqd([r]N0(p0+r+1)max M0(q0+r+1))
;;   K1  K1Def:K1 eqd([r]N1(p0+r+1)max M1(q0+r+1))
;;   K  KDef:K eqd([r](K1(PosS r)+K1(PosS r))max K0(PosS r))
;;   xs0SerLim:RealConvLim([n]RealSum Zero n xs0)x0 M0
;;   ys0SerLim:RealConvLim([n]RealSum Zero n ys0)y0 N0
;;   RC xs1 M1:RealCauchy xs1 M1
;;   RC ys1 N1:RealCauchy ys1 N1
;;   xs1Bound:all n xs1 n<<=2**p0
;;   ys1Bound:all n ys1 n<<=2**q0
;;   Mon K0:Mon K0
;;   Mon K1:Mon K1
;;   Mon K:Mon K
;;   r  n  ModBound:K r<=n
;; -----------------------------------------------------------------------------
;; ?^246:abs(RealSum Zero(Succ(n*n+n+n))
;;           ([k]
;;             [if (lft(RtD k)+rht(RtD k)<=n) (xs0 lft(RtD k)*ys0 rht(RtD k)) 0])+ 
;;           ~(cRE x*cRE y))<<=
;;       (1#2**r)

(simp "<-" "x0Def")
(simp "<-" "y0Def")
(use "RealCauchyProdLimE"
     (pt "x") (pt "y") (pt "M0") (pt "N0") (pt "p0") (pt "q0") (pt "K0")
     (pt "xs1") (pt "ys1") (pt "M1") (pt "N1") (pt "p0") (pt "q0") (pt "K1"))
;; RealCauchyProdLimE 1
(use "Rx")
;; RealCauchyProdLimE 2
(use "Ry")
;; RealCauchyProdLimE 3
(assume "n0")
(simp "xs0Def")
(use "RealEqRefl")
(realproof)
;; RealCauchyProdLimE 4
(assume "n0")
(simp "ys0Def")
(use "RealEqRefl")
(realproof)
;; RealCauchyProdLimE 5
(simp "<-" "x0Def")
(use "xs0SerLim")
;; RealCauchyProdLimE 6
(simp "<-" "y0Def")
(use "ys0SerLim")
;; RealCauchyProdLimE 7
(assume "n0")
(use "RealLeTrans" (pt "xs1 n0"))
;; RealLeTrans 1
(simp "xs1Def")
(ng #t)
(simp "RSumExFree")
(use "RealLeAbsSum")
(assume "n1")
(simp "xs0Def")
(realproof)
;;; RealLeTrans 2
(use "xs1Bound")
;; RealCauchyProdLimE 8
(assume "n0")
(use "RealLeTrans" (pt "ys1 n0"))
;;; RealLeTrans 1
(simp "ys1Def")
(ng #t)
(simp "RSumExFree")
(use "RealLeAbsSum")
(assume "n1")
(simp "ys0Def")
(realproof)
;;; RealLeTrans 2
(use "ys1Bound")
;; RealCauchyProdLimE 9
(assume "r0")
(simp "K0Def")
(use "Truth")
;; RealCauchyProdLimE 10
(assume "n0")
(simp "xs1Def")
(ng #t)
(simp "RSumExFree")
(use "RealEqRefl")
(simp "xs0Def")
(realproof)
;; RealCauchyProdLimE 11
(assume "n0")
(simp "ys1Def")
(ng #t)
(simp "RSumExFree")
(use "RealEqRefl")
(simp "ys0Def")
(realproof)
;; RealCauchyProdLimE 12
(use "RC xs1 M1")
;; RealCauchyProdLimE 13
(use "RC ys1 N1")
;; RealCauchyProdLimE 14
(use "xs1Bound")
;; RealCauchyProdLimE 15
(use "ys1Bound")
;; RealCauchyProdLimE 16
(assume "r0")
(simp "K1Def")
(use "Truth")
;; RealCauchyProdLimE 17
(simphyp-to "ModBound" "KDef" "ModBoundExp")
(use "ModBoundExp")
;; Proof finished.
;; (cp)
(save "RealCauchyProdLimECor")

;; 2024-12-30

;; For RealSumEqDiag we need permutations to deal with the different
;; order of reals (xs k) w.r.t. Rt coding and Gs coding

;; (remove-program-constant "PmOd")
(add-program-constant "PmOd" (py "nat=>nat=>nat"))
(add-computation-rules
 "PmOd Zero k" "k"
 "PmOd(Succ n)k"
 "[if (k<Succ(Succ(n+n))) (Succ(PmOd n k)) [if (k=Succ(Succ(n+n))) Zero k]]")

(set-totality-goal "PmOd")
(assert
 "all k^(TotalNat k^ -> all n^(TotalNat n^ -> TotalNat(PmOd n^ k^)))")
(fold-alltotal)
(assume "k")
(fold-alltotal)
(ind)
(use "TotalVar")
(assume "n" "IH")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalNatSucc")
(use "IH")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; Assertion proved.
(assume "A")
(search)
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "PmOd 1 Zero")))
;; (pp (nt (pt "PmOd 1 1")))
;; (pp (nt (pt "PmOd 1 2")))
;; (pp (nt (pt "PmOd 1 3")))
;; (pp (nt (pt "PmOd 1 4")))
;; (pp (nt (pt "PmOd 1 5")))

;; > Succ Zero
;; > Succ(Succ Zero)
;; > Zero
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ(Succ(Succ(Succ Zero))))

;; (pp (nt (pt "PmOd 2 Zero")))
;; (pp (nt (pt "PmOd 2 1")))
;; (pp (nt (pt "PmOd 2 2")))
;; (pp (nt (pt "PmOd 2 3")))
;; (pp (nt (pt "PmOd 2 4")))
;; (pp (nt (pt "PmOd 2 5")))
;; (pp (nt (pt "PmOd 2 6")))
;; (pp (nt (pt "PmOd 2 7")))

;; > Succ(Succ Zero)
;; > Succ(Succ(Succ Zero))
;; > Succ Zero
;; > Succ(Succ(Succ(Succ Zero)))
;; > Zero
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))

;; (pp (nt (pt "PmOd 3 Zero")))
;; (pp (nt (pt "PmOd 3 1")))
;; (pp (nt (pt "PmOd 3 2")))
;; (pp (nt (pt "PmOd 3 3")))
;; (pp (nt (pt "PmOd 3 4")))
;; (pp (nt (pt "PmOd 3 5")))
;; (pp (nt (pt "PmOd 3 6")))
;; (pp (nt (pt "PmOd 3 7")))
;; (pp (nt (pt "PmOd 3 8")))
;; (pp (nt (pt "PmOd 3 9")))

;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ Zero)
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ Zero
;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Zero
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))))

(add-program-constant "PmOdInv" (py "nat=>nat=>nat"))
(add-computation-rules
 "PmOdInv Zero k" "k"
 "PmOdInv(Succ n)k"
 "[if (k=Zero) (Succ(Succ(n+n)))
      [if (Succ(Succ(n+n))<k) k (PmOdInv n(Pred k))]]")

(set-totality-goal "PmOdInv")
(fold-alltotal)
(assert "all n,k TotalNat(PmOdInv n k)")
(ind)
(assume "k")
(use "TotalVar")
(assume "n" "IH")
(assume "k")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "IH")
;; Assertion proved.
(assume "A" "n")
(fold-alltotal)
(use "A")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "PmOdInv 1 Zero")))
;; (pp (nt (pt "PmOdInv 1 1")))
;; (pp (nt (pt "PmOdInv 1 2")))
;; (pp (nt (pt "PmOdInv 1 3")))
;; (pp (nt (pt "PmOdInv 1 4")))

;; > Succ(Succ Zero)
;; > Zero
;; > Succ Zero
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ Zero)))

;; (pp (nt (pt "PmOdInv 2 Zero")))
;; (pp (nt (pt "PmOdInv 2 1")))
;; (pp (nt (pt "PmOdInv 2 2")))
;; (pp (nt (pt "PmOdInv 2 3")))
;; (pp (nt (pt "PmOdInv 2 4")))
;; (pp (nt (pt "PmOdInv 2 5")))
;; (pp (nt (pt "PmOdInv 2 6")))

;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ Zero)
;; > Zero
;; > Succ Zero
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))

;; (pp (nt (pt "PmOdInv 3 Zero")))
;; (pp (nt (pt "PmOdInv 3 1")))
;; (pp (nt (pt "PmOdInv 3 2")))
;; (pp (nt (pt "PmOdInv 3 3")))
;; (pp (nt (pt "PmOdInv 3 4")))
;; (pp (nt (pt "PmOdInv 3 5")))
;; (pp (nt (pt "PmOdInv 3 6")))
;; (pp (nt (pt "PmOdInv 3 7")))
;; (pp (nt (pt "PmOdInv 3 8")))

;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ Zero)
;; > Zero
;; > Succ Zero
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))

;; (pp (nt (pt "PmOdInv 2(PmOd 2 Zero)")))
;; > Zero

;; (display-pconst "PmOd" "PmOdInv")

;; PmOd(Succ n)k
;; [if (k<Succ(Succ(n+n))) (Succ(PmOd n k)) [if (k=Succ(Succ(n+n))) Zero k]]

;; PmOdInv(Succ n)k
;;[if (k=Zero) (Succ(Succ(n+n))) [if (Succ(Succ(n+n))<k) k (PmOdInv n(Pred k))]]

;; PmOdEqStep
(set-goal "all k,n(k<Succ(Succ(n+n)) ->  PmOd(Succ n)k=Succ(PmOd n k))")
(assume "k" "n" "LtH")
(simp "PmOd1CompRule")
(simp "LtH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PmOdEqStep")

(set-goal "all k,n(k=n+n ->  PmOd n k=Zero)")
(assume "k")
(cases)
(assume "k=0")
(simp "k=0")
(use "Truth")
(assume "n" "EqH")
(simp "<-" "EqH")
(simp "<-" "EqH")
(use "Truth")
;; Proof finished.

;; PmOdZero
(set-goal "all n PmOd n(n+n)=Zero")
(cases)
(use "Truth")
(assume "n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PmOdZero")

;; (display-pconst "PmOd")
;; (search-about "PmOdInv")

;; PmOdEqZero
(set-goal "all n PmOd n(n+n)=Zero")
(cases)
(use "Truth")
(assume "n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PmOdEqZero")

;; PmOdEqId
(set-goal "all k,n(Succ(Succ(n+n))<k ->  PmOd(Succ n)k=k)")
(assume "k" "n" "LtH")
(ng #t)
(simp (pf "k<Succ(Succ(n+n)) -> F"))
(simp (pf "k=Succ(Succ(n+n)) -> F"))
(use "Truth")
(assume "kEq")
(simphyp-to "LtH" "kEq" "Absurd")
(use "Absurd")
;; ?^5:k<Succ(Succ(n+n)) -> F
(assume "LtH1")
(assert "k<k")
(use "NatLtTrans" (pt "Succ(Succ(n+n))"))
(use "LtH1")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PmOdEqId")

;; PmOdInvEqZero
(set-goal "all n PmOdInv n Zero=n+n")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PmOdInvEqZero")

;; PmOdInvEqId
(set-goal "all k,n(Succ(Succ(n+n))<k ->  PmOdInv(Succ n)k=k)")
(assume "k" "n" "LtH")
(ng #t)
(simp (pf "k=Zero -> F"))
(simp "LtH")
(use "Truth")
;; ?^5:k=Zero -> F
(assume "k=0")
(simphyp-to "LtH" "k=0" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PmOdInvEqId")

;; PmOdInvEqStep
(set-goal "all k,n(k<Succ(Succ(n+n)) -> PmOdInv(Succ n)(Succ k)=(PmOdInv n k))")
(assume "k" "n" "LtH")
(simp "PmOdInv1CompRule")
(ng #t)
(simp (pf "Succ(n+n)<k -> F"))
(use "Truth")
(assume "LtH1")
(assert "k<k")
(use "NatLeLtTrans" (pt "Succ(n+n)"))
(use "NatLtSuccToLe")
(use "LtH")
(use "LtH1")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PmOdInvEqStep")

(set-goal "all n PmOd n Zero=n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)

(set-goal "all n PmOdInv n n=Zero")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp (pf "Succ(n+n)<n -> F"))
(use "IH")
(simp "<-" "NatPlus1CompRule")
(simp "NatLt5RewRule")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(cp)

;; PmOdAtZero
(set-goal "all n PmOd n Zero=n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "PmOdAtZero")

;; PmOdBd
(set-goal "all n,k(k<Succ(Succ(n+n)) -> PmOd n k<Succ(Succ(n+n)))")
(ind)
;; 2,3
(ng)
(assume "k" "LtH")
(use "LtH")
(assume "n" "IH" "k" "kBd")
(use "NatLtSuccCases" (pt "k") (pt "Succ(Succ n+Succ n)"))
;; 7-9
(use "kBd")
;; ?^8:k<Succ(Succ n+Succ n) -> PmOd(Succ n)k<Succ(Succ(Succ n+Succ n))
(drop "kBd")
(assume "kBd1")
(ng "kBd1")
(use "NatLtSuccCases" (pt "k") (pt "Succ(Succ(n+n))"))
;; 13-15
(use "kBd1")
;; ?^14:k<Succ(Succ(n+n)) -> PmOd(Succ n)k<Succ(Succ(Succ n+Succ n))
(drop "kBd1")
(assume "kBd2")
(simp "PmOd1CompRule")
(simp "kBd2")
(ng #t)
(use "NatLtTrans" (pt "Succ(Succ(n+n))"))
;; 21,22
(use "IH")
(use "kBd2")
;; 22
(use "Truth")
;; 15
(drop "kBd1")
(assume "kEq")
(simp "PmOd1CompRule")
(simp "kEq")
(simp "kEq")
(use "Truth")
;; 9
(assume "kEq")
(drop "kBd")
(ng "kEq")
(simp "PmOd1CompRule")
(simp "kEq")
(ng #t)
(simp (pf "Succ(n+n)=n+n -> F"))
(use "Truth")
;; ?^36:Succ(n+n)=n+n -> F
(assert "all m(Succ m=m -> F)")
(ind)
(assume "Absurd")
(use "Absurd")
(ng #t)
(assume "m" "NH")
(use "NH")
;; Assertion proved.
(assume "A1")
(use "A1")
;; Proof finished.
;; (cp)
(save "PmOdBd")

;; PmOdId1
(set-goal "all n,k PmOdInv n(PmOd n k)=k")
(ind)
(assume "k")
(use "Truth")
(assume "n" "IH" "k")
;; ?^5:PmOdInv(Succ n)(PmOd(Succ n)k)=k
(use "NatLeLtCases" (pt "Succ(Succ(n+n))") (pt "k"))
;; 6,7
(assume "LeH")
(use "NatLeCases" (pt "Succ(Succ(n+n))") (pt "k"))
(use "LeH")
(assume "LtH")
(simp "PmOdEqId")
;; ?^13:PmOdInv(Succ n)k=k
(use "PmOdInvEqId")
(use "LtH")
(use "LtH")
;; ?^11:Succ(Succ(n+n))=k -> PmOdInv(Succ n)(PmOd(Succ n)k)=k
(assume "EqH")
(inst-with-to "PmOdZero" (pt "Succ n") "Inst")
(simphyp-to "Inst" (pf "Succ n+Succ n=Succ(Succ(n+n))") "InstS")
(simphyp-with-to "InstS" "EqH" "InstSS")
(simp "InstSS")
;; ?^24:PmOdInv(Succ n)Zero=k
(simp "PmOdInvEqZero")
(use "EqH")
(use "Truth")
;; ?^7:k<Succ(Succ(n+n)) -> PmOdInv(Succ n)(PmOd(Succ n)k)=k
(assume "LtH")
(simp "PmOdEqStep")
(inst-with "PmOdInvEqStep" (pt "PmOd n k") (pt "n") "?")
(simp 3)
(use "IH")
;; ?^29:PmOd n k<Succ(Succ(n+n))
(use "PmOdBd")
(use "LtH")
(use "LtH")
;; Proof finished.
;; (cp)
(save "PmOdId1")

;; PmOdInvBd
(set-goal "all n,k(k<Succ(Succ(n+n)) -> PmOdInv n k<Succ(Succ(n+n)))")
(ind)
;; 2,3
(assume "k" "LtH")
(use "LtH")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(assume "Useless")
(use "NatLtTrans" (pt "Succ(n+n)"))
(use "Truth")
(use "Truth")
(assume "k" "kBd")
(ng "kBd")
(use "NatLtSuccCases" (pt "k") (pt "Succ(Succ(n+n))"))
;; 14-16
(use "kBd")
(drop "kBd")
(assume "kBd1")
(simp "PmOdInv1CompRule")
(ng #t)
(cases (pt "Succ(n+n)<k"))
;; 21,22
(assume "Useless")
(ng #t)
(use "NatLtTrans" (pt "Succ(Succ(n+n))"))
(use "kBd1")
(use "Truth")
;; 22
(drop "kBd1")
(assume "kH")
(assert "k<Succ(Succ(n+n))")
(use "NatLeToLtSucc")
(use "NatNotLtToLe")
(use "kH")
;; Assertion proved.
(assume "kBd2")
(drop "kH")
(ng #t)
(use "NatLtTrans" (pt "Succ(Succ(n+n))"))
(use "IH")
(use "kBd2")
(ng #t)
(use "NatLtTrans" (pt "Succ(n+n)"))
(use "Truth")
(use "Truth")
;; ?^16:k=Succ(Succ(n+n)) -> PmOdInv(Succ n)(Succ k)<Succ(Succ(Succ n+Succ n))
(assume "kEq")
(drop "kBd")
(simp "PmOdInv1CompRule")
(ng #t)
(simp "kEq")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PmOdInvBd")

;; PmOdInvEqStep
;; all k,n(k<Succ(Succ(n+n)) -> PmOdInv(Succ n)(Succ k)=PmOdInv n k)

;; PmOdId2
(set-goal "all n,k PmOd n(PmOdInv n k)=k")
(ind)
(assume "k")
(use "Truth")
(assume "n" "IH")
(cases)
;; 6,7
(use "Truth")
(assume "k")
;; ?^8:PmOd(Succ n)(PmOdInv(Succ n)(Succ k))=Succ k
(cases (pt "k<Succ(Succ(n+n))"))
;; 9,10
(assume "kBd")
(simp "PmOdInvEqStep")
(simp "PmOd1CompRule")
(simp "IH")
;; ?^15:[if (PmOdInv n k<Succ(Succ(n+n)))
;;        (Succ k)
;;        [if (PmOdInv n k=Succ(Succ(n+n))) Zero (PmOdInv n k)]]=
;;      Succ k
;; Need PmOdInvBd: PmOdInv n k<Succ(Succ(n+n))
(simp "PmOdInvBd")
(use "Truth")
(use "kBd")
(use "kBd")
;; ?^10:(k<Succ(Succ(n+n)) -> F) -> PmOd(Succ n)(PmOdInv(Succ n)(Succ k))=Succ k
(assume "kH")
(assert "Succ(Succ(n+n))<Succ k")
(use "NatLeToLtSucc")
(use "NatNotLtToLe")
(use "kH")
;; Assertion proved.
(assume "kBd")
(simp "PmOdInvEqId")
(use "PmOdEqId")
(use "kBd")
(use "kBd")
;; Proof finished.
;; (cp)
(save "PmOdId2")

;; (search-about "PmOdId")

;; PmOdId2
;; all n,k PmOd n(PmOdInv n k)=k

;; PmOdId1
;; all n,k PmOdInv n(PmOd n k)=k

;; End 2024-12-30

;; 2025-01-02

;; GqCRtD n k is of interest for k<=n*n+n+n only
;; RtCGqD n k is of interest for k<=n*n+n+n only

;; (pp (nt (pt "RtCGqD 2 Zero")))
;; (pp (nt (pt "RtCGqD 2 1")))
;; (pp (nt (pt "RtCGqD 2 2")))
;; (pp (nt (pt "RtCGqD 2 3")))
;; (pp (nt (pt "RtCGqD 2 4")))
;; (pp (nt (pt "RtCGqD 2 5")))
;; (pp (nt (pt "RtCGqD 2 6")))
;; (pp (nt (pt "RtCGqD 2 7")))
;; (pp (nt (pt "RtCGqD 2 8")))

;; > Zero
;; > Succ(Succ Zero)
;; > Succ Zero
;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))

;; (pp (nt (pt "GqCRtD 2 Zero")))
;; (pp (nt (pt "GqCRtD 2 1")))
;; (pp (nt (pt "GqCRtD 2 2")))
;; (pp (nt (pt "GqCRtD 2 3")))
;; (pp (nt (pt "GqCRtD 2 4")))
;; (pp (nt (pt "GqCRtD 2 5")))
;; (pp (nt (pt "GqCRtD 2 6")))
;; (pp (nt (pt "GqCRtD 2 7")))
;; (pp (nt (pt "GqCRtD 2 8")))

;; > Zero
;; > Succ(Succ Zero)
;; > Succ Zero
;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ Zero))
;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))

;; Length here is 9.  At the next length 15 the interesting arguments
;; for RtCGqD are 6 7 8 9  (Gq codes of the diagonal elements)
;; for GqCRtD are 12 7 5 9 (Rt codes of the diagonal elements)

;; (pp (nt (pt "RtCGqD 3 6")))
;; (pp (nt (pt "RtCGqD 3 7")))
;; (pp (nt (pt "RtCGqD 3 8")))
;; (pp (nt (pt "RtCGqD 3 9")))

;;> Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ(Succ(Succ Zero))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))))
;;
;; i.e., 12 7 5 8 (Rt codes of the diagonal elements)

;; (pp (nt (pt "GqCRtD 3 12")))
;; (pp (nt (pt "GqCRtD 3 7")))
;; (pp (nt (pt "GqCRtD 3 5")))
;; (pp (nt (pt "GqCRtD 3 9")))

;; > Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero)))))))
;; > Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ Zero))))))))

;; i.e., 6 7 8 9  (Gq codes of the diagonal elements)

;; (pp (nt (pt "PmOd 1 Zero")))
;; (pp (nt (pt "PmOd 1 1")))
;; (pp (nt (pt "PmOd 1 2")))
;; (pp (nt (pt "PmOd 1 3")))

;; > Succ Zero
;; > Succ(Succ Zero)
;; > Zero
;; > Succ(Succ(Succ Zero))

;; (pp (nt (pt "PmOd 2 Zero")))
;; (pp (nt (pt "PmOd 2 1")))
;; (pp (nt (pt "PmOd 2 2")))
;; (pp (nt (pt "PmOd 2 3")))
;; (pp (nt (pt "PmOd 2 4")))
;; (pp (nt (pt "PmOd 2 5")))

;; > Succ(Succ Zero)
;; > Succ(Succ(Succ Zero))
;; > Succ Zero
;; > Succ(Succ(Succ(Succ Zero)))
;; > Zero
;; > Succ(Succ(Succ(Succ(Succ Zero))))

;; End 2025-01-02

;; 2025-01-10

(add-pvar-name "X" (make-arity (py "nat")))

;; IndTwo
(set-goal "X^ Zero -> X^(Succ Zero) ->
 all n(X^ n -> X^(n+Succ(Succ Zero))) -> all n X^ n")
(assert "X^ Zero andi X^(Succ Zero) ->
 all n(X^ n andi X^(Succ n) -> X^(Succ n) andi X^(n+Succ(Succ Zero))) ->
 all n(X^ n andi X^(Succ n))")
(assume "Init" "Step")
(ind)
(use "Init")
(assume "n" "IH")
(use "Step")
(use "IH")
;; Assertion proved.
(assume "A0")
(assume "Init0" "Init1" "Step")

(assert "all n(X^ n andi X^(Succ n))")
(ind)
(split)
(use "Init0")
(use "Init1")
(assume "n" "IH")
;; 17,18
(use "A0")
(split)
(use "Init0")
(use "Init1")
;; 19
(assume "m" "IHm")
(split)
(use "IHm")
(use "A0")
(split)
(use "Init0")
(use "Init1")
(assume "l" "Conj")
(split)
(use "Conj")
(use "Step")
(use "Conj")
;; ?^11:all n(X^ n andnc X^(Succ n)) -> all n X^ n
(assume "AllAndHyp" "n")
(use "AllAndHyp")
;; Proof finished.
;; (cp)
(save "IndTwo")

;; IndTwoCr
(set-goal "X Zero -> X(Succ Zero) ->
 all n(X n -> X(n+Succ(Succ Zero))) -> all n X n")
(assert "X Zero andi X(Succ Zero) ->
 all n(X n andi X(Succ n) -> X(Succ n) andi X(n+Succ(Succ Zero))) ->
 all n(X n andi X(Succ n))")
(assume "Init" "Step")
(ind)
(use "Init")
(assume "n" "IH")
(use "Step")
(use "IH")
;; Assertion proved.
(assume "A0")
(assume "Init0" "Init1" "Step")

(assert "all n(X n andi X(Succ n))")
(ind)
(split)
(use "Init0")
(use "Init1")
(assume "n" "IH")
;; 17,18
(use "A0")
(split)
(use "Init0")
(use "Init1")
;; 19
(assume "m" "IHm")
(split)
(use "IHm")
(use "A0")
(split)
(use "Init0")
(use "Init1")
(assume "l" "Conj")
(split)
(use "Conj")
(use "Step")
(use "Conj")
;; ?^11:all n(X n andd X(Succ n)) -> all n X n
(assume "AllAndHyp" "n")
(use "AllAndHyp")
;; Proof finished.
;; (cp)
(save "IndTwoCr")

(add-program-constant "RtToGs" (py "nat=>nat=>nat"))
(add-computation-rules
 "RtToGs Zero m" "m"
 "RtToGs(Succ Zero)m" "[if (m=Zero) (Succ Zero) [if (m=Succ Zero) Zero m]]"
 "RtToGs(Succ(Succ n))m"
 "[if (m=Succ(Succ n)) Zero
  [if (m=Succ n) (Succ(Succ n))
  [if (m<=n) (Succ(RtToGs n m)) m]]]")

(set-totality-goal "RtToGs")
(assert
 "all m^(TotalNat m^ -> all n^(TotalNat n^ -> TotalNat(RtToGs n^ m^)))")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(use "IndTwoCr")
;; 7-9
(ng #t)
(use "TotalVar")
;; 8
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; 9
(assume "n" "IH")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalNatSucc")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(assume "A")
(strip)
(search)
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "RtToGs 2 Zero")))
;; (pp (nt (pt "RtToGs 2 1")))
;; (pp (nt (pt "RtToGs 2 2")))

;; > Succ Zero
;; > Succ(Succ Zero)
;; > Zero

;; (pp (nt (pt "RtToGs 3 Zero")))
;; (pp (nt (pt "RtToGs 3 1")))
;; (pp (nt (pt "RtToGs 3 2")))
;; (pp (nt (pt "RtToGs 3 3")))

;; > Succ(Succ Zero)
;; > Succ Zero
;; > Succ(Succ(Succ Zero))
;; > Zero

;; (pp (nt (pt "RtToGs 4 Zero")))
;; (pp (nt (pt "RtToGs 4 1")))
;; (pp (nt (pt "RtToGs 4 2")))
;; (pp (nt (pt "RtToGs 4 3")))
;; (pp (nt (pt "RtToGs 4 4")))

;; > Succ(Succ Zero)
;; > Succ(Succ(Succ Zero))
;; > Succ Zero
;; > Succ(Succ(Succ(Succ Zero)))
;; > Zero

(add-program-constant "GsToRt" (py "nat=>nat=>nat"))
(add-computation-rules
 "GsToRt Zero m" "m"
 "GsToRt(Succ Zero)m" "[if (m=Zero) (Succ Zero) [if (m=Succ Zero) Zero m]]"
 "GsToRt(Succ(Succ n))m"
 "[if (m=Zero) (Succ(Succ n))
  [if (m=Succ(Succ n)) (Succ n)
  [if (m<=Succ n) (GsToRt n(Pred m)) m]]]")

(set-totality-goal "GsToRt")
(assert "all n^(TotalNat n^ -> all m TotalNat(GsToRt n^ m))")
(fold-alltotal)
(use "IndTwoCr")
;; 5-7
(assume "m")
(use "TotalVar")
;; 6
(assume "m")
(use "TotalVar")
;; 7
(assume "n" "IH" "m")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(assume "A")
(assume "n^" "Tn")
(fold-alltotal)
(use "A")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "GsToRt 2 Zero")))
;; (pp (nt (pt "GsToRt 2 1")))
;; (pp (nt (pt "GsToRt 2 2")))

;; > Succ(Succ Zero)
;; > Zero
;; > Succ Zero

;; (pp (nt (pt "GsToRt 3 Zero")))
;; (pp (nt (pt "GsToRt 3 1")))
;; (pp (nt (pt "GsToRt 3 2")))
;; (pp (nt (pt "GsToRt 3 3")))

;; > Succ(Succ(Succ Zero))
;; > Succ Zero
;; > Zero
;; > Succ(Succ Zero)

;; (pp (nt (pt "GsToRt 4 Zero")))
;; (pp (nt (pt "GsToRt 4 1")))
;; (pp (nt (pt "GsToRt 4 2")))
;; (pp (nt (pt "GsToRt 4 3")))
;; (pp (nt (pt "GsToRt 4 4")))

;; > Succ(Succ(Succ(Succ Zero)))
;; > Succ(Succ Zero)
;; > Zero
;; > Succ Zero
;; > Succ(Succ(Succ Zero))

;; RtToGsBd
(set-goal "all n,m(m<=n -> RtToGs n m<=n)")
(use "IndTwo")
;; 2-4
(assume "m" "m=0")
(ng)
(use "m=0")
;; 3
(ng)
(cases)
(assume "Useless")
(use "Truth")
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
;; 4
(assume "n" "IH")
(ng #t)
(assume "m" "m<=SSn")
(use "NatLeCases" (pt "m") (pt "Succ(Succ n)"))
;; 17-19
(use "m<=SSn")
(assume "m<SSn")
(use "NatLtSuccCases" (pt "m") (pt "Succ n"))
(use "m<SSn")
(assume "m<Sn")
(simp (pf "m=Succ(Succ n) -> F"))
(ng #t)
(simp (pf "m=Succ n -> F"))
(ng #t)
(simp (pf "m<=n"))
(ng #t)
(use "NatLeTrans" (pt "n"))
(use "IH")
(use "NatLtSuccToLe")
(use "m<Sn")
(use "Truth")
(use "NatLtSuccToLe")
(use "m<Sn")
;; 29
(assume "m=Sn")
(simphyp-with "m<Sn" "m=Sn")
(use 6)
;; 26
(assume "m=SSn")
(simphyp-with "m<SSn" "m=SSn")
(use 6)
;; 23
(assume "m=Sn")
(simp (pf "m=Succ n"))
(simp (pf "m=Succ n"))
(ng #t)
(cases (pt "n=Succ n"))
(assume "Useless")
(use "Truth")
(assume "Useless")
(use "Truth")
(use "m=Sn")
(use "m=Sn")
;; 19
(assume "m=SSn")
(simp "m=SSn")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtToGsBd")

;; RtToGsId
(set-goal "all n,m(n<m -> RtToGs n m=m)")
(use "IndTwo")
;; 2-4
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "1<n")
(ng #t)
(simp (pf "n=Zero -> F"))
(simp (pf "n=Succ Zero -> F"))
(use "Truth")
(assume "n=1")
(simphyp-with-to "1<n" "n=1" "Absurd")
(use "Absurd")
;; 9
(assume "n=0")
(simphyp-with-to "1<n" "n=0" "Absurd")
(use "Absurd")
;; 4
(assume "n" "IH" "m")
(ng #t)
(assume "SSn<m")
(simp (pf "m=Succ(Succ n) -> F"))
(ng #t)
(simp (pf "m=Succ n -> F"))
(ng #t)
(simp (pf "m<=n -> F"))
(use "Truth")
(assume "m<=n")
(assert "Succ(Succ n)<n")
(use "NatLtLeTrans" (pt "m"))
(use "SSn<m")
(use "m<=n")
(assume "SSn<n")
(assert "Succ n<n")
(use "NatLtTrans" (pt "Succ(Succ n)"))
(use "Truth")
(use "SSn<n")
(assume "Absurd")
(use "Absurd")
;; ?^25:m=Succ n -> F
(assume "m=Sn")
(simphyp-with-to "SSn<m" "m=Sn" "Absurd")
(use "Absurd")
;; ?^22:m=Succ(Succ n) -> F
(assume "m=SSn")
(simphyp-with-to "SSn<m" "m=SSn" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "RtToGsId")

;; RtToGsUp
(set-goal "all n RtToGs n n=Zero")
(cases)
(use "Truth")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof fnishedd.
;; (cp)
(save "RtToGsUp")

;; RtToGsDn
(set-goal "all n RtToGs n(Pred n)=n")
(cases)
(use "Truth")
(cases)
(use "Truth")
(assume "n")
(ng #t)
(simp "NatNotEqSucc")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtToGsDn")

;; RtToGsMd
(set-goal "all n,m(m<=n -> RtToGs(Succ(Succ n))m=Succ(RtToGs n m))")
(assume "n" "m" "m<=n")
(simp "RtToGs2CompRule")
(simp (pf "m=Succ(Succ n) -> F"))
;; 4,5
(simp (pf "m=Succ n -> F"))
;; 6,7
(simp "m<=n")
(use "Truth")
;; ?^7:m=Succ n -> F
(assume "m=Sn")
(simphyp-with-to "m<=n" "m=Sn" "Absurd")
(use "Absurd")
;; ?^5:m=Succ(Succ n) -> F
(assume "m=SSn")
(simphyp-with-to "m<=n" "m=SSn" "SSn<=n")

(assert "all l(Succ(Succ l)<=l -> F)")
;; 15,16
(ind)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "l" "IH")
(ng #t)
(use "IH")
;; Assertion proved.
(assume "A")

(use-with "A" (pt "n") "SSn<=n")
;; Proof finished.
;; (cp)
(save "RtToGsMd")

;; Similar properties of GsToRt

;; GsToRtBd
(set-goal "all n,m(m<=n -> GsToRt n m<=n)")
(use "IndTwo")
;; 2-4
(assume "m" "m=0")
(ng)
(use "m=0")
;; 3
(ng)
(cases)
(assume "Useless")
(use "Truth")
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
;; 4
(assume "n" "IH")
(ng #t)
(cases)
(assume "Useless")
(use "Truth")
(assume "m")
(ng #t)
(assume "m<=Sn")
(use "NatLeCases" (pt "m") (pt "Succ n"))
;; 22-24
(use "m<=Sn")
(assume "m<Sn")
(use "NatLtSuccCases" (pt "m") (pt "n"))
(use "m<Sn")
(assume "m<n")
(simp (pf "m=Succ n -> F"))
(ng #t)
(simp (pf "m<=n"))
(ng #t)
(use "NatLeTrans" (pt "n"))
(use "IH")
(use "NatLtSuccToLe")
(use "m<Sn")
(use "NatLeTrans" (pt "Succ n"))
(use "Truth")
(use "Truth")
(use "NatLtToLe")
(use "m<n")
(assume "m=Sn")
(simphyp-with-to "m<n" "m=Sn" "Absurd")
(use "Absurd")
;; 28
(assume "m=n")
(simp "m=n")
(ng #t)
(simp "NatNotEqSucc")
(ng #t)
(use "NatLeTrans" (pt "n"))
(use "IH")
(use "Truth")
(use "NatLeTrans" (pt "Succ n"))
(use "Truth")
(use "Truth")
;; 24
(assume "m=Sn")
(simp "m=Sn")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsToRtBd")

;; GsToRtId
(set-goal "all n,m(n<m -> GsToRt n m=m)")
(use "IndTwo")
;; 2-4
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "1<n")
(ng #t)
(simp (pf "n=Zero -> F"))
(simp (pf "n=Succ Zero -> F"))
(use "Truth")
(assume "n=1")
(simphyp-with-to "1<n" "n=1" "Absurd")
(use "Absurd")
;; 9
(assume "n=0")
(simphyp-with-to "1<n" "n=0" "Absurd")
(use "Absurd")
;; 4
(assume "n" "IH")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "m")
(ng #t)
(assume "Sn<m")
(simp (pf "m=Succ n -> F"))
(ng #t)
(simp (pf "m<=n -> F"))
(use "Truth")
(assume "m<=n")
(assert "Succ n<n")
(use "NatLtLeTrans" (pt "m"))
(use "Sn<m")
(use "m<=n")
(assume "Absurd")
(use "Absurd")
;; 27
(assume "m=Sn")
(simphyp-with-to "Sn<m" "m=Sn" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsToRtId")

;; GsToRtUp
(set-goal "all n GsToRt n Zero=n")
(cases)
(use "Truth")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof fnishedd.
;; (cp)
(save "GsToRtUp")

;; GsToRtDn
(set-goal "all n GsToRt n n=Pred n")
(cases)
(use "Truth")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsToRtDn")

;; GsToRtMd
(set-goal "all n,m(Succ m<n -> GsToRt(Succ(Succ n))(Succ m)=GsToRt n m)")
(assume "n" "m" "Sm<n")
(ng #t)
(simp (pf "m=Succ n -> F"))
;; 4,5
(ng #t)
(simp (pf "m<=n"))
;; 7,8
(use "Truth")
;; 8
(use "NatLtToLe")
(use "NatLtTrans" (pt "Succ m"))
(use "Truth")
(use "Sm<n")
;; 5
(assume "m=Sn")
(simphyp-with-to "Sm<n" "m=Sn" "SSn<n")
(assert "n<Succ(Succ n)")
(use "NatLtTrans" (pt "Succ n"))
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "n<SSn")
(assert "n<n")
(use "NatLtTrans" (pt "Succ(Succ n)"))
(use "n<SSn")
(use "SSn<n")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsToRtMd")

;; GsToRtToGsId
(set-goal "all n,m GsToRt n(RtToGs n m)=m")
(use "IndTwo")
;; 2-4
(assume "m")
(use "Truth")
;; 3
(assume "m")
(ng #t)
(cases (pt "m"))
;; 8,9
(assume "m=0")
(ng #t)
(use "Truth")
;; 9
(assume "n" "m=Sn")
(ng #t)
(simp "<-" "m=Sn")
(cases (pt "n"))
;; 15,16
(assume "n=0")
(ng #t)
(simp "m=Sn")
(simp "n=0")
(use "Truth")
;; 16
(assume "l" "n=Sl")
(ng #t)
(simp "m=Sn")
(ng #t)
(simp "n=Sl")
(use "Truth")
;; 4
(assume "n" "IH" "m")
(simp (pf "n+Succ(Succ Zero)=Succ(Succ n)"))
;;   n  IH:all m GsToRt n(RtToGs n m)=m
;;   m
;; ----------------------------------------------------------------------------
;; ?^27:GsToRt(Succ(Succ n))(RtToGs(Succ(Succ n))m)=m

(use "NatLeLtCases" (pt "m") (pt "Succ(Succ n)"))
;; 29,30
(assume "m<=SSn")
(use "NatLeCases" (pt "m") (pt "Succ(Succ n)"))
;; 32-34
(use "m<=SSn")
;; 33
(assume "m<SSn")
(assert "m<=Succ n")
(use "NatLtSuccToLe")
(use "m<SSn")
(assume "m<=Sn")
(use "NatLeCases" (pt "m") (pt "Succ n"))
;; 40-42
(use "m<=Sn")
;; 41
(assume "m<Sn")
(simp "RtToGsMd")
(simp "GsToRt2CompRule")
(ng #t)
(simp "IH")
(assert "RtToGs n m<=n")
(use "RtToGsBd")
(use "NatLtSuccToLe")
(use "m<Sn")
(assume "LeH")
(simp "LeH")
(ng #t)
(simp (pf "RtToGs n m=Succ n -> F"))
(use "Truth")
(assume "EqH")
(simphyp-with-to "LeH" "EqH" "Absurd")
(use "Absurd")
(use "NatLtSuccToLe")
(use "m<Sn")
;; 42
(assume "m=Sn")
(simp "m=Sn")
(ng #t)
(simp (pf "n=Succ n -> F"))
(ng #t)
(use "Truth")
(use "NatNotEqSucc")
;; 34
(assume "m=SSn")
(simp "m=SSn")
(ng #t)
(use "Truth")
;; 30
(assume "SSn<m")
(simp "RtToGsId")
(simp "GsToRtId")
(use "Truth")
(use "SSn<m")
(use "SSn<m")
;; 28
(use "Truth")
;; Proof finished.
;; (cp)
;; uses RtToGsMd RtToGsBd RtToGsId GsToRtId
(save "GsToRtToGsId")

;; RtToGsToRtId
(set-goal "all n,m RtToGs n(GsToRt n m)=m")
(use "IndTwo")
;; 2-4
(assume "m")
(use "Truth")
;; 3
(assume "m")
(ng #t)
(cases (pt "m"))
;; 8,9
(assume "m=0")
(ng #t)
(use "Truth")
;; 9
(assume "n" "m=Sn")
(ng #t)
(simp "<-" "m=Sn")
(cases (pt "n"))
;; 15,16
(assume "n=0")
(ng #t)
(simp "m=Sn")
(simp "n=0")
(use "Truth")
;; 16
(assume "l" "n=Sl")
(ng #t)
(simp "m=Sn")
(ng #t)
(simp "n=Sl")
(use "Truth")
;; 4
(assume "n" "IH" "m")
(simp (pf "n+Succ(Succ Zero)=Succ(Succ n)"))
;;   n  IH:all m RtToGs n(GsToRt n m)=m
;;   m
;; ----------------------------------------------------------------------------
;; ?^27:RtToGs(Succ(Succ n))(GsToRt(Succ(Succ n))m)=m
(use "NatLeLtCases" (pt "m") (pt "Succ(Succ n)"))
;; 29,30
(assume "m<=SSn")
(use "NatLeCases" (pt "m") (pt "Succ(Succ n)"))
;; 32-34
(use "m<=SSn")
;; 33
(assume "m<SSn")
(cases (pt "m"))
;; 36,37
(assume "m=0")
(simp "GsToRt2CompRule")
(ng #t)
(use "Truth")
;; 37
(assume "l" "m=Sl")
(simp "GsToRt2CompRule")
(simp (pf "Succ l=Zero -> F"))
;; 43,44
(simp "IfFalse")
(simp (pf "Succ l=Succ(Succ n) -> F"))
;; 46,47
(simp "IfFalse")
(simp (pf "Succ l<=Succ n"))
;; 49,50
(simp "IfTrue")
(simp (pf "Pred(Succ l)=l"))
;; 52,53
;; ?^52:RtToGs(Succ(Succ n))(GsToRt n l)=Succ l
(simp "<-" "m=Sl")
;; ?^54:RtToGs(Succ(Succ n))(GsToRt n l)=m
(simp "RtToGsMd")
;; 55,56
(simp "IH")
(use "NatEqSym")
(use "m=Sl")
;; ?^56:GsToRt n l<=n
(use "GsToRtBd")
(simp "<-" "NatLe2CompRule")
(simp "<-" "m=Sl")
(use "NatLtSuccToLe")
(use "m<SSn")
;; 53
(use "Truth")
;; 50
(simp "<-" "m=Sl")
(use "NatLtSuccToLe")
(use "m<SSn")
;; 47
(simp "<-" "m=Sl")
(assume "m=SSn")
(simphyp-with-to "m<SSn" "m=SSn" "Absurd")
(use "Absurd")
;; 44
(assume "Absurd")
(use "Absurd")
;; ?^34:m=Succ(Succ n) -> RtToGs(Succ(Succ n))(GsToRt(Succ(Succ n))m)=m
(assume "m=SSn")
(simp "m=SSn")
(simp "GsToRtDn")
(ng #t)
(simp "NatNotEqSucc")
(use "Truth")
;; ?^30:Succ(Succ n)<m -> RtToGs(Succ(Succ n))(GsToRt(Succ(Succ n))m)=m
(assume "SSn<m")
(simp "GsToRtId")
;; 76,77
(simp "RtToGsId")
(use "Truth")
(use "SSn<m")
(use "SSn<m")
;; 28
(use "Truth")
;; Proof finished.
;; (cp)
;; uses RtToGsMd RtToGsId GsToRnBd GsToRtDn GsosToRtId
(save "RtToGsToRtId")

;; (pp "GsToRtToGsId")
;; (pp "RtToGsToRtId")

;; > all n,m GsToRt n(RtToGs n m)=m
;; > all n,m RtToGs n(GsToRt n m)=m

;; To prepare RealSumEqDiag we single out the essential middle part.

;; RealSumSplitGsCor1
(set-goal "all xs(all n Real(xs n) -> all n,m(n=Pred m ->
 all l(l<Gs n -> xs l===0) ->
 all l(Gs m<=l -> xs l===0) ->
 RealSum Zero(Gs n)([n]0)+
 RealSum Zero m([l]xs(Gs n+l))+
 RealSum(Gs m)(Gs n)([n]0)===
 RealSum Zero(m*m)xs))")
(assume "xs" "Rxs" "n" "m" "nDef" "HL" "HR")

(simpreal (pf "RealSum(Gs m)(Gs n)([n0]0)===0"))
(simpreal "RealPlusZero")
(simpreal (pf "RealSum Zero(Gs n)([n0]0)===0"))
(simpreal "RealZeroPlus")
;; ?^9:RealSum Zero m([l]xs(Gs n+l))===RealSum Zero(m*m)xs

(simpreal "<-" "RealSumSplitGsCor")
(simp "<-" "nDef")
(simpreal (pf "RealSum(Gs m)(Gs n)xs===0"))
(simpreal "RealPlusZero")
(simpreal (pf "RealSum Zero(Gs n)xs===0"))
(simpreal "RealZeroPlus")

(simpreal "<-" "RealSumZeroShiftDown")
(use "RealEqRefl")
(autoreal)
(use "Rxs")
(autoreal)
(use "RealEqTrans" (pt "RealSum Zero(Gs n)([n]0)"))
(use "RealSumCompat")
(ng #t)
(assume "l" "Useless")
(use "HL")
(use "RealSumZeros")
(assume "l")
(use "RealEqRefl")
(use "RealRat")
(autoreal)
;; ?^15:RealSum(Gs m)(Gs n)xs===0
(use "RealEqTrans" (pt "RealSum(Gs m)(Gs n)([n]0)"))
(use "RealSumCompat")
(ng #t)
(assume "l" "LeH" "LtH")
(use "HR")
(use "LeH")
(use "RealSumZeros")
(assume "l")
(use "RealEqRefl")
(use "RealRat")
(use "Rxs")
(autoreal)
;; ?^8:RealSum Zero(Gs n)([n0]0)===0
(use "RealSumZeros")
(assume "l")
(use "RealEqRefl")
(use "RealRat")
(autoreal)
;; ?^4:RealSum(Gs m)(Gs n)([n0]0)===0
(use "RealSumZerosSharp")
(assume "l")
(use "RealRat")
(assume "l" "LeBd" "LtBd")
(use "RealEqRefl")
(use "RealRat")
;; Proof finished.
;; (cp)
(save "RealSumSplitGsCor1")

;; 2025-02-07

;; Plan: RealSumEqDiag with rht instead of lft.  Idea: use RealSumComm
;; in the middle part.  Otherwise use the proof of RealSumEqDiag done
;; 2025-01-31

;; RealSumEqDiag holds for Zero:

;; RealSumEqDiagZero
(set-goal "all xs(
     all n Real(xs n) -> 
     all zss,n(n=Zero ->
      zss eqd([ij][if (lft ij+rht ij=n) (xs rht ij) 0]) -> 
      RealSum Zero(Succ n)xs===RealSum Zero(Succ n*Succ n)([k]zss(RtD k))))")
(assume "xs" "Rxs" "zss" "n" "n=0" "zssDef")
(simp "n=0")
(ng #t)
(simp "zssDef")
(ng #t)
(simp "n=0")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumEqDiagZero")

;; RealSumEqDiagSucc
(set-goal "all xs(
     all n Real(xs n) -> 
     all zss,n(Zero<n ->
      zss eqd([ij][if (lft ij+rht ij=n) (xs rht ij) 0]) -> 
      RealSum Zero(Succ n)xs===RealSum Zero(Succ n*Succ n)([k]zss(RtD k))))")
(assume "xs" "Rxs" "zss" "n" "0<n" "zssDef")
(simpreal "RealSumPmsGqCor")
(simp "zssDef")
(drop "zssDef")
(def "xs0" "([k]([ij][if (lft ij+rht ij=n) (xs rht ij) 0]) (GqD n k))")
(drop "xs0Def")
(bpe-ng #t)
(simp "Pred1CompRule")
;; ?^16:RealSum Zero(Succ n)xs===
;;      RealSum Zero(Succ n*Succ n)
;;      ([k]([ij][if (lft ij+rht ij=n) (xs rht ij) 0])(GqD n k))
(simpreal "<-" "RealSumSplitGsCor1" (pt "n"))
;; 17-21
;; ?^17:RealSum Zero(Succ n)xs===
;;    RealSum Zero(Gs n)([n0]0)+
;;    RealSum Zero(Succ n)
;;    ([l]([k]([ij][if (lft ij+rht ij=n) (xs rht ij) 0])(GqD n k))(Gs n+l))+
;;    RealSum(Gs(Succ n))(Gs n)([n0]0)
(simpreal (pf "RealSum(Gs(Succ n))(Gs n)([n0]0)===0"))
;; 22,23
(simpreal "RealPlusZero")
(simpreal (pf "RealSum Zero(Gs n)([n0]0)===0"))
;; 26,27
(simpreal "RealZeroPlus")
;; Now the middle part
(bpe-ng #t)
;; ?^30:RealSum Zero(Succ n)xs===
;;      RealSum Zero(Succ n)
;;      ([l]
;;        [if (lft(GqD n(Gs n+l))+rht(GqD n(Gs n+l))=n)
;;          (xs rht(GqD n(Gs n+l)))
;;          0])
;; Here we need to invert the order of the second sum, with RealSumComm

;; (pp "RealSumComm")

(use "RealSumComm")
(use "Rxs")
(assume "n0")
(autoreal)
(bpe-ng #t)
(assume "n0" "Useless" "n0<Sn")
(simp (pf "Zero+Zero+Pred(Succ n)--n0=n--n0"))
(assert "n0<=n")
(use "NatLtSuccToLe")
(use "n0<Sn")
;; Assertion proved.
(assume "n0<=n")

(simp (pf "GqD n(Gs n+n0)=GsD(Gs n+n0)"))
;; 43,44
(assert "GsD(Gs n+n0)=(n0 pair n--n0)")
;; 45,46
(assert "GsC(GsD(Gs n+n0))=GsC(n0 pair n--n0)") ;H1
;; 47,48
(simp "GsCDId")
(ng #t)
(simp (pf "n0+(n--n0)=n--n0+n0"))
(simp "NatMinusPlusEq")
(use "Truth")
(use "n0<=n")
(use "NatPlusComm")
;; Assertion proved.
(assume "H1")
;;   H1:GsC(GsD(Gs n+n0))=GsC(n0 pair n--n0)
;; ---------------------------------------------------------------------------
;; ?^55:GsD(Gs n+n0)=(n0 pair n--n0)

(assert "all ij,ij0(GsC ij=GsC ij0 -> ij=ij0)")
(assume "ij" "ij0" "ij=ij0")
(simp "<-" "GsDCId")
(simp "<-" (pf "GsD(GsC ij0)=ij0"))
(simp "ij=ij0")
(use "Truth")
(use "GsDCId")
;; Assertion proved.
(assume "GsCInj")
;; ?^63:GsD(Gs n+n0)=(n0 pair n--n0)
(use "GsCInj")
(simp "GsCDId")
(ng #t)
(simp (pf "n0+(n--n0)=n--n0+n0"))
(simp "NatMinusPlusEq")
(use "Truth")
(use "n0<=n")
(use "NatPlusComm")
;; Assertion proved.
(assume "EqH")
(simp "EqH")
(ng #t)
(simp (pf "n0+(n--n0)=n--n0+n0"))
(simp "NatMinusPlusEq")
(use "RealEqRefl")
(autoreal)
(use "n0<=n")
(use "NatPlusComm")
;; ?^44:GqD n(Gs n+n0)=GsD(Gs n+n0)
(simp "GqD0CompRule")
(simp (pf "Gs n+n0<Gs(Succ n)"))
(use "Truth")
(ng #t)
(use "NatLeToLtSucc")
(use "n0<=n")
;; ?^38:Zero+Zero+Pred(Succ n)--n0=n--n0
(use "Truth")
(autoreal)
;; This concludes the middle part
;; ?^27:RealSum Zero(Gs n)([n0]0)===0

(use "RealSumZeros")
(assume "n0")
(use "RealEqRefl")
(use "RealRat")
(autoreal)

;; ?^23:RealSum(Gs(Succ n))(Gs n)([n0]0)===0
(use "RealSumZeros")
(assume "n0")
(use "RealEqRefl")
(use "RealRat")

(assume "k" "kBd")
(bpe-ng #t)

;;   zss  n  0<n:Zero<n
;;   xs0  k  kBd:Gs(Succ n)<=k
;; ---------------------------------------------------------------------------
;; ?^91:[if (lft(GqD n k)+rht(GqD n k)=n) (xs rht(GqD n k)) 0]===0
(assert "n<lft(GqD n k)+rht(GqD n k)")
(use "NatLeLtCases" (pt "Succ n*Succ n") (pt "k"))
;; 94,95
;; ?^94:n<lft(GqD n k)+rht(GqD n k)
;; 
(get 95)
(assume "LtH")
(simp "GqGtChar")
(simp "<-" "NatPairEq")
(simp "GqCDId")
(use "kBd")
(ng "LtH")
(use "NatLtSuccToLe")
(use "LtH")
;; ?^94:Succ n*Succ n<=k -> n<lft(GqD n k)+rht(GqD n k)
(simp "<-" "GsProp")
(assume "u1")

(assert "GqD n k eqd(n pair n)")
;; 105,106
(simp "GqD0CompRule")
(simp (pf "k<Gs(Succ n) -> F"))
;; 108,109
(simp "IfFalse")
(simp "GdsCToMl0CompRule")
(simp (pf "Succ(k--Gs(Succ n))<Gs n -> F"))
;; 112,113
(simp "IfFalse")
(simp (pf "GdsCToMlEq n=GdsCToMlEq(Succ(Pred n))"))
(simp "GdsCToMlEq1CompRule")
(simp "GqMlToIj0CompRule")
(ng #t)
(simp "NatSuccPred")
(use "InitEqD")
(use "0<n")
;; 116
(simp "NatSuccPred")
(use "Truth")
(use "0<n")
;; 113
(assert "Gs n<=Succ(k--Gs(Succ n))")
(use "NatLeTrans" (pt "k--Gs(Succ n)"))
(use "NatLePlusCancelR" (pt "Gs(Succ n)"))
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(use "u1")
(use "kBd")
(use "Truth")
;; Assertion proved.
(assume "u2" "u3")
(assert "Gs n<Gs n")
(use "NatLeLtTrans" (pt "Succ(k--Gs(Succ n))"))
(use "u2")
(use "u3")
(assume "Absurd")
(use "Absurd")
;; ?^109:k<Gs(Succ n) -> F
(assume "u2")
(assert "k<k")
(use "NatLtLeTrans" (pt "Gs(Succ n)"))
(use "u2")
(use "kBd")
(assume "Absurd")
(use "Absurd")
;; ?^105:GqD n k eqd(n pair n) -> n<lft(GqD n k)+rht(GqD n k)
(assume "u2")
(simp "u2")
(ng #t)
(use "NatLeLtTrans" (pt "n+Zero"))
(use "Truth")
(simp "NatLt4RewRule")
(use "0<n")
;; 92
(assume "LtH")
(assert "lft(GqD n k)+rht(GqD n k)=n -> F")
;; 151,152
(assume "EqH")
(assert "n<n")
(use "NatLtLeTrans" (pt "lft(GqD n k)+rht(GqD n k)"))
(use "LtH")
(simp "EqH")
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "u1")
(simp "u1")
(simp "IfFalse")
(use "RealEqRefl")
(autoreal)
;; ?^20:all l(
;;       l<Gs n -> 
;;       ([k][if (lft(GqD n k)+rht(GqD n k)=n) (xs rht(GqD n k)) 0])l===0)

(assume "k" "kBd")
(bpe-ng #t)
;; Want GsD(k) instead of GqD(n,k).  This follows from the definition of GqD
(simp (pf "GqD n k eqd GsD k"))
;; 166,167
(assert "lft(GsD k)+rht(GsD k)<n")
(simp "GsCL")
(simp "<-" "NatPairEq")
(simp "GsCDId")
(use "kBd")
;; Assertion proved.
(assume "u1")
(simp (pf "lft(GsD k)+rht(GsD k)=n -> F"))
(use "RealEqRefl")
(use "RealRat")
(assume "u2")
(simphyp-with-to "u1" "u2" "u3")
(use "u3")
;; ?^167:GqD n k eqd GsD k
(simp "GqD0CompRule")
(simp (pf "k<Gs(Succ n)"))
(ng #t)
(use "InitEqD")
(use "NatLtTrans" (pt "Gs n"))
(use "kBd")
(ng #t)
(use "NatLeToLtSucc")
(use "Truth")
(use "Truth")

;; ?^18:all n0
;; Real(([k][if (lft(GqD n k)+rht(GqD n k)=n) (xs rht(GqD n k)) 0])n0)
(assume "n0")
(autoreal)

;; ?^4:all ij Real(zss ij)
(assume "ij")
(simp "zssDef")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumEqDiagSucc")

;; RealSumEqDiag
(set-goal "all xs(
     all n Real(xs n) -> 
     all n,zss(
      zss eqd([ij][if (lft ij+rht ij=n) (xs rht ij) 0]) -> 
      RealSum Zero(Succ n)xs===RealSum Zero(Succ n*Succ n)([k]zss(RtD k))))")
(assume "xs" "Rxs")
(cases)
;; 3,4
(assume "zss" "zssDef")
(use "RealSumEqDiagZero")
(use "Rxs")
(use "Truth")
(use "zssDef")
;; 4
(assume "n" "zss" "zssDef")
(use "RealSumEqDiagSucc")
(use "Rxs")
(use "Truth")
(use "zssDef")
;; Proof finished.
;; (cp)
(save "RealSumEqDiag")

;; Need RealSumEqDiagCor with usage of zss removed.  Idea: Instanciate
;; RealSumEqDiag with ([ij][if (lft ij+rht ij=n) (xs rht ij) 0])
;; for zss.

;; RealSumEqDiagCor
(set-goal "all xs(all n Real(xs n) ->
 all n RealSum Zero n xs===
       RealSum Zero(n**2)
         ([k][if (Succ(lft(RtD k)+rht(RtD k))=n) (xs(rht(RtD k))) 0]))")
(assume "xs" "Rxs")
(cases)
(use "RealEqRefl")
(use "RealRat")
(assume "n")

(assert "RealSum Zero(Succ n)xs===
         RealSum Zero(Succ n*Succ n)
         ([k]([ij][if (lft ij+rht ij=n) (xs rht ij) 0])(RtD k))")
(use "RealSumEqDiag")
(use "Rxs")
(use "InitEqD")
(bpe-ng #t)
(assume "EqH")
(use "EqH")
;; Proof finished.
;; (cp)
(save "RealSumEqDiagCor")

;; End 2025-02-07

;; 2025-02-03

;; RealEFunEq
(set-goal "all x,y(Real x -> Real y -> cRE(x+y)===(cRE x)*(cRE y))")
(assume "x" "y" "Rx" "Ry")

;; Needed for RealCauchyProdLimECor
(def "xs0" "[n](1#PosF n)*x**n")
(def "ys0" "[n](1#PosF n)*y**n")

;; Needed to prove RConvLim(cRESeq(x+y))(cRE x*cRE y)K
(inst-with-to
 "RealCauchyProdLimECor"
 (pt "xs0") (pt "ys0") (pt "x") (pt "y") "Rx" "Ry" "xs0Def" "ys0Def" "tmp")
(by-assume "tmp" "K" "Conj")
(elim "Conj")
(drop "Conj")
(assume "MonK" "RCPLEC")

;; Needed from realproof
(assert "Real(cRE x)")
(use "cREReal")
(use "Rx")
(assume "RcREx")

(assert "Real(cRE y)")
(use "cREReal")
(use "Ry")
(assume "RcREy")

(assert "all n Real(cRESeq(x+y)n)")
(simp "RESeqExFree")
(ng #t)
(assume "n")
(simp "RSumExFree")
(realproof)
(assume "RcRESeqPlus"))

;; Proof
(use "RealConvLimUniq" (pt "cRESeq(x+y)") (pt "cREMod(x+y)") (pt "K"))
;; RealConvLimUniq 1
(use "RealEConvLim")
(realproof)
;; RealConvLimUniq 2
(intro 0)
;; RealConvLimIntro 1
(use "RcRESeqPlus")
;; RealConvLimIntro 2
(realproof)
;; RealConvLimIntro 3
(use "MonK")
;; RealConvLimIntro 4
(intro 0)
(assume "p" "n" "nBd")
(simpreal (pf "cRESeq(x+y)n===RealSum Zero(Succ(n*n+n+n))
 ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs0 lft(RtD k)*ys0 rht(RtD k)) 0])"))
;; Simp 1
(use "RCPLEC")
(use "nBd")
;; Simp 2
(simp "RESeqExFree")
(simp "RealESeq0CompRule")
(simp "RSumExFree")

(assert "all n Real(xs0 n)")
(assume "n0")
(simp "xs0Def")
(realproof)
(assume "Rxs0")

(assert "all n Real(ys0 n)")
(assume "n0")
(simp "ys0Def")
(realproof)
(assume "Rys0")
;; ?^64:RealSum Zero(Succ n)([n0](1#PosF n0)*(x+y)**n0)===
;;      RealSum Zero(Succ(n*n+n+n))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs0 lft(RtD k)*ys0 rht(RtD k)) 0])
;; Provide SuccSquare: (n+1)*(n+1)=Succ(n*n+n+n)
(assert "(n+1)*(n+1)=Succ(n*n+n+n)")
(ng #t)
(use "Truth")
(assume "SuccSquare")

(simp "<-" "SuccSquare")
;; ?^69:RealSum Zero(Succ n)([n0](1#PosF n0)*(x+y)**n0)===
;;      RealSum Zero((n+1)*(n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs0 lft(RtD k)*ys0 rht(RtD k)) 0])

(simpreal "<-" "RealSumDiags")
;; 70-72
;; RealSumDiags 1
(use "RealSumCompat")
(assume "l" "Useless" "l<n+1")
(bpe-ng #t)
(use "RealEqTrans"
 (pt "RealSum Zero(Succ l)([m](1#PosF(l--m))*x**(l--m)*(1#PosF m)*y**m)"))
;; RealEqTrans 1
(use "RealBinomPosF")
;; RealBinomPosF 1..2
(use "Rx")
(use "Ry")
;; ?^77:RealSum Zero(Succ l)([m](1#PosF(l--m))*x**(l--m)*(1#PosF m)*y**m)===
;;      RealSum Zero((l+1)*(l+1))
;;       ([k][if (lft(RtD k)+rht(RtD k)=l) (xs0 lft(RtD k)*ys0 rht(RtD k)) 0])

;; RealEqTrans 2
(simpreal "RealSumEqDiagCor")
;; 80,81
;; RealSumEqDiag 1
(bpe-ng #t)
(simp (pf "Succ l**2=((l+1)*(l+1))"))
;; Simp 1
(use "RealSumCompat")
(assume "l0" "Useless1" "l0Bd")
(bpe-ng #t)
(simp (pf "(Succ(lft(RtD l0)+rht(RtD l0))=Succ l)=
           (lft(RtD l0)+rht(RtD l0)=l)"))
(casedist (pt "(lft(RtD l0)+rht(RtD l0)=l)"))
;; Casedist 1
(simp "IfTrue")
(simp "IfTrue")
(simp "xs0Def")
(simp "ys0Def")
(bpe-ng #t)
(assume "lft(RtD l0)+rht(RtD l0)=l")
(simp (pf "l--rht(RtD l0)=lft(RtD l0)"))
;;; Simp 1
(simpreal "RealTimesAssoc")
;; RealTimesAssoc 1
(use "RealEqRefl")
(realproof)
;; RealTimesAssoc 2
(realproof)
;; RealTimesAssoc 3
(realproof)
;; RealTimesAssoc 4
(realproof)
;;; Simp 2
(simp "<-" "lft(RtD l0)+rht(RtD l0)=l")
(use "Truth")

;; Casedist 2
(assume "NegH")
(simp "IfFalse")
(simp "IfFalse")
(use "RealEqRefl")
(realproof)
;; Simp 2
(use "Truth")
;; ?^84:Succ l**2=(l+1)*(l+1)
(use "Truth")

;; RealSumEqDiag 2
(assume "n0")
(realproof)

;; RealSumDiags 2
(use "Rys0")

;; RealSumDiags 3
(use "Rxs0")
;; Proof finished.
;; (cp)
(save "RealEFunEq")

;; RealECompat
(set-goal "all x,y(x===y -> cRE x===cRE y)")
(assume "x" "y" "x=y")
(use "RealConvLimUniq"
 (pt "cRESeq x") (pt "cREMod x") (pt "[p]cREMod x p max cREMod y p"))
;; RealConvLimUniq 1
(use "RealEConvLim")
(realproof)
;; RealConvLimUniq 2
(use "RealConvLimMonLe" (pt "cREMod y"))
;; RealConvLimMonLe 1
(use "RealConvLimCompat" (pt "cRESeq y") (pt "cRE y ") (pt "cREMod y"))
;; RealConvLimCompat 1
(assume "n")
(simp "RESeqExFree")
(simp "RESeqExFree")
(ng #t)
(simp "RSumExFree")
(simp "RSumExFree")
(use "RealSumCompat")
(assume "l" "0<=l" "l<n+1")
(ng #t)
(simpreal "x=y")
(use "RealEqRefl")
(realproof)
;; RealConvLimCompat 2
(use "RealEqRefl")
(realproof)
;; RealConvLimCompat 3
(assume "p")
(use "Truth")
;; RealConvLimCompat 4
(use "RealEConvLim")
(realproof)
;; RealConvLimMonLe 2
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(assert "all x0(Real x0 -> cREMod x0 p<=cREMod x0 q)")
;; Assert 1
(assume "x0" "Rx0")
(use "MonElim")
;; MonElim 1
(use "RealEModMon")
(realproof)
;; MonElim 2
(use "p<=q")
;; Assert 2
(assume "lemma")
(use "NatLeMonMax")
;; NatLeMonMax 1
(use "lemma")
(realproof)
;; NatLeMonMax 2
(use "lemma")
(realproof)
;; RealConvLimMonLe 3
(ng #t)
(assume "p")
(use "NatMaxUB2")
;; (cp)
(save "RealECompat")

;; RealEFunEqZero
(set-goal "all x(Real x -> 1===cRE x*cRE(~x))")
(assume "x" "Rx")
(simpreal "<-" "RealEFunEq")
;; RealEFunEq 1
(simpreal "RealECompat" (pt "0"))
;; RealECompat 1
(use "RealConvLimUniq" (pt "cRESeq 0") (pt "[p]Zero") (pt "cREMod 0"))
;; RealConvLimUniq 1
(intro 0)
;; RealConvLimIntro 0
(assume "n")
(simp "RESeqExFree")
(ng #t)
(simp "RSumExFree")
(realproof)
;; RealConvLimIntro 1
(realproof)
;; RealConvLimIntro 2
(use "MonConst")
;; RealConvLimIntro 3
(intro 0)
(assume "p" "n")
(simp "RESeqExFree")
(ng #t)
(assume "T")
(simp "RSumExFree")
(simpreal "<-" "RealSumZeroSuccBegin")
;; RealSumZeroSuccBegin 1
(ng #t)
(simpreal "RealSumZerosSharp")
;; RealSumZerosSharp 1
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; RealSumZerosSharp 2
(ng #t)
(assume "l" "1<=l" "l<=n")
(assert "RealExp 0 l===0")
;; Assert 1
(simpreal "<-" "RatExpRealExp")
(simp "<-" "PosToNatToPosId")
(simp "PosToNatToIntId")
;; PosToNatToIntId 1
(ng #t)
(use "RealEqRefl")
(realproof)
;; PosToNatToIntId 2
(use "NatSuccLeToLt")
(use "1<=l")
;; Assert 2
(assume "0**l=0")
(simpreal "0**l=0")
(use "RealTimesZero")
(realproof)
;; RealSumZerosSharp 3
(assume "n0")
(realproof)
;; RealSumZeroSuccBegin 2
(assume "n0")
(realproof)
;; RealConvLimUniq 2
(ng #t)
(use "RealEConvLim")
(realproof)
;; RealECompat 2
(simpreal "RealPlusMinusZero")
;; RealPlusMinusZero 1
(use "RealEqRefl")
(realproof)
;; RealPlusMinusZero 2
(use "Rx")
;; RealEFunEq 2
(realproof)
;; RealEFunEq 3
(use "Rx")
;; Proof finished.
;; (cp)
(save "RealEFunEqZero")

;; RealELeZero (corollary (a))
(set-goal "all x(Real x -> RealNNeg(cRE x))")

;; Lemma 1
(assert "all x(0<<=x -> 1<<=cRE x)")
(assume "x" "0<=x")

(assert "Real x")
(use "RealLeElim1" (pt "0"))
(use "0<=x")
(assume "Rx")

(assert "all p 0 seq(0 mod(PosS p))<=x seq(x mod(PosS p))+(1#2**p)")
(use "RealLeElim2")
(use "0<=x")
(assume "est:0<=x")

(simp "REExFree")
(ng #t)

(use "RealConvLimLe"
(pt "[n] 1") (pt "cRESeq x") (pt "[p]NatMax Zero Zero") (pt "cREMod x"))

;; RealConvLimLe 1
(assume "n")
(simp "RESeqExFree")
(ng #t)
(simp "RSumExFree")
(simpreal "<-" "RealSumZeroSuccBegin")
;; RealSumZeroSuccBegin 1
(ng #t)
(use "RealLeTrans" (pt "1+RealConstr([n]0)([p]Zero)"))
;; RealLeTrans 1
(use "RealLeRefl")
(realproof)
;; RealLeTrans 2
(use "RealLeMonPlusR")
;; RealLeMonPlusR 1
(realproof)
;; RealLeMonPlusR 2
(use "RealNNegToZeroLe")
(use "RealNNegSeqRealSum")
(assume "n0")
(use "RealZeroLeToNNeg")
(ng #t)
(simpreal "<-" "RealZeroTimes" (pt "x**n0"))
;; RealZeroTimes 1
(use "RealLeMonTimes")
;; RealLeMonTimes 1
(use "RealExpZeroLe")
(use "0<=x")
;; RealLeMonTimes 2
(use "RatLeToRealLe")
(use "Truth")
;; RealZeroTimes 2
(realproof)
;; RealSumZeroSuccBegin 2
(assume "n0")
(realproof)

;; RealConvLimLe 2
(use "RealConvLimConstRat")
;; RealConvLimConstRat 1
(realproof)
;; RealConvLimConstRat 2
(intro 0)
(ng #t)
(strip)
(use "Truth")

;; "RealConvLimLe" 3
(simp "<-" "REExFree")
(use "RealEConvLim")
(use "Rx")

(assume "Lemma 1")

;; Main Proof

(assume "x" "Rx")

;; Common stuff
(assert "Real(cRE x)")
(use "cREReal")
(use "Rx")
(assume "RcREx")

(assert "Real(cRE ~x)")
(use "cREReal")
(realproof)
(assume "RcRE~x")
;; End Common Stuff

(use "RealZeroLeToNNeg")
(use "RealLeStab")
;; (use "RealRat")
;; (use "RcREx")
(assume "cRE x<0")
(use "RealLeCases" (pt "x") (pt "0"))

;; RealLeCases 1
(use "Rx")
;; RealLeCases 2
(realproof)
;; RealLeCases 3
(assume "x<=0")

(assert "1<<=cRE(~x)")
;; assert 1
(use "Lemma 1")
(simpreal (pf "0===RealUMinus 0"))
;; 0 === ~0: 1
(use "RealLeUMinus")
(use "x<=0")
;; 0 === ~0: 2
(use "RealEqRefl")
(realproof)
;; assert 2
(assume "1<=cRE(-x)")

(use "cRE x<0")
(defnc "p" "1")
(simpreal (pf "cRE x===cRE x*1"))
;; cRE x === cRE x*1: 1

;; The following two assertions are needed to realsimplify
;; with a goal containing RealTimesUDivR
(assert "RealPos 1 1")
(use "Truth")
(assume "RlPos 1 1")

(assert "RealPos(cRE ~x)1") 
;; assert 1
(use "RealLeToPosZero")
(use "1<=cRE(-x)")
;; assert 2
(assume "RealPos(cRE~x)1")

(simpreal "<-" "RealTimesUDivR" (pt "cRE (~x)") (pt "1"))
;; RealTimesUDivR 1
(simpreal "RealTimesAssoc")
;; RealTimesAssoc 1
(simpreal "<-" "RealEFunEqZero")
;; RealEFunEqZero 1
(simpreal "RealOneTimes")
;; RealOneTimes 1
(use "RealPosToZeroLeUDiv")
(use "RcRE~x")
(use "RealPos(cRE~x)1")
;; RealOneTimes 2
(realproof)
;; RealEFunEqZero 2
(use "Rx")
;; RealTimesAssoc 2
(realproof)
;; RealTimesAssoc 3
(use "RcRE~x")
;; RealTimesAssoc 4
(use "RcREx")
;; RealTimesUDivR 2
(use "RealPos(cRE~x)1")
;; RealTimesUDivR 3
(use "RcRE~x")
;; cRE x===cRE x*1: 2
(simpreal "RealTimesOne")
;; RealTimesOne 1
(use "RealEqRefl")
(use "RcREx")
;; RealTimesOne 2
(use "RcREx")

;; RealLeCases 4
(assume "0<=x")
(use "cRE x<0")
(use "RealLeTrans" (pt "1"))
;; RealLeTrans 1
(use "RatLeToRealLe")
(use "Truth")
;; RealLeTrans 2
(use "Lemma 1")
(use "0<=x")
;; Proof finished.
;; (cp)
(save "RealELeZero")

;; Korr (b)
;; RealEPos
(set-goal "all x (Real x -> exl p RealPos(cRE x)p)")
(assume "x" "Rx")

(assert "Real(cRE x)")
(use "cREReal")
(use "Rx")
(assume "RcREx")

(assert "Real(cRE ~x)")
(use "cREReal")
(realproof)
(assume "RcRE-x")

;; value of witness due to RealLeToPos and RealLeBound
(def "n" "(cRBd((cRE ~x)seq)((cRE ~x)mod))")
(intro 0 (pt "NatToPos(Succ(Succ n))"))
(simp "SuccPosS")
;; SuccPosS 1
(use "RealLeToPos")
(def "p" "NatToPos(Succ n)")
(simp "<-" "pDef")
(cut "(1#2**p)<<=(1#2**p)*2**p*cRE x")
;; cut 1
(assume "est")
(ng "est")
(simpreal (pf "cRE x===(2**p#2**p)*cRE x"))
;; cRE x === (2**p#2**p)*cRE x: 1
(use "est")
;; cRE x === (2**p#2**p)*cRE x: 2
(simpreal (pf "(2**p#2**p)===1"))
;; (2**p#2**p)===1: 1
(use "RealEqSym")
(use "RealOneTimes")
(use "RcREx")
;; (2**p#2**p)===1: 2
(use "RatEqvToRealEq")
(use "Truth")
;; cut 2
(use "RealLeTrans" (pt "RealAbs(1#2**p)*(RealAbs(2**p)*cRE x)"))
;; RealLeTrans 1
(use "RealLeTrans" (pt "RealAbs(1#2**p)*1"))
;; RealLeTrans .1
(use "RealLeRefl")
(realproof)
;; RealLeTrans .2
(use "RealLeMonTimesR")
;; RealLeMonTimesR 1
(use "RatLeToRealLe")
(use "Truth")
;; RealLeMonTimesR 2
(simpreal "RealEFunEqZero" (pt "x"))
;; RealEFunEqZero 1
(simpreal "RealTimesComm")
;; RealTimesComm 1
(use "RealLeMonTimes")
;; RealLeMonTimes 1
(use "RealNNegToZeroLe")
(use "RealELeZero")
(use "Rx")
;; RealLeMonTimes 2
(ng #t)
(simp "pDef")
(use "RealLeTrans" (pt "RealAbs(2**n)"))
;; RealLeTrans .1
(ng #t)
(simp "nDef")
(use "RealLeBound")
(use "RcRE-x")
;; RealLeTrans .2
(simp "<-" "NatPosExFree")
(ng #t)
(use "RatLeToRealLe")
(ng #t)
(use "NatLeMonTwoExp")
(simp "NatPosExFree")
(simp "PosToNatToPosId")
;; PosToNatToPosId 1
(use "Truth")
;; PosToNatToPosId 2
(use "Truth")
;; RealTimesComm 2
(use "RcRE-x")
;; RealTimesComm 3
(use "RcREx")
;; RealEFunEqZero 2
(use "Rx")
;; RealLeTrans 2
(simpreal "RealTimesAssoc")
;; RealTimesAssoc 1
(use "RealLeRefl")
(realproof)
;; RealTimesAssoc 2
(use "RcREx")
;; RealTimesAssoc 3
(realproof)
;; RealTimesAssoc 4
(realproof)

;; SuccPosS 2
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEPos")

;; Korr (c)
;; RealEInvEqMinus
(set-goal "all x(Real x -> exl p cRE~x===RealUDiv(cRE x)p)")
(assume "x" "Rx")

(assert "Real(cRE x)")
(use "cREReal")
(use "Rx")
(assume "RcREx")

(assert "Real(cRE ~x)")
(use "cREReal")
(realproof)
(assume "RcRE-x")

(inst-with-to "RealEPos" (pt "x") "Rx" "tmp")
(elim "tmp")
(drop "tmp")
(assume "p" "0<cREx")
(intro 0 (pt "p"))
(cut "1*cRE(~x)===RealUDiv(cRE x)p*cRE x*cRE(~x)")
(assume "eq")
(use "RealEqTrans" (pt "1*cRE ~x"))
;; RealEqTrans 1
(use "RealEqSym")
(use "RealOneTimes")
(use "RcRE-x")
;; RealEqTrans 2
(use "RealEqTrans" (pt "RealUDiv(cRE x)p*cRE x*cRE~x"))
;; RealEqTrans 1
(use "eq")
;; RealEqTrans 2
(simpreal "<-" "RealTimesAssoc")
;; RealTimesAssoc 1
(simpreal "<-" "RealEFunEqZero")
;; RealEFunEqZero 1
(use "RealTimesOne")
(realproof)
;; RealEFunEqZero 2
(use "Rx")
;; RealTimesAssoc 2
(use "RcRE-x")
;; RealTimesAssoc 3
(use "RcREx")
;; RealTimesAssoc 4
(realproof)
;; cut 2
(use "RealTimesCompat")
;; RealTimesCompat 1
(simpreal "RealTimesComm")
;; RealTimesComm 1
(use "RealEqSym")
(use "RealTimesUDivR")
;; RealTimesUDivR 1
(use "RcREx")
;; RealTimesUDivR 2
(use "0<cREx")
;; RealTimesComm 2
(use "RcREx")
;; RealTimesComm 3
(use "RealUDivReal")
;; RealUDivReal 1
(use "RcREx")
;; RealUDivReal 2
(use "RealPosToPosAbs")
(use "0<cREx")
;; RealTimesCompat 2
(use "RealEqRefl")
(use "RcRE-x")
;; Proof finished.
;; (cp)
(save "RealEInvEqMinus")

;; Korr (d) Teil 1
;; RealEToExpNat
(set-goal "all n cRE n===cRE 1**n")
(ind)
;; Ind 1
(ng #t)

(assert "Real(cRE 0)")
(use "cREReal")
(realproof)
(assume "RcRE0")

(simpreal "RealEFunEqZero" (pt "0"))
;; RealEFunEqZero 1
(ng #t)
(simpreal "<-" "RealEFunEq")
;; RealEFunEq 1
(use "RealEqRefl")
(use "RcRE0")
;; RealEFunEq 2
(realproof)
;; RealEFunEq 3
(realproof)
;; RealEFunEqZero 2
(realproof)
;; Ind 2
(assume "n" "IH")

(assert "Real(cRE 1)")
(use "cREReal")
(realproof)
(assume "RcRE1")

(simpreal "RealECompat" (pt "RealPlus n 1"))
;; Simp 1
(simpreal "RealEFunEq")
;; RealEFunEq 1
(ng #t)
(simpreal "IH")
(use "RealEqRefl")
(realproof)
;; RealEFunEq 2
(realproof)
;; RealEFunEq 3
(realproof)
;; Simp 2
(ng #t)
(simp "IntPlusIdOne")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealEToExpNat")

;; Korr (d) Teil 2
;; RealEToExpNeg
(set-goal "all n exl p(cRE ~n)===(RealUDiv(cRE 1)p)**n")
(assume "n")

(assert "Real 1")
(realproof)
(assume "as1")
(inst-with-to "RealEInvEqMinus" (pt "1") "as1" "tmp")
(by-assume "tmp" "p" "RealEInvEqMinus 1")
(drop "as1")
(intro 0 (pt "p"))

(assert "Real(cRE~1)")
(use "cREReal")
(realproof)
(assume "RcRE~1")

(assert "Real(cRE IntN 1)")
(use "cREReal")
(realproof)
(assume "RcRE~1v2")

(use "RealEqTrans" (pt "(cRE~1)**n"))
;; RealEqTrans 1
(ind (pt "n"))
;; Ind 1
(ng #t)
(cut "cRE Zero===cRE 1**Zero")
;; Cut 1
(ng #t)
(prop)
;; Cut 2
(use-with "RealEToExpNat" (pt "Zero"))

;; Ind 2
(assume "n0" "IH")
(simpreal "RealECompat" (pt "RealPlus ~n0 (IntN 1)"))
;; Simp 1
(simpreal "RealEFunEq")
;; RealEFunEq 1
(ng #t)
(simpreal "IH")
(use "RealEqRefl")
(realproof)
;; RealEFunEq 2
(realproof)
;; RealEFunEq 3
(realproof)
;; Simp 2
(ng #t)
(use "RatEqvToRealEq")
(simp "IntPlusIntNOneIntPred")
(use "Truth")

;; RealEqTrans 2
(simpreal "<-" "RealEInvEqMinus 1")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cp)
(save "RealEToExpNeg")

