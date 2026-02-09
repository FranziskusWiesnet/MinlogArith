;; 2025-07-28.  rseq.scm.  Based on librseq17.scm leaving out theorems
;; for reordering finite sums, and NatSum NatProd Gauss tricks

#|
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
;; (set! COMMENT-FLAG #t)
|#

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")
	(if (not (assoc "int" ALGEBRAS))
	    (myerror "First execute (libload \"int.scm\")")
	    (if (not (assoc "rat" ALGEBRAS))
		(myerror "First execute (libload \"rat.scm\")")
		(if (not (assoc "rea" ALGEBRAS))
		    (myerror "First execute (libload \"rea.scm\")"))))))

(display "loading rseq.scm ...") (newline)

;; Index

;; Theorems in 1.  Completeness and convergence
;; (pp "RCauchyElim")
;; (pp "RealCauchyToReals")
;; (pp "RealCauchyToMon")
;; (pp "RealCauchyToRCauchy")
;; (pp "RealCompleteAux1")
;; (pp "RealCompleteAux2")
;; (pp "RLim")
;; (pp "RLimExFree")
;; (pp "RealLimReal")
;; (pp "RealCompleteAux3") (was RealCauchyConvMod)
;; (pp "RealComplete")
;; (pp "RConvLimElim")
;; (pp "RealConvLimElim1") (appears in src/pproof.scm)
;; (pp "RealConvLimElim2") (appears in src/pproof.scm)
;; (pp "RealConvLimToMon")
;; (pp "RealConvLimToRConvLim")
;; (pp "RealCompleteCor")
;; (pp "RealConvLimLe")
;; (pp "RealConvLimEq")
;; (pp "RCauchyCompat")
;; (pp "MonCompat")
;; (pp "RealConvLimUniq")
;; (pp "RealLimConst")
;; (pp "RConvLimCompat") (pp "RealConvLimCompat")
;; (pp "RConvLimMonLe") (pp "RealConvLimMonLe")
;; (pp "RealConvLimPlusConstR") (pp "RealConvLimPlusConstL")
;; (pp "RealConvLimPlus")
;; (pp "RealConvLimUMinus")
;; (pp "RealConvLimTimesConstR") (pp "RealConvLimTimesConstL")
;; (pp "RConvLimTimes") (pp "RealConvLimTimes")
;; (pp "RConvLimTimesSym") (pp "RealConvLimTimesSym")
;; (pp "RealCauchyCompat")
;; (pp "RCauchyMon") (pp "RealCauchyMon")
;; (pp "RCauchyAbs") (pp "RealCauchyAbs")
;; (pp "RConvLimToRCauchy") (pp "RealConvLimToCauchy")
;; (pp "RCauchyBdTimes") (pp "RealCauchyBdTimes")
;; (pp "RCauchyPlusConvZero") (pp "RealCauchyPlusConvZero")
;; (pp "GeomSeqRealConvLimAux")
;; (pp "GeomSeqRealConvLim")

;; Theorems in 2.  Series
;; (pp "RSerConvLimElim")
;; (pp "RealSerConvLimToReals")
;; (pp "RealSerConvLimToReal")
;; (pp "RealSerConvLimToMon")
;; (pp "RealSerConvLimToRSerConvLim")
;; (pp "RealSerConvToReals")
;; (pp "RealSerConvToMon")
;; (pp "RealSerConvToRSerConv")
;; (pp "RSerAbsConvToConv") (pp "RealSerAbsConvToConv")
;; (pp "GeomSumEq")
;; (pp "RConvLimShiftStrengthened") (pp "RealConvLimShiftStrengthened")
;; (pp "GeomSerRealConvLimAuxStrengthened")
;; (pp "GeomSerRealConvLimStrengthened")
;; (pp "GeomSerRealCauchyStrengthened")

;; Theorems in 3.  Comparison and ratio test
;; (pp "RComparisonTest") (pp "RealComparisonTest")
;; (pp "RComparisonTestMax") (pp "RealComparisonTestMax")
;; (pp "RCauchyTimesConstR") (pp "RealCauchyTimesConstR")
;; (pp "RSerConvTimesConstR") (pp "RealSerConvTimesConstR")
;; (pp "RSerConvShiftUp") (pp "RealSerConvShiftUp")
;; (pp "RSerConvShiftDown") (pp "RealSerConvShiftDown
;; (pp "RCauchyShiftUp") (pp "RealCauchyShiftUp")
;; (pp "RCauchyShiftDown") (pp "RealCauchyShiftDown")
;; (pp "RCauchyExpToRSerConvExp") (pp "RealCauchyExpToRealSerConvExp")
;; (pp "RealRatioTestZero")
;; (pp "RealRatioTest")
;; (pp "RealRatioTestMax")
;; (pp "GeomSumOneHalfEq")
;; (pp "GeomSumOneHalfEqRat")
;; (pp "RSerConvExpOneHalf")

;; Theorems in 4.  Cauchy Product
;; (pp "NatLtPlusToLtMax") for RealCauchyProdLimAbs
;; (pp "RealLeSumPlusMax") not used
;; (pp "RealSumMinusSquareMod") for RealUpperTriangLimZero
;; (pp "RealConvLimZStar") for RealCauchyProdLim
;; (pp "RealUpperTriangLimZeroAux") for RealUpperTriangLimZero
;; (pp "RealSquareMinusLowTriangEqUp") for RealLeAbsMinusZStarZMinusPStar
;; (pp "RealSquareMinusLowTriangEqUpMod") not used
;; (pp "RealLeAbsMinusZStarZMinusPStar") for RealUpperTriangLimZero
;; (pp "NatLePlusToLeMax") for RealUpperTriangLeMinusSquare
;; (pp "RealUpperTriangLeMinusSquare") for RealUpperTriangLimZero
;; (pp "RealUpperTriangLimZero") for RealCauchyProdLim
;; (pp "RealCauchyProdLim")
;; (pp "RealCauchyProdLimAbs")

;; Dependence tree

;; RealCauchyProdLimAbs
;;   RealCauchyProdLim
;;     RealUpperTriangLimZero
;;       RealLeAbsMinusZStarZMinusPStar
;;         RealSquareMinusLowTriangEqUp
;;       RealUpperTriangLeMinusSquare
;;       RealSumMinusSquareMod
;;       RealUpperTriangLimZeroAux
;;     RealConvLimZStar

;; 1.  Completeness and convergence
;; ================================

;; We define the predicates (RCauchy xs M), (RealCauchy xs M) and
;; (RealConvLim xs x M).  Then we define the constant (RealLim xs M).
;; Since (RealLim xs M) is not normal, we provide (cRLim xs M) as an
;; equivalent alternative (provided RLim is animated).  Then we prove
;; RealComplete: RealCauchy xs M -> RealConvLim xs(RealLim xs M)M.
;; This says that every modulated Cauchy sequence of reals converges
;; with the same modulus to its limit.

;; (add-var-name "xs" "ys" (py "nat=>rea"))

(add-ids
 (list (list "RCauchy" (make-arity (py "nat=>rea") (py "pos=>nat"))))
 '("all xs,M(
    all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
    RCauchy xs M)" "RCauchyIntro"))

;; RCauchyElim
(set-goal "all xs,M(RCauchy xs M ->
    all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RCauchyElim")

;; We will also need RealCauchy

(add-ids
 (list (list "RealCauchy" (make-arity (py "nat=>rea") (py "pos=>nat"))))
 '("all xs,M(
   all n Real(xs n) -> Mon M -> RCauchy xs M -> RealCauchy xs M)"
   "RealCauchyIntro"))

;; RealCauchyToReals
(set-goal "all xs,M(RealCauchy xs M -> all n Real(xs n))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealCauchyToReals")

;; RealCauchyToMon
(set-goal "all xs,M(RealCauchy xs M -> Mon M)")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealCauchyToMon")

;; RealCauchyToRCauchy
(set-goal "all xs,M(RealCauchy xs M -> RCauchy xs M)")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealCauchyToRCauchy")

;; The real numbers were built by completion of the rationals viewed as
;; metric space.  We show that a further completion (this time of the
;; reals) does not yield anything new, i.e., that every Cauchy sequence
;; xs of reals with modulus M converges (even with the same modulus) to
;; an already existing real, defined as RealLim xs M.  This is the
;; content of the theorem RealComplete below.

;; The first part uses work of Max Zeuner (semws18/completeness.scm) and
;; Wolfgang Boehnisch (semws19/completeness.scm).  The second part is
;; based on Jan Belle's Master Thesis (2021).

;; To define RealLim we need to diagonalize.

(add-var-name "ass" (py "nat=>nat=>rat"))
(add-var-name "Ns" (py "nat=>pos=>nat"))

;; RealCompleteAux1
(set-goal "all ass,Ns,xs,bs(
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 all n Real(xs n) ->
 all n bs n=ass n(Ns n(NatToPos n)) ->
 all n abs(bs n+ ~(xs n))<<=(1#2**n))")
(assume "ass" "Ns" "xs" "bs" "xsDef" "Rxs" "bsDef" "n")
(use "RealLeTrans" (pt "RealConstr([n0](1#2**NatToPos n))([p]Zero)"))
;; 3,4
(simp "xsDef")
(simp "bsDef")
(use "RatCauchyConvMod")
(simp "<-" "xsDef")
(use "Rxs")
(use "Truth")
;; ?^4:(1#2**NatToPos n)<<=(1#2**n)
(use "RatLeToRealLe")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "IntLe4CompRule")
(use "PosLeMonPosExp")
(cases (pt "n"))
(assume "Useless")
(use "Truth")
(assume "n0" "Useless")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealCompleteAux1")

;; RealCompleteAux2
(set-goal "all ass,Ns,xs,M,bs,K(
 all n Real(xs n) ->
 all p,n,m(M p<=n -> M p<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) ->
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 all n bs n=ass n(Ns n(NatToPos n)) ->
 all p K p=M(PosS p)max PosS(PosS p) ->
 all p,n,m(K p<=n -> K p<=m -> abs(bs n+ ~(bs m))<<=(1#2**p)))")
(assume "ass" "Ns" "xs" "M" "bs" "K" "Rxs" "xsCs" "xsDef" "bsDef" "KDef"
	"p" "n" "m" "nBd" "mBd")

;; Split (1#2**p)
(use "RealLeTrans" (pt "RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)"))
;; 3,4
;; ?^3:abs(bs n+ ~(bs m))<<=RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)
;; First replace ~,+,abs on rat by their counterparts on rea
(use "RealLeTrans" (pt "abs(bs n+RealUMinus(bs m))"))

;; 5,6
(simpreal "<-" "RatUMinusRealUMinus")
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatAbsRealAbs")
(use "RealLeRefl")
(autoreal)
;; 6
(simpreal
 (pf "bs n+RealUMinus(bs m)===bs n+ ~(xs n)+(xs n+ RealUMinus(bs m))"))
;; This will be proved by RealPlusInsert
(use "RealLeTrans" (pt "abs(bs n+ ~(xs n))+abs(xs n+ RealUMinus(bs m))"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusTwo")
;; 21,22
;; ?^22:abs(xs n+ ~(bs m))<<=RealPlus(1#2**PosS p)(1#2**m)
;; ?^21:abs(bs n+ ~(xs n))<<=(1#2**n)
(use "RealCompleteAux1" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
;; 22
;; Here with RealUMinus
(simpreal
 (pf "xs n+RealUMinus(bs m)===xs n+ ~(xs m)+(xs m+ RealUMinus(bs m))"))
;; 26,27
;; 26 will be proved by RealPlusInsert
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))+abs(xs m+ RealUMinus(bs m))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "xsCs")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB1")
(use "mBd")
;; ?^39:abs(xs m+ ~(bs m))<<=(1#2**m)
(simpreal "RealPlusComm")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
;; ?^50:abs(bs m+ ~(xs m))<<=(1#2**m)
(use "RealCompleteAux1" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
(autoreal)
;; ?^27:xs n+ ~(bs m)===xs n+ ~(xs m)+(xs m+ ~(bs m))
(use "RealPlusInsert")
(autoreal)
;; ?^12:bs n+ ~(bs m)===bs n+ ~(xs n)+(xs n+ ~(bs m))
(use "RealPlusInsert")
(autoreal)
;; ?^4:RealPlus(1#2**n)(1#2**PosS p)+(1#2**m)<<=(1#2**p)
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatPlusRealPlus")
(use "RatLeToRealLe")
(use "RatLeTrans" (pt "(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "RatLeMonPlus")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB2")
(use "nBd")
(use "Truth")
(ng #t)
(use "PosLeMonPosExp")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB2")
(use "mBd")
;; ?^65:(1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
(simp
 (pf "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))"))
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "RatLeRefl")
(use "Truth")
(use "RatPlusComm")
;; Proof finished.
;; (cp)
(save "RealCompleteAux2")

(add-program-constant "RealLim" (py "(nat=>rea)=>(pos=>nat)=>rea"))

(add-computation-rules
 "RealLim xs M"
 "RealConstr([n](xs n)seq((xs n)mod(NatToPos n)))
            ([p]M(PosS p)max PosS(PosS p))")

;; RealLimTotal
(set-totality-goal "RealLim")
(assume "xs^" "Txs" "M^" "TM")
(ng)
(intro 0)
(fold-alltotal)
(assume "n")
(use "RealSeqTotal")
(use "Txs")
(use "NatTotalVar")
(use "RealModTotal")
(use "Txs")
(use "NatTotalVar")
(use "PosTotalVar")
;; 5
(fold-alltotal)
(assume "p")
(use "NatMaxTotal")
(use "TM")
(use "PosTotalVar")
(use "NatTotalVar")
;; Proof finished.
;; (cdp)
(save-totality)

;; RLim
(set-goal "all xs,M exl x x eqd RealLim xs M")
(assume "xs" "M")
(intro 0 (pt "RealLim xs M"))
(intro 0)
;; Proof finished.
;; (cp)
(save "RLim")

(animate "RLim")

;; RLimExFree
(set-goal "all xs,M cRLim xs M eqd RealLim xs M")
(assume "xs" "M")
(ng #t)
(intro 0)
;; Proof finished.
;; (cp)
(save "RLimExFree")

(deanimate "RLim")

(set-totality-goal "cRLim")
(fold-alltotal)
(assume "xs")
(fold-alltotal)
(assume "M")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use the deanimated cRLim instead of RealLim.

;; RealLimReal
(set-goal "all xs,M(RealCauchy xs M -> Real(cRLim xs M))")
(assume "xs" "M" "RC")

(assert "all n Real(xs n)")
(use "RealCauchyToReals" (pt "M"))
(use "RC")
;; Assertion proved.
(assume "Rxs")

(assert "Mon M")
(use "RealCauchyToMon" (pt "xs"))
(use "RC")
;; Assertion proved.
(assume "MonM")

(assert "RCauchy xs M")
(use "RealCauchyToRCauchy")
(use "RC")
;; Assertion proved.
(assume "RCxsM")

(simp "RLimExFree")
(intro 0)
;; 16,17
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(use "RealLeToRatLe")
(ng #t)

;; To apply RealCompleteAux2 we need assDef NsDef xsChar bsDef KDef
;; Introduce assDef
(assert "exl ass all n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")

;; Introduce NsDef
(assert "exl Ns all n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")

;; Introduce xsChar
(assert "all n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")

;; Introduce bsDef
(assert "exl bs all n bs n =ass n(Ns n(NatToPos n))")
(intro 0 (pt "[n]ass n(Ns n(NatToPos n))"))
(assume "n1")
(use "Truth")
(assume "bsEx")
(by-assume "bsEx" "bs" "bsDef")

;; Introduce KDef
(assert "exl K all p K p=M(PosS p)max PosS(PosS p)")
(intro 0 (pt "[p]M(PosS p)max PosS(PosS p)"))
(assume "p1")
(use "Truth")
(assume "KEx")
(by-assume "KEx" "K" "KDef")

(simp "<-" "assDef")
(simp "<-" "NsDef")
(simp "<-" "bsDef")
(simp "<-" "assDef")
(simp "<-" "NsDef")
(simp "<-" "bsDef")
(use "RealCompleteAux2" (pt "ass") (pt "Ns") (pt "xs") (pt "M") (pt "K"))
(use "Rxs")
(use "RCauchyElim")
(use "RCxsM")
(use "xsChar")
(use "bsDef")
(use "KDef")
;; ?^64:K p<=n
(simp "KDef")
(use "NatLeTrans" (pt "(RealLim xs M)mod p"))
(ng #t)
(use "Truth")
(use "nBd")
(use "NatLeTrans" (pt "(RealLim xs M)mod p"))
(simp "KDef")
(use "Truth")
(use "mBd")
;; ?^17:Mon((RealLim xs M)mod)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "NatLeMonMax")
(use "MonElim")
(use "MonM")
(use "p<=q")
(simp "PosToNatLe")
(use "p<=q")
;; Proof finished.
;; (cp)
(save "RealLimReal")

;; RealLimRealCor
(set-goal "all xs,M(
 all n Real(xs n) -> 
 all p,n,m(M p<=n -> n<=m -> abs(xs n+ ~(xs m))<<=(1#2**p)) -> 
 all p,q(p<=q -> M p<=M q) -> Real(cRLim xs M))")
(assume "xs" "M" "Rxs" "xsCs" "MMon")
(use "RealLimReal")
;; 3-5
(intro 0)
(use "Rxs")
;; 4
(intro 0)
(use "MMon")
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(use "NatLeLeCases" (pt "n") (pt "m"))
;; 10,11
(assume "n<=m")
(use "xsCs")
(use "nBd")
(use "n<=m")
;; 11
(assume "m<=n")
(simpreal "RealAbsPlusUMinus")
(use "xsCs")
(use "mBd")
(use "m<=n")
(use "Rxs")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealLimRealCor")

;; RealCompleteAux3 (was RealCauchyConvMod)
(set-goal "all ass,Ns,xs,M,bs,K,x(
 all n xs n eqd RealConstr(ass n)(Ns n) ->
 RealCauchy xs M ->
 all n bs n=ass n(Ns n(NatToPos n)) ->
 all q K q=M(PosS q)max PosS(PosS q) ->
 x===RealConstr bs K ->
 all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)))")
(assume "ass" "Ns" "xs" "M" "bs" "K" "x" "xsDef" "CxsM" "bsDef"
	"KDef" "xEq" "p" "n" "nBd")
(assert "all n Real(xs n)")
(use "RealCauchyToReals" (pt "M"))
(use "CxsM")
(assume  "Rxs")
(use "RealLeAllPlusToLe")
(autoreal)
(assume "q")
;; ?^10:abs(xs n+ ~x)<<=RealPlus(1#2**p)(1#2**q)
(defnc "m" "(M p)max(PosS q max K(PosS q))")
(simpreal (pf "xs n+ ~x===xs n+ ~(xs m)+((xs m)+ ~x)"))
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))+abs(xs m+ ~x)"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
;; 24,25
;; ?^24:abs(xs n+ ~(xs m))<<=(1#2**p)
(assert "RCauchy xs M")
(use "RealCauchyToRCauchy")
(use "CxsM")
(assume "RCxsM")
(use "RCauchyElim" (pt "M"))
(use "RCxsM")
(use "nBd")
(simp "mDef")
(use "NatMaxUB1")
;; ?^25:abs(xs m+ ~x)<<=(1#2**q)
(simpreal (pf "(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)"))
;; 34,35
;; ?^34:(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q) will be provable by
;; RatPlusHalfExpPosS
(simpreal (pf "xs m+ ~x===xs m+RealUMinus(bs m)+(bs m+ ~x)"))
(use "RealLeTrans" (pt "abs(xs m+RealUMinus(bs m))+abs(bs m+ ~x)"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
;; ?^42:abs(xs m+ ~(bs m))<<=(1#2**PosS q)
(simpreal "RealPlusComm")
(simpreal "<-" "RealAbsUMinus")
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
;; ?^52:abs(bs m+ ~(xs m))<<=(1#2**PosS q)
(use "RealLeTrans" (pt "RealConstr([n](1#2**m))([p]Zero)"))
(use "RealCompleteAux1" (pt "ass") (pt "Ns"))
(use "xsDef")
(use "Rxs")
(use "bsDef")
;; ?^55:(1#2**m)<<=(1#2**PosS q)
(use "RatLeToRealLe")
(simp "RatLe0CompRule")
(simp "IntTimes2RewRule")
(simp "IntTimes2RewRule")
(simp "IntLe4CompRule")
(use "PosLeMonPosExp")
(simp "mDef")
(use "NatLeTrans" (pt "PosS q max K(PosS q)"))
(use "NatMaxUB1")
(use "NatMaxUB2")
(autoreal)
;; ?^43:abs(bs m+ ~x)<<=(1#2**PosS q)
(simpreal "xEq")
(use "RatCauchyConvMod")
(autoreal)
(simp "mDef")
(use "NatLeTrans" (pt "PosS q max K(PosS q)"))
(use "NatMaxUB2")
(use "NatMaxUB2")
;; ?^37:xs m+ ~x===xs m+ ~(bs m)+(bs m+ ~x)
(use "RealPlusInsert")
(autoreal)
;; ?^35:(1#2**q)===RealPlus(1#2**PosS q)(1#2**PosS q)
(simpreal "<-" "RatPlusRealPlus")
(use "RatEqvToRealEq")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; ?^19:xs n+ ~x===xs n+ ~(xs m)+(xs m+ ~x)
(use "RealPlusInsert")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealCompleteAux3")

;; Every Cauchy sequence xs of reals with monotone modulus M converges
;; with the same modulus M to its limit RealLim xs M

;; RealComplete
(set-goal "all xs,M(RealCauchy xs M -> 
 all p,n(M p<=n -> abs(xs n+ ~(cRLim xs M))<<=(1#2**p)))")
(assume "xs" "M" "RC")

(assert "all n Real(xs n)")
(use "RealCauchyToReals" (pt "M"))
(use "RC")
;; Assertion proved.
(assume "Rxs")

(assert "Mon M")
(use "RealCauchyToMon" (pt "xs"))
(use "RC")
;; Assertion proved.
(assume "MonM")

(assert "RCauchy xs M")
(use "RealCauchyToRCauchy")
(use "RC")
;; Assertion proved.
(assume "RCxsM")

;; Introduce assDef
(assert "exl ass all n ass n eqd(xs n)seq")
(intro 0 (pt "[n](xs n)seq"))
(assume "n1")
(use "InitEqD")
(assume "assEx")
(by-assume "assEx" "ass" "assDef")

;; Introduce NsDef
(assert "exl Ns all n Ns n eqd(xs n)mod")
(intro 0 (pt "[n](xs n)mod"))
(assume "n1")
(use "InitEqD")
(assume "NsEx")
(by-assume "NsEx" "Ns" "NsDef")

;; Introduce xsChar
(assert "all n xs n eqd RealConstr(ass n)(Ns n)")
(assume "n1")
(simp "assDef")
(simp "NsDef")
(cases (pt "xs n1"))
(ng #t)
(assume "as" "M1" "Useless")
(use "InitEqD")
(assume "xsChar")

;; Introduce bsDef
(assert "exl bs all n bs n =ass n(Ns n(NatToPos n))")
(intro 0 (pt "[n]ass n(Ns n(NatToPos n))"))
(assume "n1")
(use "Truth")
(assume "bsEx")
(by-assume "bsEx" "bs" "bsDef")

;; Introduce KDef
(assert "exl K all p K p=M(PosS p)max PosS(PosS p)")
(intro 0 (pt "[p]M(PosS p)max PosS(PosS p)"))
(assume "p1")
(use "Truth")
(assume "KEx")
(by-assume "KEx" "K" "KDef")

;; ?^55:all p,n(M p<=n -> abs(xs n+ ~(cRLim xs M))<<=(1#2**p))
(assume "p" "n")
(use "RealCompleteAux3" (pt "ass") (pt"Ns") (pt "bs") (pt "K"))
(use "xsChar")
(use "RC")
(use "bsDef")
(use "KDef")
;; ?^61:cRLim xs M===RealConstr bs K
(simp "RLimExFree")
;; ?^62:RealLim xs M===RealConstr bs K
(use "RealSeqEqToEq" (pt "Zero"))
(simp "<-" "RLimExFree")
(use "RealLimReal")
(use "RC")
;; ?^64:Real(RealConstr bs K)
(intro 0)
(ng #t)
(intro 0)
(assume "p1" "n1" "m1" "n1Bd" "m1Bd")
(use "RealLeToRatLe")
(use "RealCompleteAux2" (pt "ass") (pt "Ns") (pt "xs") (pt "M") (pt "K"))
(use "Rxs")
(use "RCauchyElim")
(use "RCxsM")
(use "xsChar")
(use "bsDef")
(use "KDef")
(use "n1Bd")
(use "m1Bd")
(intro 0)
(assume "p1" "q1" "p1<=q1")
(ng #t)
(simp "KDef")
(simp "KDef")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM")
(use "p1<=q1")
(simp "PosToNatLe")
(use "p1<=q1")
;; ?^65:all n(Zero<=n -> (RealLim xs M)seq n==(RealConstr bs K)seq n)
(assume "n1" "Useless")
(ng #t)
(simp "xsChar")
(ng #t)
(simp "bsDef")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealComplete")

;; We reformulate RealComplete using the predicate RealConvLim

(add-ids
 (list (list "RConvLim"
	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
 '("all xs,x,M(
    all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)) -> RConvLim xs x M)"
   "RConvLimIntro"))

;; RConvLimElim
(set-goal "all xs,x,M(
 RConvLim xs x M -> all p,n(M p<=n -> abs(xs n+ ~x)<<=(1#2**p)))")
(assume "xs" "x" "M" "CxsxM")
(elim "CxsxM")
(search)
;; Proof fnished.
;; (cp)
(save "RConvLimElim")

(add-ids
 (list (list "RealConvLim"
	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
 '("all xs,x,M(all n Real(xs n) -> Real x -> Mon M -> RConvLim xs x M ->
               RealConvLim xs x M)" "RealConvLimIntro"))

;; RealConvLimElim1
(set-goal "all xs,x,M(RealConvLim xs x M -> all n Real(xs n))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealConvLimElim1")

;; RealConvLimElim2
(set-goal "all xs,x,M(RealConvLim xs x M -> Real x)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealConvLimElim2")

;; RealConvLimToMon
(set-goal "all xs,x,M(RealConvLim xs x M -> Mon M)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealConvLimToMon")

;; RealConvLimToRConvLim
(set-goal "all xs,x,M(RealConvLim xs x M -> RConvLim xs x M)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealConvLimToRConvLim")

;; RealCompleteCor
(set-goal "all xs,M(RealCauchy xs M -> RealConvLim xs(cRLim xs M)M)")
(assume "xs" "M" "RC")
(intro 0)
;; 3-6
(use "RealCauchyToReals" (pt "M"))
(use "RC")
;; 4
(use "RealLimReal")
(use "RC")
;; 5
(use "RealCauchyToMon" (pt "xs"))
(use "RC")
;; ?^6:RConvLim xs(cRLim xs M)M
(intro 0)
(use "RealComplete")
(use "RC")
;; Proof finished.
;; (cp)
(save "RealCompleteCor")

;; We add further properties of RealConvLim

;; This section begins with RealConvLimLe RealConvLimUniq (was
;; RealConvLimEq) moved here from rea.scm.  Then we take material from
;; rseq.scm until RealConvLimTimesConstL

;; 2022-12-28.  The following should be done in rea.scm already.

;; (add-var-name "zs" (py "nat=>rea"))

;; We prove further properties of RealConvLim.

;; RealConvLimLe
(set-goal "all x,y,xs,ys,M,N(
 all n xs n<<=ys n -> RealConvLim xs x M -> RealConvLim ys y N -> x<<=y)")
(assume "x" "y" "xs" "ys" "M" "N" "LeHyp" "xsConv" "ysConv")
(use "RealLeAllPlusToLe")
(autoreal)
;; ?^5:all p x<<=y+(1#2**p)
(assume "p")
;; Idea: for n := M(PosS p)max N(PosS p) we have x<<=
;; xs n+(1#2**PosS p)<<=
;; ys n+(1#2**PosS p)<<=
;; y+(1#2**PosS p)+(1#2**PosS p)<<=
;; y+(1#2**p)

(defnc "n" "M(PosS p)max N(PosS p)")
(use "RealLeTrans" (pt "xs n+(1#2**PosS p)"))
;; ?^14:x<<=xs n+(1#2**PosS p)
(use "RealLeAbsMinus2")
(autoreal)
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "xsConv")
(simp "nDef")
(use "NatMaxUB1")
;; ?^15:xs n+(1#2**PosS p)<<=y+(1#2**p)
(use "RealLeTrans" (pt "ys n+(1#2**PosS p)"))
(use "RealLeMonPlus")
(autoreal)
(use "LeHyp")
;; ?^24:ys n+(1#2**PosS p)<<=y+(1#2**p)
(use "RealLeTrans" (pt "y+(1#2**PosS p)+(1#2**PosS p)"))
(use "RealLeMonPlus")
(autoreal)
;; ?^30:ys n<<=y+(1#2**PosS p)
(use "RealLeAbsMinus1")
(autoreal)
(use "RConvLimElim" (pt "N"))
(use "RealConvLimToRConvLim")
(use "ysConv")
(simp "nDef")
(use "NatMaxUB2")
;; ?^28:y+(1#2**PosS p)+(1#2**PosS p)<<=y+(1#2**p)
(simpreal "<-" "RealPlusAssoc")
(use "RealLeMonPlusR")
(autoreal)
(use "RatLeToRealLe")
(simprat
 (pf "(2**PosS p+2**PosS p#2**PosS p*2**PosS p)==(1#2**PosS p)+(1#2**PosS p)"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimLe")

;; RealConvLimEq
(set-goal "all x,y,xs,ys,M,N(
 all n xs n===ys n -> RealConvLim xs x M -> RealConvLim ys y N -> x===y)")
(assume "x" "y" "xs" "ys" "M" "N" "EqHyp" "xsConv" "ysConv")
(use "RealLeAntiSym")
;; 3,4
(use "RealConvLimLe" (pt "xs") (pt "ys") (pt "M") (pt "N"))
(assume "n")
(use "RealEqElim0")
(use "EqHyp")
(use "xsConv")
(use "ysConv")
;; 4
(use "RealConvLimLe" (pt "ys") (pt "xs") (pt "N") (pt "M"))
(assume "n")
(use "RealEqElim1")
(use "EqHyp")
(use "ysConv")
(use "xsConv")
;; Proof finished.
;; (cp)
(save "RealConvLimEq")

;; RCauchyCompat
(set-goal "all xs,M,ys,N(
     all n xs n===ys n -> all p M p=N p -> RCauchy xs M -> RCauchy ys N)")
(assume "xs" "M" "ys" "N" "xs=ys" "M=N" "CxsM")
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(simpreal "<-" "xs=ys")
(simpreal "<-" "xs=ys")
(use "RCauchyElim" (pt "M"))
(use "CxsM")
(simp "M=N")
(use "nBd")
(simp "M=N")
(use "mBd")
;; Proof finished.
;; (cp)
(save "RCauchyCompat")

;; MonCompat
(set-goal "all M,N(all p M p=N p -> Mon M -> Mon N)")
(assume "M" "N" "M=N" "MonM")
(intro 0)
(assume "p" "q" "p<=q")
(simp "<-" "M=N")
(simp "<-" "M=N")
(use "MonElim")
(use "MonM")
(use "p<=q")
;; Proof finished.
;; (cp)
(save "MonCompat")

;; RealConvLimUniq
(set-goal "all xs,y,M,z,N(RealConvLim xs y M -> RealConvLim xs z N -> y===z)")
(assume "xs" "y" "M" "z" "N" "xsyConv" "xszConv")
(use "RealConvLimEq" (pt "xs") (pt "xs") (pt "M") (pt "N"))
(inst-with-to "RealConvLimElim1" (pt "xs") (pt "y") (pt "M") "xsyConv" "Rxs")
(assume "n")
(use "RealEqRefl")
(use "Rxs")
(use "xsyConv")
(use "xszConv")
;; Proof finished.
;; (cp)
(save "RealConvLimUniq")

;; Using RealConvLimUniq and RealCompleteCor we prove

;; RealLimConst
(set-goal "all x,M(Real x -> Mon M -> cRLim([n]x)M===x)")
(assume "x" "M" "Rx" "MonM")
(use "RealConvLimUniq" (pt "[n]x") (pt "M") (pt "M"))
;; 3,4
(use "RealCompleteCor")
(intro 0)
;; 6-8
(assume "n")
(use "Rx")
;; 7
(use "MonM")
;; ?^8:RCauchy([n]x)M
(intro 0)
(ng #t)
(assume "p" "n" "m" "nBd" "mBd")
(simpreal "RealPlusMinusZero")
(use "RatLeToRealLe")
(use "Truth")
(use "Rx")
;; ?^4:RealConvLim([n]x)x M
(intro 0)
;; 16-18
(assume "n")
(use "Rx")
;; 17
(use "Rx")
;; 18
(use "MonM")
;; 19
(intro 0)
(ng #t)
(assume "p" "n" "nBd")
(simpreal "RealPlusMinusZero")
(use "RatLeToRealLe")
(use "Truth")
(use "Rx")
;; Proof finished.
;; (cp)
(save "RealLimConst")

;; RConvLimCompat
(set-goal "all xs,x,M,ys,y,N(all n(xs n===ys n) -> x===y -> all p(M p=N p) ->
 RConvLim xs x M -> RConvLim ys y N)")
(assume "xs" "x" "M" "ys" "y" "N" "xs=ys" "x=y" "M=N" "CxsxM")
(intro 0)
;; 3-6
(assume "p" "n" "nBd")
(simpreal "<-" "xs=ys")
(simpreal "<-" "x=y")
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(simp "M=N")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RConvLimCompat")

;; RealConvLimCompat
(set-goal "all xs,x,M,ys,y,N(all n(xs n===ys n) -> x===y -> all p(M p=N p) ->
 RealConvLim xs x M -> RealConvLim ys y N)")
(assume "xs" "x" "M" "ys" "y" "N" "xs=ys" "x=y" "M=N" "CxsxM")
(intro 0)
;; 3-6
(assume "n")
(autoreal)
;; ?^5:Mon N
(intro 0)
(assume "p" "q" "p<=q")
(simp "<-" "M=N")
(simp "<-" "M=N")
(use "MonElim")
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=q")
;; ?^6:RConvLim ys y N
(use "RConvLimCompat" (pt "xs") (pt "x") (pt "M"))
(auto)
(use "RealConvLimToRConvLim")
(use "CxsxM")
;; Proof finished.
;; (cp)
(save "RealConvLimCompat")

;; RConvLimMonLe
(set-goal "all xs,x,M,N(RConvLim xs x M -> Mon N -> all p M p<=N p -> 
 RConvLim xs x N)")
(assume "xs" "x" "M" "N" "CxsxM" "NMon" "M<=N")
(intro 0)
;; 3-6
(assume "p" "n" "nBd")
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(use "NatLeTrans" (pt "N p"))
(auto)
;; Proof finished.
;; (cp)
(save "RConvLimMonLe")

;; RealConvLimMonLe
(set-goal "all xs,x,M,N(RealConvLim xs x M -> Mon N -> all p M p<=N p -> 
 RealConvLim xs x N)")
(assume "xs" "x" "M" "N" "CxsxM" "NMon" "M<=N")
(intro 0)
;; 3-6
(use "RealConvLimElim1" (pt "x") (pt "M"))
(use "CxsxM")
(autoreal)
;; 5
(use "NMon")
;; ?^6:RConvLim xs x N
(use "RConvLimMonLe" (pt "M"))
(use "RealConvLimToRConvLim")
(auto)
;; Proof finished.
;; (cp)
(save "RealConvLimMonLe")

;; RealConvLimPlusConstR
(set-goal "all xs,x,M,y(RealConvLim xs x M -> Real y ->
 RealConvLim([n]xs n+y)(x+y)M)")
(assume "xs" "x" "M" "y" "CxsxM" "Ry")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon M
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "CxsxM")
;; 6
(ng #t)
;; ?^10:RConvLim([n]xs n+y)(x+y)M
(intro 0)
(assume "p" "n" "nBd")
(simpreal (pf "x+y===y+x"))
(simpreal "RealUMinusPlus")
(ng #t)
(simpreal (pf "xs n+y+(~y+ ~x)===xs n+(y+ ~y+ ~x)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
;; ?^23:abs(xs n+ ~x)<<=(1#2**p)
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "CxsxM")
(use "nBd")
(autoreal)
;; ?^20:xs n+y+(~y+ ~x)===xs n+(y+ ~y+ ~x)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimPlusConstR")

;; RealConvLimPlusConstL
(set-goal "all xs,x,M,y(RealConvLim xs x M -> Real y ->
 RealConvLim([n]y+xs n)(y+x)M)")
(assume "xs" "x" "M" "y" "CxsxM" "Ry")
(use "RealConvLimCompat" (pt "[n]xs n+y") (pt "x+y") (pt "M"))
;; 3-6
(ng #t)
(assume "n")
(use "RealPlusComm")
(autoreal)
;; 4
(use "RealPlusComm")
(autoreal)
;; 5
(search)
;; 6
(use "RealConvLimPlusConstR")
(auto)
;; Proof finished.
;; (cp)
(save "RealConvLimPlusConstL")

;; RealConvLimPlus
(set-goal "all xs,x,M,ys,y,N(
 RealConvLim xs x M -> 
 RealConvLim ys y N ->
 RealConvLim([n]xs n+ys n)(x+y)([p]M(PosS p)max N(PosS p)))")
(assume "xs" "x" "M" "ys" "y" "N" "xsxConv" "ysyConv")
(intro 0)
;; 3-6
;; ?^3:all n Real(([n0]xs n0+ys n0)n)
(assume "n")
(ng #t)
;; ?^8:Real(xs n+ys n)
(autoreal)
;; ?^5:Mon([p]M(PosS p)max N(PosS p))
(intro 0)
(ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "xsxConv")
(use "p<=q")
(use "MonElim")
(use "RealConvLimToMon" (pt "ys") (pt "y"))
(use "ysyConv")
(use "p<=q")
;; ?^6:RConvLim([n]xs n+ys n)(x+y)([p]M(PosS p)max N(PosS p))
(intro 0)
(assume "p" "n")
(ng #t)
;; ?^22:M(PosS p)max N(PosS p)<=n -> abs(xs n+ys n+ ~(x+y))<<=(1#2**p)
(assume "nBd")
(simpreal (pf "xs n+ys n+ ~(x+y)===xs n+ ~x+(ys n+ ~y)"))
;; 24,25
(use "RealLeTrans" (pt "abs(xs n+ ~x)+abs(ys n+ ~y)"))
(use "RealLeAbsPlus")
(autoreal)
;; ?^27:abs(xs n+ ~x)+abs(ys n+ ~y)<<=(1#2**p)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
(use "RealLeMonPlusTwo")
;; 32,33
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "xsxConv")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "nBd")
;; ?^33:abs(ys n+ ~y)<<=(1#2**PosS p)
(use "RConvLimElim" (pt "N"))
(use "RealConvLimToRConvLim")
(use "ysyConv")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "nBd")
;; ?^31:RealPlus(1#2**PosS p)(1#2**PosS p)<<=(1#2**p)
(use "RatLeToRealLe")
(simprat
 (pf "(2**PosS p+2**PosS p#2**PosS p*2**PosS p)==(1#2**PosS p)+(1#2**PosS p)"))
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
;; ?^25:xs n+ys n+ ~(x+y)===xs n+ ~x+(ys n+ ~y)
(simpreal "RealUMinusPlus")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimPlus")

;; RealConvLimUMinus
(set-goal "all xs,x,M(RealConvLim xs x M -> RealConvLim([n]~(xs n))(~x)M)")
(assume "xs" "x" "M" "xsxConv")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon M
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "xsxConv")
;; ?^6:RConvLim([n]~(xs n))(~x)M
(intro 0)
;; ?^10:all p,n(M p<=n -> abs(([n0]~(xs n0))n+ ~ ~x)<<=(1#2**p))
(assume "p" "n" "nBd")
(ng #t)
;; ?^12:abs(~(xs n)+ ~ ~x)<<=(1#2**p)
(simpreal "<-" "RealUMinusPlus")
(simpreal "RealAbsUMinus")
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "xsxConv")
(use "nBd")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimUMinus")

;; RealConvLimTimesConstR
(set-goal "all xs,x,M,y,q(RealConvLim xs x M -> Real y -> abs y<<=2**q ->
 RealConvLim([n]xs n*y)(x*y)([p]M(p+q)))")
(assume "xs" "x" "M" "y" "q" "CxsxM" "Ry" "yBd")
(intro 0)
;; 3-6
(assume "n")
(ng #t)
(autoreal)
;; ?^5:Mon([p]M(p+q))
(intro 0)
(assume "p" "r" "p<=r")
(ng #t)
(use "MonElim")
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=r")
;; 6
(intro 0)
(ng #t)
(assume "p" "n" "nBd")
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(1#2**(p+q))(2**q)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
;; ?^32:abs(xs n+ ~x)<<=(1#2**(p+q))
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "CxsxM")
(use "nBd")
(use "yBd")
;; ?^29:RealTimes(1#2**(p+q))(2**q)<<=(1#2**p)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealConvLimTimesConstR")

;; RealConvLimTimesConstL
(set-goal "all xs,x,M,y,q(RealConvLim xs x M -> Real y -> abs y<<=2**q ->
 RealConvLim([n]y*xs n)(y*x)([p]M(p+q)))")
(assume "xs" "x" "M" "y" "q" "CxsxM" "Ry" "yBd")
(use "RealConvLimCompat" (pt "[n]xs n*y") (pt "x*y") (pt "[p]M(p+q)"))
;; 3-6
(ng #t)
(assume "n")
(use "RealTimesComm")
(autoreal)
;; 4
(use "RealTimesComm")
(autoreal)
;; 5
(search)
;; 6
(use "RealConvLimTimesConstR")
(auto)
;; Proof finished.
;; (cp)
(save "RealConvLimTimesConstL")

;; 2023-01-12.  RConvLimTimes reformulated s.t. the modulus is symmetric.

;; RConvLimTimes
(set-goal "all xs,x,M,ys,y,N,p,q,K(
 all n Real(xs n) ->
 all n Real(ys n) ->
 Real x ->
 Real y -> 
 RConvLim xs x M ->
 RConvLim ys y N ->
 all n(abs(xs n)<<=2**p) ->
 abs y<<=2**q ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RConvLim([n]xs n*ys n)(x*y)K)")
(assume "xs" "x" "M" "ys" "y" "N" "p" "q" "K" "Rxs" "Rys" "Rx" "Ry"
	"CxsxM" "CysyN" "xsBd" "yBd" "KDef")
(intro 0)
(assume "r" "n" "nBd")
(bpe-ng #t)
;; ?^5:abs(xs n*ys n+ ~(x*y))<<=(1#2**r)
(simpreal (pf "xs n*ys n+ ~(x*y)===xs n*(ys n)+ ~(xs n*y)+(xs n*y+ ~(x*y))"))
;; 6,7
(use "RealLeTrans" (pt "abs(xs n*ys n+ ~(xs n*y))+abs(xs n*y+ ~(x*y))"))
(use "RealLeAbsPlus")
(autoreal)
;; ?^9:abs(xs n*ys n+ ~(xs n*y))+abs(xs n*y+ ~(x*y))<<=(1#2**r)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS r)(1#2**PosS r)"))
(use "RealLeMonPlusTwo")
;; 14,15
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
;; ?^19:abs(xs n*(ys n+ ~y))<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "(2**p)*abs(ys n+ ~y)"))
;; 26,27
;; ?^26:abs(xs n)*abs(ys n+ ~y)<<=2**p*abs(ys n+ ~y)
(use "RealLeMonTimes")
(use "RealLeZeroAbs")
(autoreal)
;; ?^29:abs(xs n)<<=2**p
(use "xsBd")
;; ?^27:2**p*abs(ys n+ ~y)<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(2**p)(1#2**(p+r+1))"))
;; 31,32
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RConvLimElim" (pt "N"))
(use "CysyN")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB1")
(use "nBd")
;; 32
(use "RatLeToRealLe")
(simp "<-" "PosPlus0CompRule")
(ng #t)
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlusAssoc")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(use "Truth")
(autoreal)
;; ?^15:abs(xs n*y+ ~(x*y))<<=(1#2**PosS r)
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
;; ?^56:abs((xs n+ ~x)*y)<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
;; ?^60:abs(xs n+ ~x)*abs y<<=(1#2**PosS r)
(use "RealLeTrans" (pt "abs(xs n+ ~x)*(2**q)"))
;; 63,64
;; ?^63:abs(xs n+ ~x)*abs y<<=abs(xs n+ ~x)*2**q
(use "RealLeMonTimesR")
(use "RealLeZeroAbs")
(autoreal)
(use "yBd")
;; ?^64:abs(xs n+ ~x)*2**q<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(1#2**(q+r+1))(2**q)"))
;; 68,69
(use "RealLeMonTimes")
(use "RatLeToRealLe")
(use "Truth")
;; ?^71:abs(xs n+ ~x)<<=(1#2**(q+r+1))
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB2")
(use "nBd")
;; 69
(use "RatLeToRealLe")
(simp "<-" "PosPlus0CompRule")
(ng #t)
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlusAssoc")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(use "Truth")
(autoreal)
;; ?^13:RealPlus(1#2**PosS r)(1#2**PosS r)<<=(1#2**r)
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")
;; ?^7:xs n*ys n+ ~(x*y)===xs n*ys n+ ~(xs n*y)+(xs n*y+ ~(x*y))
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~(xs n*y)+xs n*y===xs n*y+ ~(xs n*y)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RConvLimTimes")

;; 2023-02-16.  RConvLimTimesSym symmetric version of RConvLimTimes

;; RConvLimTimesSym
(set-goal "all xs,x,M,ys,y,N,p,q,K(
 all n Real(xs n) ->
 all n Real(ys n) ->
 Real x ->
 Real y -> 
 RConvLim xs x M ->
 RConvLim ys y N ->
 all n(abs(xs n)<<=2**p) ->
 all n(abs(ys n)<<=2**q) ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RConvLim([n]xs n*ys n)(x*y)K)")
(assume "xs" "x" "M" "ys" "y" "N" "p" "q" "K" "Rxs" "Rys" "Rx" "Ry"
	"CxsxM" "CysyN" "xsBd" "ysBd" "KDef")
(intro 0)
(assume "r" "n" "nBd")
(bpe-ng #t)
;; ?^5:abs(xs n*ys n+ ~(x*y))<<=(1#2**r)
(simpreal (pf "xs n*ys n+ ~(x*y)===xs n*(ys n)+ ~(xs n*y)+(xs n*y+ ~(x*y))"))
;; 6,7
(use "RealLeTrans" (pt "abs(xs n*ys n+ ~(xs n*y))+abs(xs n*y+ ~(x*y))"))
(use "RealLeAbsPlus")
(autoreal)
;; ?^9:abs(xs n*ys n+ ~(xs n*y))+abs(xs n*y+ ~(x*y))<<=(1#2**r)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS r)(1#2**PosS r)"))
(use "RealLeMonPlusTwo")
;; 14,15
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
;; ?^19:abs(xs n*(ys n+ ~y))<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "(2**p)*abs(ys n+ ~y)"))
;; 26,27
;; ?^26:abs(xs n)*abs(ys n+ ~y)<<=2**p*abs(ys n+ ~y)
(use "RealLeMonTimes")
(use "RealLeZeroAbs")
(autoreal)
;; ?^29:abs(xs n)<<=2**p
(use "xsBd")
;; ?^27:2**p*abs(ys n+ ~y)<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(2**p)(1#2**(p+r+1))"))
;; 31,32
(use "RealLeMonTimesR")
(use "RatLeToRealLe")
(use "Truth")
(use "RConvLimElim" (pt "N"))
(use "CysyN")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB1")
(use "nBd")
;; 32
(use "RatLeToRealLe")
(simp "<-" "PosPlus0CompRule")
(ng #t)
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlusAssoc")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(use "Truth")
(autoreal)
;; ?^15:abs(xs n*y+ ~(x*y))<<=(1#2**PosS r)
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
;; ?^56:abs((xs n+ ~x)*y)<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
;; ?^60:abs(xs n+ ~x)*abs y<<=(1#2**PosS r)
(use "RealLeTrans" (pt "abs(xs n+ ~x)*(2**q)"))
;; 63,64
;; ?^63:abs(xs n+ ~x)*abs y<<=abs(xs n+ ~x)*2**q
(use "RealLeMonTimesR")
(use "RealLeZeroAbs")
(autoreal)
;; ?^66:abs y<<=2**q
(use "RealLeAllPlusToLe")
(autoreal)
(assume "p0")
;; ?^71:abs y<<=RealPlus(2**q)(1#2**p0)
;; Need n0 such that abs(ys n0+ ~y)<<=(1#2**p0).  Take (M p0)
;; (pp "RConvLimElim")
(assert "abs(ys(N p0)+ ~y)<<=(1#2**p0)")
(use "RConvLimElim" (pt "N"))
(use "CysyN")
(use "Truth")
;; Assertion proved.
(assume "Assertion")
(use "RealLeTrans" (pt "abs(ys(N p0))+abs(~(ys(N p0)+ ~y))"))
(use "RealLeTrans" (pt "abs(ys(N p0)+ ~(ys(N p0)+ ~y))"))
(simpreal "RealUMinusPlus")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(simpreal "RealUMinusUMinus")
(use "RealLeRefl")
(autoreal)
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlusTwo")
(use "ysBd")
(simpreal "RealAbsUMinus")
(use "RConvLimElim" (pt "N"))
(use "CysyN")
(use "Truth")
(autoreal)
;; ?^64:abs(xs n+ ~x)*2**q<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(1#2**(q+r+1))(2**q)"))
;; 103,104
(use "RealLeMonTimes")
(use "RatLeToRealLe")
(use "Truth")
;; ?^106:abs(xs n+ ~x)<<=(1#2**(q+r+1))
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB2")
(use "nBd")
;; 104
(use "RatLeToRealLe")
(simp "<-" "PosPlus0CompRule")
(ng #t)
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlus0CompRule")
(simp "<-" "PosPlusAssoc")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(simp "PosToNatPlus")
(simp "<-" "PosExpTwoNatPlus")
(use "Truth")
(autoreal)
;; ?^13:RealPlus(1#2**PosS r)(1#2**PosS r)<<=(1#2**r)
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")
;; ?^7:xs n*ys n+ ~(x*y)===xs n*ys n+ ~(xs n*y)+(xs n*y+ ~(x*y))
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~(xs n*y)+xs n*y===xs n*y+ ~(xs n*y)"))
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RConvLimTimesSym")

;; RealConvLimTimes
(set-goal "all xs,x,M,ys,y,N,p,q,K(
 RealConvLim xs x M -> RealConvLim ys y N ->
 all n(abs(xs n)<<=2**p) ->
 abs y<<=2**q ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RealConvLim([n]xs n*ys n)(x*y)K)")
(assume "xs" "x" "M" "ys" "y" "N" "p" "q" "K"
	"CxsxM" "CysyN" "xsBd" "yBd" "KDef")
(inst-with-to "RealConvLimElim1" (pt "xs") (pt "x") (pt "M") "CxsxM" "Rxs")
(inst-with-to "RealConvLimElim1" (pt "ys") (pt "y") (pt "N") "CysyN" "Rys")
(inst-with-to "RealConvLimElim2" (pt "xs") (pt "x") (pt "M") "CxsxM" "Rx")
(inst-with-to "RealConvLimElim2" (pt "ys") (pt "y") (pt "N") "CysyN" "Ry")
(inst-with-to "RealConvLimToMon" (pt "xs") (pt "x") (pt "M") "CxsxM" "MonM")
(inst-with-to "RealConvLimToMon" (pt "ys") (pt "y") (pt "N") "CysyN" "MonN")
(inst-with-to "RealConvLimToRConvLim" (pt "xs") (pt "x") (pt "M") "CxsxM" "RCxsx")
(inst-with-to "RealConvLimToRConvLim" (pt "ys") (pt "y") (pt "N") "CysyN" "RCysy")
(drop "CxsxM" "CysyN")
(intro 0)
;; 20-23
(assume "n")
(autoreal)
;; ?^22:Mon K
(intro 0)
(assume "p0" "q0" "p0<=q0")
(simp "KDef")
(simp "KDef")
(use "NatLeMonMax")
(use "MonElim")
(use "MonN")
(ng #t)
(use "p0<=q0")
(use "MonElim")
(use "MonM")
(ng #t)
(use "p0<=q0")
;; ?^23:RConvLim([n]xs n*ys n)(x*y)L
(use "RConvLimTimes" (pt "M") (pt "N") (pt "p") (pt "q"))
;; 37-46
(auto)
;; Proof finished.
;; (cp)
(save "RealConvLimTimes")

;; RealConvLimTimesSym
(set-goal "all xs,x,M,ys,y,N,p,q,K(
 RealConvLim xs x M -> RealConvLim ys y N ->
 all n(abs(xs n)<<=2**p) ->
 all n(abs(ys n)<<=2**q) ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RealConvLim([n]xs n*ys n)(x*y)K)")
(assume "xs" "x" "M" "ys" "y" "N" "p" "q" "K"
	"CxsxM" "CysyN" "xsBd" "ysBd" "KDef")
(inst-with-to "RealConvLimElim1" (pt "xs") (pt "x") (pt "M") "CxsxM" "Rxs")
(inst-with-to "RealConvLimElim1" (pt "ys") (pt "y") (pt "N") "CysyN" "Rys")
(inst-with-to "RealConvLimElim2" (pt "xs") (pt "x") (pt "M") "CxsxM" "Rx")
(inst-with-to "RealConvLimElim2" (pt "ys") (pt "y") (pt "N") "CysyN" "Ry")
(inst-with-to "RealConvLimToMon" (pt "xs") (pt "x") (pt "M") "CxsxM" "MonM")
(inst-with-to "RealConvLimToMon" (pt "ys") (pt "y") (pt "N") "CysyN" "MonN")
(inst-with-to "RealConvLimToRConvLim" (pt "xs") (pt "x") (pt "M") "CxsxM" "RCxsx")
(inst-with-to "RealConvLimToRConvLim" (pt "ys") (pt "y") (pt "N") "CysyN" "RCysy")
(drop "CxsxM" "CysyN")
(intro 0)
;; 20-23
(assume "n")
(autoreal)
;; ?^22:Mon K
(intro 0)
(assume "p0" "q0" "p0<=q0")
(simp "KDef")
(simp "KDef")
(use "NatLeMonMax")
(use "MonElim")
(use "MonN")
(ng #t)
(use "p0<=q0")
(use "MonElim")
(use "MonM")
(ng #t)
(use "p0<=q0")
;; ?^23:RConvLim([n]xs n*ys n)(x*y)L
(use "RConvLimTimesSym" (pt "M") (pt "N") (pt "p") (pt "q"))
;; 37-46
(auto)
;; Proof finished.
;; (cp)
(save "RealConvLimTimesSym")

;; RealCauchyCompat
(set-goal "all xs,M,ys,N(
     all n xs n===ys n -> all p M p=N p -> RealCauchy xs M -> RealCauchy ys N)")
(assume "xs" "M" "ys" "N" "xs=ys" "M=N" "CxsM")
(intro 0)
;; 3-5
;; ?^3:all n Real(ys n)
(assume "n")
(autoreal)
;; ?^4:Mon N
(use "MonCompat" (pt "M"))
(use "M=N")
(use "RealCauchyToMon" (pt "xs"))
(use "CxsM")
;; ?^5:RCauchy ys N
(use "RCauchyCompat" (pt "xs") (pt "M"))
(use "xs=ys")
(use "M=N")
(use "RealCauchyToRCauchy")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealCauchyCompat")

;; 2023-03-30
;; RCauchyMon
(set-goal "all xs,M,N(all p M p<=N p -> RCauchy xs M -> RCauchy xs N)")
(assume "xs" "M" "N" "M<=N" "CxsM")
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(use "RCauchyElim" (pt "M"))
(use "CxsM")
(use "NatLeTrans" (pt "N p"))
(use "M<=N")
(use "nBd")
(use "NatLeTrans" (pt "N p"))
(use "M<=N")
(use "mBd")
;; Proof finished.
;; (cp)
(save "RCauchyMon")

;; RealCauchyMon
(set-goal "all xs,M,N(all p M p<=N p -> Mon N -> 
 RealCauchy xs M -> RealCauchy xs N)")
(assume "xs" "M" "N" "M<=N" "MonN" "CxsM")
(intro 0)
(use "RealCauchyToReals" (pt "M"))
(use "CxsM")
(use "MonN")
(use "RCauchyMon" (pt "M"))
(use "M<=N")
(use "RealCauchyToRCauchy")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealCauchyMon")

;; 2022-12-26
;; RCauchyAbs
(set-goal "all xs,M(
 all n Real(xs n) ->
 RCauchy xs M -> RCauchy([n]abs(xs n))M)")
(assume "xs" "M" "Rxs" "CxsM")
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(ng #t)
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))"))
(use "RealLeAbsMinusAbs")
(autoreal)
(use "RCauchyElim" (pt "M"))
(auto)
;; Proof finished.
;; (cp)
(save "RCauchyAbs")

;; RealCauchyAbs
(set-goal "all xs,M(RealCauchy xs M -> RealCauchy([n]abs(xs n))M)")
(assume "xs" "M" "CxsM")
(inst-with-to "RealCauchyToReals" (pt "xs") (pt "M") "CxsM" "Rxs")
(inst-with-to "RealCauchyToMon" (pt "xs") (pt "M") "CxsM" "MonM")
(inst-with-to "RealCauchyToRCauchy" (pt "xs") (pt "M") "CxsM" "RCxsM")
(intro 0)
(assume "n")
(ng #t)
(autoreal)
(use "MonM")
(use "RCauchyAbs")
(use "Rxs")
(use "RCxsM")
;; Proof finished.
;; (cp)
(save "RealCauchyAbs")

;; RConvLimToRCauchy
(set-goal "all xs,x,M(all n Real(xs n) -> Real x -> 
 RConvLim xs x M -> RCauchy xs([p]M(PosS p)))")
(assume "xs" "x" "M" "Rxs" "Rx" "CxsxM")
(intro 0)
(assume "p" "n" "m")
(ng #t)
(assume "nBd" "mBd")
;; ?^6:abs(xs n+ ~(xs m))<<=(1#2**p)
(use "RealLeTrans" (pt "abs(xs n+ ~x)+abs(x+ ~(xs m))"))
(use "RealLeAbsMinus")
(use "Rxs")
(use "Rxs")
(use "Rx")
;; 8
(simpreal (pf "abs(x+ ~(xs m))===abs((xs m)+ ~x)"))
(use "RealLeTrans" (pt "RealPlus(1#2**PosS p)(1#2**PosS p)"))
;; 14,15
(use "RealLeMonPlusTwo")
;; 16,17
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(use "nBd")
;; 17
(use "RConvLimElim" (pt "M"))
(use "CxsxM")
(use "mBd")
;; 15
(simpreal "RealPlusHalfExpPosS")
(use "RatLeToRealLe")
(use "Truth")
;; 13
(use "RealAbsPlusUMinus")
(use "Rx")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RConvLimToRCauchy")

;; RealConvLimToCauchy
(set-goal "all xs,x,M(RealConvLim xs x M -> RealCauchy xs([p]M(PosS p)))")
(assume "xs" "x" "M" "CxsxM")
(intro 0)
;; 3-5
(use "RealConvLimElim1" (pt "x") (pt "M"))
(use "CxsxM")
;; 4
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "MonElim")
(use "RealConvLimToMon" (pt "xs") (pt "x"))
(use "CxsxM")
(use "p<=q")
;; ?^5:RCauchy xs([p]M(PosS p))
(use "RConvLimToRCauchy" (pt "x"))
;; 13-15
(use "RealConvLimElim1" (pt "x") (pt "M"))
(use "CxsxM")
;; 14
(use "RealConvLimElim2" (pt "xs") (pt "M"))
(use "CxsxM")
;; 15
(use "RealConvLimToRConvLim")
(use "CxsxM")
;; Proof finished.
;; (cp)
(save "RealConvLimToCauchy")

;; 2022-12-23.  We prove a variant of RealConvLimTimes where the limit
;; is not needed but instead bounds on the members of xs, ys.

;; RCauchyBdTimes
(set-goal "all xs,M,ys,N,p,q,K(
 all n Real(xs n) -> all n Real(ys n) ->
 RCauchy xs M -> RCauchy ys N ->
 Mon M -> Mon N ->
 all n abs(xs n)<<=2**p ->
 all n abs(ys n)<<=2**q ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RCauchy([n]xs n*ys n)K)")
(assume "xs" "M" "ys" "N" "p" "q" "K"
	"Rxs" "Rys" "xsConv" "ysConv" "MonM" "MonN" "xsBd" "ysBd" "KDef")
(intro 0)
(assume "r" "n" "m" "nBd" "mBd")
(ng #t)
;; ?^5:abs(xs n*ys n+ ~(xs m*ys m))<<=(1#2**r)
(simpreal (pf "xs n*ys n+ ~((xs m)*(ys m))===
               xs n*ys n+ ~(xs n*ys m)+(xs n*ys m)+ ~(xs m*ys m)"))
;; 6,7
(use "RealLeTrans"
     (pt "abs(xs n*ys n+ ~(xs n*ys m))+abs(xs n*ys m+ ~(xs m*ys m))"))
(simpreal "<-" "RealPlusAssoc")
(use "RealLeAbsPlus")
(autoreal)
;; ?^9:abs(xs n*ys n+ ~(xs n*ys m))+abs(xs n*ys m+ ~(xs m*ys m))<<=(1#2**r)
(use "RealLeTrans" (pt "RealPlus(1#2**PosS r)(1#2**PosS r)"))
(use "RealLeMonPlusTwo")
;; 18,19
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
;; ?^23:abs(xs n*(ys n+ ~(ys m)))<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
;; ?^27:abs(xs n)*abs(ys n+ ~(ys m))<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(2**p)(1#2**(p+r+1))"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "xsBd")
;; ?^35:abs(ys n+ ~(ys m))<<=(1#2**(p+r+1))
(use "RCauchyElim" (pt "N"))
(use "ysConv")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB1")
(use "mBd")
;; ?^31:RealTimes(2**p)(1#2**(p+r+1))<<=(1#2**PosS r)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoNatPlus")
(use "PosLeMonPosExp")
(simp "<-" "PosPlus2RewRule")
(simp "PosToNatPlus")
(use "NatLeMonPlus")
(use "Truth")
(use "Truth")
(autoreal)
;; ?^19:abs(xs n*ys m+ ~(xs m*ys m))<<=(1#2**PosS r)
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
;; ?^58:abs((xs n+ ~(xs m))*ys m)<<=(1#2**PosS r)
(simpreal "RealAbsTimes")
;; ?^62:abs(xs n+ ~(xs m))*abs(ys m)<<=(1#2**PosS r)
(use "RealLeTrans" (pt "RealTimes(1#2**(q+r+1))(2**q)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
;; ?^69:abs(xs n+ ~(xs m))<<=(1#2**(q+r+1))
(use "RCauchyElim" (pt "M"))
(use "xsConv")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "K r"))
(simp "KDef")
(use "NatMaxUB2")
(use "mBd")
;; ?^70:abs(ys m)<<=2**q
(use "ysBd")
;; ?^66:RealTimes(1#2**(q+r+1))(2**q)<<=(1#2**PosS r)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoNatPlus")
(use "PosLeMonPosExp")
(simp "<-" "PosPlus2RewRule")
(simp "PosToNatPlus")
(use "NatLeMonPlus")
(use "Truth")
(use "Truth")
(autoreal)
;; ?^17:RealPlus(1#2**PosS r)(1#2**PosS r)<<=(1#2**r)
(simpreal "RealPlusHalfExpPosS")
(use "RealLeRefl")
(autoreal)
;; ?^7:xs n*ys n+ ~(xs m*ys m)===xs n*ys n+ ~(xs n*ys m)+xs n*ys m+ ~(xs m*ys m)
(use "RealPlusCompat")
(use "RealEqTrans" (pt "xs n*ys n+0"))
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusMinusZero")
(simpreal "RealPlusComm")
(simpreal "RealPlusMinusZero")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RCauchyBdTimes")

;; RealCauchyBdTimes
(set-goal "all xs,M,ys,N,p,q,K(
 RealCauchy xs M -> RealCauchy ys N ->
 all n abs(xs n)<<=2**p ->
 all n abs(ys n)<<=2**q ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RealCauchy([n]xs n*ys n)K)")
(assume "xs" "M" "ys" "N" "p" "q" "K"	"xsConv" "ysConv" "xsBd" "ysBd" "KDef")
(inst-with-to "RealCauchyToReals" (pt "xs") (pt "M") "xsConv" "Rxs")
(inst-with-to "RealCauchyToReals" (pt "ys") (pt "N") "ysConv" "Rys")
(inst-with-to "RealCauchyToMon" (pt "xs") (pt "M") "xsConv" "MonM")
(inst-with-to "RealCauchyToMon" (pt "ys") (pt "N") "ysConv" "MonN")
(inst-with-to "RealCauchyToRCauchy" (pt "xs") (pt "M") "xsConv" "RCxs")
(inst-with-to "RealCauchyToRCauchy" (pt "ys") (pt "N") "ysConv" "RCys")
(drop "xsConv" "ysConv")
(intro 0)
;; 16-18
(assume "n")
(autoreal)
;; ?^17:Mon K
(intro 0)
(assume "p0" "q0" "p0<=q0")
(simp "KDef")
(simp "KDef")
(use "NatLeMonMax")
(use "MonElim")
(use "MonN")
(use "p0<=q0")
(use "MonElim")
(use "MonM")
(use "p0<=q0")
;; ?^18:RCauchy([n]xs n*ys n)K
(use "RCauchyBdTimes" (pt "M") (pt "N") (pt "p") (pt "q"))
(auto)
;; Proof finished.
;; (cp)
(save "RealCauchyBdTimes")

;; RealCauchyBdTimesCor
(set-goal "all xs,ys,xs0,M,ys0,N,p,q,K(
 all n Real(xs n) -> 
 all n Real(ys n) -> 
 all n xs0 n===RealSum Zero n([i]abs(xs i)) ->
 all n ys0 n===RealSum Zero n([j]abs(ys j)) ->
 RealCauchy xs0 M -> 
 RealCauchy ys0 N -> 
 all n xs0 n<<=2**p -> 
 all n ys0 n<<=2**q ->
 all r K r=N(p+r+1)max M(q+r+1) ->
 RealCauchy([n]xs0 n*ys0 n)K)")
(assume "xs" "ys" "xs0" "M" "ys0" "N" "p" "q" "K" "Rxs" "Rys" "xs0Def" "ys0Def"
	"Cxs0M" "Cys0N" "pBd" "qBd" "KDef")
(use "RealCauchyBdTimes" (pt "M") (pt "N") (pt "p") (pt "q"))
(auto)
;; ?^5:all n abs(xs0 n)<<=2**p
(assume "n")
(simpreal "xs0Def")
(simpreal "RealEqAbsId")
(simpreal "<-" "xs0Def")
(use "pBd")
;; ?^11:0<<=RealSum Zero n([i]abs(xs i))
(use "RealLeTrans" (pt "RealSum Zero n([i]0)"))
;; ?^13:0<<=RealSum Zero n([n0]0)
(ind (pt "n"))
;; 15,16
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 16
(assume "n0" "IH")
(ng #t)
(simpreal "RealPlusZero")
(use "IH")
(autoreal)
;; ?^14:RealSum Zero n([n0]0)<<=RealSum Zero n([i]abs(xs i))
(use "RealLeMonSum")
(assume "m" "Useless" "m<n")
(ng #t)
(use "RealLeZeroAbs")
(use "Rxs")
;; ?^6:all n abs(ys0 n)<<=2**q
(assume "n")
(simpreal "ys0Def")
(simpreal "RealEqAbsId")
(simpreal "<-" "ys0Def")
(use "qBd")
;; ?^30:0<<=RealSum Zero n([j]abs(ys j))
(use "RealLeTrans" (pt "RealSum Zero n([j]0)"))
;; ?^32:0<<=RealSum Zero n([n0]0)
(ind (pt "n"))
;; 34,35
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 35
(assume "n0" "IH")
(ng #t)
(simpreal "RealPlusZero")
(use "IH")
(autoreal)
;; ?^33:RealSum Zero n([n0]0)<<=RealSum Zero n([j]abs(ys j))
(use "RealLeMonSum")
(assume "m" "Useless" "m<n")
(ng #t)
(use "RealLeZeroAbs")
(use "Rys")
;; ?^7:all r K r=N(p+r+1)max M(q+r+1)
(use "KDef")
;; Proof finished.
;; (cp)
(save "RealCauchyBdTimesCor")

;; 2022-12-24.
;; RCauchyPlusConvZero
(set-goal "all xs,M,zs,N,K(
 all n Real(xs n) ->
 all n Real(zs n) ->
 RCauchy xs M -> RConvLim zs 0 N ->
 all p K p=M(PosS p)max N(PosS(PosS p)) ->
 RCauchy([n]xs n+zs n)K)")
(assume "xs" "M" "zs" "N" "K" "Rxs" "Rzs" "CxsM" "Czs0N" "KDef")
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(ng #t)
;; ?^5:abs(xs n+zs n+ ~(xs m+zs m))<<=(1#2**p)
(simpreal "RealUMinusPlus")
(simpreal (pf "xs n+zs n+(~(xs m)+ ~(zs m))===xs n+ ~(xs m)+zs n+  ~(zs m)"))
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m)+zs n)+abs~(zs m)"))
(use "RealLeAbsPlus")
(autoreal)
(simpreal "RealAbsUMinus")
(use "RealLeTrans" (pt "abs(xs n+ ~(xs m))+abs(zs n)+abs(zs m)"))
(use "RealLeMonPlus")
(autoreal)
(use "RealLeAbsPlus")
(autoreal)
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlusTwo")
;; 28,29
(use "RCauchyElim" (pt "M"))
(use "CxsM")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB1")
(use "mBd")
;; 29
(simpreal "<-" "RealPlusHalfExpPosS")
(use "RealLeMonPlusTwo")
;; 40,41
;; ?^40:abs(zs n)<<=(1#2**PosS(PosS p))
(simpreal "<-" (pf "zs n+ RealUMinus 0===zs n"))
(use "RConvLimElim" (pt "N"))
(use "Czs0N")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB2")
(use "nBd")
(ng #t)
(use "RealPlusZero")
(autoreal)
;; ?^41:abs(zs m)<<=(1#2**PosS(PosS p))
(simpreal "<-" (pf "zs m+ RealUMinus 0===zs m"))
(use "RConvLimElim" (pt "N"))
(use "Czs0N")
(use "NatLeTrans" (pt "K p"))
(simp "KDef")
(use "NatMaxUB2")
(use "mBd")
(ng #t)
(use "RealPlusZero")
(autoreal)
;; ?^10:xs n+zs n+(~(xs m)+ ~(zs m))===xs n+ ~(xs m)+zs n+ ~(zs m)
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RCauchyPlusConvZero")

;; RealCauchyPlusConvZero
(set-goal "all xs,M,zs,N,K(
 RealCauchy xs M -> RealConvLim zs 0 N ->
 all p K p=M(PosS p)max N(PosS(PosS p)) ->
 RealCauchy([n]xs n+zs n)K)")
(assume "xs" "M" "zs" "N" "K" "CxsM" "Czs0N" "KDef")
(inst-with-to "RealCauchyToReals" (pt "xs") (pt "M") "CxsM" "Rxs")
(inst-with-to
 "RealConvLimElim1"
 (pt "zs") (pt "RealConstr([n](0#1))([p]Zero)") (pt "N") "Czs0N" "Rzs")
(inst-with-to "RealCauchyToMon" (pt "xs") (pt "M") "CxsM" "MonM")
(inst-with-to
 "RealConvLimToMon"
 (pt "zs") (pt "RealConstr([n](0#1))([p]Zero)") (pt "N") "Czs0N" "MonN")
(inst-with-to "RealCauchyToRCauchy" (pt "xs") (pt "M") "CxsM" "xsConv")
(inst-with-to
 "RealConvLimToRConvLim"
 (pt "zs") (pt "RealConstr([n](0#1))([p]Zero)") (pt "N") "Czs0N" "zs0Conv")
(drop "CxsM" "Czs0N")
(intro 0)
(assume "n")
(autoreal)
;; ?^17:Mon K
(intro 0)
(assume "p" "q" "p<=q")
(simp "KDef")
(simp "KDef")
(use "NatLeMonMax")
(use "MonElim")
(use "MonM")
(use "p<=q")
(use "MonElim")
(use "MonN")
(use "p<=q")
;; ?^18:RCauchy([n]xs n+zs n)K
(use "RCauchyPlusConvZero" (pt "M") (pt "N"))
(auto)
;; Proof finished.
;; (cp)
(save "RealCauchyPlusConvZero")

;; As an example we prove that the geometric sequence converges to 0,
;; with an explicit modulus of convergence.

;; GeomSeqRealConvLimAux
(set-goal "all p,x,q,n(
     Real x ->
     RealPos(1+ ~(abs x))p -> PosPred(2**PosS p)*q<=n -> abs(x**n)<<=(1#2**q))")
(assume "p" "x" "q" "n" "Rx" "absx<1" "Mq<=n")
(use "RealLeTrans" (pt "RealExp(1+ RealUMinus(1#2**PosS p))n"))
;; 3,4
(simpreal "RealAbsExp")
(use "RealLeMonExpBase")
(use "RealLeZeroAbs")
(use "Rx")
(use "RealLePlusUMinusR")
(autoreal)
(use "RealPosToLe")
(autoreal)
(use "absx<1")
(use "Rx")
;; ?^4:(1+ ~(1#2**PosS p))**n<<=(1#2**q)
(use "RealLeCompat"
     (pt "RealConstr([m](1+ ~(1#2**(PosS p)))**n)([p]Zero)")
     (pt "RealConstr([n]1#2**q)([p]Zero)"))
;; 15-17
(use "RatExpRealExp")
(use "RealEqRefl")
(use "RealRat")
;; ?^17:(1+ ~(1#2**PosS p))**n<<=(1#2**q)
(use "RatLeToRealLe")
(ng #t)
;; ?^20:([if (2**PosS p=1) 0 (2**PosS p--1)]#2**PosS p)**n<=(1#2**q)
(simp "PosMinusOnePred")
;; ?^21:([if (2**PosS p=1) 0 (PosPred(2**PosS p))]#2**PosS p)**n<=(1#2**q)
(assert "2**(PosS p) = 1 -> F")
(assume "2**(p+1)=1")
(assert "2<=1")
(use "PosLeTrans" (pt "2**(PosS p)"))
(use "Truth")
(simp "2**(p+1)=1")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(assume "2**(p+1)/=1")
(simp "2**(p+1)/=1")
(ng #t)
(use "RatLeUDivUDivInv")
(use "Truth")
;; ?^36:RatUDiv(1#2**q)<=RatUDiv((PosPred(2**PosS p)#2**PosS p)**n)
(simprat "RatUDivExp")
;; ?^37:RatUDiv(1#2**q)<=RatUDiv(PosPred(2**PosS p)#2**PosS p)**n
(ng #t)
;; ?^38:2**q<=(2**PosS p#PosPred(2**PosS p))**n
(assert "all p0 p0*(1#p0)==1")
(assume "p0")
(use "Truth")
(assume "RatTimesInv")
(simp
 "RatLeCompat"
 (pt "(1+PosToNat(PosPred(2**PosS p))*(1#(PosPred(2**PosS p))))**(PosToNat q)")
 (pt "(1+(1#(PosPred(2**PosS p))))**n"))
;; 43-45
;; ?^43:(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q<=
;;      (1+(1#PosPred(2**PosS p)))**n
(use
 "RatLeTrans"
 (pt "((1+(1#(PosPred(2**PosS p))))**(PosToNat(PosPred(2**PosS p))))**
      (PosToNat q)"))
;; 46,47
;; ?^46:(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q<=
;;      (1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)**q
(use "RatLeMonExpBase")
;; 48,49
(simp "PosToNatToIntId")
(simprat "RatTimesInv")
(use "Truth")
;; ?^49:1+PosPred(2**PosS p)*(1#PosPred(2**PosS p))<=
;;      (1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)
(use "RatLeExpBernoulli")
;; ?^52:~1<=(1#PosPred(2**PosS p))
(use "Truth")
;; ?^47:(1+(1#PosPred(2**PosS p)))**PosPred(2**PosS p)**q<=
;;      (1+(1#PosPred(2**PosS p)))**n
(simprat "<-" "RatExpNatTimes")
(simp "<-" "PosToNatTimes")
(use "RatLeMonExp")
(use "Truth")
(use "Mq<=n")
;; ?^45:(2**PosS p#PosPred(2**PosS p))**n==(1+(1#PosPred(2**PosS p)))**n
(use "RatExpCompat")
;; ?^57:(2**PosS p#PosPred(2**PosS p))==1+(1#PosPred(2**PosS p))
(use "RatEqvTimesCancelR" (pt "(PosPred(2**PosS p)#1)"))
;; 58,59
;; ?^58:0<abs(PosPred(2**PosS p))
(use "RatNotZeroToZeroLtAbs")
;; ?^60:PosPred(2**PosS p)==0 -> F
(ng #t)
(assume "Absurd")
(use "Absurd")
;; ?^59:(2**PosS p#PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      (1+(1#PosPred(2**PosS p)))*PosPred(2**PosS p)
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "all p (1#p)*p==1"))
(simprat "<-" (pf "all p,q p*(RatUDiv q)==(p#q)")) ;RatTimesUDiv
;; 66,67
;; ?^66:2**PosS p*RatUDiv(PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      RatTimes 1(PosPred(2**PosS p))+1
(simp "<-" "RatTimesAssoc")
(simprat (pf "RatUDiv(PosPred(2**PosS p))*(PosPred(2**PosS p))==
              (PosPred(2**PosS p))*RatUDiv(PosPred(2**PosS p))"))
(simprat "RatTimesUDivR")
(ng #t)
;; ?^73:2**PosS p=PosS(PosPred(2**PosS p))
(simp "PosSPosPredId")
(use "Truth")
(use "Truth")
;; ?^72:0<abs(PosPred(2**PosS p))
(use "RatNotZeroToZeroLtAbs")
;; ?^76:PosPred(2**PosS p)==0 -> F
(ng #t)
(assume "Absurd")
(use "Absurd")
;; ?^70:RatUDiv(PosPred(2**PosS p))*PosPred(2**PosS p)==
;;      PosPred(2**PosS p)*RatUDiv(PosPred(2**PosS p))
(use "Truth")
;; ?^67:all p,q p*RatUDiv q==(p#q)
(strip)
(use "Truth")
;; ?^65:all p (1#p)*p==1
(strip)
(use "Truth")
;; ?^44:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "PosToNatToIntId")
;; ?^81:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "PosToNatToIntId")
;; ?^82:2**q==(1+PosPred(2**PosS p)*(1#PosPred(2**PosS p)))**q
(simp "RatTimes0CompRule")
(simp (pf "2**q=RatExp 2 q"))
(use "RatExpCompat")
(simp "PosTimes0RewRule")
(simp "IntTimes1RewRule")
(simp (pf "2=RatPlus 1 1"))
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished
;; (cp)
(save "GeomSeqRealConvLimAux")

;; (pp "GeomSeqConv")

;; We show that convergence also holds in the sense that we can prove
;; RealConvLim([n]x**n)0([q]PosPred(2**PosS p)*q)

;; GeomSeqRealConvLim
(set-goal "all x,p,M(
 Real x -> 
 RealPos(1+ ~abs x)p ->
 all q M q=PosToNat(PosPred(2**PosS p)*q) ->
 RealConvLim([n]x**n)0 M)")
(assume "x" "p" "M" "Rx" "absx<1" "MDef")
(intro 0)
;; 3-6
(ng #t)
(assume "n")
(autoreal)
;; ?^5:Mon M
(intro 0)
(assume "p1" "q" "p1<=q")
(simp "MDef")
(simp "MDef")
(simp "PosToNatLe")
(use "p1<=q")
;; ?^6:RConvLim([n]x**n)0 M
(intro 0)
(assume "q" "n")
(simp "MDef")
(assume "nBd")
(ng #t)
(simpreal "RealPlusZero")
(use "GeomSeqRealConvLimAux" (pt "p"))
(use "Rx")
(use "absx<1")
(use "nBd")
(autoreal)
;; Proof finished.
;; (cp)
(save "GeomSeqRealConvLim")

;; 2.  Series
;; ==========

(add-ids
 (list (list "RSerConvLim"
	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
 '("all xs,x,M(all p,n(M p<=n -> abs(cRSum Zero(Succ n)xs+ ~x)<<=(1#2**p)) ->
               RSerConvLim xs x M)"
   "RSerConvLimIntro"))

;; RSerConvLimElim
(set-goal "all xs,x,M(
     RSerConvLim xs x M -> 
     all p,n(M p<=n -> abs(cRSum Zero(Succ n)xs+ ~x)<<=(1#2**p)))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RSerConvLimElim")

(add-ids
 (list (list "RealSerConvLim"
	     (make-arity (py "nat=>rea") (py "rea") (py "pos=>nat"))))
 '("all xs,x,M(all n Real(xs n) -> Real x -> Mon M -> RSerConvLim xs x M ->
               RealSerConvLim xs x M)" "RealSerConvLimIntro"))

;; RealSerConvLimToReals
(set-goal "all xs,x,M(RealSerConvLim xs x M -> all n Real(xs n))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvLimToReals")

;; RealSerConvLimToReal
(set-goal "all xs,x,M(RealSerConvLim xs x M -> Real x)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvLimToReal")

;; RealSerConvLimToMon
(set-goal "all xs,x,M(RealSerConvLim xs x M -> Mon M)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvLimToMon")

;; RealSerConvLimToRSerConvLim
(set-goal "all xs,x,M(RealSerConvLim xs x M -> RSerConvLim xs x M)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvLimToRSerConvLim")

;; Need to relate RealSerConvLim with RealConvLim

;; RSerConvLimToRConvLimSum
(set-goal "all xs,x,M(
 RSerConvLim xs x M -> RConvLim([n]cRSum Zero(Succ n)xs)x M)")
(assume "xs" "x" "M" "CxsxM")
(intro 0)
(ng #t)
(assume "p" "n" "nBd")
(use "RSerConvLimElim" (pt "M"))
(use "CxsxM")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RSerConvLimToRConvLimSum")

;; RealSerConvLimToRealConvLimSum
(set-goal "all xs,x,M(
 RealSerConvLim xs x M -> RealConvLim([n]cRSum Zero(Succ n)xs)x M)")
(assume "xs" "x" "M" "CxsxM")

(assert "Real x")
(use "RealSerConvLimToReal" (pt "xs") (pt "M"))
(use "CxsxM")
(assume "Rx")

(assert "all n Real(xs n)")
(use "RealSerConvLimToReals" (pt "x") (pt "M"))
(use "CxsxM")
(assume "Rxs")
(intro 0)
(ng #t)
(assume "n")
(simp "RSumExFree")
(autoreal)

;; ?^13:Mon M
(use "RealSerConvLimToMon" (pt "xs") (pt "x"))
(use "CxsxM")

;; ?^14:RConvLim([n]cRSum Zero(Succ n)xs)x M
(use "RSerConvLimToRConvLimSum")
(use "RealSerConvLimToRSerConvLim")
(use "CxsxM")
;; Proof finished.
;; (cp)
(save "RealSerConvLimToRealConvLimSum")

;; RealSerConvLimUniq (was RealSerConvLimEq)
(set-goal "all x,y,xs,ys,M,N(
 all n xs n===ys n -> RealSerConvLim xs x M -> RealSerConvLim ys y N -> x===y)")
(assume "x" "y" "xs" "ys" "M" "N" "EqHyp" "xsConv" "ysConv")
(use "RealConvLimEq"
     (pt "[n]cRSum Zero(Succ n)xs") (pt "[n]cRSum Zero(Succ n)ys")
(pt "M") (pt "N"))
;; 3,4
(assume "n")
(bpe-ng #t)
(simp "RSumExFree")
(simp "RSumExFree")
(use "RealSumCompat")
(assume "l" "Useless1" "Useless2")
(use "EqHyp")
;; ?^4:RealConvLim([n]cRSum Zero(Succ n)xs)x M
(use "RealSerConvLimToRealConvLimSum")
(use "xsConv")
;; ?^5:RealConvLim([n]cRSum Zero(Succ n)ys)y N
(use "RealSerConvLimToRealConvLimSum")
(use "ysConv")
;; Proof finished.
;; (cp)
(save "RealSerConvLimUniq")

;; 2023-01-06.  New definition of RSerConv with n rather than Succ n.
;; Redone until GeomSerRealCauchy (end of 2.  Series)

;; 2023-03-26.  Definition of RSerConv adapted to the new definition
;; of (RealSum n m xs) where m is the length of the sum.

(add-ids
 (list (list "RSerConv" (make-arity (py "nat=>rea") (py "pos=>nat"))))
 '("all xs,M(all p,n,m(M p<=n -> abs(RealSum n m xs)<<=(1#2**p)) ->
    RSerConv xs M)" "RSerConvIntro"))

;; RSerConvElim
(set-goal "all xs,M(
     RSerConv xs M -> 
     all p,n,m(M p<=n -> abs(RealSum n m xs)<<=(1#2**p)))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RSerConvElim")

(add-ids
 (list (list "RealSerConv" (make-arity (py "nat=>rea") (py "pos=>nat"))))
 '("all xs,M(
   all n Real(xs n) -> Mon M -> RSerConv xs M -> RealSerConv xs M)"
   "RealSerConvIntro"))

;; RealSerConvToReals 
(set-goal "all xs,M(RealSerConv xs M -> all n Real(xs n))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvToReals")

;; RealSerConvToMon
(set-goal "all xs,M(RealSerConv xs M -> Mon M)")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvToMon")

;; RealSerConvToRSerConv
(set-goal "all xs,M(RealSerConv xs M -> RSerConv xs M)")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
;; (cp)
(save "RealSerConvToRSerConv")

;; 2023-05-12.
;; RSerAbsConvToConv
(set-goal "all xs,M(all n Real(xs n) ->
 RSerConv([n]abs(xs n))M -> RSerConv xs M)")
(assume "xs" "M" "Rxs" "CAbs")
(intro 0)
(assume "p" "n" "m" "nBd")
(use "RealLeTrans" (pt "abs(RealSum n m([l]abs(xs l)))"))
(use "RealLeTrans" (pt "RealSum n m([l]abs(xs l))"))
(use "RealLeAbsSum")
(use "Rxs")
(use "RealLeIdAbs")
(autoreal)
(use "RSerConvElim" (pt "M"))
(use "CAbs")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RSerAbsConvToConv")

;; RealSerAbsConvToConv
(set-goal "all xs,M(all n Real(xs n) ->
 RealSerConv([n]abs(xs n))M -> RealSerConv xs M)")
(assume "xs" "M" "Rxs" "CAbs")
(intro 0)
;; 3-5
(use "Rxs")
;; 4
(use "RealSerConvToMon" (pt "[n]abs(xs n)"))
(use "CAbs")
;; 5
(use "RSerAbsConvToConv")
(use "Rxs")
(use "RealSerConvToRSerConv")
(use "CAbs")
;; Proof finished.
;; (cp)
(save "RealSerAbsConvToConv")

;; GeomSumEq
(set-goal "all x,p(
     Real x -> 
     RealPos abs(1+ ~x)p -> 
     all n RealSum Zero n(RealExp x)===(1+ ~(x**n))*RealUDiv(1+ ~x)p)")
(assume "x" "p" "Rx" "x/=1" "n0")
(ind (pt "n0"))
;; 3,4
(ng #t)
(simpreal "RealZeroTimes")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
;; 4
(assume "n" "IH")
(assert "Real(RealUDiv(1+ ~x)p)")
(use "RealUDivReal")
(realproof)
(use "x/=1")
;; Assertion proved.
(assume "Real1/(1-x)")
(ng #t)
(use "RealEqTrans" (pt "(1+ ~(x**n))*(RealUDiv(1+ ~x) p)+x**n"))
;; 16,17
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(realproof)
;; 17
(use "RealEqTrans"
     (pt "(1+ ~(x**n))*(RealUDiv(1+ ~x) p)+
          (x**n+ ~(x**(Succ n)))*(RealUDiv(1+ ~x) p)"))
;; 21,22
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "x**n*1"))
(use "RealEqSym")
(use "RealTimesOne")
(realproof)
(use "RealEqTrans" (pt "x**n*((1+ ~x)*(RealUDiv(1+ ~x) p))"))
;; 30,31
(simpreal "RealTimesUDivR2")
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
(use "x/=1")
(autoreal)
;; ?^31:x**n*((1+ ~x)*RealUDiv(1+ ~x)p)===(x**n+ ~(x**Succ n))*RealUDiv(1+ ~x)p
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
;; 42,43
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesOne")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealTimesIdUMinus")
(autoreal)
;; ?^43:RealUDiv(1+ ~x)p===RealUDiv(1+ ~x)p
(use "RealEqRefl")
(autoreal)
;; 22
(simpreal "<-" "RealTimesPlusDistrLeft")
(use "RealTimesCompat")
;; 61,62
(ng #t)
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~(x**n)+x**n=== x**n+ ~(x**n)"))
(simpreal "RealPlusMinusZero")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "GeomSumEq")

;; 2023-03-12.  We strengthen RConvLimShift by weakening its premise
;; M0 p=Pred(M p) to Pred(M p)<=M0 p

;; RConvLimShiftStrengthened
(set-goal "all xs,y,M,M0(all p Pred(M p)<=M0 p ->
 RConvLim xs y M -> RConvLim([n]xs(Succ n))y M0)")
(assume "xs" "y" "M" "M0" "M0Prop" "MProp")
(intro 0)
(ng #t)
(assume "p" "n" "nBd")
(use "RConvLimElim" (pt "M"))
(use "MProp")
(cases (pt "M p"))
;; 8,9
(assume "Useless")
(use "Truth")
;; 9
(assume "m" "Mp=Sm")
(ng #t)
(use "NatLeTrans" (pt "M0 p"))
(inst-with-to "M0Prop" (pt "p") "M0PropInst")
(simphyp-with-to "M0PropInst" "Mp=Sm" "InstInst")
(use "InstInst")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RConvLimShiftStrengthened")

;; 2023-03-12.  We strengthen RealConvLimShift by weakening its
;; premise M0 p=Pred(M p) to Pred(M p)<=M0 p.  Here we need to require
;; monotonicity for M0 rather than M

;; RealConvLimShiftStrengthened
(set-goal "all xs,y,M,M0(all n Real(xs n) -> Real y -> Mon M0 ->
 all p Pred(M p)<=M0 p ->
 RealConvLim xs y M -> RealConvLim([n]xs(Succ n))y M0)")
(assume "xs" "y" "M" "M0" "Rxs" "Ry" "M0Mon" "M0Prop" "MProp")
(intro 0)
(ng #t)
(assume "n")
(use "Rxs")
(use "Ry")
;; Mon M0
(use "M0Mon")
;; ?^6:RConvLim([n]xs(Succ n))y M0
(use "RConvLimShiftStrengthened" (pt "M"))
(use "M0Prop")
(use "RealConvLimToRConvLim")
(use "MProp")
;; Proof finished.
;; (cp)
(save "RealConvLimShiftStrengthened")

;; GeomSerRealConvLimAuxStrengthened
(set-goal "all x,p,M,y(Real x -> Real y -> 
     RealPos abs(1+ ~x)p ->
     RealConvLim(RealExp x)0 M -> 
     y eqd RealUDiv(1+ ~x)(PosS p) -> 
     RealConvLim([n]([m]1+ ~(x**m))n*y)(RealUDiv(1+ ~x)(PosS p))
     ([q]M(q+PosS p)))")
(assume "x" "p" "M" "y" "Rx" "Ry" "x/=1p" "GSeqConv" "yDef")
(simpreal (pf "(RealUDiv(1+ ~x)(PosS p))===1*(RealUDiv(1+ ~x)(PosS p))"))
(simp "yDef")
(use "RealConvLimTimesConstR")
;; 6-8
;; ?^6:RealConvLim([m]1+ ~(x**m))1 M
(use "RealConvLimCompat"
     (pt "[m]1+ ([l]~(x**l))m")  (pt "1+RealUMinus 0") (pt "M"))
;; 9-11
(ng #t)
(assume "n")
(use "RealEqRefl")
(autoreal)
(simpreal (pf "RealUMinus 0===0"))
(use "RealPlusZero")
(autoreal)
(use "RatEqvToRealEq")
(use "Truth")
;; 11
(assume "q")
(use "Truth")
;; 12
(use "RealConvLimPlusConstL")
;; 21,22
(use "RealConvLimUMinus")
(use "GSeqConv")
(use "RealRat")
;; ?^7:Real(RealUDiv(1+ ~x)(PosS p))
(use "RealUDivReal")
(autoreal)
(use "RealPosPosS")
(autoreal)
(use "x/=1p")
;; ?^8:abs(RealUDiv(1+ ~x)(PosS p))<<=2**PosS p
(simpreal "RealAbsUDiv")
(use "RealLeUDivTwoExp")
(use "RealPosPosS")
(autoreal)
(use "x/=1p")
;; ?^32:(1#2**PosS p)<<=abs(1+ ~x)
(use "RealPosToLe")
(autoreal)
(use "x/=1p")
;; ?^30:RealPos abs(1+ ~x)(PosS p)
(use "RealPosPosS")
(autoreal)
(use "x/=1p")
(autoreal)
;; ?^4:RealUDiv(1+ ~x)(PosS p)===1*RealUDiv(1+ ~x)(PosS p)
(use "RealEqSym")
(use "RealOneTimes")
(use "RealUDivReal")
(autoreal)
(use "RealPosPosS")
(autoreal)
(use "x/=1p")
;; Proof finished.
;; (cp)
(save "GeomSerRealConvLimAuxStrengthened")

;; GeomSerRealConvLimStrengthened
(set-goal "all x,p,M(Real x ->
     RealPos abs(1+ ~x)p ->
     RealConvLim(RealExp x)0 M -> 
     RealConvLim([n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS p))
     (RealUDiv(1+ ~x)(PosS p))
     ([q]M(q+PosS p)))")
(assume "x" "p" "M" "Rx" "x/=1p" "GSeqConvLim")
(simp (pf "([n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS p))eqd
           ([n](([m]1+ ~(x**m))n)*RealUDiv(1+ ~x)(PosS p))"))
(use "GeomSerRealConvLimAuxStrengthened")
;; 5-9
(use "Rx")
;; 6
(use "RealUDivReal")
(realproof)
(use "RealPosPosS")
(realproof)
(use "x/=1p")
;; 7
(use "x/=1p")
;; 8
(use "GSeqConvLim")
;; 9
(use "InitEqD")
;; 4
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "GeomSerRealConvLimStrengthened")

;; GeomSerRealCauchyStrengthened
(set-goal "all x,p,M(Real x ->
 RealPos abs(1+ ~x)p ->
 RealConvLim(RealExp x)0 M -> 
 RealCauchy([n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS p))([q]M(PosS(PosS(q+p)))))")
(assume "x" "p" "M" "Rx" "x/=1p" "GeomSeqConvLimHyp")
(inst-with-to
 "RealConvLimToCauchy"
 (pt "[n](1+ ~(x**n))*RealUDiv(1+ ~x)(PosS p)")
 (pt "RealUDiv(1+ ~x)(PosS p)")
 (pt "[r]M(PosS(r+p))")
 "Inst")
(ng "Inst")
(use "Inst")
(drop "Inst")
(use "GeomSerRealConvLimStrengthened")
(use "Rx")
(use "x/=1p")
(use "GeomSeqConvLimHyp")
;; Proof finished.
;; (cp)
(save "GeomSerRealCauchyStrengthened")

;; 3.  Comparison and ratio test
;; =============================

;; RComparisonTest
(set-goal "all xs,ys,M(
     all n 0<<=xs n -> 
     all n xs n<<=ys n -> 
     RSerConv ys M -> RSerConv xs M)")
(assume "xs" "ys" "M" "0<=xs" "xs<=ys" "CysM")
(intro 0)
(assume "p" "n" "m" "nBd")
(use "RealLeTrans" (pt "abs(RealSum n m ys)"))
(simpreal "RealEqAbsId")
(simpreal "RealEqAbsId")
(use "RealLeMonSum")
(assume "l" "Useless1" "Useless2")
(use "xs<=ys")
(use "RealLeTrans" (pt "RealSum n m xs"))
(use "RealLeTrans" (pt "RealSum n m([n]0)"))
(simpreal "RealSumZeros")
(use "RatLeToRealLe")
(use "Truth")
(assume "l")
(bpe-ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 16
(use "RealLeMonSum")
(assume "l" "Useless1" "Useless2")
(bpe-ng #t)
(use "0<=xs")
;; 14
(use "RealLeMonSum")
(assume "l" "Useless1" "Useless2")
(use "xs<=ys")
;; 8
(use "RealLeTrans" (pt "RealSum n m([n]0)"))
(simpreal "RealSumZeros")
(use "RatLeToRealLe")
(use "Truth")
(assume "l")
(bpe-ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 29
(use "RealLeMonSum")
(assume "l" "Useless1" "Useless2")
(use "0<=xs")
;; 6
(use "RSerConvElim" (pt "M"))
(use "CysM")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RComparisonTest")

;; 2022-12-22.  Reformulation of ComparisonTest and RatioTest which
;; allows a generalization to complex numbers: avoid 0<=xs n and use
;; abs(xs n) instead.

;; RealComparisonTest
(set-goal "all xs,ys,M(
     all n Real(xs n) ->
     all n abs(xs n)<<=ys n -> 
     RealSerConv ys M -> RealSerConv([n]abs(xs n)) M)")
(assume "xs" "ys" "M" "Rxs" "|xs|<=ys" "CysM")
(intro 0)
;; 3-5
(assume "n")
(autoreal)
;; 4
(use "RealSerConvToMon" (pt "ys"))
(use "CysM")
;; 5:RSerConv([n]abs(xs n))M
(use "RComparisonTest" (pt "ys"))
(assume "n")
(ng #t)
(use "RealLeZeroAbs")
(use "Rxs")
(use "|xs|<=ys")
(use "RealSerConvToRSerConv" (pt "ys"))
(use "CysM")
;; Proof finished.
;; (cp)
(save "RealComparisonTest")

;; 2023-04-18.  Strengthening Zero |-> n

;; RComparisonTestMax
(set-goal "all xs,ys,M,m(
     all n 0<<=xs n -> 
     all n Real(ys n) ->
     all n(m<=n -> xs n<<=ys n) -> 
     RSerConv ys M -> RSerConv xs([p]M p max m))")
(assume "xs" "ys" "M" "m" "0<=xs" "Rys" "xs<=ys" "CysM")
(intro 0)
(bpe-ng #t)
(assume "p" "n" "m0" "nBd")
(use "RealLeTrans" (pt "abs(RealSum n m0 ys)"))
(simpreal "RealEqAbsId")
(simpreal "RealEqAbsId")
(use "RealLeMonSum")
(assume "l" "n<=l" "Useless")
(use "xs<=ys")
(use"NatLeTrans" (pt "M p max m"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "n<=l")
;; ?^11:0<<=RealSum n m0 ys
(use "RealLeTrans" (pt "RealSum n m0 xs"))
(use "RealLeTrans" (pt "RealSum n m0([n]0)"))
(simpreal "RealSumZeros")
(use "RatLeToRealLe")
(use "Truth")
(bpe-ng #t)
(assume "l")
(use "RatEqvToRealEq")
(use "Truth")
;; 22
(use "RealLeMonSum")
(bpe-ng #t)
(assume "l" "Useless1" "Useless2")
(use "0<=xs")
;; 20
(use "RealLeMonSum")
(assume "l" "n<=l" "Useless")
(use "xs<=ys")
(use"NatLeTrans" (pt "M p max m"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "n<=l")
;; ?^9:0<<=RealSum n m0 xs
(use "RealLeTrans" (pt "RealSum n m0([n]0)"))
(simpreal "RealSumZeros")
(use "RatLeToRealLe")
(use "Truth")
(bpe-ng #t)
(assume "l")
(use "RatEqvToRealEq")
(use "Truth")
;; 40
(use "RealLeMonSum")
(assume "l" "n<=l" "Useless")
(bpe-ng #t)
(use "0<=xs")
;; 7
(use "RSerConvElim" (pt "M"))
(use "CysM")
(use "NatLeTrans" (pt "M p max m"))
(use "NatMaxUB1")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RComparisonTestMax")

;; RealComparisonTestMax
(set-goal "all xs,ys,M,m(
     all n Real(xs n) ->
     all n 0<<=ys n ->
     all n(m<=n ->  abs(xs n)<<=ys n) -> 
     RealSerConv ys M -> RealSerConv([n]abs(xs n))([p]M p max m))")
(assume "xs" "ys" "M" "m" "Rxs" "0<=ys" "|xs|<=ys" "CysM")
(intro 0)
;; 3-5
(assume "n")
(autoreal)
;; 4
(intro 0)
(bpe-ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMax")
(use "MonElim")
(use "RealSerConvToMon" (pt "ys"))
(use "CysM")
(use "p<=q")
(use "Truth")
;; ?^5:RSerConv([n]abs(xs n))([p]M p max m)
(use "RComparisonTestMax" (pt "ys"))
(bpe-ng #t)
(assume "l")
(use "RealLeZeroAbs")
(use "Rxs")
(assume "l")
(autoreal)
(bpe-ng #t)
(use "|xs|<=ys")
(use "RealSerConvToRSerConv" (pt "ys"))
(use "CysM")
;; Proof finished.
;; (cp)
(save "RealComparisonTestMax")

;; Preparations for RatioTest

;; RCauchyTimesConstR
(set-goal "all xs,M,y,q(all n Real(xs n) -> Real y -> abs y<<=2**q -> 
 RCauchy xs M -> RCauchy([n]xs n*y)([p]M(p+q)))")
(assume "xs" "M" "y" "q" "Rxs" "Ry" "yBd" "CxsM")
(intro 0)
(assume "p" "n" "m")
(ng #t)
(assume "nBd" "mBd")
(simpreal "<-" "RealTimesUMinusId")
(simpreal "<-" "RealTimesPlusDistrLeft")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(1#2**(p+q))(2**q)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "RCauchyElim" (pt "M"))
(use "CxsM")
(use "nBd")
(use "mBd")
(use "yBd")
;; ?^18:RealTimes(1#2**(p+q))(2**q)<<=(1#2**p)
(use "RatLeToRealLe")
(ng #t)
(simp "PosToNatPlus")
(ng #t)
(simp "PosTimesComm")
(simp "PosExpTwoPosPlus")
(simp "<-" "PosToNatPlus")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cp)
(save "RCauchyTimesConstR")

;; RealCauchyTimesConstR
(set-goal "all xs,M,y,q(Real y -> abs y<<=2**q -> 
 RealCauchy xs M -> RealCauchy([n]xs n*y)([p]M(p+q)))")
(assume "xs" "M" "y" "q" "Ry" "yBd" "CxsM")
(inst-with-to "RealCauchyToReals" (pt "xs") (pt "M") "CxsM" "Rxs")
(intro 0)
;; 5-7
(assume "n")
(ng #t)
(autoreal)
;; ?^6:Mon([p]M(p+q))
(inst-with-to "RealCauchyToMon" (pt "xs") (pt "M") "CxsM" "MMon")
(intro 0)
(assume "p" "q0" "p<=q0")
(ng #t)
(use "MonElim")
(use "MMon")
(use "p<=q0")
;; ?^7:RCauchy([n]xs n*y)([p]M(p+q))
(use "RCauchyTimesConstR")
(auto)
(use "RealCauchyToRCauchy")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealCauchyTimesConstR")

;; RSerConvTimesConstR
(set-goal "all xs,M,y,q(all n Real(xs n) -> Real y -> abs y<<=2**q -> 
 RSerConv xs M -> RSerConv([n]xs n*y)([p]M(q+p)))")
(assume "xs" "M" "y" "q" "Rxs" "Ry" "yBd" "CxsM")
(intro 0)
(assume "p" "n" "m")
(ng #t)
(assume "nBd")
;; ?^6:abs(RealSum(Succ n)m([n0]xs n0*y))<<=(1#2**p)
(simpreal "<-" "RealTimesSumDistrLeft")
;; ?^7:abs(RealSum(Succ n)m xs*y)<<=(1#2**p)
(simpreal "RealAbsTimes")
(simpreal (pf "(1#2**p)===RealTimes(1#2**(q+p))(2**q#1)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealLeZeroAbs")
(autoreal)
(use "RSerConvElim" (pt "M"))
(use "CxsM")
(use "nBd")
(use "yBd")
;; ?^14:(1#2**p)===RealTimes(1#2**(q+p))(2**q)
(ng #t)
(use "RatEqvToRealEq")
(ng #t)
(simp "PosExpTwoPosPlus")
(use "Truth")
(autoreal)
(use "Rxs")
(use "Ry")
;; Proof finished.
;; (cp)
(save "RSerConvTimesConstR")

;; RealSerConvTimesConstR
(set-goal "all xs,M,y,q(Real y -> abs y<<=2**q -> 
 RealSerConv xs M -> RealSerConv([n]xs n*y)([p]M(q+p)))")
(assume "xs" "M" "y" "q" "Ry" "yBd" "CxsM")
(use "RealSerConvIntro")
;; 3-5
(ng #t)
(assume "n")
(use "RealTimesReal")
(use "RealSerConvToReals" (pt "M"))
(use "CxsM")
(use "Ry")
;; ?^4:Mon([p]M(q+p))
(intro 0)
(assume "p" "q0" "p<=q0")
(ng #t)
(use "MonElim")
(use "RealSerConvToMon" (pt "xs"))
(use "CxsM")
(use "p<=q0")
;; ?^5:RSerConv([n]xs n*y)([p]M(q+p))
(use "RSerConvTimesConstR")
(use "RealSerConvToReals" (pt "M"))
(use "CxsM")
(use "Ry")
(use "yBd")
(use "RealSerConvToRSerConv")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealSerConvTimesConstR")

;; 2023-03-30
;; RSerConvShiftUp
(set-goal "all xs,M,l(all n Real(xs n) ->
 RSerConv xs M -> RSerConv([n]xs(l+n))([p]M p--l))")
(assume "xs" "M" "l" "Rxs" "CxsM")
(intro 0)
(ng #t)
(assume "p" "n" "m" "Mp-l<=n")
(simpreal "RealSumShiftUp")
(use "RSerConvElim" (pt "M"))
(use "CxsM")
(simp "NatPlusComm")
(use "NatLeTrans" (pt "M p--l+l"))
(use "NatMinusPlusLe")
(use "Mp-l<=n")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RSerConvShiftUp")

;; RealSerConvShiftUp
(set-goal "all xs,M,l(
 RealSerConv xs M -> RealSerConv([n]xs(l+n))([p]M p--l))")
(assume "xs" "M" "l" "CxsM")
(intro 0)
;; 3-5
(bpe-ng #t)
(assume "n")
(use "RealSerConvToReals" (pt "M"))
(use "CxsM")
;; ?^4:Mon([p]M p--l)
(intro 0)
(bpe-ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMinusLeft")
(use "MonElim")
(use "RealSerConvToMon" (pt "xs"))
(use "CxsM")
(use "p<=q")
;; ?^5:RSerConv([n]xs(l+n))([p]M p--l)
(use "RSerConvShiftUp")
(use "RealSerConvToReals" (pt "M"))
(use "CxsM")
(use "RealSerConvToRSerConv")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealSerConvShiftUp")

;; 2023-04-06
;; RSerConvShiftDown
(set-goal "all xs,M,l(all n Real(xs n) ->
 RSerConv([n]xs(l+n))M -> RSerConv xs([p]M p+l))")
(assume "xs" "M" "l" "Rxs" "CxsM")
(intro 0)
(bpe-ng #t)
(assume "p" "n" "m" "Mp+l<=n")
(simpreal "RealSumShiftDown" (pt "l"))
;; 6-8
(use "RSerConvElim" (pt "M"))
(use "CxsM")
;; ?^10:M p<=n--l
(use "NatLePlusCancelR" (pt "l"))
(use "NatLeTrans" (pt "n"))
(use "Mp+l<=n")
(use "NatMinusPlusLe")
;; ?^8:l<=n
(use "NatLeTrans" (pt "M p+l"))
(use "Truth")
(use "Mp+l<=n")
;; 7
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RSerConvShiftDown")

;; RealSerConvShiftDown
(set-goal "all xs,M,l(all n Real(xs n) ->
 RealSerConv([n]xs(l+n))M -> RealSerConv xs([p]M p+l))")
(assume "xs" "M" "l" "Rxs" "CxsM")
(intro 0)
;; 3-5
(use "Rxs")
;; ?^4:Mon([p]M p+l)
(intro 0)
(bpe-ng #t)
(assume "p" "q" "p<=q")
(use "MonElim")
(use "RealSerConvToMon" (pt "[n]xs(l+n)"))
(use "CxsM")
(use "p<=q")
;; ?^5:RSerConv xs([p]M p+l)
(use "RSerConvShiftDown")
(use "Rxs")
(use "RealSerConvToRSerConv" (pt "[n]xs(l+n)"))
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealSerConvShiftDown")

;; RCauchyShiftUp
(set-goal "all xs,M,l(RCauchy xs M -> RCauchy([n]xs(l+n))([p]M p--l))")
(assume "xs" "M" "l" "CHyp")
(intro 0)
(bpe-ng #t)
(assume "p" "n" "m" "nBd" "mBd")
(inst-with-to "RCauchyElim" (pt "xs") (pt "M") "CHyp"
 (pt "p") (pt "l+n") (pt "l+m") "Inst")
(use "Inst")
;; ?^8:M p<=l+n
(simp "NatPlusComm")
(use "NatLeTrans" (pt "M p--l+l"))
(use "NatMinusPlusLe")
(use "nBd")
;; ?^9:M p<=l+m
(simp "NatPlusComm")
(use "NatLeTrans" (pt "M p--l+l"))
(use "NatMinusPlusLe")
(use "mBd")
;; Proof finished.
;; (cp)
(save "RCauchyShiftUp")

;; RealCauchyShiftUp
(set-goal "all xs,M,l(RealCauchy xs M -> RealCauchy([n]xs(l+n))([p]M p--l))")
(assume "xs" "M" "l" "CHyp")
(intro 0)
;; 3-5
(bpe-ng #t)
(assume "n")
(inst-with-to "RealCauchyToReals" (pt "xs") (pt "M") "CHyp" "Rxs")
(use "Rxs")
;; 4
(intro 0)
(bpe-ng #t)
(assume "p" "q" "p<=q")
(use "NatLeMonMinus")
(use "MonElim")
(use "RealCauchyToMon" (pt "xs"))
(use "CHyp")
(use "p<=q")
(use "Truth")
;; ?^5:RCauchy([n]xs(l+n))([p]M p--l)
(use "RCauchyShiftUp")
(use "RealCauchyToRCauchy")
(use "CHyp")
;; Proof finished.
;; (cp)
(save "RealCauchyShiftUp")

;; RCauchyShiftDown
(set-goal "all xs,M,l(RCauchy([n]xs(l+n))M -> RCauchy xs([p]M p+l))")
(assume "xs" "M" "l" "CHyp")
(intro 0)
(bpe-ng #t)
(assume "p" "n" "m" "nBd" "mBd")
(inst-with-to "RCauchyElim" (pt "[n]xs(l+n)") (pt "M") "CHyp"
 (pt "p") (pt "n--l") (pt "m--l") "Inst")
(bpe-ng "Inst")
(simp "<-" (pf "l+(n--l)=n"))
(simp "<-" (pf "l+(m--l)=m"))
(use "Inst")
(use "NatLePlusCancelR" (pt "l"))
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "NatMinusPlusLe")
(use "NatLePlusCancelR" (pt "l"))
(use "NatLeTrans" (pt "m"))
(use "mBd")
(use "NatMinusPlusLe")
;; ?^12:l+(m--l)=m
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLeTrans" (pt "M p+l"))
(use "Truth")
(use "mBd")
;; ?^10:l+(n--l)=n
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLeTrans" (pt "M p+l"))
(use "Truth")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RCauchyShiftDown")

;; RealCauchyShiftDown
(set-goal "all xs,M,l(all n Real(xs n) ->
 RealCauchy([n]xs(l+n))M -> RealCauchy xs([p]M p+l))")
(assume "xs" "M" "l" "Rxs" "CHyp")
(intro 0)
;; 3-6
(use "Rxs")
;; 4
(intro 0)
(bpe-ng #t)
(assume "p" "q" "p<=q")
(use "MonElim")
(use "RealCauchyToMon" (pt "[n]xs(l+n)"))
(use "CHyp")
(use "p<=q")
;; ?^5:RCauchy xs([p]M p+l)
(use "RCauchyShiftDown")
(use "RealCauchyToRCauchy")
(use "CHyp")
;; Proof finished.
;; (cp)
(save "RealCauchyShiftDown")

;; RCauchyExpToRSerConvExp
(set-goal "all x,p,M(0<<=x -> RealPos(1+ ~x)p -> 
 RCauchy(RealExp x)M -> RSerConv(RealExp x)([p0]M(PosS(p0+p))))")
(assume "x" "p" "M" "0<=x" "x<1" "MMod")
(intro 0)
(ng #t)
(assume "r" "m" "n" "mBd")
;; ?^5:abs(RealSum m n(RealExp x))<<=(1#2**r)
(assert "RealSum Zero(m+n)(RealExp x)+ ~(RealSum Zero m(RealExp x))===
         RealSum(Zero+m)n(RealExp x)")
(use "RealSumMinus")
(assume "l")
(autoreal)
;; Assertion proved.
(assume "RealSumMinusInst")
(simpreal "<-" "RealSumMinusInst")
(drop "RealSumMinusInst")
;; ?^12:abs(RealSum Zero(m+n)(RealExp x)+ ~(RealSum Zero m(RealExp x)))<<=
;; (1#2**r)
(simpreal "GeomSumEq" (pt "p"))
(simpreal "GeomSumEq" (pt "p"))
;; ?^16:abs((1+ ~(x**(m+n)))*RealUDiv(1+ ~x)p+ ~((1+ ~(x**m))*RealUDiv(1+ ~x)p))
;; <<=(1#2**r)
(simpreal "<-" (pf "(~(1+ ~(x**m))*RealUDiv(1+ ~x)p)===
                    ~((1+ ~(x**m))*RealUDiv(1+ ~x)p)"))
;; 19,20
(get 20)
(use "RealTimesUMinusId")
(autoreal)
;; ?^19:abs((1+ ~(x**(m+n)))*RealUDiv(1+ ~x)p+ ~(1+ ~(x**m))*RealUDiv(1+ ~x)p)
;; <<=(1#2**r)
(simpreal "<-" "RealTimesPlusDistrLeft")
;; ?^23:abs((1+ ~(x**(m+n))+ ~(1+ ~(x**m)))*RealUDiv(1+ ~x)p)<<=(1#2**r)
(simpreal "RealUMinusPlus")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusAssoc")
(simpreal (pf "1+ ~(x**(m+n))+ RealUMinus 1===1+RealUMinus 1+ ~(x**(m+n))"))
(simpreal "RealPlusMinusZero")
(simpreal "RealZeroPlus")
(simpreal "RealAbsTimes")
(simpreal (pf "abs(RealUDiv(1+ ~x)p)===(RealUDiv(1+ ~x)p)"))
(assert "0<<=RealUDiv(1+ ~x)p")
(use "RealPosToZeroLeUDiv")
(autoreal)
(use "x<1")
(assume "LeUDiv")
(assert "0<<=1+ ~x")
(use "RealPosToZeroLe" (pt "p"))
(autoreal)
(use "x<1")
(assume "0<=1-x")
;; ?^56:abs(~(x**(m+n))+x**m)*RealUDiv(1+ ~x)p<<=(1#2**r)
(assert "x<<=1")
(use "RealLePlusCancelR" (pt "~x"))
(autoreal)
(simpreal "RealPlusMinusZero")
(use "0<=1-x")
(autoreal)
(assume "x<=1")
;; ?^65:abs(~(x**(m+n))+x**m)*RealUDiv(1+ ~x)p<<=(1#2**r)
(use "RealLeTrans" (pt "abs(~(x**(m+n))+x**m)*1*RealUDiv(1+ ~x)p"))
(use "RealLeMonTimes")
(use "LeUDiv")
(simpreal "RealTimesOne")
(use "RealLeRefl")
(autoreal)
(simpreal "RealTimesOne")
;; ?^73:abs(~(x**(m+n))+x**m)*RealUDiv(1+ ~x)p<<=(1#2**r)
(simpreal "RealPlusComm")
(use "RealLeTrans" (pt "RealTimes(1#2**PosS(r+p))(2**PosS p)"))
(use "RealLeMonTimesTwo")
(use "RealLeZeroAbs")
(autoreal)
(use "RealPosToZeroLeUDiv")
(autoreal)
(use "x<1")
;; ?^82:abs(x**m+ ~(x**(m+n)))<<=(1#2**PosS(r+p))
(use "RCauchyElim" (pt "M"))
(auto)
(use "NatLeTrans" (pt "m"))
(use "mBd")
(use "Truth")
;; ?^83:RealUDiv(1+ ~x)p<<=2**PosS p
(use "RealLeUDivTwoExpPosS")
(use "x<1")
;; ?^93:(1#2**PosS p)<<=1+ ~x
(use "RealPosToLe")
(autoreal)
(use "x<1")
;; ?^79:RealTimes(1#2**PosS(r+p))(2**PosS p)<<=(1#2**r)
(use "RatLeToRealLe")
(ng #t)
(simp "PosExpTwoPosPlus")
(ng #t)
(simp "PosPlusComm")
(use "Truth")
(autoreal)
;; ?^46:abs(RealUDiv(1+ ~x)p)===RealUDiv(1+ ~x)p
(use "RealEqAbsId")
(use "RealPosToZeroLeUDiv")
(autoreal)
(use "x<1")
(autoreal)
;; ?^37:1+ ~(x**(m+n))+ ~1===1+ ~1+ ~(x**(m+n))
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RatEqvToRealEq")
(use "Truth")
(use "RealPlusComm")
(autoreal)
;; ?^18:RealPos abs(1+ ~x)p
(use "RealPosToPosAbs")
(use "x<1")
(autoreal)
;; ?^15:RealPos abs(1+ ~x)p
(use "RealPosToPosAbs")
(use "x<1")
(autoreal)
;; Proof finished.
;; (cp)
(save "RCauchyExpToRSerConvExp")

;; RealCauchyExpToRealSerConvExp
(set-goal "all x,p,M(0<<=x -> RealPos(1+ ~x)p -> 
 RealCauchy(RealExp x)M -> RealSerConv(RealExp x)([p0]M(PosS(p0+p))))")
(assume "x" "p" "M" "0<=x" "x<1" "MMod")
(intro 0)
;; 3-5
(assume "n")
(autoreal)
;; 4
(intro 0)
(assume "p0" "q" "p0<=q")
(ng #t)
(use "MonElim")
(use "RealCauchyToMon" (pt "RealExp x"))
(use "MMod")
(use "p0<=q")
;; ?^5:RSerConv(RealExp x)([p0]M(PosS(p0+p)))
(use "RCauchyExpToRSerConvExp")
(auto)
(use "RealCauchyToRCauchy" (pt "RealExp x"))
(auto)
;; Proof finished.
;; (cp)
(save "RealCauchyExpToRealSerConvExp")

;; In RealRatioTestZero below we use q+p0+p+1 rather than its normal form
;; PosS(q+p0+p) to make RealCauchyExpToRealSerConvExp directly usable.

;; RealRatioTestZero
(set-goal "all xs,z,p,M,q(
     all n Real(xs n) -> 
     0<<=z ->
     RealPos(1+ ~z)p ->
     RealCauchy(RealExp z)M -> 
     all n abs(xs(Succ n))<<=z*abs(xs n) ->
     abs(xs Zero)<<=2**q ->
     RealSerConv([n]abs(xs n))([p0]M(q+p0+p+1)))")
(assume "xs" "z" "p" "M" "q" "Rxs" "0<=z" "z<1" "MMod" "LeHyp" "xs0Bd")
(assert "all n abs(xs n)<<=z**n*abs(xs Zero)")
(ind)
;; 5,6
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
;; 6
(assume "n" "IH")
(ng #t)
(use "RealLeTrans" (pt "z*abs(xs n)"))
(use "LeHyp")
(use "RealLeTrans" (pt "z*(z**n*abs(xs Zero))"))
(use "RealLeMonTimesR")
(use "0<=z")
(use "IH")
(simpreal "RealTimesAssoc")
(use "RealLeMonTimes")
(use "RealLeZeroAbs")
(use "Rxs")
(simpreal "RealTimesComm")
(use "RealLeRefl")
(autoreal)
;; Assertion proved.
(assume "Assertion")
(use "RealComparisonTest" (pt "[n]z**n*abs(xs Zero)"))
(assume "n")
(use "Rxs")
(ng #t)
(use "Assertion")
(drop "Assertion" "LeHyp")
(use "RealSerConvTimesConstR")
(autoreal)
(simpreal "RealEqAbsId")
(use "xs0Bd")
(use "RealLeZeroAbs")
(use "Rxs")
;;   MMod:RealCauchy(RealExp z)M
;;   xs0Bd:abs(xs Zero)<<=2**q
;; -----------------------------------------------------------------------------
;; ?^39:RealSerConv(RealExp z)([p^]M(p^ +p+1))
(ng #t)
;; ?^43:RealSerConv(RealExp z)([p0]M(PosS(p0+p)))
(use "RealCauchyExpToRealSerConvExp")
(use "0<=z")
(use "z<1")
(use "MMod")
;; Proof finished.
;; (cp)
(save "RealRatioTestZero")

;; RealRatioTest
(set-goal "all xs,z,p,M,m,q(
     all n Real(xs n) -> 
     0<<=z ->
     RealPos(1+ ~z)p ->
     RealCauchy(RealExp z)M -> 
     all n(m<=n -> abs(xs(Succ n))<<=z*abs(xs n)) ->
     abs(xs m)<<=2**q ->
     RealSerConv([n]abs(xs(n+m)))([p0]M(q+p0+p+1)+m))")
(assume "xs" "z" "p" "M" "m" "q" "Rxs" "0<=z" "z<1" "MMod" "LeHyp" "xsmBd")
(inst-with-to "RealRatioTestZero"
(pt "[n]xs(n+m)") (pt "z") (pt "p") (pt "[p]M p+m") (pt "q") "Inst")
(bpe-ng "Inst")
(use "Inst")
;; 6-11
(assume "n")
(use "Rxs")
;; 7
(use "0<=z")
;; 8
(use "z<1")
;; ?^9:RealCauchy(RealExp z)([p]M p+m)
(drop "Inst")
(intro 0)
(assume "n")
(autoreal)
(intro 0)
(bpe-ng #t)
(assume "p0" "q0" "p0<=q0")
(use "MonElim")
(use "RealCauchyToMon" (pt "RealExp z"))
(use "MMod")
(use "p0<=q0")
;; ?^16:RCauchy(RealExp z)([p]M p+m)
(use "RCauchyMon" (pt "M"))
(bpe-ng #t)
(assume "p0")
(use "Truth")
(use "RealCauchyToRCauchy")
(use "MMod")
;; ?^10:all n abs(xs(Succ n+m))<<=z*abs(xs(n+m))
(drop "Inst")
(assume "n")
(use "LeHyp")
(use "Truth")
(use "xsmBd")
;; Proof finished.
;; (cp)
(save "RealRatioTest")

;; 2023-04-08.  RealRatioTestMax with (max m) for (+ m):

;; RealRatioTestMax
(set-goal "all xs,z,p,M,m,q(
     all n Real(xs n) -> 
     0<<=z ->
     RealPos(1+ ~z)p ->
     RealCauchy(RealExp z)M -> 
     all n(m<=n -> abs(xs(Succ n))<<=z*abs(xs n)) ->
     abs(xs m)<<=2**q ->
     RealSerConv([n]abs(xs(n+m)))([p0]M(q+p0+p+1) max m))")
(assume "xs" "z" "p" "M" "m" "q" "Rxs" "0<=z" "z<1" "MMod" "LeHyp" "xsmBd")
(inst-with-to "RealRatioTestZero"
(pt "[n]xs(n+m)") (pt "z") (pt "p") (pt "[p]M p max m") (pt "q") "Inst")
(bpe-ng "Inst")
(use "Inst")
;; 6-11
(assume "n")
(use "Rxs")
;; 7
(use "0<=z")
;; 8
(use "z<1")
;; ?^9:RealCauchy(RealExp z)([p]M p max m)
(drop "Inst")
(intro 0)
(assume "n")
(autoreal)
(intro 0)
(bpe-ng #t)
(assume "p0" "q0" "p0<=q0")
(use "NatLeMonMax")
(use "MonElim")
(use "RealCauchyToMon" (pt "RealExp z"))
(use "MMod")
(use "p0<=q0")
(use "Truth")
;; ?^16:RCauchy(RealExp z)([p]M p max m)
(use "RCauchyMon" (pt "M"))
(bpe-ng #t)
(assume "p0")
(use "NatMaxUB1")
(use "RealCauchyToRCauchy")
(use "MMod")
;; ?^10:all n abs(xs(Succ n+m))<<=z*abs(xs(n+m))
(drop "Inst")
(assume "n")
(use "LeHyp")
(use "Truth")
(use "xsmBd")
;; Proof finished.
;; (cp)
(save "RealRatioTestMax")

;; GeomSumOneHalfEq
(set-goal "all n RealSum Zero n(RealExp(1#2))===2*(1+ ~((1#2)**n))")
(ind)
;; 2,3
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 3
(assume "n" "IH")
(ng #t)
(simpreal "IH")
(simpreal (pf "RealExp(1#2)n===(1#2)**n"))
(use "RatEqvToRealEq")
;; ?^11:2*(1+ ~((1#2)**n))+(1#2)**n==2*(1+ ~((1#2)**n*(1#2)))
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simprat (pf "~(2*(1#2)**n)== ~((1#2)**n+(1#2)**n)"))
(ng #t)
(simprat "RatEqvPlusMinus")
(use "RatUMinusCompat")
(simp "RatTimesComm")
(use "Truth")
;; 19
(use "RatUMinusCompat")
(use "RatEqvSym")
(use "RatDoubleEqv")
;; ?^10:RealExp(1#2)n===(1#2)**n
(ind (pt "n"))
;; 26,27
(use "RatEqvToRealEq")
(use "Truth")
;; 27
(assume "m" "IHm")
(ng #t)
(simpreal "IHm")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GeomSumOneHalfEq")

;; GeomSumOneHalfEqRat
(set-goal "all n RealSum Zero n([m](1#2)**m)===2*(1+ ~((1#2)**n))")
(ind)
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
(assume "n" "IH")
(ng #t)
(simpreal "IH")
(use "RatEqvToRealEq")
;; ?^9:2*(1+ ~((1#2)**n))+(1#2)**n==2*(1+ ~((1#2)**n*(1#2)))
;; Now as in the proof of GeomSumOneHalfEq
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simprat (pf "~(2*(1#2)**n)== ~((1#2)**n+(1#2)**n)"))
(ng #t)
(simprat "RatEqvPlusMinus")
(use "RatUMinusCompat")
(simp "RatTimesComm")
(use "Truth")
;; 17
(use "RatUMinusCompat")
(use "RatEqvSym")
(use "RatDoubleEqv")
;; Proof finished.
;; (cp)
(save "GeomSumOneHalfEqRat")

;; ;; Special case of RealRatioTestMax for z := (1#2) and M := PosToNat

;; (set-goal "all xs,p,m,q,n,l(
;;      all n Real(xs n) -> 
;;      abs(xs m)<<=2**q ->
;;      all n abs(xs(m+n))<<=(1#2)**n*abs(xs m) ->
;;      (p+q+1)max m<=n ->
;;      RealSum(m+n)l xs<<=(1#2)**p)")

;; RSerConvExpOneHalf
(set-goal "RSerConv(RealExp(1#2))([p]PosToNat(PosS p))")
(intro 0)
(ng #t)
(assume "p" "m" "n" "mBd")
;; ?^4:abs(RealSum m n(RealExp(1#2)))<<=(1#2**p)
(use "RealLeTrans" (pt "RealSum m n([n0]abs(RealExp(1#2)n0))"))
;; 5,6
(use "RealLeAbsSum")
(assume "n0")
(autoreal)
;; ?^6:RealSum m n([n0]abs(RealExp(1#2)n0))<<=(1#2**p)
(simpreal "RealSumShiftDown" (pt "m"))
(bpe-ng #t)
;; ?^12:RealSum(m--m)n([n0]abs(RealExp(1#2)(m+n0)))<<=(1#2**p)
(simp (pf "m--m=Zero"))
;; ?^13:RealSum Zero n([n0]abs(RealExp(1#2)(m+n0)))<<=(1#2**p)
(simpreal (pf "(RealSum Zero n([n0]abs(RealExp(1#2)(m+n0))))===
               (RealSum Zero n([n0]RealExp(1#2)m*RealExp(1#2)n0))"))
;; 15,16
(simpreal "<-" "RealTimesSumDistr")
;; ?^17:RealExp(1#2)m*RealSum Zero n(RealExp(1#2))<<=(1#2**p)
(use "RealLeTrans" (pt "RealExp(1#2)m*2"))
;; 20,21
;; ?^20:RealExp(1#2)m*RealSum Zero n(RealExp(1#2))<<=RealExp(1#2)m*2
(use "RealLeMonTimesR")
;; 22,23
(use "RealExpZeroLe")
(use "RatLeToRealLe")
(use "Truth")
;; ?^23:RealSum Zero n(RealExp(1#2))<<=2
(simpreal "GeomSumOneHalfEq")
;; ?^26:2*(1+ ~((1#2)**n))<<=2
(use "RatLeToRealLe")
(simprat "RatTimesPlusDistr")
(ng #t)
;; ?^29:2+ ~(2*(1#2)**n)<=2
(use "RatLeTrans" (pt "2+RatUMinus Zero"))
(use "RatLeMonPlus")
(use "Truth")
(simp "RatLeUMinus")
;; ?^34:Zero<=2*(1#2)**n
(ind (pt "n"))
(use "Truth")
(assume "n0" "IH")
(ng #t)
(simprat (pf "0==0*(1#2)"))
(use "RatLeMonTimes")
(use "Truth")
(use "IH")
(use "Truth")
;; 31
(use "Truth")
;; ?^21:RealExp(1#2)m*2<<=(1#2**p)
(use "RealLeTrans" (pt "RealTimes(1#2**PosS p)2"))
(use "RealLeMonTimes")
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeTrans" (pt "RealConstr([n](1#2**m))([p]Zero)"))
;; ?^48:RealExp(1#2)m<<=(1#2**m)
(ind (pt "m"))
(use "RatLeToRealLe")
(use "Truth")
(assume "n0" "IH")
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#2**n0)(1#2)"))
(use "RealLeMonTimes")
(use "RatLeToRealLe")
(use "Truth")
(use "IH")
(use "RatLeToRealLe")
(ng #t)
(use "Truth")
;; ?^49:(1#2**m)<<=(1#2**PosS p)
(use "RatLeToRealLe")
(ng #t)
(use "PosLeMonPosExp")
(use "mBd")
;; ?^44:RealTimes(1#2**PosS p)2<<=(1#2**p)
(use "RatLeToRealLe")
(simp "<-" "PosPlus0RewRule")
(simp "<-" "PosExpTwoPosPlus")
(ng #t)
(use "Truth")
;; 19
(assume "n0")
(autoreal)
;; ?^16:RealSum Zero n([n0]abs(RealExp(1#2)(m+n0)))===
;;      RealSum Zero n([n0]RealExp(1#2)m*RealExp(1#2)n0)
(use "RealSumCompat")
(ng #t)
(assume "l" "Useless" "l<n")
(simpreal "RealAbsExp")
(simpreal "RealEqAbsId")
(use "RealExpPlus")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?^14:m--m=Zero
(use "Truth")
;; 11
(use "Truth")
;; 10
(assume "n0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RSerConvExpOneHalf")

;; 4.  Cauchy Product
;; ==================

;; We now aim at RealCauchyProdLim and RealCauchyProdLimAbs.  This
;; will be used in examples/analysis/eser.scm for a proof of the
;; functional equation for the exponential series.

(add-var-name "xss" (py "nat=>nat=>rea"))

;; RealLeSumPlusMax
(set-goal "all xss,n,m(
     m+m<=n ->
     all n,m 0<<=xss n m -> 
     RealSum Zero(n*n)
     ([k][if (n<lft(RtD k)+rht(RtD k))
             (xss(lft(RtD k))(rht(RtD k))) 0])<<=
     RealSum Zero(n*n)
     ([k][if (m<lft(RtD k)max rht(RtD k))
             (xss(lft(RtD k))(rht(RtD k))) 0]))")
(assume "xss" "n" "m" "2m<=n" "0<=xss")
(use "RealLeMonSum")
(assume "l" "Useless" "l<=n*n")
(bpe-ng #t)
(use "RealIfImpToLe")
(use "0<=xss")
(use "NatLtPlusToLtMax")
(use "2m<=n")
;; Proof finished.
;; (cp)
(save "RealLeSumPlusMax")

;; RealSumMinusSquareMod
(set-goal "all xss,m,n(
     all n0,m0 Real(xss n0 m0) -> 
     m<=n -> 
     RealSum Zero(n*n)([k]xss lft(RtD k)rht(RtD k))+ 
     ~(RealSum Zero(m*m)([k]xss lft(RtD k)rht(RtD k)))===
     RealSum Zero(n*n)
     ([k]
       [if (m<=lft(RtD k)max rht(RtD k))
         (xss lft(RtD k)rht(RtD k))
         0]))")
(assume "xss" "m" "n" "Rxss" "m<=n")
(simpreal "RealSumZeroMinusMod")
(use "RealEqTrans"
     (pt "RealSum Zero(m*m)([k][if (m<=lft(RtD k) max rht(RtD k))
				   (xss(lft(RtD k))(rht(RtD k))) 0])+
          RealSum(m*m)(n*n--m*m)
          ([k][if (m<=lft(RtD k) max rht(RtD k))
		  (xss(lft(RtD k))(rht(RtD k))) 0])"))
;; 6,7
(simpreal
 (pf "RealSum Zero(m*m)([k][if (m<=lft(RtD k) max rht(RtD k)) (xss(lft(RtD k))(rht(RtD k))) 0])===0"))
;; 8,9
(simpreal "RealZeroPlus")
(use "RealSumCompat")
(assume "l" "m*m<=l" "l<=n*n")
(bpe-ng)
(simp (pf "m<=lft(RtD l) max rht(RtD l)"))
(use "RealEqRefl")
(autoreal)
;; 16,17
;; ?^16:m<=lft(RtD l)max rht(RtD l)
(use "LeSqRtCChar1")
;; was (use "LeSquareRtCToLeIdMax")
;; ?^18:m*m<=RtC(lft(RtD l)pair rht(RtD l))
(simp "<-" "NatPairEq")
(simp "RtCDId")
(use "m*m<=l")
(autoreal)
;; ?^9:RealSum Zero(m*m)
;;     ([k]
;;       [if (m<=lft(RtD k)max rht(RtD k))
;;         (xss lft(RtD k)rht(RtD k))
;;         0])===
;;     0
(use "RealEqTrans"
     (pt "RealSum Zero(m*m)
     ([k][if False (xss(lft(RtD k))(rht(RtD k))) 0])"))
(use "RealSumCompat")
(assume "l" "Useless" "l<m*m")
(ng #t)
(simp (pf "m<=lft(RtD l) max rht(RtD l) -> F"))
(use "RealEqRefl")
(use "RealRat")
(assume "m<=i max j")
(assert "m*m<=l")
(use "LeIdMaxRtDLRToLeSqId")
;; was(use "LeIdMaxRtDLRToLeSquareId")
(use "m<=i max j")
(assume "m*m<=l")
(assert "l<l")
(use "NatLtLeTrans" (pt "m*m"))
(use "l<m*m")
(use "m*m<=l")
(assume "Absurd")
(use "Absurd")
;; ?^22
(ng #t)
;; ?^39:RealSum Zero(m*m)([n]0)===0
(use "RealSumZeros")
(assume "l")
(use "RealEqRefl")
(use "RealRat")
;; 7
(use "RealSumZeroSplitMod")
(assume "l")
(autoreal)
(use "NatLeMonTimes")
(use "m<=n")
(use "m<=n")
(use "NatLeMonTimes")
(use "m<=n")
(use "m<=n")
;; 4
(assume "l")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumMinusSquareMod")

;; 2023-02-03.

;; By the properties of the root based pair coding we have

;; ----      ----------------
;;  \ |      |              | 
;;   \|      |              | 
;;       sub |              |
;;           |              |
;;           ----           |
;;              |           |
;;              -------------

;; This follows from
;; (pp "NatLtPlusToLtMax")
;; all n,l,i,j(l+l<=n -> n<i+j -> l<i max j)

;; Clearer in RealLeSumPlusMax, with xss and without abs
;; (pp "RealLeSumPlusMax")
;; all xss,n,m(
;;  m+m<=n -> 
;;  all n0,m0 0<<=xss n0 m0 -> 
;;  RealSum Zero(n*n)([k][if (n<cL k+cR k) (xss(cL k)(cR k)) 0])<<=
;;  RealSum Zero(n*n)([k][if (m<cL k max cR k) (xss(cL k)(cR k)) 0]))

;; 2023-02-17.  Plan.

;; 1.  The product ZStar of the partial sums (RealSum Zero n xs) and
;; (RealSum Zero n ys) is (RealSum Zero(n*n)([k]xs(cL k)*ys(cR k))).
;; This is

;; (pp "RealSumTimes")
;; all xs,ys(
;;  all n Real(xs n) -> 
;;  all n Real(ys n) -> 
;;  all n 
;;   RealSum Zero n xs*RealSum Zero n ys===
;;   RealSum Zero(n*n)([k]xs(cL k)*ys(cR k)))

;; 2.  Since ([n]RealSum Zero n xs) and ([n]RealSum Zero n ys)
;; converge with limit x and y, their product (i.e., ZStar) converges
;; with limit x*y

;; RealConvLimZStar
(set-goal "all xs,ys,x,y,M,N,p,q,K(
 all n Real(xs n) ->
 all n Real(ys n) ->
 Real x -> 
 Real y -> 
 RealConvLim([n]RealSum Zero n xs)x M ->
 RealConvLim([n]RealSum Zero n ys)y N -> 
 all n abs(RealSum Zero n xs)<<=2**p -> 
 all n abs(RealSum Zero n ys)<<=2**q -> 
 all r K r=N(p+r+1)max M(q+r+1) -> 
 RealConvLim([n]RealSum Zero(n*n)
                        ([k]xs(lft(RtD k))*ys(rht(RtD k))))(x*y)K)")
(assume "xs" "ys" "x" "y" "M" "N" "p" "q" "K" "Rxs" "Rys" "Rx" "Ry"
        "CxsxM" "CysyN" "xsBd" "ysBd" "KDef")
(use "RealConvLimCompat"
 (pt "[n]RealSum Zero n xs*RealSum Zero n ys") (pt "x*y") (pt "K"))
;; 3-6
(assume "n")
(bpe-ng #t)
(use "RealSumTimes")
(use "Rxs")
(use "Rys")
;; 4
(use "RealEqRefl")
(autoreal)
;; 5
(assume "p0")
(use "Truth")
;; ?^6:RealConvLim([n]RealSum Zero n xs*RealSum Zero n ys)(x*y)K
(use-with
 "RealConvLimTimesSym"
 (pt "([n]RealSum Zero n xs)") (pt "x") (pt "M")
 (pt "([n]RealSum Zero n ys)") (pt "y") (pt "N")
 (pt "p") (pt "q") (pt "K") "CxsxM" "CysyN"  "xsBd" "ysBd" "KDef")
;; Proof finished.
;; (cp)
(save "RealConvLimZStar")

;; 3.  The upper triangles
;; (RealSum Zero(n*n)([k][if (n<cL k+cR k) (xs(cL k)*ys(cR k)) 0]))
;; (i.e., ZStar_n+ ~(Z_n)) converge with limit 0 and modulus 2*K r

;; 2023-02-18

;; New attempt for RealUpperTriangLimZeroAux, where the abbreviations
;; xs0 n*ys0 n are used for better readability

;; RealUpperTriangLimZeroAux
(set-goal "all xs,ys,xs0,M,ys0,N,p,q,K(
 all n Real(xs n) -> 
 all n Real(ys n) -> 
 all n xs0 n===RealSum Zero n([i]abs(xs i)) -> 
 all n ys0 n===RealSum Zero n([j]abs(ys j)) -> 
 RealCauchy xs0 M -> 
 RealCauchy ys0 N -> 
 all n xs0 n<<=2**p -> 
 all n ys0 n<<=2**q -> 
 all r K r=N(p+r+1)max M(q+r+1) ->
 all n,r(K r<=n ->
 abs(xs0 n*ys0 n+ ~(xs0(K r)*ys0(K r)))<<=(1#2**r)))")
(assume "xs" "ys" "xs0" "M" "ys0" "N" "p" "q" "K" "Rxs" "Rys" "xs0Def" "ys0Def"
        "Cxs0M" "Cys0N" "xs0Bd" "ys0Bd" "KDef" "n" "r" "Kr<=n")
;; ?^2:abs(xs0 n*ys0 n+ ~(xs0(K r)*ys0(K r)))<<=(1#2**r)
(inst-with-to "RCauchyElim" (pt "[n]xs0 n*ys0 n") (pt "K") "Inst1")
(use "Inst1")
(drop "Inst1")
(inst-with-to "RealCauchyToRCauchy" (pt "[n]xs0 n*ys0 n") (pt "K") "Inst2")
(use "Inst2")
(drop "Inst2")
(use
 "RealCauchyBdTimesCor" (pt "xs") (pt "ys") (pt "M") (pt "N") (pt "p") (pt "q"))
(auto)
;; Proof finished.
;; (cp)
(save "RealUpperTriangLimZeroAux")

;; RealSquareMinusLowTriangEqUp
(set-goal "all xs,ys,n(
     all n0 Real(xs n0) -> 
     all n0 Real(ys n0) -> 
     RealSum Zero(n*n)([k]xs lft(RtD k)*ys rht(RtD k))+ 
     ~(RealSum Zero(n*n)
       ([k]
         [if (lft(RtD k)+rht(RtD k)<n)
           (xs lft(RtD k)*ys rht(RtD k))
           0]))===
     RealSum Zero(n*n)
     ([k]
       [if (n<=lft(RtD k)+rht(RtD k))
         (xs lft(RtD k)*ys rht(RtD k))
         0]))")
(assume "xs" "ys" "n" "Rxs" "Rys")
(use "RealEqvPlusCancelR"
     (pt "(RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<n)
                                    (xs(lft(RtD k))*ys(rht(RtD k)))
                                    0]))"))
(autoreal)
(simpreal "RealEqvPlusMinus")
(simpreal "RealSumPlus")
(use "RealSumCompat")
(assume "m" "Useless" "m<n*n")
(bpe-ng #t)
(def "i" "lft(RtD m)")
(simp "<-" "iDef")
(def "j" "rht(RtD m)")
(simp "<-" "jDef")
;; ?^31:xs i*ys j===[if (n<=i+j) (xs i*ys j) 0]+[if (i+j<n) (xs i*ys j) 0]
(simpreal "RealPlusComm")
(use "RealEqSym")
(use "RealPlusIfNatLtLe")
(autoreal)
(assume "m")
(autoreal)
(assume "m")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSquareMinusLowTriangEqUp")

;; RealSquareMinusLowTriangEqUpMod
(set-goal "all xss,n(
     all n0,m Real(xss n0 m) -> 
     RealSum Zero(n*n)([k]xss lft(RtD k)rht(RtD k))+ 
     ~(RealSum Zero(n*n)
       ([k]
         [if (lft(RtD k)+rht(RtD k)<n)
           (xss lft(RtD k)rht(RtD k))
           0]))===
     RealSum Zero(n*n)
     ([k]
       [if (n<=lft(RtD k)+rht(RtD k))
         (xss lft(RtD k)rht(RtD k))
         0]))")
(assume "xss" "n" "Rxss")
(use "RealEqvPlusCancelR"
     (pt "(RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<n)
                                    (xss(lft(RtD k))(rht(RtD k)))
                                    0]))"))
(autoreal)
(simpreal "RealEqvPlusMinus")
(simpreal "RealSumPlus")
(use "RealSumCompat")
(assume "m" "Useless" "m<n*n")
(bpe-ng #t)
;; ?^15:xss lft(RtD m)rht(RtD m)===
;;      [if (n<=lft(RtD m)+rht(RtD m))
;;        (xss lft(RtD m)rht(RtD m))
;;        0]+
;;      [if (lft(RtD m)+rht(RtD m)<n)
;;        (xss lft(RtD m)rht(RtD m))
;;        0]
(simpreal "RealPlusComm")
(use "RealEqSym")
(use "RealPlusIfNatLtLe")
(autoreal)
(assume "m")
(autoreal)
(assume "m")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSquareMinusLowTriangEqUpMod")

;; We prove the left estimate from (pp "RealSquareMinusLowTriangEqUp")

;; RealLeAbsMinusZStarZMinusPStar
(set-goal "all xs,ys,n(
     all n0 Real(xs n0) -> 
     all n0 Real(ys n0) -> 
     abs(RealSum Zero(n*n)([k]xs lft(RtD k)*ys rht(RtD k))+ 
         ~(RealSum Zero(n*n)
           ([k]
             [if (lft(RtD k)+rht(RtD k)<n)
               (xs lft(RtD k)*ys rht(RtD k))
               0])))<<=
     RealSum Zero(n*n)
     ([k]
       [if (n<=lft(RtD k)+rht(RtD k))
         (abs(xs lft(RtD k))*abs(ys rht(RtD k)))
         0]))")
(assume "xs" "ys" "n" "Rxs" "Rys")
;; 2
(simpreal "RealSquareMinusLowTriangEqUp")
;; 3-5
(simpreal "<-"
 (pf "RealSum Zero(n*n)([k][if (n<=lft(RtD k)+rht(RtD k))
 (abs(xs(lft(RtD k))*ys(rht(RtD k)))) 0])===
 RealSum Zero(n*n)([k][if (n<=lft(RtD k)+rht(RtD k))
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])"))
;; 6,7
(simpreal
(pf "RealSum Zero(n*n)([k][if (n<=lft(RtD k)+rht(RtD k))
 (abs(xs(lft(RtD k))*ys(rht(RtD k)))) 0])===
     RealSum Zero(n*n)([k]abs[if (n<=lft(RtD k)+rht(RtD k))
 (xs(lft(RtD k))*ys(rht(RtD k))) 0])"))
;; 8,9
(use "RealLeAbsSum")
(assume "n0")
(autoreal)
;; 9
(use "RealSumCompat")
(assume "m" "Useless" "m<n+n")
(bpe-ng #t)
(simpreal "RealAbsIf")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 7
(use "RealSumCompat")
(assume "m" "Useless" "m<n+n")
(bpe-ng #t)
(simpreal "RealAbsTimes")
(use "RealEqRefl")
(autoreal)
;; 5
(use "Rys")
;; 4
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealLeAbsMinusZStarZMinusPStar")

;; RealUpperTriangLeMinusSquare
(set-goal "all xs,ys,m,n(
     all n0 Real(xs n0) -> 
     all n0 Real(ys n0) -> 
     m+m<=n -> 
     RealSum Zero(n*n)
     ([k]
       [if (n<=lft(RtD k)+rht(RtD k))
         (abs(xs lft(RtD k))*abs(ys rht(RtD k)))
         0])<<=
     RealSum Zero(n*n)
     ([k]
       [if (m<=lft(RtD k)max rht(RtD k))
         (abs(xs lft(RtD k))*abs(ys rht(RtD k)))
         0]))")
(assume "xs" "ys" "m" "n" "Rxs" "Rys" "2m<=n")
(use "RealLeMonSum")
(assume "m0" "Useless" "m0<=n*n")
(bpe-ng #t)
(use "RealIfImpToLe")
(simpreal "<-" "RealAbsTimes")
(use "RealLeZeroAbs")
(autoreal)
(use "NatLePlusToLeMax")
(use "2m<=n")
;; Proof finished.
;; (cp)
(save "RealUpperTriangLeMinusSquare")

;; 4.  The Lower triangles
;; (RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<=n)
;;  (xs(lft(RtD k))*ys(rht(RtD k))) 0]))
;; (i.e., Z_n) converge with limit x*y.

;; RealUpperTriangLimZero
(set-goal "all xs,ys,xs0,M,ys0,N,p,q,K(
     all n Real(xs n) -> 
     all n Real(ys n) -> 
     all n xs0 n===RealSum Zero n([i]abs(xs i)) -> 
     all n ys0 n===RealSum Zero n([j]abs(ys j)) -> 
     RealCauchy xs0 M -> 
     RealCauchy ys0 N -> 
     all n xs0 n<<=2**p -> 
     all n ys0 n<<=2**q -> 
     all r K r=N(p+r+1)max M(q+r+1) -> 
     all r,n(
      K r+K r<=n -> 
      abs(RealSum Zero(n*n)([k]xs lft(RtD k)*ys rht(RtD k))+ 
          ~(RealSum Zero(n*n)
            ([k]
              [if (lft(RtD k)+rht(RtD k)<n)
                (xs lft(RtD k)*ys rht(RtD k))
                0])))<<=
      (1#2**r)))")
(assume "xs" "ys" "xs0" "M" "ys0" "N" "p" "q" "K0"
"Rxs" "Rys" "xs0Def" "ys0Def" "Cxs0M" "Cys0N" "xs0Bd" "ys0Bd" "K0Def"
"r" "n" "2K0Bd")
;; First apply Llft
(use "RealLeTrans"
  (pt "RealSum Zero(n*n)
     ([k][if (n<=lft(RtD k)+rht(RtD k))
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])"))
;; 3,4
(use "RealLeAbsMinusZStarZMinusPStar")
(use "Rxs")
(use "Rys")
;; 4
;; Next apply Lmid
(use "RealLeTrans"
  (pt "RealSum Zero(n*n)
     ([k][if (K0 r<=lft(RtD k) max rht(RtD k))
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])"))
;; 7,8
(use "RealUpperTriangLeMinusSquare")
(use "Rxs")
(use "Rys")
(use "2K0Bd")
;; 8
;; Finally use Lrht
(use "RealLeTrans" (pt "abs(xs0 n*ys0 n+ ~(xs0(K0 r)*ys0(K0 r)))"))
;; 12,13
(get 13)
(use "RealUpperTriangLimZeroAux"
 (pt "xs") (pt "ys") (pt "M") (pt "N") (pt "p") (pt "q"))
(use "Rxs")
(use "Rys")
(use "xs0Def")
(use "ys0Def")
(use "Cxs0M")
(use "Cys0N")
(use "xs0Bd")
(use "ys0Bd")
(use "K0Def")
(use "NatLeTrans" (pt "K0 r+K0 r"))
(use "Truth")
(use "2K0Bd")
;; 12
(inst-with-to
 "RealSumMinusSquareMod"
 (pt "[i,j]abs(xs i)*abs(ys j)")
 "Inst")
(bpe-ng "Inst")
(simpreal "<-" "Inst")
(drop "Inst")
(simpreal "xs0Def")
(simpreal "ys0Def")
(simpreal "RealSumTimes")
(bpe-ng #t)
(simpreal "xs0Def")
(simpreal "ys0Def")
(simpreal "RealSumTimes")
(bpe-ng #t)
(use "RealLeIdAbs")
(autoreal)
(assume "n0")
(autoreal)
(assume "n0")
(autoreal)
(assume "n0")
(autoreal)
(assume "n0")
(autoreal)
;; 31
(use  "NatLeTrans" (pt "K0 r+K0 r"))
(use "Truth")
(use "2K0Bd")
;; 30
(assume "n0" "m0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealUpperTriangLimZero")

;; Finally we combine RealConvLimZStar and RealUpperTriangLimZero

;; RealCauchyProdLim
(set-goal "all xs,ys,x,y,M,N,p,q,K,xs0,ys0,M0,N0,p0,q0,K0(
     all n Real(xs n) -> 
     all n Real(ys n) -> 
     RealConvLim([n]RealSum Zero n xs)x M -> 
     RealConvLim([n]RealSum Zero n ys)y N -> 
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
      abs(RealSum Zero(n*n)
          ([k]
            [if (lft(RtD k)+rht(RtD k)<n)
              (xs lft(RtD k)*ys rht(RtD k))
              0])+ 
          ~(x*y))<<=
      (1#2**r)))")
(assume "xs" "ys" "x" "y" "M" "N" "p" "q" "K"
"xs0" "ys0" "M0" "N0" "p0" "q0" "K0"
"Rxs" "Rys" "CxsxM" "CysyN" "xsBd" "ysBd" "KDef"
"xs0Def" "ys0Def" "Cxs0M0" "Cys0N0" "xs0Bd" "ys0Bd" "K0Def"
"r" "n" "nBd")
(simpreal
 (pf "RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<n)
 (xs(lft(RtD k))*ys(rht(RtD k))) 0])===
      RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<n)
 (xs(lft(RtD k))*ys(rht(RtD k))) 0])+
      ~(RealSum Zero(n*n)([k]xs(lft(RtD k))*ys(rht(RtD k))))+
      RealSum Zero(n*n)([k]xs(lft(RtD k))*ys(rht(RtD k)))"))
;; 3,4
(simpreal "<-" "RealPlusAssoc")
(use "RealLeTrans"
 (pt "abs(RealSum Zero(n*n)([k][if (lft(RtD k)+rht(RtD k)<n)
 (xs(lft(RtD k))*ys(rht(RtD k))) 0])+ 
        ~(RealSum Zero(n*n)([k]xs(lft(RtD k))*ys(rht(RtD k)))))+
      abs(RealSum Zero(n*n)
		  ([k]xs(lft(RtD k))*ys(rht(RtD k)))+ ~(x*y))"))
;; 9,10
(use "RealLeAbsPlus")
(autoreal)
;; 10
(simpreal (pf "(1#2**r)===RealPlus(1#2**PosS r)(1#2**PosS r)"))
;; 13,14
(use "RealLeMonPlusTwo")
;; 15,16
(simpreal "RealAbsPlusUMinus")
(use "RealUpperTriangLimZero"
  (pt "xs0") (pt "M0") (pt "ys0") (pt "N0") (pt "p0") (pt "q0") (pt "K0"))
(auto)
(use "NatLeTrans" (pt "(K0(PosS r)+K0(PosS r))max K(PosS r)"))
(use "NatMaxUB1")
(use "nBd")
(autoreal)
;; 16
(assert "RealConvLim([n]RealSum Zero(n*n)
		     ([k]xs(lft(RtD k))*ys(rht(RtD k))))(x*y)K")
(use "RealConvLimZStar" (pt "M") (pt "N") (pt "p") (pt "q"))
(auto)
;; ?^36:Real x
(use "RealConvLimElim2" (pt "[n]RealSum Zero n xs") (pt "M"))
(use "CxsxM")
;; ?^37:Real y
(use "RealConvLimElim2" (pt "[n]RealSum Zero n ys") (pt "N"))
(use "CysyN")
(auto)
;; Assertion proved
(assume "Assertion1")
(assert "RConvLim([n]RealSum Zero(n*n)
		  ([k]xs(lft(RtD k))*ys(rht(RtD k))))(x*y)K")
(use "RealConvLimToRConvLim")
(use "Assertion1")
;; Assertion proved
(assume "Assertion2")
;; ?^49:abs(RealSum Zero(n*n)
;; ([k]xs(lft(RtD k))*ys(rht(RtD k)))+ ~(x*y))<<=(1#2**PosS r)
(use-with "RConvLimElim"
 (pt "[n]RealSum Zero(n*n)([k]xs(lft(RtD k))*ys(rht(RtD k)))") (pt "x*y") (pt "K")
"?" (pt "PosS r") (pt "n") "?")
(use "Assertion2")
(use "NatLeTrans" (pt "(K0(PosS r)+K0(PosS r))max K(PosS r)"))
(use "NatMaxUB2")
(use "nBd")
;; ?^14:(1#2**r)===RealPlus(1#2**PosS r)(1#2**PosS r)
(use "RealEqSym")
(use "RealPlusHalfExpPosS")
;; 8
(autoreal)
;; 4
(simpreal "RealEqvPlusMinus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealCauchyProdLim")

;; We show that the lower triangles w.r.t. absolute values converge to
;; the product of the limits of the two series of absolute values.

;; RealCauchyProdLimAbs
(set-goal "all xs,ys,x,y,M,N,p,q,K,xs0,ys0,M0,N0,p0,q0,K0(
 all n Real(xs n) -> 
 all n Real(ys n) -> 
 RealConvLim([n]RealSum Zero n([i]abs(xs i)))x M -> 
 RealConvLim([n]RealSum Zero n([j]abs(ys j)))y N -> 
 all n RealSum Zero n([i]abs(xs i))<<=2**p -> 
 all n RealSum Zero n([j]abs(ys j))<<=2**q -> 
 all r K r=N(p+r+1)max M(q+r+1) -> 
 all n xs0 n===RealSum Zero n([i]abs(xs i)) -> 
 all n ys0 n===RealSum Zero n([j]abs(ys j)) -> 
 RealCauchy xs0 M0 -> 
 RealCauchy ys0 N0 -> 
 all n xs0 n<<=2**p0 -> 
 all n ys0 n<<=2**q0 -> 
 all r K0 r=N0(p0+r+1)max M0(q0+r+1) -> 
 RSerConvLim
 ([m]
    RealSum Zero((m+1)*(m+1))
    ([k][if (lft(RtD k)+rht(RtD k)=m) (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0]))(x*y)
 ([r](K0(PosS r)+K0(PosS r))max K(PosS r)))")
(assume "xs" "ys" "x" "y" "M" "N" "p" "q" "K"
"xs0" "ys0" "M0" "N0" "p0" "q0" "K0"
"Rxs" "Rys" "CxsxM" "CysyN" "xsBd" "ysBd" "KDef"
"xs0Def" "ys0Def" "Cxs0M0" "Cys0N0" "xs0Bd" "ys0Bd" "K0Def")
(intro 0)
(bpe-ng #t)
(assume "r" "n" "nBd")
(simpreal
 (pf "cRSum Zero(Succ n)
    ([m]
      RealSum Zero((m+1)*(m+1))
      ([k][if (lft(RtD k)+rht(RtD k)=m)
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0]))===
    RealSum Zero((n+1)*(n+1))
    ([k][if (lft(RtD k)+rht(RtD k)<=n)
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])"))
(get 7)
(simp "RSumExFree")
(use-with
 "RealSumDiags"
 (pt "[i]abs(xs i)")
 (pt "[j]abs(ys j)")
 "?" "?" (pt "n"))
;; 9,10
(bpe-ng #t)
(assume "n0")
(autoreal)
;; 10
(bpe-ng #t)
(assume "n0")
(autoreal)
;; 6
(simpreal (pf "RealSum Zero((n+1)*(n+1))
        ([k][if (lft(RtD k)+rht(RtD k)<=n)
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])===
 RealSum Zero((n+1)*(n+1))
        ([k][if (lft(RtD k)+rht(RtD k)<n+1)
 (abs(xs(lft(RtD k)))*abs(ys(rht(RtD k)))) 0])"))
;; 15
(use-with
 "RealCauchyProdLim"
 (pt "[i]abs(xs i)") (pt "[j]abs(ys j)") (pt "x") (pt "y") (pt "M") (pt "N")
 (pt "p") (pt "q") (pt "K")
 (pt "xs0") (pt "ys0")  (pt "M0") (pt "N0") (pt "p0") (pt "q0") (pt "K0")
 "?" "?" "CxsxM" "CysyN"
 "?" "?" "?" "?" "?" "?" "?" "?" "?" "?" (pt "r") (pt "n+1") "?")
;; 17-29
(assume "n0")
(autoreal)
;; 18
(assume "n0")
(autoreal)
;; 19
(assume "n0")
(simpreal (pf "abs(RealSum Zero n0([i]abs(xs i)))===
                   RealSum Zero n0([i]abs(xs i))"))
(use "xsBd")
(use "RealEqAbsId")
(simpreal "<-" (pf "RealSum Zero n0([n]0)===0"))
;; 36,37
(use "RealLeMonSum")
(bpe-ng #t)
(assume "m" "Useless1" "Useless2")
(use "RealLeZeroAbs")
(autoreal)
;; 37
(use "RealSumZeros")
(assume "n1")
(use "RatEqvToRealEq")
(use "Truth")
;; 20 similar to 19
(assume "n0")
(simpreal (pf "abs(RealSum Zero n0([i]abs(ys i)))===
                   RealSum Zero n0([i]abs(ys i))"))
(use "ysBd")
(use "RealEqAbsId")
(simpreal "<-" (pf "RealSum Zero n0([n]0)===0"))
;; 49,50
(use "RealLeMonSum")
(bpe-ng #t)
(assume "m" "Useless1" "Useless2")
(use "RealLeZeroAbs")
(autoreal)
(use "RealSumZeros")
(assume "n1")
(use "RatEqvToRealEq")
(use "Truth")
;; 21
(use "KDef")
;; 22
(assume "n0")
(bpe-ng #t)
(use "xs0Def")
;; 23
(bpe-ng #t)
(use "ys0Def")
;; 24
(use "Cxs0M0")
;; 25
(use "Cys0N0")
;; 26
(use "xs0Bd")
;; 27
(use "ys0Bd")
;; 28
(use "K0Def")
;; 29
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
;; 16
(use "RealSumCompat")
(assume "l" "Useless1" "Useless2")
(bpe-ng #t)
(simp (pf "(lft(RtD l)+rht(RtD l)<=n)=
           (lft(RtD l)+rht(RtD l)<n+1)"))
(use "RealEqRefl")
(autoreal)
;; 67
(use "BooleAeqToEq")
(use "NatLeToLtSucc")
(use "NatLtSuccToLe")
;; Proof finished.
;; (cp)
(save "RealCauchyProdLimAbs")

;; 5.  Bounds and convergent series
;; ================================

(add-program-constant "RealSeqBd" (py "(nat=>rea)=>(pos=>nat)=>nat"))
(add-computation-rules
 "RealSeqBd xs M"
 "Succ(ListNatMax(cRBound map xs fbar Succ(M 1)))")

(set-totality-goal "RealSeqBd")
(fold-alltotal)
(assume "xs")
(fold-alltotal)
(assume "M")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; RSeqBd
(set-goal "all xs,M(RealCauchy xs M -> exl n n=RealSeqBd xs M)")
(assume "xs" "M" "RCasM")
(intro 0 (pt "RealSeqBd xs M"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "RSeqBd")

(animate "RSeqBd")

;; RSeqBdExFree
(set-goal "all xs,M(RealCauchy xs M -> cRSeqBd xs M=RealSeqBd xs M)")
(assume "xs" "M" "RCasM")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RSeqBdExFree")

(deanimate "RSeqBd")

(set-totality-goal "cRSeqBd")
(fold-alltotal)
(assume "xs")
(fold-alltotal)
(assume "M")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Adapted from RealBdProp
;; RealSeqBdPos
(set-goal "all xs,M(RealCauchy xs M -> all n(abs(xs n)<<=2**(cRSeqBd xs M)))")
(assume "xs" "M" "RCas xs M" "n")

(assert "all n Real(xs n)")
(use "RealCauchyToReals" (pt "M"))
(use "RCas xs M")
(assume "Rxs")

;; Lemma1
(assert
 "all n(n<=M 1 -> abs(xs n)<<=2**(ListNatMax(cRBound map xs fbar Succ(M 1))))")
(assume "n0" "n0<=M 1")
(use "RealLeTrans" (pt "2**cRBound(xs n0)"))
;; Here the new x-and-x-list-to-proof-and-new-num-goals-and-maxgoal is needed

;;; RealLeTrans 1
(use "RealBoundProp1")
(use "Rxs")
;;; RealLeTrans 2
(use "RatLeToRealLe")
(use "NatLeMonTwoExp")
(use-with "ListNatMaxFBar"
 (pt "[k]cRBound(xs k)") (pt "n0") (pt "Succ(M 1)") "?")
(use "NatLeToLtSucc")
(use "n0<=M 1")
;; Assertion provedx2
(assume "Lemma1")

(simp "RSeqBdExFree")
;; RSeqBdExFree 1
(simp "RealSeqBd0CompRule")
(cases (pt "n<=M 1"))
;; Cases 1
(assume "n<=M 1")
(use "RealLeTrans" (pt "2**ListNatMax(cRBound map xs fbar Succ(M 1))"))
;; RealLeTrans 1
(use "Lemma1")
(use "n<=M 1")
;; RealLeTrans 2
(use "RatLeToRealLe")
(use "Truth")
;; Cases 2
(assume "n>M 1")
(use "RealLeTrans" (pt "abs(xs(M 1))+(abs(xs n)+ ~(abs(xs(M 1))))"))
;; RealLeTrans 1
(assert "all x,y(Real x -> Real y -> x === y+(x+ ~y))")
;; Assert 1
(assume "x" "y" "Rx" "Ry")
(simpreal "RealPlusComm")
;; RealPlusComm 1
(use "RealEqSym")
(use "RealEqPlusMinus")
;; RealEqPlusMinus 1 2
(realproof)
(realproof)
;; RealPlusComm 2 3
(realproof)
(realproof)
;; Assert 2
(assume "Assertion")
(use "RealEqElim0")
(use "Assertion")
;; Assertion 1 2
(realproof)
(realproof)
;; RealLeTrans 2
(assert "all n(2**Succ n === 2**n+2**n)")
;; Assert 1
(assume "n0")
(ng #t)
(simp "SZeroPosPlus")
(use "RealEqRefl")
(realproof)
;; Assert 2
(assume "Assertion")
(simpreal "Assertion")
(use-with "RealLeMonPlusTwo"
          (pt "abs(xs(M 1))")
          (pt "2**ListNatMax(cRBound map xs fbar Succ(M 1))")
          (pt "(abs(xs n)+ ~abs(xs(M 1)))")
          (pt "2**ListNatMax(cRBound map xs fbar Succ(M 1))")
          "?" "?")
;; RealLeMonPlus 1
(use "Lemma1")
(use "Truth")
;; RealLeMonPlus 2
(use "RealLeTrans" (pt "abs(abs(xs n)+ ~abs(xs(M 1)))"))
;; RealLeTrans 1
(use "RealLeIdAbs")
(realproof)
;; RealLeTrans 2
(use "RealLeTrans" (pt "abs(xs n+ ~(xs(M 1)))"))
;; RealLeTrans 1
(use "RealLeAbsMinusAbs")
;; RealLeAbsMinusAbs 1 2
(realproof) (realproof)
;; RealLeTrans 2
(use "RealLeTrans" (pt "1#2**1"))
;; RealLeTrans 1
(use "RCauchyElim" (pt "M"))
;; RCauchyElim 1
(use "RealCauchyToRCauchy")
(use "RCas xs M")
;; RCauchyElim 2
(use "NatNotLtToLe")
(assume "n<M 1")
(use "n>M 1")
(use "NatLtToLe")
(use "n<M 1")
;; RCauchyElim 3
(use "Truth")
;; RealLeTrans 2
(use "RatLeToRealLe")
(use "Truth")
;; RSeqBdExFree 2
(use "RCas xs M")
;; Proof finished.
;; (cp)
(save "RealSeqBdPos")

;; Adapted from archive/herrmann/utils.scm

;; RealConvLimShiftDown
(set-goal "all xs,x,M,n(all n Real(xs n) ->
 RealConvLim([k]xs(k+n))x M -> RealConvLim xs x ([p]M p+n))")
(assume "xs" "x" "M" "n" "Rxs" "LimShift")

(assert "Real x")
(use "RealConvLimElim2" (pt "[k]xs(k+n)") (pt "M"))
(use "LimShift")
;; Assertion proved.
(assume "Rx")

;; ?^6:RealConvLim xs x([p]M p+n)
(intro 0)
(use "Rxs")
(use "Rx")
;; ?^9:Mon([p]M p+n)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "MonElim")
(use "RealConvLimToMon" (pt "[k]xs(k+n)") (pt "x"))
(use "LimShift")
(use "p<=q")
;; ?^10:RConvLim xs x([p]M p+n)
(intro 0)
(ng #t)
(assume "p" "n0" "n0Bd")
;; ?^19:abs(xs n0+ ~x)<<=(1#2**p)

(assert "n<=n0")
(use "NatLeTrans" (pt "M p+n"))
(use "Truth")
(use "n0Bd")
;; Assertion proved.
(assume "n<=n0")

(simp (pf "xs n0 eqd(([k]xs(k+n))(n0--n))"))
;; 25,26
;; ?^25:abs(([k]xs(k+n))(n0--n)+ ~x)<<=(1#2**p)
(use "RConvLimElim" (pt "M"))
(use "RealConvLimToRConvLim")
(use "LimShift")
;; ?^28:M p<=n0--n
(use "NatLeTrans" (pt "M p+n--n"))
(use "Truth")
(use "NatLeMonMinusLeft")
(use "n0Bd")
;; ?^26:xs n0 eqd([k]xs(k+n))(n0--n)
(ng #t)
(simp "NatMinusPlusEq")
(use "InitEqD")
(use "n<=n0")
;; Proof finished.
;; (cp)
(save "RealConvLimShiftDown")

;; RealCauchyShiftUpWithoutMod
(set-goal "all xs,M,l(RealCauchy xs M -> RealCauchy([n]xs(l+n))M)")
(assume "xs" "M" "l" "RCxsM")
(use "RealCauchyMon" (pt "[p]M p--l"))
;; RealCauchyMon 1
(assume "p")
(use "Truth")
;; RealCauchyMon 2
(use "RealCauchyToMon" (pt "xs"))
(use "RCxsM")
;; RealCauchyMon 3
(use "RealCauchyShiftUp")
(use "RCxsM")
;; Proof finished.
;; (cp)
(save "RealCauchyShiftUpWithoutMod")

;; RealSerConvToCauchy
(set-goal "all xs,M(RealSerConv xs M -> RealCauchy([n]cRSum Zero n xs)M)")
(assume "xs" "M" "RealSerConv xs M")

(assert "all n Real(xs n)")
(use "RealSerConvToReals" (pt "M"))
(use "RealSerConv xs M")
;; Assertion proved.
(assume "Rxs")

(assert "Mon M")
(use "RealSerConvToMon" (pt "xs"))
(use "RealSerConv xs M")
;; Assertion proved.
(assume "Mon M")

(assert "RSerConv xs M")
(use "RealSerConvToRSerConv")
(use "RealSerConv xs M")
;; Assertion proved.
(assume "RSerConv xs M")

;; ?^10:RealCauchy([n]cRSum Zero n xs)M
(intro 0)
;; RealCauchyIntro 1
(ng #t)
(assume "n")
(simp "RSumExFree")
(realproof)
;; RealCauchyIntro 2
(use "Mon M")
;; RealCauchyIntro 3
(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(ng #t)
(simp "RSumExFree")
(simp "RSumExFree")

(assert "all p0,n0,m0(M p0<=n0 -> abs(RealSum n0 m0 xs)<<=(1#2**p0))")
(use "RSerConvElim")
(use "RSerConv xs M")
;; Assertion proved.
(assume "est: RSerConv xs M")

;; Lemma
(assert "all m,n(m<=n -> M p<=m ->
 abs(RealSum Zero n xs+ ~(RealSum Zero m xs))<<=(1#2**p))")
(assume "m0" "n0" "m0<=n0" "M p<=m0")
(simpreal-with "RealSumZeroMinusMod"
	       (pt "xs") "Rxs" (pt "m0") (pt "n0") "m0<=n0")
(use "est: RSerConv xs M")
(use "M p<=m0")
;; Assertion proved.
(assume "Lemma")

(use "NatLeLeCases" (pt "n") (pt "m"))

;; NatLeLeCases 1
(assume "n<=m")
(simpreal "<-" "RealAbsUMinus")
;; RealAbsUMinus 1
(simpreal "RealUMinusPlus")
;; RealUMinusPlus 1
(simpreal "RealUMinusUMinus")
;; RealUMinusUMinus 1
(simpreal "RealPlusComm")
;; RealPlusComm 1
(use "Lemma")
;; Lemma 1
(use "n<=m")
;; Lemma 2
(use "nBd")
;; RealPlusComm 2
(realproof)
;; RealPlusComm 3
(realproof)
;; RealUMinusUMinus 2
(realproof)
;; RealUMinusPlus 2
(realproof)
;; RealUMinusPlus 3
(realproof)
;; RealAbsUMinus 2
(realproof)
;; NatLeLeCases 2
(assume "m<=n")
(use "Lemma")
;; Lemma 1
(use "m<=n")
;; Lemma 2
(use "mBd")
;; Proof finished.
;; (cp)
(save "RealSerConvToCauchy")

;; RSerConvCompat
(set-goal "all xs,M,ys,N(all n(xs n===ys n) ->  all p(M p=N p) ->
 RSerConv xs M -> RSerConv ys N)")
(assume "xs" "M" "ys" "N" "xs=ys" "M=N" "CxsM")
(intro 0)
(assume "p" "n" "m" "nBd")
(simpreal "<-" "RealSumCompat" (pt "xs"))
(use "RSerConvElim" (pt "M"))
(use "CxsM")
(simp "M=N")
(use "nBd")
;; 6
(assume "l" "Useless1" "Useless2")
(use "xs=ys")
;; Proof finished.
;; (cp)
(save "RSerConvCompat")

;; RealSerConvCompat
(set-goal "all xs,M,ys,N(
 all n xs n===ys n -> 
 all p M p=N p ->
 RealSerConv xs M -> RealSerConv ys N)")
(assume "xs" "M" "ys" "N" "xs=ys" "M=N" "CxsM")
(intro 0)
;; 3-5
(assume "n")
(autoreal)
;; ?^4:Mon N
(intro 0)
(assume "p" "q" "p<=q")
(simp "<-" "M=N")
(simp "<-" "M=N")
(use "MonElim")
(use "RealSerConvToMon" (pt "xs"))
(use "CxsM")
(use "p<=q")
;; ?^5:RSerConv ys N
(use "RSerConvCompat" (pt "xs") (pt "M"))
(use "xs=ys")
(use "M=N")
(use "RealSerConvToRSerConv")
(use "CxsM")
;; Proof finished.
;; (cp)
(save "RealSerConvCompat")

;; 2024-12-12

;; RCauchyChar1
(set-goal "all xs,M(all n Real(xs n) ->
 all p,n,m(M p<=n -> abs(xs(n+m)+ ~(xs n))<<=(1#2**p)) -> 
 RCauchy xs M)")
(assume "xs" "M" "Rxs" "Crit")

(assert "all p,n,m(n<=m -> M p<=n -> abs(xs m+ ~(xs n))<<=(1#2**p))")
(assume "p" "n" "m" "n<=m" "nBd")
(simp (pf "m=n+(m--n)"))
(use "Crit")
(use "nBd")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "n<=m")
;; Assertion proved.
(assume "A")

(intro 0)
(assume "p" "n" "m" "nBd" "mBd")
(use "NatLeLeCases" (pt "n") (pt "m"))
;; 15,16
(assume "n<=m")
(simpreal "RealAbsPlusUMinus")
(use "A")
(use "n<=m")
(use "nBd")
(autoreal)
;; 16
(assume "m<=n")
(use "A")
(use "m<=n")
(use "mBd")
;; Proof finished.
;; (cp)
(save "RCauchyChar1")

;; The other direction holds as well

;; RCauchyChar2
(set-goal "all xs,M(all n Real(xs n) ->
 RCauchy xs M ->
 all p,n,m(M p<=n -> abs(xs(n+m)+ ~(xs n))<<=(1#2**p)))")
(assume "xs" "M" "Rxs" "CauchyH")
(assume "p" "n" "m" "nBd")
(use "RCauchyElim" (pt "M"))
(use "CauchyH")
(use "NatLeTrans" (pt "n"))
(use "nBd")
(use "Truth")
(use "nBd")
;; Proof finished.
;; (cp)
(save "RCauchyChar2")

;; RSerConvToCauchySum
(set-goal "all xs,M(all n Real(xs n) ->
 RSerConv xs M ->
 RCauchy([n]RealSum Zero n xs)M)")
(assume "xs" "M" "Rxs" "ConvH")
(use "RCauchyChar1")
;; 3,4
(assume "n")
(autoreal)
;; 4
(assume "p" "n" "m" "nBd")
(bpe-ng #t)
(simpreal "RealSumZeroMinus")
(use "RSerConvElim" (pt "M"))
(use "ConvH")
(use "nBd")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RSerConvToCauchySum")

;; Convergence of a series implies Cauchyness of the partial sums.

;; RealSerConvToCauchySum
(set-goal "all xs,M(all n Real(xs n) ->
 RealSerConv xs M ->
 RealCauchy([n]RealSum Zero n xs)M)")
(assume "xs" "M" "Rxs" "ConvH")
(intro 0)
;; 3-5
(assume "n")
(realproof)
;; ?^4:Mon M
(use "RealSerConvToMon" (pt "xs"))
(use "ConvH")
;; ?^5:RCauchy([n]RealSum Zero n xs)M
(use "RSerConvToCauchySum")
(use "Rxs")
(use "RealSerConvToRSerConv")
(use "ConvH")
;; Proof finished.
;; (cp)
(save "RealSerConvToCauchySum")

;; The other direction holds as well:

;; RCauchySumToSerConv
(set-goal "all xs,M(all n Real(xs n) ->
 RCauchy([n]RealSum Zero n xs)M ->
 RSerConv xs M)")
(assume "xs" "M" "Rxs" "CauchyH")
(intro 0)
(assume "p" "n" "m" "nBd")
;; 5,6
(simpreal "<-" "RealSumZeroMinus")
(use-with "RCauchyChar2" (pt "([n]RealSum Zero n xs)") (pt "M") "?" "CauchyH"
	  (pt "p") (pt "n") (pt "m") "nBd")
(assume "n0")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RCauchySumToSerConv")

;; RealCauchySumToSerConv
(set-goal "all xs,M(all n Real(xs n) ->
 RealCauchy([n]RealSum Zero n xs)M ->
 RealSerConv xs M)")
(assume "xs" "M" "Rxs" "CauchyH")
(intro 0)
;; 3-5
(use "Rxs")
(use "RealCauchyToMon" (pt "([n]RealSum Zero n xs)"))
(use "CauchyH")
;; ?^5:RSerConv xs M
(use "RCauchySumToSerConv")
(use "Rxs")
(use "RealCauchyToRCauchy")
(use "CauchyH")
;; Proof finished.
;; (cp)
(save "RealCauchySumToSerConv")

