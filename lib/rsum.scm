;; 2025-04-01.  rsum.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (libload "rea.scm")
;; (remove-var-name "k" "i" "j" "ml" "ij")
;; ;; natpair.scm uses k,i,j as nat variables and ml, ij as pair variable
;; (libload "natpair.scm")
;; (set! COMMENT-FLAG #t)

(display "loading rsum.scm ...") (newline)

;; Theorems:
;; (pp "RealIfReal")
;; (pp "RealIfCompat")
;; (pp "RealAbsIf")
;; (pp "RealPlusIf")
;; (pp "RealUMinusIf")
;; (pp "RealTimesIf")
;; (pp "RealIfImpToLe")
;; (pp "RealLeMonIf")
;; (pp "RealPlusIfNatLtLe")

;; (pp "RSum")
;; (pp "RSumExFree")
;; (pp "RealSumReal")
;; (pp "RealSumZeroSucc")
;; (pp "RealLeMonSum")
;; (pp "RealSumCompat")
;; (pp "RealSumShiftUp")
;; (pp "RealSumShiftDown")
;; (pp "RealSumZeroShiftDown")
;; (pp "RealSumShiftUpMinus")
;; (pp "RealSumZeroShiftUp")
;; (pp "RealTimesSumDistr")
;; (pp "RealTimesSumDistrLeft")
;; (pp "RealSumSplit")
;; (pp "RealSumZeroSplit")
;; (pp "RealSumZeroSplitMod")
;; (pp "RealSumMinus")
;; (pp "RealSumZeroMinus")
;; (pp "RealSumZeroMinusMod")
;; (pp "RealSumOne")
;; (pp "RealSumSplitL")
;; (pp "RealSumPlus")
;; (pp "RealSumUMinus")
;; (pp "RealLeAbsSum")
;; (pp "RealSumZeros")
;; (pp "RealSumZerosSharp")
;; (pp "RealSumZerosL")
;; (pp "RealSumZerosR")
;; (pp "RealSumZerosLR")
;; (pp "RealIfImpToIfIf")
;; (pp "RealSumSplitTwo")
;; (pp "RatSumRealSum")
;; (pp "RealGeomSumEqvNoDivAux1")
;; (pp "RealGeomSumEqvNoDivOneHalf")

;; 1.  Properties of if-terms with a boolean test and real alternatives
;; ====================================================================

;; (pp "RealIfReal")
;; (pp "RealIfCompat")
;; (pp "RealIfCompatFull")
;; (pp "RealAbsIf")
;; (pp "RealPlusIf")
;; (pp "RealUMinusIf")
;; (pp "RealTimesIf")
;; (pp "RealIfImpToLe")
;; (pp "RealLeMonIf")
;; (pp "RealPlusIfNatLtLe")
;; (pp "RealPlusIfNatLeLt")

;; 2023-01-24.  Properties of if-terms with a boolean test and real
;; alternatives.  Will be needed for conditional real sums.

;; RealIfReal (was RealIfBooleReal)
(set-goal "all boole,x,y(Real x -> Real y -> Real[if boole x y])")
(cases)
(auto)
;; Proof finished.
;; (cp)
(save "RealIfReal")

;; RealIfCompat (was RealIfBooleCompat)
(set-goal
 "all boole,x,x0,y,y0(x===x0 -> y===y0 -> [if boole x y]===[if boole x0 y0])")
(cases)
(auto)
;; Proof finished.
;; (cp)
(save "RealIfCompat")

;; RealIfCompatFull
(set-goal
 "all boole,boole0,x,x0,y,y0(boole=boole0 -> x===x0 -> y===y0 ->
 [if boole x y]===[if boole0 x0 y0])")
(cases)
;; 2,3
(cases)
;; 4,5
(ng #t)
(search)
;; 5
(assume "x" "x0" "y" "y0" "Absurd")
(ng "Absurd")
(efproof)
;; 3
(cases)
;; 9,10
(assume "x" "x0" "y" "y0" "Absurd")
(ng "Absurd")
(efproof)
;; 10
(ng #t)
(search)
;; Proof finished.
;; (cp)
(save "RealIfCompatFull")

;; RealAbsIf (was RealIfBooleAbs)
(set-goal "all boole,x,y(Real x -> Real y ->
 abs[if boole x y]===[if boole (abs x) (abs y)])")
(cases)
;; 2,3
(assume "x" "y" "Rx" "Ry")
(use "RealEqRefl")
(autoreal)
;; 3
(assume "x" "y" "Rx" "Ry")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealAbsIf")

;; RealPlusIf
(set-goal "all x,y,x0,y0(Real x -> Real y -> Real x0 -> Real y0 ->
 all boole [if boole x y]+[if boole x0 y0]===[if boole (x+x0) (y+y0)])")
(assume "x" "y" "x0" "y0" "Rx" "Ry" "Rx0" "Ry0")
(cases)
(ng #t)
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealPlusIf")

;;  RealUMinusIf
(set-goal "all x,y(Real x -> Real y ->
 all boole ~[if boole x y]===[if boole (~x) (~y)])")
(assume "x" "y" "Rx" "Ry")
(cases)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealUMinusIf")

;; RealTimesIf
(set-goal "all x,y,x0,y0(Real x -> Real y -> Real x0 -> Real y0 ->
 all boole [if boole x y]*[if boole x0 y0]===[if boole (x*x0) (y*y0)])")
(assume "x" "y" "x0" "y0" "Rx" "Ry" "Rx0" "Ry0")
(cases)
(ng #t)
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealTimesIf")

;; RealIfImpToLe (was RealIfBooleImpToLe)
(set-goal "all x(
 0<<=x -> 
 all boole,boole0(
  (boole -> boole0) -> [if boole x 0]<<=[if boole0 x 0]))")
(assume "x" "0<=x")
(cases)
(cases)
(assume "Useless")
(use "RealLeRefl")
(autoreal)
;; 6
(assume "Absurd")
(use "EfRealLe")
(use "Absurd")
(use "Truth")
;; 4
(cases)
(assume "Useless")
(ng #t)
(use "0<=x")
(assume "Useless")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finshed.
;; (cp)
(save "RealIfImpToLe")

;; RealLeMonIf
(set-goal "all x,y,x0,y0(Real x -> Real y -> Real x0 -> Real y0 ->
 all boole((boole -> x<<=x0) -> (negb boole -> y<<=y0) ->
 [if boole x y]<<=[if boole x0 y0]))")
(assume "x" "y" "x0" "y0" "Rx" "Ry" "Rx0" "Ry0")
(cases)
(ng #t)
(assume "THyp" "Useless")
(use "THyp")
(use "Truth")
(assume "Useless" "FHyp")
(use "FHyp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLeMonIf")

;; RealPlusIfNatLtLe
(set-goal "all n,m,x(Real x ->  [if (m<n) x 0]+[if (n<=m) x 0]===x)")
(assume "n" "m" "x" "Rx")
(use "NatLeLtCases" (pt "n") (pt "m"))
;; 3,4
(assume "n<=m")
(simp "n<=m")
(ng #t)
(simp (pf "m<n -> F"))
(ng #t)
(use "RealZeroPlus")
(use "Rx")
(assume "m<n")
(assert "n<n")
(use "NatLeLtTrans" (pt "m"))
(use "n<=m")
(use "m<n")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "m<n")
(simp "m<n")
(ng #t)
(simp (pf "n<=m -> F"))
(ng #t)
(use "RealPlusZero")
(use "Rx")
(assume "n<=m")
(assert "n<n")
(use "NatLeLtTrans" (pt "m"))
(use "n<=m")
(use "m<n")
(assume "Absurd")
(use "Absurd")
;; Proof finshed.
;; (cp)
(save "RealPlusIfNatLtLe")

;; RealPlusIfNatLeLt
(set-goal "all n,m,x(Real x ->  [if (m<=n) x 0]+[if (n<m) x 0]===x)")
(assume "n" "m" "x" "Rx")
(use "NatLeLtCases" (pt "m") (pt "n"))
;; 3,4
(assume "m<=n")
(simp "m<=n")
(ng #t)
(simp (pf "n<m -> F"))
(ng #t)
(use "RealPlusZero")
(use "Rx")
(assume "n<m")
(assert "n<n")
(use "NatLtLeTrans" (pt "m"))
(use "n<m")
(use "m<=n")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "n<m")
(simp "n<m")
(ng #t)
(simp (pf "m<=n -> F"))
(ng #t)
(use "RealZeroPlus")
(use "Rx")
(assume "m<=n")
(assert "n<n")
(use "NatLtLeTrans" (pt "m"))
(use "n<m")
(use "m<=n")
(assume "Absurd")
(use "Absurd")
;; Proof finshed.
;; (cp)
(save "RealPlusIfNatLeLt")

;; 2.  RealSum
;; ===========

(add-var-name "xs" "ys" "zs" (py "nat=>rea"))

(add-program-constant "RealSum" (py "nat=>nat=>(nat=>rea)=>rea"))
(add-computation-rules
 "RealSum n Zero xs" "0"
 "RealSum n(Succ m)xs" "RealSum n m xs+xs(n+m)")

;; The number m in (RealSum n m xs) says how many elements starting
;; with (xs n) are summed up.

(set-totality-goal "RealSum")
(assert "all xs,n,m TotalRea(RealSum n m xs)")
(assume "xs" "n")
(ind)
;; 5,6
(ng #t)
(use "TotalVar")
;; 6
(assume "m" "IH")
(ng #t)
(use "RealPlusTotal")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(assume "Assertion")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "xs")
(use "Assertion")
;; Proof finished.
;; (cp)
(save-totality)

;; Problem: RealSum Zero(Succ n)xs is not normal.  Solution: cRSum

;; RSum
(set-goal "all n,m,xs exl x x eqd RealSum n m xs")
(assume "n" "m" "xs")
(intro 0 (pt "RealSum n m xs"))
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "RSum")

(animate "RSum")

;; RSumExFree
(set-goal "all n,m,xs cRSum n m xs eqd RealSum n m xs")
(assume "n" "m" "xs")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "RSumExFree")

(deanimate "RSum")

(set-totality-goal "cRSum")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "xs")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Now we can use the deanimated cRSum instead of RealSum.

;; RealSumReal
(set-goal "all xs(all n Real(xs n) ->  all n,m Real(RealSum n m xs))")
(assume "xs" "Rxs")
(assert "all m,n Real(RealSum n m xs)")
(ind)
;; 5,6
(assume "n")
(ng #t)
(use "RealRat")
;; 6
(assume "m" "IH")
(ng #t)
(assume "n")
(use "RealPlusReal")
(use "IH")
(use "Rxs")
;; Assertion proved.
;; 3
(assume "Assertion" "n" "m")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "RealSumReal")

;; cRSumReal
(set-goal "all xs(all n Real(xs n) -> all n,m Real(cRSum n m xs))")
(assume "xs" "Rxs" "n" "m")
(simp "RSumExFree")
(use "RealSumReal")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "cRSumReal")

;; 2023-03-27.  RealSumZeroSucc added.  This a special case of
;; RealSum1CompRule with (xs n) instead of (Zero+xs n)

;; RealSumZeroSucc
(set-goal "all m,xs(all n Real(xs n) ->
 RealSum Zero(Succ m)xs===RealSum Zero m xs+xs m)")
(assume "n" "xs" "Rxs")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumZeroSucc")

;; RealLeMonSum
(set-goal "all xs,ys,m,n(all l(n<=l -> l<n+m -> xs l<<=ys l) ->
 RealSum n m xs<<=RealSum n m ys)")
(assume "xs" "ys")
(ind)
;; 3,4
(assume "n" "Useless")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 4
(assume "m" "IH" "n" "LeHyp")
(ng #t)
(use "RealLeMonPlusTwo")
(use "IH")
(assume "l" "n<=l" "l<n+m")
(use "LeHyp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
;; ?^11:xs(n+m)<<=ys(n+m)
(use "LeHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealLeMonSum")

;; RealSumCompat
(set-goal "all xs,ys,n,m(all l(n<=l -> l<n+m -> xs l===ys l) ->
 RealSum n m xs===RealSum n m ys)")
(assume "xs" "ys" "n" "m" "xs=ys")
(use "RealLeAntiSym")
;; 3,4
(use "RealLeMonSum")
(assume "l" "n<=l" "l<n+m")
(use "RealEqElim0")
(search)
;; 4
(use "RealLeMonSum")
(assume "l" "n<=l" "l<n+m")
(use "RealEqElim1")
(search)
;; Proof finished.
;; (cp)
(save "RealSumCompat")

;; RealSumAssocZero
(set-goal "all xs(all n Real(xs n) ->
 all m xs Zero+RealSum(Succ Zero)m xs===RealSum Zero(Succ m)xs)")
(assume "xs" "Rxs")
(ind)
(ng #t)
(use "RealPlusComm")
(autoreal)
(assume "n" "IH")
(ng #t)
(simpreal "RealPlusAssoc")
(simpreal "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumAssocZero")

;; RealSumAssoc
(set-goal "all xs(all n Real(xs n) ->
 all n,m xs n+RealSum(Succ n)m xs===RealSum n(Succ m)xs)")
(assume "xs" "Rxs" "n")
(ind)
(ng #t)
(use "RealPlusComm")
(autoreal)
(assume "m" "IH")
(ng #t)
(simpreal "RealPlusAssoc")
(simpreal "IH")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumAssoc")

;; RealSumShiftSucc
(set-goal "all xs,ys(
     all n xs n===ys(Succ n) -> Real(ys Zero) -> 
     all n,m RealSum n m xs===RealSum(Succ n)m ys)")
(assume "xs" "ys" "xsDef" "Ry0")
(assert "all n Real(ys n)")
(cases)
(use "Ry0")
(assume "n")
(autoreal)
(assume "Rys" "n")
(ind)
(use "RealEqRefl")
(use "RealRat")
(assume "m" "IH")
(ng #t)
(simpreal "IH")
(simpreal "xsDef")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumShiftSucc")

;; RealSumShiftUp
(set-goal "all xs,l,n(
 all n Real(xs n) -> all m RealSum n m([n0]xs(l+n0))===RealSum(l+n)m xs)")
(assume "xs" "l" "n" "Rxs")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumShiftUp")

;; RealSumShiftDown
(set-goal "all xs,l,n(all n Real(xs n) -> l<=n ->
 all m RealSum n m xs===RealSum(n--l)m([n0]xs(l+n0)))")
(assume "xs" "l" "n" "Rxs" "l<=n")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(use "RealPlusCompat")
;; 9,10
(use "IH")
;; ?^10:xs(n+m)===xs(l+(n--l)+m)
(simp (pf "l+(n--l)=n"))
(use "RealEqRefl")
(autoreal)
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "l<=n")
;; Proof finished.
;; (cp)
(save "RealSumShiftDown")

;; RealSumZeroShiftDown
(set-goal "all xs,n(
 all n Real(xs n) -> 
 all m RealSum n m xs===RealSum Zero m([n0]xs(n+n0)))")
(assume "xs" "n" "Rxs""m")
(inst-with-to "RealSumShiftDown" (pt "xs") (pt "n") (pt "n") "Rxs" "Truth"
	      (pt "m") "Inst")
(use "Inst")
;; Proof finished.
;; (cp)
(save "RealSumZeroShiftDown")

;; For RealSumTimes we will need a variant of RealSumShiftUp

;; RealSumShiftUpMinus
(set-goal "all xs,l,n(
 all n0 Real(xs n0) -> all m RealSum n m xs===RealSum(n+l)m([n0]xs(n0--l)))")
(assume "xs" "l" "n" "Rxs")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(use "RealPlusCompat")
(use "IH")
(simp (pf "n+l+m--l=n+m"))
(use "RealEqRefl")
(autoreal)
(simp "<-" "NatPlusAssoc")
(simp (pf "l+m=m+l"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(save "RealSumShiftUpMinus")

;; 2023-04-20

;; RealSumZeroShiftUp
(set-goal "all xs,n(all n Real(xs n) -> all m
 RealSum Zero m xs===RealSum n m([l](xs(l--n))))")
(assume "xs" "n" "Rxs")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumZeroShiftUp")

;; RealTimesSumDistr
(set-goal "all x,xs(Real x -> all n Real(xs n) -> all n,m(
 x*RealSum n m xs===RealSum n m([l]x*xs l)))")
(assume "x" "xs" "Rx" "Rxs" "n")
(ind)
;; 3,4
(ng #t)
(use "RealTimesZero")
(use "Rx")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "RealTimesPlusDistr")
(use "RealPlusCompat")
(use "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealTimesSumDistr")

;; RealTimesSumDistrLeft
(set-goal "all x,xs(Real x -> all n Real(xs n) -> all n,m(
 (RealSum n m xs)*x===RealSum n m([l]xs l*x)))")
(assume "x" "xs" "Rx" "Rxs" "n" "m")
(use "RealEqTrans" (pt "RealSum n m([l0]x*xs l0)"))
;; 3,4
(simpreal "RealTimesComm")
(use "RealTimesSumDistr")
(auto)
(autoreal)
;; 4
(use "RealSumCompat")
(assume "l" "Useless1" "Useless2")
(ng #t)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealTimesSumDistrLeft")

;; Parallel to NatLubSplit we prove

;; RealSumSplit (was RealSumPlus)
(set-goal "all xs(all n Real(xs n) ->
 all n,m,l(RealSum n m xs+RealSum(n+m)l xs===RealSum n(m+l)xs))")
(assume "xs" "Rxs" "n" "m")
(ind)
;; 3,4
(ng #t)
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; 4
(assume "l" "IH")
(ng #t)
(simpreal "RealPlusAssoc")
(simpreal "IH")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumSplit")

;; 2023-03-27.  RealSumZeroSplit added as a special case of RealSumSplit
;; RealSumZeroSplit with n:=Zero and m instead of Zero+m

;; RealSumZeroSplit
(set-goal "all xs(all n Real(xs n) ->
 all m,l(RealSum Zero m xs+RealSum m l xs===RealSum Zero(m+l)xs))")
(assume "xs" "Rxs" "m" "l")
(simpreal (pf "RealSum m l xs===RealSum(Zero+m)l xs"))
(use "RealSumSplit")
(use "Rxs")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumZeroSplit")

;; RealSumZeroSplitMod
(set-goal "all xs(all n Real(xs n) ->
 all m,n(m<=n -> RealSum Zero m xs+RealSum m(n--m)xs===RealSum Zero n xs))")
(assume "xs" "Rxs" "m" "n" "m<=n")
(simpreal "RealSumZeroSplit")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "RealEqRefl")
(autoreal)
(use "m<=n")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumZeroSplitMod")

;; RealSumMinus (close to RealSumSplit)
(set-goal "all xs(all n Real(xs n) -> all n,m,l(
 RealSum n(m+l)xs+ ~(RealSum n m xs)===RealSum(n+m)l xs))")
(assume "xs" "Rxs" "n" "m" "l")
(use "RealEqPlusCancelL" (pt "RealSum n m xs"))
(autoreal)
(simpreal "RealSumSplit")
(simpreal "RealPlusComm")
(simpreal "<-" "RealPlusAssoc")
(use "RealEqTrans" (pt "RealSum n(m+l)xs+0"))
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal "RealPlusComm")
(use "RealPlusMinusZero")
(autoreal)
;; 17
(use "RealPlusZero")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumMinus")

;; RealSumZeroMinus
(set-goal "all xs(all n Real(xs n) -> all m,l(
 RealSum Zero(m+l)xs+ ~(RealSum Zero m xs)===RealSum m l xs))")
(assume "xs" "Rxs" "m" "l")
(simpreal (pf "RealSum m l xs===RealSum(Zero+m)l xs"))
(use "RealSumMinus")
(use "Rxs")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumZeroMinus")

;; RealSumZeroMinusMod
(set-goal "all xs(all n Real(xs n) -> all m,n(m<=n ->
 RealSum Zero n xs+ ~(RealSum Zero m xs)===RealSum m(n--m)xs))")
(assume "xs" "Rxs" "m" "n" "m<=n")
(use "RealEqvPlusCancelR" (pt "(RealSum Zero m xs)"))
(autoreal)
(simpreal "RealEqvPlusMinus")
(simpreal "RealPlusComm")
(simpreal "RealSumZeroSplitMod")
(use "RealEqRefl")
(autoreal)
(use "m<=n")
(use "Rxs")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumZeroMinusMod")

;; RealSumOne
(set-goal "all xs,n(Real(xs n) -> RealSum n(Succ Zero)xs===xs n)")
(assume "xs" "n" "Rxsn")
(ng #t)
(use "RealZeroPlus")
(use "Rxsn")
;; Proof finished.
;; (cp)
(save "RealSumOne")

;; Special case of RealSumSplit where the left sum has one element only.

;; RealSumSplitL (was RealSumPlusL)
(set-goal "all xs(all n Real(xs n) ->
 all n,m(RealSum n(Succ Zero)xs+RealSum(Succ n)m xs===RealSum n(Succ m)xs))")
(assume "xs" "Rxs" "n" "m")
(ng #t)
(inst-with-to "RealSumSplit" (pt "xs") "Rxs" (pt "n") (pt "Succ Zero") "Inst")
(ng "Inst")
(use "Inst")
;; Proof finished.
;; (cp)
(save "RealSumSplitL")

;; RealSumSplitLPred
(set-goal "all xs(all n0 Real(xs n0) -> all n,m(n<m -> 
 RealSum n(Succ Zero)xs+RealSum(Succ n)(Pred(m--n))xs===
 RealSum n(m--n)xs))")
(assume "xs" "Rxs" "n" "m" "n<m")
(inst-with-to
 "RealSumSplitL" (pt "xs") "Rxs" (pt "n") (pt "Pred(m--n)") "Inst")
(use "RealEqTrans" (pt "RealSum n(Succ(Pred(m--n)))xs"))
(use "Inst")
(simp (pf "Succ(Pred(m--n))=m--n"))
(use "RealEqRefl")
(autoreal)
;; ?^8:Succ(Pred(m--n))=m--n
(use "NatSuccPred")
(simp "<-" "NatLtMinusZero")
(use "n<m")
;; Proof finished.
;; (cp)
(save "RealSumSplitLPred")

;; RealSumSplitLPredCor
(set-goal "all xs(all n0 Real(xs n0) -> all n,m(n<m -> 
 xs n+RealSum(Succ n)(Pred(m--n))xs===RealSum n(m--n)xs))")
(assume "xs" "Rxs" "n" "m" "n<m")
(use "RealEqTrans"
     (pt "RealSum n(Succ Zero)xs+RealSum(Succ n)(Pred(m--n))xs"))
(inst-with-to
 "RealSumSplitL" (pt "xs") "Rxs" (pt "n") (pt "Pred(m--n)") "Inst")
(use "RealPlusCompat")
(ng #t)
(use "RealEqSym")
(use "RealZeroPlus")
(use "Rxs")
(use "RealEqRefl")
(autoreal)
;; ?^4:RealSum n(Succ Zero)xs+RealSum(Succ n)(Pred(m--n))xs===RealSum n(m--n)xs
(use "RealSumSplitLPred")
(use "Rxs")
(use "n<m")
;; Proof finished.
;; (cp)
(save "RealSumSplitLPredCor")

;; RealSumSplitR
(set-goal "all xs(
 all n Real(xs n) -> 
 all n,m(n<m ->
         RealSum n(m--n)xs+RealSum m(Succ Zero)xs===RealSum n(Succ(m--n))xs))")
(assume "xs" "Rxs" "n" "m" "n<m")
(inst-with-to
 "RealSumSplit" (pt "xs") "Rxs" (pt "n") (pt "m--n") (pt "Succ Zero") "Inst")
(simphyp-with-to "Inst" (pf "n+(m--n)=m") "InstS")
(simphyp-with-to "InstS" (pf "m--n+Succ Zero=Succ(m--n)") "InstSS")
(use "InstSS")
;; 9
(use "Truth")
;; ?^6:n+(m--n)=m
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "n<m")
;; Proof finshed.
;; (cp)
(save "RealSumSplitR")

;; RealSumSucc takes care of the case where the right sum has one
;; element only.

;; RealSumPlus (was RealSumPlusSeq)
(set-goal "all xs,ys(all n Real(xs n) -> all n Real(ys n) -> all m,n(
 RealSum n m xs+RealSum n m ys===RealSum n m([l]xs l+ys l)))")
(assume "xs" "ys" "Rxs" "Rys")
(ind)
;; 3,4
(assume "n")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH" "n")
(ng #t)
(simpreal "<-" "IH")
(simpreal "RealPlusAssoc")
(simpreal "RealPlusAssoc")
(use "RealPlusCompat")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "xs(n+m)+RealSum n m ys===(RealSum n m ys)+xs(n+m)"))
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumPlus")

;; RealSumUMinus
(set-goal "all xs(all n Real(xs n) -> all n,m(
 ~(RealSum n m xs)===RealSum n m([l]~(xs l))))")
(assume "xs" "Rxs" "n")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "<-" "IH")
(use "RealUMinusPlus")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumUMinus")

;; RealLeAbsSum
(set-goal "all xs(all n Real(xs n) -> all n,m(
  abs(RealSum n m xs)<<=RealSum n m([l]abs(xs l))))")
(assume "xs" "Rxs" "n")
(ind)
;; 3,4
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(use "RealLeTrans" (pt "abs(RealSum n m xs)+abs(xs(n+m))"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(autoreal)
(use "IH")
;; Proof finished.
;; (cp)
(save "RealLeAbsSum")

;; RealSumZeros
(set-goal "all xs(all n xs n===0 -> all n,m RealSum n m xs===0)")
(assume "xs" "xsProp" "n")
(ind)
;; 3,4
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "xsProp")
(simpreal "IH")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealSumZeros")

;; RealSumZerosSharp
(set-goal "all xs(all n Real(xs n) ->
 all n,m((all l(n<=l -> l<n+m -> xs l===0)-> RealSum n m xs===0)))")
(assume "xs" "Rxs" "n")
(ind)
;; 3,4
(assume "Useless")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH" "xsProp")
(ng #t)
(simpreal "IH")
(simpreal "RealZeroPlus")
(use "xsProp")
(use "Truth")
(ng #t)
(use "Truth")
(use "Rxs")
;; ?^11:all l(n<=l -> l<n+m -> xs l===0)
(assume "l" "n<=l" "l<n+m")
(use "xsProp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealSumZerosSharp")

;; RealSumZerosL
(set-goal "all xs,m1,m2(all n Real(xs n) ->
 all m(m<m1 -> xs m===0) ->
 RealSum Zero(m1+m2)xs===RealSum m1 m2 xs)")
(assume "xs" "m1" "m2" "Rxs" "L0")
(simpreal "<-" "RealSumSplit")
(assert "RealSum Zero m1 xs===0")
(use "RealSumZerosSharp")
(use "Rxs")
(assume "m" "Useless" "mProp")
(use "L0")
(use "mProp")
;; Assertion proved.
(assume "m1Prop")
(simpreal "m1Prop")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumZerosL")

;; RealSumZerosR
(set-goal "all xs,m0,m1,m2(all n Real(xs n) ->
 all m(m<m2 -> xs(m0+m1+m)===0) ->
 RealSum m0(m1+m2)xs===RealSum m0 m1 xs)")
(assume "xs" "m0" "m1" "m2" "Rxs" "R0")
(simpreal "<-" "RealSumSplit")

(assert "RealSum(m0+m1)m2 xs===0")
(use "RealSumZerosSharp")
(use "Rxs")
(assume "m" "Hl1" "Hl2")

(assert "exl l(m=m0+m1+l andnc l<m2)")
(intro 0 (pt "m--(m0+m1)"))
(split)
;; 13,14
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(use "Hl1")
;; 14
(simp (pf "m2=m2+(m0+m1)--(m0+m1)"))
(use "NatLtMonMinusLeft")
(simp "NatPlusComm")
(use "Hl2")
(use "Hl1")
(simp "NatMinus3RewRule")
(use "Truth")
;; Assertion proved.
(assume "ExH")
(by-assume "ExH" "l" "lProp")
(simp "lProp")
(use "R0")
(use "lProp")
;; Assertion proved.
;; 5
(assume "EqH")
(simpreal "EqH")
(use "RealPlusZero")
(autoreal)
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumZerosR")

;; Proof of RealSumZerosR could be simplified using SeqShiftBdElim

;; RealSumZerosLR
(set-goal "all m1,m2,m3,xs(
 all n Real(xs n) ->
 all l(l<m1 -> xs l===0) ->
 all l(m1+m2<=l -> l<m1+m2+m3 -> xs l===0) ->
 RealSum Zero(m1+m2+m3)xs===RealSum m1 m2 xs)")

;; 0 ... 6  ... 10    ... 16
;; 0 ... m1 ... m1+m2 ... m1+m2+m3

(assume "m1" "m2" "m3" "xs" "Rxs" "L0" "R0")
(simp "<-" "NatPlusAssoc")
(simpreal "RealSumZerosL")
(use "RealSumZerosR")
(use "Rxs")
(assume "m" "m<m3")
(use "R0")
(use "Truth")
(use "m<m3")
(use "L0")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumZerosLR")

;; RealIfImpToIfIf (was RealIfBooleImpToIfIf)
(set-goal "all x(Real x -> all boole, boole0((boole -> boole0) ->
 [if boole0 [if boole x 0] 0]===[if boole x 0]))")
(assume "x" "Rx")
(cases)
;; 3,4
(cases)
;; 5,6
(assume "Useless")
(ng #t)
(use "RealEqRefl")
(use "Rx")
;; 6
(assume "Absurd")
(use "EfRealEq")
(use "Absurd")
(use "Truth")
;; 4
(ng #t)
(assume "boole" "Useless")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealIfImpToIfIf")

;; 2023-03-15

;; (display-pconst "RealSum")
;; RealSum
;;   comprules
;; 0	RealSum n Zero xs	0
;; 1	RealSum n(Succ m)xs	RealSum n m xs+xs(n+m)

;; In nat.scm we had (add-var-name "ws" (py "nat=>boole"))
;; (add-var-name "qs" "rs" (py "nat=>boole"))

;; RealSumSplitTwo
(set-goal "all xs,ws(
     all n Real(xs n) -> 
     all n,m 
      RealSum n m xs===
      RealSum n m([l][if (ws l) (xs l) 0])+
      RealSum n m([l][if (ws l) 0 (xs l)]))")
(assume "xs" "ws" "Rxs" "n")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "IH")
(cases (pt "ws(n+m)"))
;; 10,11
(ng #t)
(assume "ws(n+m)")
(simpreal "RealPlusZero")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "(RealSum n m([n0][if (ws n0) 0 (xs n0)])+xs(n+m))===
               xs(n+m)+(RealSum n m([n0][if (ws n0) 0 (xs n0)]))"))
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; 11
(ng #t)
(assume "ws(n+m) -> F")
(simpreal "RealPlusZero")
(simpreal "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumSplitTwo")

;; 2023-04-19.  Another inclusion property, for RealSum

;; RatSumRealSum
(set-goal "all as,n,m RatSum n m as===RealSum n m as")
(assume "as" "n")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "RatPlusRealPlus")
(use "RealPlusCompat")
(use "IH")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RatSumRealSum")

;; RealSumSplitTwoGen
(set-goal "all xs(
     all n Real(xs n) -> 
     all n,m,ws,ws0
      RealSum n m([l][if (ws l) (xs l) 0])===
      RealSum n m([l][if (ws l andb ws0 l) (xs l) 0])+
      RealSum n m([l][if (ws l andb negb(ws0 l)) (xs l) 0]))")
(assume "xs" "Rxs" "n")
(ind)
;; 3,4
(assume "ws" "ws0")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH" "ws" "ws0")
(ng #t)
(simpreal "IH" (pt "ws0"))
(drop "IH")
(cases (pt "ws(n+m)"))
;; 12,13
(ng #t)
(assume "wsH")
(cases (pt "ws0(n+m)"))
;; 15,16
(ng #t)
(assume "ws0H")
(simpreal "RealPlusZero")
(simpreal "<-" "RealPlusAssoc")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealPlusComm")
(autoreal)
;; 17
(assume "ws0NH")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 13
(ng #t)
(assume "wsNH")
(simpreal "RealPlusZero")
(simpreal "RealPlusZero")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumSplitTwoGen")

;; RealSumSplitSuccBegin
(set-goal "all n,m,xs(all n Real(xs n) ->
 xs n+RealSum(Succ n)m xs===RealSum n(Succ m)xs)")
(assume "n" "m" "xs" "Rxs")
(simpreal "<-" "RealSumOne")
;; RealSumOne 1
(use-with "RealSumSplit" (pt "xs") "Rxs" (pt "n") (pt "Succ Zero") (pt "m"))
;; RealSumOne 2
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumSplitSuccBegin")

;; RealSumZeroSuccBegin
(set-goal "all m,xs(all n Real(xs n) ->
 xs Zero+RealSum (Succ Zero)m xs===RealSum Zero(Succ m)xs)")
(use "RealSumSplitSuccBegin")
;; Proof finihed.
;; (cp)
(save "RealSumZeroSuccBegin")

;; RealNNegSeqRealSum
(set-goal "all n,m,xs(all n RealNNeg(xs n) -> RealNNeg(RealSum n m xs))")
(assume "n" "m" "xs" "LeH")
(ind (pt "m"))
;; Ind 1
(ng #t)
(use "RealZeroLeToNNeg")
(use "RealLeRefl")
(realproof)
;; Ind 2
(assume "n0" "IH")
(ng #t)
(use "RealZeroLeToNNeg")
(use "RealLeTrans" (pt "RealPlus 0 0"))
;; RealLeTrans 1
(use "RealLeRefl")
(realproof)
;; RealLeTrans 2
(use "RealLeMonPlusTwo")
;; RealLeMonPlusTwo 1 
(use "RealNNegToZeroLe")
(use "IH")
;; RealLeMonPlusTwo 2 
(use "RealNNegToZeroLe")
(use "LeH")
;; Proof finished.
;; (cp)
(save "RealNNegSeqRealSum")

;; 2023-04-16

;; We transfer theorems on RatGeomSum to RealGeomSum, using inclusion
;; properties

;; (search-about "RatGeomSum")

;; RatGeomSumEqvNoDivOneHalf
;; all n (1#2)*RatSum Zero n([n43741](1#2)**n43741)==1+ ~((1#2)**n)

;; RatGeomSumEqvNoDiv
;; all a,n (1+ ~a)*RatSum Zero n([n43676]a**n43676)==1+ ~(a**n)

;; It is unclear how a transformation of rat-propositions into
;; real-propositions should work.  Postponed.  We only have

;; RealGeomSumEqvNoDivAux1
(set-goal "all a,n,m
 (1+ ~a)*RatSum n m(RatExp a)===(RatExp a n)*(1+ ~(RatExp a m))")
(assume "a" "n" "m")
(use "RatEqvToRealEq")
(use "RatGeomSumEqvNoDiv")
;; Proof finished.
;; (cp)
(save "RealGeomSumEqvNoDivAux1")

;; RealGeomSumEqvNoDivOneHalf
(set-goal
 "all n,m (1#2)*RealSum n m([n](1#2)**n)===(1#2)**n*(1+ RealUMinus((1#2)**m))")
(assume "n" "m")
(simpreal (pf "RealSum n m([n](1#2)**n)===RatSum n m([n](1#2)**n)"))
(get 4)
(simpreal "RatSumRealSum")
(use "RealSumCompat")
(bpe-ng #t)
(assume "l" "Useless1" "Useless2")
(use "RatEqvToRealEq")
(use "Truth")
;; 3
(simpreal "<-" "RatTimesRealTimes")
;; ?^10:(1#2)*RatSum n m([n0](1#2)**n0)===(1#2)**n*(1+ ~((1#2)**m))
;; lhs ok
(simpreal "<-" "RatUMinusRealUMinus")
(simpreal "<-" "RatPlusRealPlus")
(simpreal "<-" "RatTimesRealTimes")
(use "RatEqvToRealEq")
(use "RatGeomSumEqvNoDivOneHalf")
;; Proof finished.
;; (cp)
(save "RealGeomSumEqvNoDivOneHalf")

;; In RealSumTimes and RealSumDiags we need to refer to the root based
;; pair coding of natural numbers.  The components of a pair coded by
;; k can be obtained as lft(RtD k) and rht(RtD k).

(remove-var-name "i" "j" "k")
(add-var-name "i" "j" "k" (py "nat"))

;; RealSumTimes
(set-goal "all xs,ys(
     all n Real(xs n) -> 
     all n Real(ys n) -> 
     all n 
      RealSum Zero n xs*RealSum Zero n ys===
      RealSum Zero(n*n)([k]xs(lft(RtD k))*ys(rht(RtD k))))")
(assume "xs" "ys" "Rxs" "Rys")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "n" "IH")
(simpreal "RealSumZeroSucc")
(simpreal "RealSumZeroSucc")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "IH")
(drop "IH")
(simpreal "<-" "RealPlusAssoc")

(def "zs" "([k]xs lft(RtD k)*ys rht(RtD k))")
(simp "<-" "zsDef")

(assert "all n Real(zs n)")
(assume "n0")
(simp "zsDef")
(autoreal)
;; Assertion proved.
(assume "Rzs")

(simpreal (pf "RealSum Zero(Succ n*Succ n)zs===
               RealSum Zero(n*n)zs+RealSum(n*n)(n+n+1)zs"))
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simpreal (pf "RealSum Zero n ys===RealSum(n*n)n([k]ys(k--n*n))"))
;; 44,45
(get 45)
(inst-with-to
 "RealSumShiftUpMinus"
 (pt "ys") (pt "n*n") (pt "Zero") "Rys" (pt "n") "Inst")
(use "Inst")
;; 44
(simpreal "RealTimesSumDistr")
(bpe-ng #t)
(simpreal "<-" (pf "RealSum(n*n)n zs+RealSum(n*n+n)(n+1)zs===
                    RealSum(n*n)(n+n+1)zs"))
;; 52,53
(get 53)
(simp (pf "n+n+1=n+(n+1)"))
(use "RealSumSplit")
(assume "m")
(autoreal)
(use "Truth")
;; 52
(use "RealPlusCompat")
;; 58,59
(use "RealSumCompat")
(assume "m" "n*n<=m" "m<n*n+n")
(ng #t)
(simp "zsDef")
;; ?^63:xs n*ys(m--n*n)===([k]xs lft(RtD k)*ys rht(RtD k))m
(bpe-ng #t)
;; ?^64:xs n*ys(m--n*n)===xs lft(RtD m)*ys rht(RtD m)
;; Write m in the form n*n+l.  Then RtDUp fits.
(def "l" "m--n*n")
(assert "m=n*n+l")
(simp "lDef")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "n*n<=m")
;; Assertion proved.
(assume "A1")

(simp "A1")

(simp "RtDUp")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; ?^81:l<n
(simp "lDef")
(simp "<-" "NatPlusCancelLtR" (pt "n*n"))
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(use "m<n*n+n")
(use "n*n<=m")
;; ?^59:(RealSum Zero n xs+xs n)*ys n===RealSum(n*n+n)(n+1)zs
(simpreal "<-" "RealSumZeroSucc")
(simp (pf "n+1=Succ n"))
(simpreal (pf "RealSum Zero(Succ n)xs===
               RealSum(n*n+n)(Succ n)([k]xs(k--(n*n+n)))"))
;; 93,94
(get 94)
(inst-with-to
 "RealSumShiftUpMinus"
 (pt "xs") (pt "n*n+n") (pt "Zero") "Rxs" (pt "Succ n") "Inst")
(use "Inst")
;; 93
;; RealSum(n*n+n)(Succ n)([k]xs(k--(n*n+n)))*ys n===RealSum(n*n+n)(Succ n)zs
(simpreal "RealTimesSumDistrLeft")
(use "RealSumCompat")
(assume "k" "n*n+n<=k" "k<=n*n+n+n")
(ng #t)
(simp "zsDef")
(bpe-ng #t)
;; ?^104:xs(k--(n*n+n))*ys n===xs lft(RtD k)*ys rht(RtD k)
(def "l" "k--(n*n+n)")
(simp "<-" "lDef")
(assert "k=n*n+n+l")
(simp "lDef")
(simp "NatPlusMinusAssoc")
(simp "NatPlusComm")
(simp "<-" "NatPlusMinusAssoc")
(use "Truth")
(use "Truth")
(use "n*n+n<=k")
;; Assertion proved.
(assume "A1")

;; 121
(simphyp-with-to "k<=n*n+n+n" "A1" "HS")
(assert "l<Succ n")
(simp "<-" "NatPlusCancelLtL" (pt "n*n+n"))
(use "HS")
;; Assertion proved.
(assume "A2")

(drop "HS")
(simp "A1")
(simp "RtDFlat")
(use "RealEqRefl")
(autoreal)
(use "NatLtSuccToLe")
(use "A2")
;; 99
(assume "n0")
(autoreal)
;; 92
(use "Truth")
;; 90
(use "Rxs")
;; 50
(assume "n0")
(autoreal)
;; 40
;; RealSum Zero(Succ n*Succ n)zs===RealSum Zero(n*n)zs+RealSum(n*n)(n+n+1)zs
(simpreal "RealSumZeroSplit")
(use "RealEqRefl")
(autoreal)
(use "Rzs")
;; 25
(autoreal)
;; 11
(use "Rys")
;; 9
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumTimes")

;; RealSumIfSplit
(set-goal "all ws,ws0,zs(
 all n(ws n -> ws0 n -> F) ->
 all n Real(zs n) ->  all m(
 RealSum Zero m([n][if (ws n) (zs n) 0])+
 RealSum Zero m([n][if (ws0 n) (zs n) 0])===
 RealSum Zero m([n][if (ws n orb ws0 n) (zs n) 0])))")
(assume "ws" "ws0" "zs" "ws cap ws0=0" "Rzs")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simpreal "<-" "IH")
(drop "IH")

(assert
"[if (ws m orb ws0 m) (zs m) 0]===[if (ws m) (zs m) 0]+[if (ws0 m) (zs m) 0]")
(cases (pt "ws m"))
;; 13,14
(assume "ws m")
(ng #t)
(cases (pt "ws0 m"))
;; 17,18
(assume "ws0 m")
(inst-with-to "ws cap ws0=0" (pt "m") "ws m" "ws0 m" "Absurd")
(efproof)
;; 18
(assume "Useless")
(ng #t)
(use "RealEqSym")
(use "RealPlusZero")
(autoreal)
;; 14
(assume "Useless")
(ng #t)
(use "RealEqSym")
(use "RealZeroPlus")
(autoreal)
;; Assertion proved.
(assume "Assertion")
;; 30
(simpreal "Assertion")
(simpreal "RealPlusAssoc")
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
(save "RealSumIfSplit")

;; RealIfSplit
(set-goal "all x(Real x -> all boole,boole0(
 (boole -> boole0 -> F) ->
 [if boole x 0]+[if boole0 x 0]===[if (boole orb boole0) x 0]))")
(assume "x" "Rx")
(cases)
;; 3,4
(cases)
;; 5,6
(assume "AbsurdImp")
(assert "F")
(use "AbsurdImp")
(use "Truth")
(use "Truth")
(assume "Absurd")
(efproof)
;; 6
(assume "Useless")
(ng #t)
(use "RealPlusZero")
(use "Rx")
;; 4
(cases)
(assume "Useless")
(ng #t)
(use "RealZeroPlus")
(use "Rx")
;; 17
(assume "Useless")
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RealIfSplit")

;; 2024-10-03

;; RealSumDiags
(set-goal "all xs,ys(
     all n Real(xs n) -> 
     all n Real(ys n) -> 
     all n 
      RealSum Zero(Succ n)
      ([m]
        RealSum Zero((m+1)*(m+1))
        ([k][if (lft(RtD k)+rht(RtD k)=m) (xs(lft(RtD k))*ys(rht(RtD k))) 0]))===
      RealSum Zero((n+1)*(n+1))
      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs(lft(RtD k))*ys(rht(RtD k))) 0]))")
(assume "xs" "ys" "Rxs" "Rys")
(ind)
;; 3,4
(ng #t)
(simpreal "RealZeroPlus")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
;; 4
(assume "n" "IH")
(simpreal "RealSumZeroSucc")
(simpreal "IH")
(drop "IH")
(bpe-ng #t)

;; ?^16:RealSum Zero((n+1)*(n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0])+
;;      RealSum Zero((Succ n+1)*(Succ n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)=Succ n) (xs lft(RtD k)*ys rht(RtD k)) 0])===
;;      RealSum Zero((Succ n+1)*(Succ n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=Succ n) (xs lft(RtD k)*ys rht(RtD k)) 0])

(simpreal
   (pf "RealSum Zero((n+1)*(n+1))
        ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0])===
        RealSum Zero((Succ n+1)*(Succ n+1))
        ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0])"))
;; 17,18
(simpreal "RealSumPlus")
(bpe-ng #t)
(use "RealSumCompat")
(bpe-ng #t)
(assume "k" "Useless1" "Useless2")
(simp "<-" (pf "(lft(RtD k)+rht(RtD k)<=n)orb(lft(RtD k)+rht(RtD k)=
 Succ n)eqd(lft(RtD k)+rht(RtD k)<=Succ n)"))

;; ?^26:[if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0]+
;;      [if (lft(RtD k)+rht(RtD k)=Succ n) (xs lft(RtD k)*ys rht(RtD k)) 0]===
;;      [if (lft(RtD k)+rht(RtD k)<=n orb lft(RtD k)+rht(RtD k)=Succ n)
;;        (xs lft(RtD k)*ys rht(RtD k))
;;        0]

(use "RealIfSplit")
(autoreal)
;; 29
(assume "LeH" "EqH")
(simphyp-with-to "LeH" "EqH" "Absurd")
(ng "Absurd")
(use "Absurd")

;; ?^27:(lft(RtD k)+rht(RtD k)<=n orb lft(RtD k)+rht(RtD k)=Succ n)eqd
;;      (lft(RtD k)+rht(RtD k)<=Succ n)

(use "BooleEqToEqD")
(cases (pt "lft(RtD k)+rht(RtD k)<=n"))
;; 35,36
(assume "LeH")
(ng #t)
(simp (pf "lft(RtD k)+rht(RtD k)<=Succ n"))
(use "Truth")
(use "NatLeTrans" (pt "n"))
(use "LeH")
(use "Truth")
;; 36
(assume "NotLeH")
(ng #t)
(use "BooleAeqToEq")
;; 45,46
(assume "EqH")
(simp "EqH")
(use "Truth")
;; 46
(assume "LeH")
(use "NatLeAntiSym")
(use "LeH")
(use "NatLtToSuccLe")
(use "NatNotLeToLt")
(use "NotLeH")
;; 21
(assume "n0")
(autoreal)
;; 20
(assume "n0")
(autoreal)

;; ?^18:RealSum Zero((n+1)*(n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0])===
;;      RealSum Zero((Succ n+1)*(Succ n+1))
;;      ([k][if (lft(RtD k)+rht(RtD k)<=n) (xs lft(RtD k)*ys rht(RtD k)) 0])

(defnc "zs"
  "[k][if (lft(RtD k)+rht(RtD k)<=n) (xs(lft(RtD k))*ys(rht(RtD k))) 0]")
(assert "all n Real(zs n)")
(assume "n0")
(simp "zsDef")
(realproof)
(assume "Rzs")
(simp "<-" "zsDef")

;; ?^68:RealSum Zero((n+1)*(n+1))zs===RealSum Zero((Succ n+1)*(Succ n+1))zs

(simp (pf "(Succ n+1)*(Succ n+1)=(n+1)*(n+1)+(n+1+(n+1)+1)"))
;; 69,70
(simpreal "<-" "RealSumZeroSplit")
(simpreal (pf "RealSum((n+1)*(n+1))(n+1+(n+1)+1)zs===0"))
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; ?^74:RealSum((n+1)*(n+1))(n+1+(n+1)+1)zs===0
(simp "zsDef")
(use "RealEqTrans" (pt "RealSum((n+1)*(n+1))(n+1+(n+1)+1)([k]0)"))
;; 79,80
(use "RealSumCompat")
(assume "k" "(n+1)^2<=k" "k<(n+2)^2")
(bpe-ng #t)
(cut "lft(RtD k)+rht(RtD k)<=n -> F")
;; 84,85
(assume "FH")
(simp "FH")
(use "RatEqvToRealEq")
(use "Truth")
;; ?^85:lft(RtD k)+rht(RtD k)<=n -> F
(cut "n<lft(RtD k)+rht(RtD k)")
(assume "<H" "<=H")
(assert "n<n")
(use "NatLtLeTrans" (pt "lft(RtD k)+rht(RtD k)"))
(use "<H")
(use "<=H")
(assume "Absurd")
(use "Absurd")
;; ?^90:n<lft(RtD k)+rht(RtD k)
(cases (pt "k<(n+1)*(n+1)+(n+1)"))
;; 97,98
(assume "k<(n+1)^2+n+1")
(cut "lft(RtD k)=n+1")
(assume "EqH")
(simp "EqH")
(use "NatLtLeTrans" (pt "n+1"))
(use "Truth")
(use "Truth")
;; ?^101:lft(RtD k)=n+1
;; (simp "LExFree") ;L and cL not available in the present setting.  Use
;; (pp "RtDUp") all n,l(l<n -> RtD(n*n+l)=(n pair l))
;; with n+1 and l := (n+1)^2--k
(def "l" "k--(n+1)*(n+1)")

(assert "RtD((n+1)*(n+1)+l)=(n+1 pair l)")
(use "RtDUp")
(simp "lDef")
;;?^116:k--(n+1)*(n+1)<n+1
(simp "<-" "NatLtPlusMinus")
(simp "NatPlusComm")
(use "k<(n+1)^2+n+1")
(use "(n+1)^2<=k")
;; Assertion proved.
(assume "A1")
;; ?^120:lft(RtD k)=n+1
(simp (pf "k=(n+1)*(n+1)+l"))
(simp "A1")
(use "Truth")
;; ?^122:k=(n+1)*(n+1)+l
(simp "lDef")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(use "(n+1)^2<=k")
;; ?^98:(k<(n+1)*(n+1)+(n+1) -> F) -> n<lft(RtD k)+rht(RtD k)
(assume "NegH")
(cut "rht(RtD k)=n+1")
(assume "EqH")
(simp "EqH")
(use "NatLtLeTrans" (pt "n+1"))
(use "Truth")
(use "Truth")
;; ?^130:rht(RtD k)=n+1
(def "l" "k--((n+1)*(n+1)+(n+1))")

;; (assert "RtD")
;; (pp "RtDFlat")
;;  all n,l(l<=n -> RtD(n*n+n+l)=(l pair n))
(assert "RtD((n+1)*(n+1)+(n+1)+l)=(l pair n+1)")
(use "RtDFlat")
(simp "lDef")
;; ?^145:k--((n+1)*(n+1)+(n+1))<=n+1
(simp "<-" "NatLePlusCancelR" (pt "(n+1)*(n+1)+(n+1)"))
(use "Truth")
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(use "NatLtSuccToLe")
(use "k<(n+2)^2")
;; ?^149:(n+1)*(n+1)+(n+1)<=k
(use "NatNotLtToLe")
(use "NegH")
;; Assertion proved.
(assume "A1")
;; ?^153:rht(RtD k)=n+1
(simp (pf "k=((n+1)*(n+1)+(n+1))+l"))
(simp "A1")
(use "Truth")
;; ?^155:k=(n+1)*(n+1)+(n+1)+l
(simp "lDef")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(use "NatNotLtToLe")
(use "NegH")
;; ?^80:RealSum((n+1)*(n+1))(n+1+(n+1)+1)([n0]0)===0
(use "RealSumZeros")
(assume "n0")
(use "RatEqvToRealEq")
(use "Truth")
;; 72
(use "Rzs")
;; 70
(use "Truth")
;; 13
(assume "n0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumDiags")

;; RealSumComm
(set-goal "all xs,ys(all n Real(xs n) -> all n Real(ys n) ->
 all n,m(all n0(n<=n0 -> n0<n+m -> ys n0===xs(n+n+Pred m--n0)) ->
         RealSum n m xs===RealSum n m ys))")
(assume "xs" "ys" "Rxs" "Rys")

(assert "all n,m RealSum n m xs===RealSum n m([n0]xs(n+n+Pred m--n0))")
(assume "n")
(ind)
;; 6,7
(use "RealEqRefl")
(use "RealRat")
;; 7
(assume "m" "IH")
(simp "Pred1CompRule")
;; ?^10:RealSum n(Succ m)xs===RealSum n(Succ m)([n0]xs(n+n+m--n0))
(simp "RealSum1CompRule")
(simpreal "RealPlusComm")
(simpreal "IH")
(simpreal "<-" "RealSumAssoc")
(bpe-ng #t)
(simpreal
 (pf "RealSum n m([n0]xs(n+n+Pred m--n0))===
      RealSum(Succ n)m([n0]xs(n+n+m--n0))"))
(simp (pf "n+m=n+n+m--n"))
(use "RealEqRefl")
(autoreal)
(simp "<-" "NatPlusAssoc")
(simp "<-" "NatPlusMinusAssoc")
(simp (pf "n+m--n=m"))
(use "Truth")
(use "Truth")
(use "Truth")
;; ?^20:RealSum n m([n0]xs(n+n+Pred m--n0))===
;;      RealSum(Succ n)m([n0]xs(n+n+m--n0))
(cases (pt "m"))
;; 29,30
(assume "m=0")
(use "RealEqRefl")
(use "RealRat")
;; 30
(assume "m0" "m=Sm0")
(use "RealSumShiftSucc")
(bpe-ng #t)
(assume "n0")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 17
(assume "n0")
(autoreal)
;; Assertion proved.
(assume "H1" "n" "m" "EqH")
(simpreal "H1")
(use "RealSumCompat")
(assume "l" "n<=l" "l<=n+m")
(simpreal "EqH")
(use "RealEqRefl")
(autoreal)
(use "l<=n+m")
(use "n<=l")
;; Proof finished.
;; (cp)
(save "RealSumComm")

;; As a special case we have

;; RealSumCommZero
(set-goal "all xs,ys(all n Real(xs n) -> all n Real(ys n) ->
 all m(all n0(n0<m -> ys n0===xs(Pred m--n0)) ->
         RealSum Zero m xs===RealSum Zero m ys))")
(assume "xs" "ys" "Rxs" "Rys" "m" "ysProp")
(use "RealSumComm")
(use "Rxs")
(use "Rys")
(assume "n0" "Useless")
(use "ysProp")
;; Proof finished.
;; (cp)
(save "RealSumCommZero")

;; Needed in RealCauchyProdLimECor to simplify inside of a lambda
(animate "RSum")

(set-goal "cRSum eqd RealSum")
(ng #t)
(use "InitEqD")
;; (cp)
(save "cRSumEqDRealSum")

(deanimate "RSum")

;; 3.  Permutation pairs Pms
;; =========================

;; We aim at the finite reordering theorem for real sums.  It says
;; that an arbitrary permutation of (x0 ... xl) preserves the sum:

;; all l,xs(
;;  all k Real(xs k) -> 
;;  all ws,f,f0(
;;  Pms l ws f f0 -> RealSum Zero(Succ l)xs===RealSum Zero(Succ l)([n]xs(f n))))

;; This involves the notion (Pms m ws f f0) of a permutation pair f and fo
;; of the natural numbers {0 ... m) \cap ws.  We treat Pms first.

(add-var-name "f" "g" (py "nat=>nat"))

(add-ids
 (list (list "Pms"
	     (make-arity (py "nat") (py "nat=>boole")
			 (py "nat=>nat") (py "nat=>nat"))))
 '("all m,ws,f,f0(
  all n f0(f n)=n  ->
  all n f(f0 n)=n  ->
  all n(m<n -> ws n -> F) ->
  all n((ws n -> F) -> f n=n) ->
  Pms m ws f f0)" "PmsIntro"))

;; PmsCirc
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n f0(f n)=n)")
(assume "m" "ws" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsCirc")

;; PmsCircInv
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n f(f0 n)=n)")
(assume "m" "ws" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsCircInv")

;; PmsIdUp (was PmsFalseUp)
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n(m<n -> ws n -> F))")
(assume "m" "ws" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsIdUp")

;; PmsIdOut (was PmsFalseId)
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n((ws n -> F) -> f n=n))")
(assume "m" "ws" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsIdOut")

;; This concludes the four elimination properties for Pms.

;; PmsSucc
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> Pms(Succ m)ws f f0)")
(assume "m" "ws" "f" "f0" "PH")
(intro 0)
;; 3-6
(use "PmsCirc" (pt "m") (pt "ws"))
(use "PH")
;; 4
(use "PmsCircInv" (pt "m") (pt "ws"))
(use "PH")
;; 5
(assume "n" "Sm<n")
(use "PmsIdUp" (pt "m") (pt "f") (pt "f0"))
(use "PH")
(use "NatLtTrans" (pt "Succ m"))
(use "Truth")
(use "Sm<n")
;; 6
(use "PmsIdOut" (pt "m") (pt "f0"))
(use "PH")
;; Proof finished.
;; (cp)
(save "PmsSucc")

;; PmsSuccInv (DB: SmallerPerm)
(set-goal
 "all m,ws,f,f0(Pms(Succ m)ws f f0 -> (ws(Succ m) -> F) -> Pms m ws f f0)")
(assume "m" "ws" "f" "f0" "PmsS" "Smnotinws")
(intro 0)
;; 3-6
(use "PmsCirc" (pt "Succ m") (pt "ws"))
(use "PmsS")
;; 4
(use "PmsCircInv" (pt "Succ m") (pt "ws"))
(use "PmsS")
;; ?^5:all n(m<n -> ws n -> F)
(assume "n" "m<n")
(cut "Succ m<=n")
(assume "Sm<=n")
(cases (pt "Succ m<n"))
;; 13,14
(use-with "PmsIdUp"
 (pt "Succ m") (pt "ws") (pt "f") (pt "f0") "PmsS" (pt "n"))
(assume "Smnot<n")
(assert "n<=Succ m")
(use "NatNotLtToLe")
(use "Smnot<n")
(assume "n<=Sm")
(assert "n=Succ m")
(use "NatLeAntiSym")
(use "n<=Sm")
(use "Sm<=n")
(assume "n=Sm")
(simp "n=Sm")
(use "Smnotinws")
(use "NatLtToSuccLe")
(use "m<n")
;; ?^6:all n((ws n -> F) -> f n=n)
(use "PmsIdOut" (pt "Succ m") (pt "f0"))
(use "PmsS")
;; Proof finished.
;; (cp)
(save "PmsSuccInv")

;; PmsIn (DB: wsClosed)
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n(ws n -> ws(f n)))")
(assume "m" "ws" "f" "f0" "PH" "n" "ws n")
(use "StabAtom")
(assume "fnnotinws")
(assert "f(f n)=f n")
(use "PmsIdOut" (pt "m") (pt "ws") (pt "f0"))
(use "PH")
(use "fnnotinws")
;; Assertion proved.
(assume "ffn=fn")
(assert "f0(f(f n))=f0(f n)")
(simp "ffn=fn")
(use "Truth")
;; Assertion proved.
(assume "f0ffn=f0fn")
(use "fnnotinws")
(simp (pf "f n=n"))
(use "ws n")
(use "NatEqTrans" (pt "f0(f(f n))"))
(simp "PmsCirc" (pt "m") (pt "ws"))
(use "Truth")
(use "PH")
(simp "ffn=fn")
(simp "PmsCirc" (pt "m") (pt "ws"))
(use "Truth")
(use "PH")
;; Proof finished.
;; (cp)
(save "PmsIn")

;; We prove that for all numbers outside ws not only f is the identity,
;; but also its inverse f0

;; PmsIdOutInv
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> all n((ws n -> F) -> f0 n=n))")
(assume "m" "ws" "f" "f0" "PH" "n" "ws n -> F")
(assert "n=f n")
(use "NatEqSym")
(use "PmsIdOut" (pt "m") (pt "ws") (pt "f0"))
(use "PH")
(use "ws n -> F")
(assume "n=f n")
(use "NatEqTrans" (pt "f0(f n)"))
(simp "<-" "n=f n")
(use "Truth")
(use "PmsCirc" (pt "m") (pt "ws"))
(use "PH")
;; Proof finished.
;; (cp)
(save "PmsIdOutInv")

;; PmsSym
(set-goal "all m,ws,f,f0(Pms m ws f f0 -> Pms m ws f0 f)")
(assume "m" "ws" "f" "f0" "PH")
(intro 0)
;; 3-6
(use "PmsCircInv" (pt "m") (pt "ws"))
(use "PH")
;; 4
(use "PmsCirc" (pt "m") (pt "ws"))
(use "PH")
;; 5
(use "PmsIdUp" (pt "f") (pt "f0"))
(use "PH")
;; 6
(use "PmsIdOutInv" (pt "m") (pt "f"))
(use "PH")
;; Proof finished.
;; (cp)
(save "PmsSym")

;; This concludes the properties of Pms we need.

;; Following the first approach in D. Bondarekos's Bachelor thesis we
;; prove RealSumPerm by induction on the length of the permutation.
;; Given permutations f,f0 we need to find shorter permutations g,g0
;; such that the IH applies.

;; gPerm
(set-goal "all l,ws,f,f0,ws0,g,g0(
     Pms(Succ l)ws f f0 -> 
     ws(Succ l) -> 
     (f(Succ l)=Succ l -> F) -> 
     (f0(Succ l)=Succ l -> F) -> 
     ws0 eqd([n][if (n=Succ l) False (ws n)]) -> 
     g eqd([n][if (n=Succ l) n [if (n=f0(Succ l)) (f(f n)) (f n)]]) -> 
     g0 eqd([n][if (n=Succ l) n [if (n=f(Succ l)) (f0(f0 n)) (f0 n)]]) -> 
     Pms l ws0 g g0)")
(assume "l" "ws" "f" "f0" "ws1" "g" "g0" "PmsSl" "Slinws"
	"fSlnot=Sl" "f0Slnot=Sl" "ws1Def" "gDef" "g0Def")
(intro 0)
;; 3-6
;; ?^3:all u g0(g u)=u
(assume "n")
(simp "gDef")
(ng #t)
(cases (pt "n=Succ l"))
(assume "n=Sl")
(ng #t)
(simp "g0Def")
(ng #t)
(simp "n=Sl")
(ng #t)
(use "Truth")
(assume "nnot=Sl")
(ng #t)
(cases (pt "n=f0(Succ l)"))
(assume "n=f0Sl")
(ng #t)
(simp "n=f0Sl")
(assert "f(f0(Succ l))=Succ l")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A1")
(simp "A1")
(simp "g0Def")
(ng #t)
(cut "f(Succ l)=Succ l -> F")
(assume "A2")
(simp "A2")
(ng #t)
(assert "f0(f(Succ l))=Succ l")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A3")
(simp "A3")
(use "Truth")
(use "fSlnot=Sl")
(assume "nnot=f0Sl")
(ng #t)
(simp "g0Def")
(ng #t)
(assert "f n=Succ l -> F")
(assume "fn=Sl")
(use "nnot=f0Sl")
(simp "<-" "fn=Sl")
(use "NatEqSym")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
;; 45
(assume "A4")
(simp "A4")
(ng #t)
(assert "f n=f(Succ l) -> F")
(assume "fn=fSl")
(use "nnot=Sl")
(assert "f0(f n)=f0(f(Succ l))")
(simp "fn=fSl")
(use "Truth")
;; Assertion proved.
(assume "A5")
(use "NatEqTrans" (pt "f0(f n)"))
(use "NatEqSym")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(use "NatEqTrans" (pt "f0(f(Succ l))"))
(use "A5")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A6")
(simp "A6")
(ng #t)
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; ?^4:all n g(g0 n)=n5
(assume "n")
(simp "g0Def")
(ng #t)
(cases (pt "n=Succ l"))
;; 78,79
(assume "n=Sl")
(ng #t)
(simp "gDef")
(ng #t)
(simp "n=Sl")
(ng #t)
(use "Truth")
(assume "nnot=Sl")
(ng #t)
(cases (pt "n=f(Succ l)"))
;; 88,89
(assume "n=fSl")
(ng #t)
(simp "n=fSl")
(assert "f0(f(Succ l))=Succ l")
(use "PmsCirc" (pt "Succ l")(pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A1")
(simp "A1")
(simp "gDef")
(ng #t)
(cut "f0(Succ l)=Succ l -> F")
;; 100,101
(assume "A2")
(simp "A2")
(ng #t)
(assert "f(f0(Succ l))=Succ l")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A3")
(simp "A3")
(use "Truth")
;; 101
(use "f0Slnot=Sl")
;; 89
(assume "nnot=fSl")
(ng #t)
(simp "gDef")
(ng #t)
(assert "f0 n=Succ l -> F")
(assume "f0n=Sl")
(use "nnot=fSl")
(simp "<-" "f0n=Sl")
(use "NatEqSym")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; Assertion proved.
(assume "A4")
(simp "A4")
(ng #t)
(assert "f0 n=f0(Succ l) -> F")
;; 124,125
(assume "f0n=f0Sl")
(use "nnot=Sl")
(assert "f(f0 n)=f(f0(Succ l))")
(simp "f0n=f0Sl")
(use "Truth")
;; Assertion proved.
(assume "ff0n=ff0Sl")
(use "NatEqTrans" (pt "f(f0 n)"))
(use "NatEqSym")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(use "NatEqTrans" (pt "f(f0(Succ l))"))
(use "ff0n=ff0Sl")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; 124
;; Assertion proved.
(assume "A5")
(simp "A5")
(ng #t)
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; ?^5:all n(l<n -> ws1 n -> F)
(assume "n" "l<n")
(cases (pt "n=Succ l"))
;; 144,145
(assume "n=Sl")
(simp "n=Sl")
(simp "ws1Def")
(ng #t)
(assume "Absurd")
(use "Absurd")
(inst-with-to "PmsIdUp" (pt "Succ l") (pt "ws") (pt "f") (pt "f0")
	      "PmsSl" (pt "n") "Inst")
(assume "nnot=Sl")
(simp "ws1Def")
(ng #t)
(simp "nnot=Sl")
(ng #t)
(use "Inst")
(use "NatNotLeToLt")
(assume "n<=Sl")
(use "nnot=Sl")
(use "NatLeAntiSym")
(use "n<=Sl")
(use "NatLtToSuccLe")
(use "l<n")
;; ?^6:all n((ws1 n -> F) -> g n=n)
(assume "n" "nnotinws1")
(simp "gDef")
(ng #t)
(cases (pt "n=Succ l"))
;; 168,169
(assume "n=Sl")
(ng #t)
(use "Truth")
;; 169
(assume "nnot=Sl")
(ng #t)
(assert "ws n -> F")
(assume "ninws")
(use "nnotinws1")
(simp "ws1Def")
(ng #t)
(simp "nnot=Sl")
(ng #t)
(use "ninws")
;; Assertion proved.
(assume "nnotinws")
(assert "f n=n")
(use "PmsIdOut" (pt "Succ l") (pt "ws") (pt "f0"))
(use "PmsSl")
(use "nnotinws")
;; Assertion proved.
(assume "fn=n")
(simp "fn=n")
(simp "fn=n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "gPerm")

;; For g defined as in RealSumPerm we show that f is obtained from g
;; by swapping f(Succ l) with Succ l.

(add-program-constant "Swap" (py "nat=>nat=>nat=>nat"))
(add-computation-rules "Swap n m n0" "[if (n0=n) m [if (n0=m) n n0]]")

(set-totality-goal "Swap")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "n0")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; fSwapg
(set-goal "all l,ws,f,f0,g(
     Pms(Succ l)ws f f0 -> 
     (f0(Succ l)=Succ l -> F) -> 
     (Succ l=f(Succ l) -> F) -> 
     g eqd([n][if (n=Succ l) n [if (n=f0(Succ l)) (f(f n)) (f n)]]) -> 
     all n f n=Swap(f(Succ l))(Succ l)(g n))")
(assume "l" "ws" "f" "f0" "g" "PmsSl" "f0Slnot=Sl" "Slnot=fSl" "gDef" "n")
(cases (pt "n=Succ l"))
(assume "n=Sl")
(simp "n=Sl")
(simp "gDef")
(ng #t)
(simp "Slnot=fSl")
(ng #t)
(use "Truth")
(assume "nnot=Sl")
(cases (pt "n=f0(Succ l)"))
;; 12,13
(assume "n=f0Sl")
(simp "n=f0Sl")
(simp "gDef")
(ng #t)
(simp "f0Slnot=Sl")
(ng #t)
(assert "f(f0(Succ l))=Succ l")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(assume "ff0Sl=Sl")
(simp "ff0Sl=Sl")
(assert "f(Succ l)=Succ l -> F")
(assume "fSl=Sl")
(use "Slnot=fSl")
(use "NatEqSym")
(use "fSl=Sl")
(assume "fSlnot=Sl")
(simp "fSlnot=Sl")
(ng #t)
(use "Truth")
;; 13
(assume "nnot=f0Sl")
(simp "gDef")
(ng #t)
(simp "nnot=Sl")
(ng #t)
(simp "nnot=f0Sl")
(ng #t)
(assert "f n=Succ l -> F")
(assume "fn=Sl")
(use "nnot=f0Sl")
(assert "f0(f(n))=f0(Succ l)")
(simp "fn=Sl")
(use "Truth")
(assume "A1")
(use "NatEqTrans" (pt "f0(f n)"))
(use "NatEqSym")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(use "A1")
(assume "fnnot=Sl")
(simp "fnnot=Sl")
(ng #t)
(assert "f n=f(Succ l) -> F")
(assume "fn=fSl")
(use "nnot=Sl")
(assert "f0(f n)=f0(f(Succ l))")
(simp "fn=fSl")
(use "Truth")
(assume "A2")
(use "NatEqTrans" (pt "f0(f n)"))
(use "NatEqSym")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(simp "fn=fSl")
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(assume "A3")
(simp "A3")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "fSwapg")

;; We now aim at RealSumSwap.  This needs RealSumSplitCor1-5

;; RealSumSplitCor1
(set-goal "all xs,l,n(all n0(Real(xs n0)) -> n<Succ l ->
                    RealSum Zero(Succ l)xs===
                    RealSum Zero n xs+RealSum n(Succ l--n)xs)")
(assume "xs" "l" "n" "Rxs" "n<Sl")
(use "RealEqSym")
(inst-with-to
 "RealSumZeroSplit" (pt "xs") "Rxs" (pt "n") (pt "Succ l--n") "Inst")
(simphyp-with-to "Inst" (pf "n+(Succ l--n)=Succ l") "InstS")
(use "InstS")
;; ?^7:n+(Succ l--n)=Succ l
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "n<Sl")
;; Proof finished.
;; (cp)
(save "RealSumSplitCor1")

;; RealSumSplitCor2 (as 2024-06-02)
(set-goal "all xs,l,n,m(
     all n0 Real(xs n0) -> 
     n<m -> 
     m<Succ l -> 
     RealSum Zero n xs+RealSum n(Succ l--n)xs===
     RealSum Zero n xs+(RealSum n(Succ(m--n))xs+RealSum(Succ m)(l--m)xs))")
(assume "xs" "l" "n" "m" "Rxs" "n<m" "m<Sl")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(inst-with-to
 "RealSumSplit" (pt "xs") "Rxs" (pt "n") (pt "Succ(m--n)") (pt "l--m") "Inst")
(use "RealEqTrans" (pt "RealSum n(Succ(m--n))xs+RealSum(n+Succ(m--n))(l--m)xs"))
(assert "n+Succ(m--n)=Succ m")
(ng #t)
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "n<m")
;; Assertion proved.
(assume "A1")
(simp "A1")
(use "RealEqRefl")
(autoreal)
;; 10
(use "RealEqTrans" (pt "RealSum n(Succ(m--n)+(l--m))xs"))
(use "Inst")
(assert "Succ(m--n)+(l--m)=Succ l--n")
(ng #t)
(cut "m--n+(l--m)=l--n")
;; Assertion proved.
(assume "A2")
(use "NatEqTrans" (pt "Succ(l--n)"))
(ng #t)
(use "A2")
(use "SuccNatMinus")
(use "NatLtSuccToLe")
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "m<Sl")
(use "NatPlusMinusMinus")
(use "NatLtToLe")
(use "n<m")
(use "NatLtSuccToLe")
(use "m<Sl")
;; Assertion proved.
(assume "A3")
(simp "A3")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumSplitCor2")

;; RealSumSplitCor3
(set-goal "all xs,l,n,m(
     all n0 Real(xs n0) -> 
     n<m -> 
     m<Succ l -> 
     RealSum Zero(Succ l)([n0]xs(Swap n m n0))===
     RealSum Zero n([n0]xs(Swap n m n0))+
     RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
     RealSum(Succ m)(l--m)([n0]xs(Swap n m n0)))")
(assume "xs" "l" "n" "m" "Rxs" "n<m" "m<Sl")
(use "RealEqTrans" (pt "RealSum Zero n([n0]xs(Swap n m n0))+
                        RealSum n((Succ l)--n)([n0]xs(Swap n m n0))"))
(use "RealSumSplitCor1")
(assume "n0")
(autoreal)
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "m<Sl")
(use "RealEqTrans" (pt "RealSum Zero n([n0]xs(Swap n m n0))+
                        (RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
                        RealSum(Succ m)(l--m)([n0]xs(Swap n m n0)))"))
(use "RealSumSplitCor2")
(assume "n0")
(autoreal)
(use "n<m")
(use "m<Sl")
(use "RealPlusAssoc")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealSumSplitCor3")

;; RealSumSplitCor4
(set-goal "all xs,l,n,m(
     all n0 Real(xs n0) -> 
     n<m -> 
     m<Succ l -> 
     RealSum Zero n([n0]xs(Swap n m n0))+
     RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
     RealSum(Succ m)(l--m)([n0]xs(Swap n m n0))===
     RealSum Zero n xs+RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
     RealSum(Succ m)(l--m)xs)")
(assume "xs" "l" "n" "m" "Rxs" "n<m" "m<Sl")
(use "RealPlusCompat")
(use "RealPlusCompat")
;; First summand:
(use "RealSumCompat")
(assume "l0" "Useless" "l0<n")
(ng #t)
(assert "l0=n -> F")
(assume "l0=n")
(assert "l0<l0")
(simphyp-with-to "l0<n" "l0=n" "Absurd")
(use "Absurd")
;; 13
(assume "Absurd")
(use "Absurd")
(assume "l0not=n")
(simp "l0not=n")
(ng #t)
(assert "l0=m -> F")
(assume "l0=m")
(assert "l0<m")
(use "NatLtTrans" (pt "n"))
(use "l0<n")
(use "n<m")
(simp "l0=m")
(assume "Absurd")
(use "Absurd")
;; 21
(assume "l0notm")
(simp "l0notm")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Second summand:
;; ?^6:RealSum n(Succ(m--n))([n0]xs(Swap n m n0))===
;;     RealSum n(Succ(m--n))([n0]xs(Swap n m n0))
(use "RealEqRefl")
(autoreal)
;; Third summand:
;; ?^4:RealSum(Succ m)(l--m)([n0]xs(Swap n m n0))===RealSum(Succ m)(l--m)xs
(use "RealSumCompat")
(assume "l0" "Sm<=l0" "l0LtH")
(ng #t)
(assert "l0=n -> F")
(assume "l0=n")
(assert "n<l0")
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "NatSuccLeToLt")
(use "Sm<=l0")
(simp "l0=n")
(assume "Absurd")
(use "Absurd")
(assume "l0notn")
(simp "l0notn")
(ng #t)
(assert "l0=m -> F")
(assume "l0=m")
(simphyp-with-to "Sm<=l0" "l0=m" "Absurd")
(use "Absurd")
(assume "l0notm")
(simp "l0notm")
(ng #t)
(use "RealEqRefl")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumSplitCor4")

;; RealSumSplitCor5
(set-goal "all xs,n,m(
     all n0 Real(xs n0) -> 
     n<m -> 
     RealSum n(Succ(m--n))xs===RealSum n(Succ(m--n))([n0]xs(Swap n m n0)))")
(assume "xs" "n" "m" "Rxs" "n<m")
(use "RealEqTrans" (pt "xs n+RealSum(Succ n)(m--n)xs"))
(use "RealEqTrans" (pt "RealSum n(Succ Zero)xs+RealSum(Succ n)(m--n)xs"))
(use "RealEqSym")
(inst-with-to "RealSumSplit" (pt "xs") "Rxs" (pt "n")
	      (pt "Succ Zero") (pt "m--n") "Inst")
(use "RealEqTrans" (pt "RealSum n(Succ Zero)xs+RealSum(n+Succ Zero)(m--n)xs"))
(assert "n+Succ Zero=Succ n")
(ng #t)
(use "Truth")
(assume "Hyp")
(simp "Hyp")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "RealSum n(Succ Zero+(m--n))xs"))
(use "Inst")
(assert "Succ Zero+(m--n)=Succ(m--n)")
(ng #t)
(use "Truth")
(assume "Hyp")
(simp "Hyp")
(use "RealEqRefl")
(autoreal)
(use "RealPlusCompat")
(use "RealSumOne")
(use "Rxs")
(use "RealEqRefl")
(autoreal)
;; ?^4:xs n+RealSum(Succ n)(m--n)xs===RealSum n(Succ(m--n))([n0]xs(Swap n m n0))
(use "RealEqTrans" (pt "RealSum(Succ n)(m--n)xs+xs n"))
(use "RealPlusComm")
(autoreal)
(use "RealEqTrans" (pt "RealSum n(m--n)([n0]xs(Swap n m n0))+xs(Swap n m m)"))
(assert "Swap n m m=n")
(ng #t)
(assert "m=n -> F")
(assume "m=n")
(simphyp-with-to "n<m" "m=n" "Absurd")
(use "Absurd")
(assume "mnotn")
(simp "mnotn")
(use "Truth")
(assume "SwapEq")
(simp "SwapEq")
(use "RealPlusCompat")
;; 48,49
(get 49)
(use "RealEqRefl")
(use "Rxs")
;; ?^48:RealSum(Succ n)(m--n)xs===RealSum n(m--n)([n0]xs(Swap n m n0))
(use "RealEqTrans" (pt "RealSum(Succ n)(Pred(m--n))xs+xs m"))
(use "RealEqTrans" (pt "RealSum(Succ n)(Pred(m--n))xs+RealSum m(Succ Zero)xs"))
(use "RealEqSym")
(inst-with-to "RealSumSplit" (pt "xs") "Rxs" (pt "Succ n")
              (pt "Pred(m--n)") (pt "Succ Zero") "Inst")
(use "RealEqTrans" (pt "RealSum(Succ n)(Pred(m--n))xs+
                        RealSum(Succ n+Pred(m--n))(Succ Zero)xs"))
(assert "Succ n+Pred(m--n)=m")
(use "NatEqTrans" (pt "n+Succ(Pred(m--n))"))
(ng #t)
(use "Truth")
(assert "Succ(Pred(m--n))=m--n")
(use "NatSuccPred")
;; ?^67:Zero<m--n
(simp "<-" "NatLtMinusZero")
(use "n<m")
;; Assertion proved.
(assume "A1")
(simp "A1")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "n<m")
;; Assertion proved.
(assume "A2")
(simp "A2")
(use "RealEqRefl")
(autoreal)
;; ?^59:RealSum(Succ n)(Pred(m--n))xs+RealSum(Succ n+Pred(m--n))(Succ Zero)xs===
;;      RealSum(Succ n)(m--n)xs
(use "RealEqTrans" (pt "RealSum(Succ n)(Pred(m--n)+Succ Zero)xs"))
(use "Inst")
;; ?^78:RealSum(Succ n)(Pred(m--n)+Succ Zero)xs===RealSum(Succ n)(m--n)xs
(assert "Pred(m--n)+Succ Zero=m--n")
(ng #t)
(use "NatSuccPred")
(simp "<-" "NatLtMinusZero")
(use "n<m")
;; Assertion proved.
(assume "A3")
(simp "A3")
(use "RealEqRefl")
(autoreal)
;; ?^54:RealSum(Succ n)(Pred(m--n))xs+RealSum m(Succ Zero)xs===
;;      RealSum(Succ n)(Pred(m--n))xs+xs m
(use "RealPlusCompat") 
(use "RealEqRefl")
(autoreal)
(use "RealSumOne")
(use "Rxs")
;; ?^52:
;; RealSum(Succ n)(Pred(m--n))xs+xs m===RealSum n(m--n)([n0]xs(Swap n m n0))
(use "RealEqTrans" (pt "xs m+RealSum(Succ n)(Pred(m--n))xs"))
;; 91,92
(use "RealPlusComm")
(autoreal)
;; ?^92:
;; xs m+RealSum(Succ n)(Pred(m--n))xs===RealSum n(m--n)([n0]xs(Swap n m n0))
(use "RealEqTrans"
     (pt "xs(Swap n m n)+RealSum (Succ n)(Pred(m--n))([n0]xs(Swap n m n0))"))
;; 95,96
(assert "Swap n m n=m")
(ng #t)
(use "Truth")
;; Assertion proved.
(assume "A4")
(simp "A4")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "Rxs")
(use "RealSumCompat")
(assume "l0" "Sn<=l0" "LtH")
(ng #t)
(assert "l0=n -> F")
(assume "l0=n")
(simphyp-with-to "Sn<=l0" "l0=n" "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "l0notn")
(simp "l0notn")
(ng #t)
;; ?^115:xs l0===xs[if (l0=m) n l0]
(assert "l0=m -> F")
(assume "l0=m")
(simphyp-with-to "LtH" "l0=m" "mLtH")
(simphyp-with-to "mLtH" (pf "Succ n+Pred(m--n)=m") "mLtHS")
(use "mLtHS")
;; ?^122:Succ n+Pred(m--n)=m
(ng #t)
(simp "<-" "NatPlus1CompRule")
(simp "NatSuccPred")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "n<m")
(simp "<-" "NatLtMinusZero")
(use "n<m")
;; Assertion proved.
(assume "l0notm")
(simp "l0notm")
(use "RealEqRefl")
(use "Rxs")
;; ?^96:xs(Swap n m n)+RealSum(Succ n)(Pred(m--n))([n0]xs(Swap n m n0))===
;;      RealSum n(m--n)([n0]xs(Swap n m n0))
(simpreal (pf "xs(Swap n m n)===([n0]xs(Swap n m n0))n"))
(use "RealSumSplitLPredCor")
(assume "n0")
(autoreal)
(use "n<m")
(use "RealEqRefl")
(use "Rxs")
;; ?^35:RealSum n(m--n)([n0]xs(Swap n m n0))+xs(Swap n m m)===
;;      RealSum n(Succ(m--n))([n0]xs(Swap n m n0))
(use "RealEqTrans" (pt "RealSum n(m--n)([n0]xs(Swap n m n0))+
                        RealSum m (Succ Zero)([n0]xs(Swap n m n0))"))
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(use "RealSumOne")
(autoreal)
;; ?^142:RealSum n(m--n)([n0]xs(Swap n m n0))+
;;       RealSum m(Succ Zero)([n0]xs(Swap n m n0))===
;;       RealSum n(Succ(m--n))([n0]xs(Swap n m n0))
(use "RealSumSplitR")
(assume "n0")
(autoreal)
(use "n<m")
;; Proof finished.
;; (cp)
(save "RealSumSplitCor5")

;; From RealSumSplitCor1-5 we can now prove that any two terms in a
;; sum from zero can be swapped.

;; RealSumSwap
(set-goal "all xs,l,n,m(
     all n0 Real(xs n0) -> 
     n<m -> 
     m<Succ l -> 
     RealSum Zero(Succ l)xs===RealSum Zero(Succ l)([n0]xs(Swap n m n0)))")
(assume "xs" "l" "n" "m" "Rxs" "n<m" "m<Sl")
;; First transitivity:
(use "RealEqTrans" (pt "RealSum Zero n xs+RealSum n(Succ l--n)xs"))
(use "RealSumSplitCor1")
(use "Rxs")
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "m<Sl")
;; Second transitivity:
(use "RealEqTrans"
 (pt "RealSum Zero n xs+(RealSum n(Succ(m--n))xs+RealSum(Succ m)(l--m)xs)"))
(use "RealSumSplitCor2")
(use "Rxs")
(use "n<m")
(use "m<Sl")
;; Third transitivity:
(use "RealEqTrans" (pt "RealSum Zero n([n0]xs(Swap n m n0))+
                        RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
                        RealSum(Succ m)(l--m)([n0]xs(Swap n m n0))"))
(use "RealEqTrans" (pt "RealSum Zero n xs+
                        RealSum n(Succ(m--n))([n0]xs(Swap n m n0))+
                        RealSum(Succ m)(l--m)xs"))
(def "x1" "RealSum Zero n xs")
(def "x2" "RealSum(Succ m)(l--m)xs")
(simp "<-" "x1Def")
(simp "<-" "x2Def")
(use "RealEqTrans" (pt "x1+RealSum n(Succ(m--n))xs+x2"))
(use "RealPlusAssoc")
(simp "x1Def")
(get 38)
(simp "x2Def")
(autoreal)
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqRefl")
(simp "x1Def")
(autoreal)
(use "RealSumSplitCor5")
(use "Rxs")
(use "n<m")
(simp "x2Def")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(use "RealSumSplitCor4")
(use "Rxs")
(use "n<m")
(use "m<Sl")
(use "RealEqSym")
(use "RealSumSplitCor3")
(use "Rxs")
(use "n<m")
(use "m<Sl")
;; Proof finished.
;; (cp)
(save "RealSumSwap")

;; RealSumPms (was RealSumPerm)
(set-goal "all l,xs(
     all n Real(xs n) -> 
     all ws,f,f0(
      Pms l ws f f0 -> 
      RealSum Zero(Succ l)xs===RealSum Zero(Succ l)([n]xs(f n))))")
(ind)
;; 2,3
(assume "xs" "Rxs" "ws" "f" "f0" "Pms0")
(ng #t)
(assert "f Zero=Zero")
(cases (pt "ws Zero"))
(assume "0inws")
(assert "ws(f Zero)")
(use "PmsIn" (pt "Zero") (pt "f0"))
(use "Pms0")
(use "0inws")
(assume "ws(f Zero)")
(assert "Zero<f Zero -> F")
(assume "0<f0")
(use "PmsIdUp" (pt "Zero") (pt "ws") (pt "f") (pt "f0") (pt "f Zero"))
(use "Pms0")
(use "0<f0")
(use "ws(f Zero)")
;; Assertion proved.
(assume "0not<f0")
(assert "f Zero<=Zero")
(use "NatNotLtToLe")
(use "0not<f0")
(ng #t)
(assume "A1")
(use "A1")
;; 9
(use "PmsIdOut" (pt "Zero") (pt "f0"))
(use "Pms0")
(assume "f0=0")
(simp "f0=0")
(use "RealEqRefl")
(autoreal)
;; 3
(assume "l" "IHl")
(assume "xs" "Rxs" "ws" "f" "f0" "PmsSl")
(use "RealEqTrans" (pt "RealSum Zero(Succ l)xs+xs(Succ l)"))
;; 34,35
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(use "RealEqTrans" (pt "RealSum Zero(Succ l)([n]xs(f n))+xs(f(Succ l))"))
;; 39,40
(use "RealEqRefl")
(autoreal)
;; ?^40:RealSum Zero(Succ l)([n]xs(f n))+xs(f(Succ l))===
;;      RealSum Zero(Succ l)xs+xs(Succ l)
(cases (pt "ws(Succ l)"))
;; 42,43
;; take the simple case first: Sl is not in the permutation
(get 43)
(assume "Slnotinws")
(assert "f(Succ l)=Succ l")
(use "PmsIdOut" (pt "Succ l") (pt "ws") (pt "f0"))
(use "PmsSl")
(use "Slnotinws")
(assume "A1")
(simp "A1")
(use "RealPlusCompat")
(use "RealEqSym")
(use "IHl" (pt "ws") (pt "f0"))
(use "Rxs")
(use "PmsSuccInv")
(use "PmsSl")
(use "Slnotinws") 
(use "RealEqRefl")
(autoreal)
;; ?^42:ws(Succ l) -> 
;;      RealSum Zero(Succ l)([n]xs(f n))+xs(f(Succ l))===
;;      RealSum Zero(Succ l)xs+xs(Succ l)
;; Succ l is in the permutation:
(assume "Slinws")
;; Treat another simple case, that might cause many problems:
(cases (pt "f(Succ l)=Succ l"))
;; 60,61
(assume "f(Succ l)=Succ l")
(use "RealPlusCompat")
(use "RealEqSym")
(def "ws1" "[n][if (n=Succ l) False (ws n)]")
;; (use "IHl" (pt "ws") (pt "f0"))
(use "IHl" (pt "ws1") (pt "f0"))
(use "Rxs")
;; ?^74:Pms l ws1 f f0
;; ;; ?^74:Pms l ws f f0
(intro 0)
(use "PmsCirc" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
;; (assume "n" "l<n" "ninws")
(assume "n" "l<n" "ninws1")
(use "PmsIdUp" (pt "Succ l") (pt "ws") (pt "f") (pt "f0") (pt "n"))
(use "PmsSl")
(assert "n=Succ l -> F")
(assume "n=Succ l")
;; (assert "ws n")
(assert "ws1 n")
;; (use "ninws")
(use "ninws1")
(simp "n=Succ l")
(simp "ws1Def")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "nnot=Sl")
(use "NatNotLeToLt")
(assume "n<=Succ l")
(use "nnot=Sl")
(use "NatLeAntiSym")
(use "n<=Succ l")
(use "NatLtToSuccLe")
(use "l<n")
;; 84
(assert "n=Succ l -> F")
(assume "n=Succ l")
(assert "ws1 n")
(use "ninws1")
(simp "n=Succ l")
(simp "ws1Def")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "nnot=Sl")
(assert "ws1 n")
(use "ninws1")
(simp "ws1Def")
(ng #t)
(simp "nnot=Sl")
(ng #t)
(assume "ninws")
(use "ninws")
;; 78
(assume "n" "nnotinws1")
(cases (pt "n=Succ l"))
;; 119,120
(assume "n=Sl")
(simp "n=Sl")
(use "f(Succ l)=Succ l")
(assume "nnot=Sl")
(use "PmsIdOut" (pt "Succ l") (pt "ws") (pt "f0"))
(use "PmsSl")
(assume "ninws")
(use "nnotinws1")
(simp "ws1Def")
(ng #t)
(simp "nnot=Sl")
(ng #t)
(use "ninws")
;; ?^64:xs(f(Succ l))===xs(Succ l)
(simp "f(Succ l)=Succ l")
(use "RealEqRefl")
(autoreal)
(assume "fSlnot=Sl")
(assert "f0(Succ l)=Succ l -> F")
(assume "f0Sl=Sl")
(assert "f(f0(Succ l))=f(Succ l)")
(simp "f0Sl=Sl")
(use "Truth")
;; Assertion proved.
(assume "A3")
(use "fSlnot=Sl")
(simp "<-" "A3")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(assume "f0Slnot=Sl")
;; ?^145:RealSum Zero(Succ l)([n]xs(f n))+xs(f(Succ l))===
;;       RealSum Zero(Succ l)xs+xs(Succ l)
;; 1) New permutation ws, g, g0: old one without the Swap, involving Sl
(def "ws1" "[n][if (n=Succ l) False (ws n)]")
(def "g" "[n][if (n=Succ l) n [if (n=f0(Succ l)) (f(f n)) (f n)]]")
(def "g0" "[n][if (n=Succ l) n [if (n=f(Succ l)) (f0(f0 n)) (f0 n)]]")
(assert "Pms l ws1 g g0")
(use "gPerm" (pt "ws") (pt "f") (pt "f0"))
(use "PmsSl")
(use "Slinws")
(use "fSlnot=Sl")
(use "f0Slnot=Sl")
(use "ws1Def")
(use "gDef")
(use "g0Def")
(assume "Pmsl")
(assert "all n,m((n=m -> F) -> (g n=g m -> F))")
(assume "n" "m" "nnot=m")
(assume "gn=gm")
(assert "g0(g n)=g0(g m)")
(simp "gn=gm")
(use "Truth")
(assume "g0gn=g0gm")
(use "nnot=m")
(use "NatEqTrans" (pt "g0(g n)"))
(use "NatEqSym")
(use "PmsCirc" (pt "l") (pt "ws1"))
(use "Pmsl")
(use "NatEqTrans" (pt "g0(g m)"))
(use "g0gn=g0gm")
(use "PmsCirc" (pt "l") (pt "ws1"))
(use "Pmsl")
;; Assertion proved.
(assume "gProp")
;; 2) Use IH for g, g0
(assert "RealSum Zero(Succ l)xs===RealSum Zero(Succ l)([n]xs(g n))")
(use "IHl" (pt "ws1") (pt "g0"))
(use "Rxs")
(use "Pmsl")
;; Assertion proved.
(assume "Sum=Sumg")
;; 3) Show that Sum g equals Sum f
(use "RealEqTrans" (pt "RealSum Zero(Succ l)([n]xs(g n))+xs(Succ l)"))
(get 200)
(use "RealPlusCompat")
(use "RealEqSym")
(use "Sum=Sumg")
(use "RealEqRefl")
(autoreal)
;; Here need: f = Swap(Sl, f(Sl), g(u)):
(def "n1" "f(Succ l)")
(assert "all n(f n=Swap n1(Succ l)(g n))")
(assert "all n(f n=Swap(f(Succ l))(Succ l)(g n))")
(use "fSwapg" (pt "ws") (pt "f0"))
(use "PmsSl")
(use "f0Slnot=Sl")
(assume "Sl=fSl")
(use "fSlnot=Sl")
(use "NatEqSym")
(use "Sl=fSl")
(use "gDef")
;; Assertion proved
(assume "Prop")
(simp "n1Def")
(use "Prop")
;; Assertion proved.
(assume "f=Swapg")
(use "RealEqTrans" (pt "RealSum Zero(Succ l)([n]xs(Swap (n1)(Succ l)(g n)))+
                        xs(Swap n1(Succ l)(g(Succ l)))"))
(use "RealPlusCompat")
(assert "all m(RealSum Zero m([n]xs(f n))===
               RealSum Zero m([n]xs(Swap n1(Succ l)(g n))))")
(ind)
(ng #t)
(use "RealEqRefl")
(autoreal)
(assume "m" "IH")
(use "RealEqTrans" (pt "RealSum Zero m([n]xs(f n))+xs(f(m))"))
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "RealSum Zero m([n]xs(Swap n1(Succ l)(g n)))+
                        xs(Swap n1(Succ l)(g m))"))
(use "RealPlusCompat")
(use "IH")
(simp "f=Swapg")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
(assume "IHhelp")
(inst-with-to "IHhelp" (pt "Succ l") "Obvious")
(drop "IHhelp")
(use "Obvious")
(assert "g(Succ l)=Succ l")
(simp "gDef")
(ng #t)
(use "Truth")
(assume "ObV")
(simp "ObV")
(ng #t)
(simp "n1Def")
(cases (pt "Succ l=f(Succ l)"))
;; 260,261
(assume "Sl=fSl")
(ng #t)
(simp "<-" "Sl=fSl")
(use "RealEqRefl")
(autoreal)
;; 261
(assume "Slnot=fSl")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; 227
(use "RealEqTrans"
     (pt "RealSum Zero(Succ(Succ l))([n]xs(Swap n1(Succ l)(g n)))"))
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans" (pt "RealSum Zero(Succ(Succ l))([n]xs(g n))"))
(use "RealEqSym")
;; (pp "RealSumSwap")
(inst-with-to "RealSumSwap" (pt "[n]xs(g n)")
	      (pt "Succ l") (pt "f0(Succ l)") (pt "Succ l") "Inst")
(assert "n1=g(f0(Succ l))")
(simp "gDef")
(ng #t)
(simp "f0Slnot=Sl")
(ng #t)
(assert "f(f0(Succ l))=Succ l")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(assume "ff0Sl=Sl")
(simp "ff0Sl=Sl")
(simp "n1Def")
(use "Truth")
(assume "n1Prop")
(simp "n1Prop")
(use "RealEqTrans"
(pt "RealSum Zero(Succ(Succ l))([n]([n0]xs(g n0))(Swap(f0(Succ l))(Succ l)n))"))
(use "Inst")
(assume "n")
(autoreal)
(use "NatNotLeToLt")
(assume "Sl<=f0(Sl)")
(assert "Succ l<f0(Succ l)")
(use "NatNotLeToLt")
(assume "f0Sl<=Sl")
(assert "f0(Succ l)=Succ l")
(use "NatLeAntiSym")
(use "f0Sl<=Sl")
(use "Sl<=f0(Sl)")
(use "f0Slnot=Sl")
(assume "Sl<f0Sl")
(assert "f(f0(Succ l))=Succ l")
(use "PmsCircInv" (pt "Succ l") (pt "ws"))
(use "PmsSl")
(assume "ff0Sl=Sl")
(assert "ws(f0(Succ l)) -> F")
(use "PmsIdUp" (pt "Succ l") (pt "f") (pt "f0"))
(use "PmsSl")
(use "Sl<f0Sl")
;; Assertion proved.
(assume "f0Slnotinws")
(assert "f(f0(Succ l))=f0(Succ l)")
(use "PmsIdOut" (pt "Succ l") (pt "ws") (pt "f0"))
(use "PmsSl")
(use "f0Slnotinws")
;; Assertion proved.
(assume "ff0Sl=f0Sl")
(assert "f0(Succ l)=Succ l")
(use "NatEqTrans" (pt "f(f0(Succ l))"))
(use "NatEqSym")
(use "ff0Sl=f0Sl")
(use "ff0Sl=Sl")
(use "f0Slnot=Sl")
(use "Truth")
(drop "Inst")
(use "RealPlusCompat")
;; 328,329
(get 329)
;; last summands are equal
(assert "Succ l=f0(Succ l) -> F")
(assume "Slnot=f0Sl")
(use "f0Slnot=Sl")
(use "NatEqSym")
(use "Slnot=f0Sl")
;; Assertion proved.
(assume "A1")
(simp "A1")
(ng #t)
(assert "g(Succ l)=g(f0(Succ l)) -> F")
(use "gProp")
(use "A1")
(assume "gSlnot=gf0Sl")
(simp "gSlnot=gf0Sl")
(ng #t)
(assert "g(Succ l)=Succ l")
(simp "gDef")
(use "Truth")
(assume "A2")
(simp "A2")
(ng #t)
(use "RealEqRefl")
(use "Rxs")
;; 
;; now other 2 summands
(use "RealPlusCompat")
(get 352)
;; second last summands
(cases (pt "l=f0(Succ l)"))
(assume "A1")
(ng #t)
(assert "g l=g(f0(Succ l))")
(simp "<-" "A1")
(use "Truth")
(assume "A2")
(simp "A2")
(ng #t)
(assert "g(Succ l)=Succ l")
(simp "gDef")
(use "Truth")
(assume "A3")
(simp "A3")
(use "RealEqRefl")
(use "Rxs")
(assume "lnot=f0Sl")
(ng #t)
(assert "g l=g(f0(Succ l)) -> F")
(use "gProp")
(use "lnot=f0Sl")
(assume "A4")
(simp "A4")
(ng #t)
(assert "(l=Succ l)=F")
(use "SuccTotalFPFalseR")
(assume "A5")
(simp "A5")
(ng #t)
(assert "g l=Succ l -> F")
(assert "Succ l=g(Succ l)")
(simp "gDef")
(use "Truth")
(assume "Sl=gSl")
(simp "Sl=gSl")
(use "gProp")
(simp "A5")
(assume "Absurd")
(use "Absurd")
(assume "A6")
(simp "A6")
(ng #t)
(use "RealEqRefl")
(use "Rxs")
;; 351
;; lastly, equality of small sums
(use "RealSumCompat")
(assume "n")
(assume "0<=n")
(assume "n<l")
(ng #t)
(cases (pt "n=f0(Succ l)"))
;; 400,401
(assume "A1")
(ng #t)
(assert "g n=g(f0(Succ l))")
(simp "A1")
(use "Truth")
(assume "A2")
(simp "A2")
(ng #t)
(assert "g(Succ l)=Succ l")
(simp "gDef")
(use "Truth")
(assume "A3")
(simp "A3")
(use "RealEqRefl")
(use "Rxs")
;; 401
(assume "A1")
(ng #t)
(assert "g n=g(f0(Succ l)) -> F")
(use "gProp")
(use "A1")
(assume "A2")
(ng #t)
(cases (pt "n=Succ l"))
;; 423,424
;; ?^423:n=Succ l -> 
;;       xs(g[if True (f0(Succ l)) n])===
;;       xs
;;     [if (g n=g(f0(Succ l))) (Succ l) [if (g n=Succ l) (g(f0(Succ l))) (g n)]]
(assume "A3")
(ng #t)
(assert "g n=g(f0(Succ l)) -> F")
(assume "gn=fg0Sl")
(assert "g0(g n)=g0(g(f0(Succ l)))")
(simp "gn=fg0Sl")
(auto)
(assume "Wrong")
(simp "Wrong")
(ng #t)
(assert "g n=Succ l")
(simp "A3")
(simp "gDef")
(use "Truth")
(assume "A4")
(simp "A4")
(ng #t)
(use "RealEqRefl")
(use "Rxs")
(assume "A3")
(ng #t)
(simp "A2")
(ng #t)
(assert "Succ l=g(Succ l)")
(simp "gDef")
(use "Truth")
(assume "Sl=gSl")
(assert "g n=Succ l -> F")
(simp "Sl=gSl")
(use "gProp")
(use "A3")
(assume "A4")
(simp "A4")
(ng #t)
(use "RealEqRefl")
(use "Rxs")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(simp "gDef")
(use "RealEqRefl")
(use "Rxs")
;; Proof finished.
;; (cp)
(save "RealSumPms")

;; 2024-08-25

(add-ids
 (list (list "PmsAll"
	     (make-arity (py "nat") (py "nat=>nat") (py "nat=>nat"))))
 '("all m,f,f0(
  all n f0(f n)=n  ->
  all n f(f0 n)=n  ->
  all n(m<n -> f n=n) ->
  PmsAll m f f0)" "PmsAllIntro"))

;; PmsAllCirc
(set-goal "all m,f,f0(PmsAll m f f0 -> all n f0(f n)=n)")
(assume "m" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsAllCirc")

;; PmsAllCircInv
(set-goal "all m,f,f0(PmsAll m f f0 -> all n f(f0 n)=n)")
(assume "m" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsAllCircInv")

;; PmsAllIdOut
(set-goal "all m,f,f0(PmsAll m f f0 -> all n(m<n -> f n=n))")
(assume "m" "f" "f0" "PH")
(elim "PH")
(search)
;; Proof finished.
;; (cp)
(save "PmsAllIdOut")

;; PmsAllToPms
(set-goal "all m,f,f0(PmsAll m f f0 -> Pms m([n]n<=m)f f0)")
(assume "m" "f" "f0" "PH")
(intro 0)
;; 3-6
(use "PmsAllCirc" (pt "m"))
(use "PH")
;; 4
(use "PmsAllCircInv" (pt "m"))
(use "PH")
;; 5
(bpe-ng #t)
(assume "n" "LtH" "LeH")
(assert "n<n")
(use "NatLeLtTrans" (pt "m"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; 6
(bpe-ng #t)
(assume "n" "NegH")
(use "PmsAllIdOut" (pt "m") (pt "f0"))
(use "PH")
(use "NatNotLeToLt")
(use "NegH")
;; Proof finished.
;; (cp)
(save "PmsAllToPms")

;; PmsToPmsAll
(set-goal "all m,f,f0(Pms m([n]n<=m)f f0 -> PmsAll m f f0)")
(assume "m" "f" "f0" "PH")
(intro 0)
;; 3-5
(use "PmsCirc" (pt "m") (pt "[n]n<=m"))
(use "PH")
;; 4
(use "PmsCircInv" (pt "m") (pt "[n]n<=m"))
(use "PH")
;; 5
(assume "n" "LtH")
(use "PmsIdOut" (pt "m") (pt "[n]n<=m") (pt "f0"))
(use "PH")
(bpe-ng #t)
(assume "LeH")
(assert "n<n")
(use "NatLeLtTrans" (pt "m"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PmsToPmsAll")

;; RealSumPmsAll
(set-goal
 "all l,xs(
     all n Real(xs n) -> 
     all f,f0(
      PmsAll l f f0 -> 
      RealSum Zero(Succ l)xs===RealSum Zero(Succ l)([n]xs(f n))))")
(assume "l" "xs" "Rxs" "f" "f0" "PH")
(use "RealSumPms" (pt "[n]n<=l") (pt "f0"))
;; 3,4
(use "Rxs")
(use "PmsAllToPms")
(use "PH")
;; Proof finished.
;; (cp)
(save "RealSumPmsAll")

;; RealSumPmsAllCor
(set-goal
 "all l,xs(
     all n Real(xs n) -> 
     all f,f0,g,g0(
      PmsAll l f f0 -> PmsAll l g g0 -> 
      RealSum Zero(Succ l)([n]xs(f n))===RealSum Zero(Succ l)([n]xs(g n))))")
(assume "l" "xs" "Rxs" "f" "f0" "g" "g0" "PHf" "PHg")
(use "RealEqTrans" (pt "RealSum Zero(Succ l)xs"))
;; 3,4
(use "RealEqSym")
(use "RealSumPmsAll" (pt "f0"))
(use "Rxs")
(use "PHf")
;; 4
(use "RealSumPmsAll" (pt "g0"))
(use "Rxs")
(use "PHg")
;; Proof finished.
;; (cp)
(save "RealSumPmsAllCor")

;; End 2024-08-25

;; 4.  Binomial coefficients and theorem
;; =====================================

;; Instance of RealSumSplit for l:=0 and n:=1 and n0:=Succ n

;; RealBinomSplitAux
(set-goal "all xs(all n Real(xs n) ->
 all n(xs Zero+RealSum(Succ Zero)(Succ n)xs===RealSum Zero(Succ(Succ n))xs))")
(assume "xs" "Rxs" "n")
(inst-with-to "RealSumSplit" (pt "xs") "Rxs" (pt "Zero") (pt "Succ Zero")
	      (pt "Succ n") "Inst")
(ng)
(simpreal "<-" "Inst")
(simpreal "RealZeroPlus")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealBinomSplitAux")

;; Instance of RealSumShift for xs:=[m]xs(Pred m), l:=0, n:=1, n0:=n
;; RealBinomShiftAux
(set-goal "all xs(all n Real(xs n) ->
 all n RealSum Zero n xs===RealSum(Succ Zero)n([m]xs(Pred m)))")
(assume "xs" "Rxs" "n")
;; (pp "RealSumShiftUpMinus")
(inst-with-to
 "RealSumShiftUpMinus"
 (pt "xs") (pt "Succ Zero") (pt "Zero") "Rxs" (pt "n") "Inst")
(ng "Inst")
(use "Inst")
;; Proof finished.
;; (cp)
(save "RealBinomShiftAux")

;; RealBinom
(set-goal "all x,y(
     Real x -> 
     Real y -> 
     all n (x+y)**n===RealSum Zero(Succ n)([m]x**(n--m)*y**m*Choose n m))")
(assume "x" "y" "Rx" "Ry")
(ind)
;; 3,4
(ng #t)
(use "RatEqvToRealEq")
(use "Truth")
;; 4
(assume "n" "IH")
;; In (x+y)**Succ n i.e., (x+y)**n*x + (x+y)**n*y we treat the two summands
;; separately, using the IH in each case.
(use "RealEqTrans" (pt "(x+y)**n*x+(x+y)**n*y"))
;; 8,9
(ng #t)
(use "RealTimesPlusDistr")
(autoreal)
;; 9
(simpreal "IH")
(use "RealEqTrans"
     (pt "RealSum Zero(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)+
          RealSum Zero(Succ n)([m]x**(n--m)*y**Succ m*Choose n m)"))
;; 15,16
(use "RealPlusCompat")
;; 17,18
;; ?^17:RealSum Zero(Succ n)([m]x**(n--m)*y**m*Choose n m)*x===
;;      RealSum Zero(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)
(simpreal "RealTimesSumDistrLeft")
(bpe-ng #t)
(use "RealSumCompat")
(ng #t)
(assume "m" "Useless" "m<n+1")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealTimesCompat")
(simpreal "RealTimesComm")
(use "RealEqTrans" (pt "x**Succ(n--m)"))
(ng #t)
(use "RealEqRefl")
(autoreal)
(simp "SuccNatMinus")
(use "RealEqRefl")
(autoreal)
(use "NatLtSuccToLe")
(use "m<n+1")
(autoreal)
(use "RealEqRefl")
(autoreal)
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(assume "n0")
(autoreal)
;; ?^18:RealSum Zero(Succ n)([m]x**(n--m)*y**m*Choose n m)*y===
;;      RealSum Zero(Succ n)([m]x**(n--m)*y**Succ m*Choose n m)
(simpreal "RealTimesSumDistrLeft")
(bpe-ng #t)
(use "RealSumCompat")
(ng #t)
(assume "m" "Useless" "m<n+1")
(simpreal "<-" "RealTimesAssoc")
(simpreal (pf "Choose n m*y===y*Choose n m"))
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(use "RealEqRefl")
(autoreal)
(use "RealTimesComm")
(autoreal)
(assume "n0")
(autoreal)
;; ?^16:RealSum Zero(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)+
;;      RealSum Zero(Succ n)([m]x**(n--m)*y**Succ m*Choose n m)===
;;      RealSum Zero(Succ(Succ n))([m]x**(Succ n--m)*y**m*Choose(Succ n)m)
(use "RealEqTrans"
 (pt "x**Succ n+
      RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)+
      RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n(Pred m))"))
;; 80,81
(use "RealPlusCompat")
;; 82,83
(use "RealEqTrans"
 (pt "RealSum Zero(Succ(Succ n))([m]x**(Succ n--m)*y**m*Choose n m)"))
;; 84,85
(use "RealEqTrans"
 (pt "RealSum Zero(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)+
   x**(Succ n--(Succ n))*y**(Succ n)*Choose n(Succ n)"))
;; 86,87
(ng #t)
(simpreal "RealTimesZero")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; 87
(ng #t)
(use "RealEqRefl")
(autoreal)
;; ?^85:RealSum Zero(Succ(Succ n))([m]x**(Succ n--m)*y**m*Choose n m)===
;;      x**Succ n+RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)
(simpreal (pf "x**Succ n===([m]x**(Succ n--m)*y**m*Choose n m)Zero"))
(use "RealEqSym")
(use "RealBinomSplitAux")
(assume "n0")
(autoreal)
(ng #t)
(simpreal "RealTimesOne")
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
;; ?^83:RealSum Zero(Succ n)([m]x**(n--m)*y**Succ m*Choose n m)===
;;      RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n(Pred m))
(use "RealEqTrans"
     (pt "RealSum(Succ Zero)(Succ n)
         ([m]x**(n--Pred m)*y**Succ(Pred m)*Choose n(Pred m))"))
;; 107,108
(use "RealBinomShiftAux")
(assume "m")
(autoreal)
;; ?^108:RealSum(Succ Zero)(Succ n)
;;       ([m]x**(n--Pred m)*y**Succ(Pred m)*Choose n(Pred m))===
;;       RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n(Pred m))
(use "RealSumCompat")
(ng #t)
(assume "m" "1<=m" "m<n+2")
(simp (pf "m=Succ(Pred m)"))
(ng #t)
(use "RealEqRefl")
(autoreal)
(simp "NatSuccPred")
(use "Truth")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "1<=m")
;; ?^81:x**Succ n+RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n m)+
;;      RealSum(Succ Zero)(Succ n)([m]x**(Succ n--m)*y**m*Choose n(Pred m))===
;;      RealSum Zero(Succ(Succ n))([m]x**(Succ n--m)*y**m*Choose(Succ n)m)
(simpreal "<-" "RealPlusAssoc")
(simpreal "RealSumPlus")
(bpe-ng #t)
(simpreal (pf "RealSum(Succ Zero)(Succ n)
      ([l]
        x**(Succ n--l)*y**l*Choose n l+x**(Succ n--l)*y**l*Choose n(Pred l))===
      RealSum(Succ Zero)(Succ n)
      ([l]
        x**(Succ n--l)*y**l*(Choose n l+Choose n(Pred l)))"))
;; 130,131
(simpreal (pf "RealSum(Succ Zero)(Succ n)
      ([l]x**(Succ n--l)*y**l*(Choose n l+Choose n(Pred l)))===
 RealSum(Succ Zero)(Succ n)([l]x**(Succ n--l)*y**l*(Choose(Succ n)l))"))
;; 132,133
;; ?^132:x**Succ n+
;;       RealSum(Succ Zero)(Succ n)([l]x**(Succ n--l)*y**l*Choose(Succ n)l)===
;;       RealSum Zero(Succ(Succ n))([m]x**(Succ n--m)*y**m*Choose(Succ n)m)
(simpreal "<-" "RealBinomSplitAux")
;; 134,135
(use "RealPlusCompat")
(ng #t)
(simpreal "RealTimesOne")
(simpreal "RealTimesOne")
(use "RealEqRefl")
(autoreal)
;; 137
(use "RealEqRefl")
(autoreal)
;; 135
(assume "m")
(autoreal)
;; 133
(use "RealSumCompat")
(ng #t)
(assume "m" "1<=m" "m<n+2")
(use "RealTimesCompat")
;; 149,150
(use "RealEqRefl")
(autoreal)
;; 150
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(ng #t)
(assume "n0" "Useless")
(simp "NatPlusComm")
(simp "<-" "NatPosToChooseSuccPred")
(use "Truth")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "1<=m")
;; 131
(use "RealSumCompat")
(ng #t)
(assume "m" "1<=m" "m<n+2")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealTimesCompat")
(use "RealEqRefl")
(autoreal)
;; 170
(use "RealSeqEqToEq" (pt "Zero"))
(autoreal)
(ng #t)
(assume "n0" "Useless")
(use "NatToIntPlus")
;; 168
(autoreal)
;; 128
(assume "n0")
(autoreal)
;; 127
(assume "n0")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealBinom")

;; This is the end of the old rseq.scm.

;; RealBinomCor
(set-goal "all x,y(
     Real x -> 
     Real y -> 
     all n (x+y)**n===RealSum Zero(Succ n)([m]x**m*y**(n--m)*Choose n m))")
(assume "x" "y" "Rx" "Ry" "n")
(simpreal "RealPlusComm")
(simpreal
 (pf "RealSum Zero(Succ n)([m]x**m*y**(n--m)*Choose n m)===
      RealSum Zero(Succ n)([m]y**(n--m)*x**m*Choose n m)"))
(use "RealBinom")
(autoreal)
(use "RealSumCompat")
(ng #t)
(assume "l" "Useless1" "Useless2")
(simpreal (pf "x**l*y**(n--l)===y**(n--l)*x**l"))
(use "RealEqRefl")
(realproof)
(use "RealTimesComm")
(autoreal)
;; Proof finished.
;; (cp)
(save "RealBinomCor")


