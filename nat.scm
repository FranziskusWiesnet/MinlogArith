;; 2025-04-01.  nat.scm

;; NatProdSplit NatProdShift NatNotEqSucc added.  Franziskus Wiesnet's
;; nat_add.scm included: Theorems NatThirdBinom NatLtPosToLtTimes
;; NatLtTimesPos NatLeTimesPos NatLtMonTimesLeft NatLtMonTimesRight
;; NatTimesEqualOneToOne NatPosTimes NatLeNotEqToLt NatLtSuccNotEqToLt
;; NatTimesProd NatProdShiftZeroDown NatProdOne NatEvenMinus
;; NatOddTimesToOdd0 NatOddTimesToOdd1 NatHalfLtMonEven NatHalfTimes
;; NatHalfMinus NatMinusPred NatMinusMinus NatEvenOrOdd EvenNotEqOdd
;; NatLeToNotLt NatLtMonTimes NatLeMonSquare NatLeMonSquareInv
;; NatLeSquarePred NatSuccPlusLtTimes NatLeMonHalf NatDoubleToTwoTimes
;; NatLtZeroNatF NatLtSqrtToSquareLt NatSqrtLeToLeSquare
;; NatSquareSqrtId NatSqrtBound NatSqrtBoundPred NatSqr NatSqrExFree
;; added.

;; New variable names are w:boole, ws:nat=>boole

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
 
(display "loading nat.scm ...") (newline)

(add-algs "nat" '("Zero" "nat") '("Succ" "nat=>nat"))
(add-var-name "n" "m" "l" (py "nat")) ;l instead of k, which will be an int

(define (make-numeric-term-wrt-nat n)
  (if (= n 0)
      (pt "Zero")
      (make-term-in-app-form
       (pt "Succ")
       (make-numeric-term-wrt-nat (- n 1)))))

;; The following is in term.scm, because it is used for term-to-expr
;; (define (is-numeric-term-wrt-nat? term)
;;   (or
;;    (and (term-in-const-form? term)
;; 	(string=? "Zero" (const-to-name (term-in-const-form-to-const term))))
;;    (and (term-in-app-form? term)
;; 	(let ((op (term-in-app-form-to-op term)))
;; 	  (and (term-in-const-form? op)
;; 	       (string=? "Succ" (const-to-name
;; 				 (term-in-const-form-to-const op)))
;; 	       (is-numeric-term-wrt-nat? (term-in-app-form-to-arg term)))))))

;; (define (numeric-term-wrt-nat-to-number term)
;;   (if (equal? term (pt "Zero"))
;;       0
;;       (+ 1 (numeric-term-wrt-nat-to-number (term-in-app-form-to-arg term)))))

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take either pos or nat as default.

(define NAT-NUMBERS #t)

(define (make-numeric-term x)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat x)
      (make-numeric-term-wrt-pos x)))

(define (is-numeric-term? x)
  (if NAT-NUMBERS
      (is-numeric-term-wrt-nat? x)
      (is-numeric-term-wrt-pos? x)))

(define (numeric-term-to-number x)
  (if NAT-NUMBERS
      (numeric-term-wrt-nat-to-number x)
      (numeric-term-wrt-pos-to-number x)))

(add-totality "nat")

;; This adds the c.r. predicate TotalNat with clauses
;; TotalNatZero:	TotalNat Zero
;; TotalNatSucc:	allnc nat^(TotalNat nat^ -> TotalNat(Succ nat^))

(add-totalnc "nat")
(add-co "TotalNat")
(add-co "TotalNatNc")

(add-mr-ids "TotalNat")
(add-co "TotalNatMR")

(add-eqp "nat")
(add-eqpnc "nat")
(add-co "EqPNat")
(add-co "EqPNatNc")

(add-mr-ids "EqPNat")
(add-co "EqPNatMR")

;; NatTotalVar
(set-goal "all n TotalNat n")
(use "AllTotalIntro")
(assume "n^" "Tn")
(use "Tn")
;; Proof finished
;; (cp)
(save "NatTotalVar")

;; We collect properties of TotalNat and EqPNat, including the Nc, Co
;; and MR variants.  These are

;; EfTotalNat
;; EfTotalNatNc
;; TotalNatToCoTotal
;; TotalNatNcToCoTotalNc
;; EfCoTotalNat
;; EfCoTotalNatNc
;; EfCoTotalNatMR
;; TotalNatMRToEqD
;; TotalNatMRToTotalNcLeft
;; TotalNatMRToTotalNcRight
;; TotalNatMRRefl
;; EfCoTotalNatMR
;; TotalNatMRToCoTotalMR

;; EfEqPNat
;; EfEqPNatNc
;; EqPNatNcToEqD
;; EqPNatSym
;; EqPNatNcSym
;; EqPNatRefl
;; EqPNatNcRefl
;; EqPNatToTotalLeft
;; EqPNatNcToTotalNcLeft
;; EqPNatToTotalRight
;; EqPNatNcToTotalNcRight
;; EqPNatNcTrans
;; EqPNatNcToEq
;; EqNatToEqPNc

;; EfCoEqPNat
;; EfCoEqPNatNc
;; CoEqPNatNcToEqD
;; CoEqPNatSym
;; CoEqPNatNcSym
;; CoEqPNatRefl
;; CoEqPNatNcRefl
;; CoEqPNatToCoTotalLeft
;; CoEqPNatNcToCoTotalNcLeft
;; CoEqPNatToCoTotalRight
;; CoEqPNatNcToCoTotalNcRight
;; CoEqPNatNcTrans
;; EqPNatToCoEqP
;; EqPNatNcToCoEqPNc
;; EfEqPNatMR
;; EqPNatMRToEqDLeft
;; EqPNatMRToEqDRight
;; EqPNatNcToTotalMR
;; TotalNatMRToEqPNc
;; EqPNatMRToTotalNc
;; EqPNatMRRefl
;; EqPNatNcToEqPMR
;; EqPNatMRToEqPNcLeft
;; EqPNatMRToEqPNcRight
;; EfCoEqPNatMR
;; EqPNatMRToCoEqPMR
;; CoEqPNatNcToCoTotalMR
;; CoTotalNatMRToCoEqPNc
;; CoEqPNatMRRefl
;; CoEqPNatNcToCoEqPMR
;; CoEqPNatMRToCoEqPNcLeft
;; CoEqPNatMRToCoEqPNcRight

;; EfTotalNat
(set-goal "allnc n^(F -> TotalNat n^)")
(assume "n^" "Absurd")
(simp (pf "n^ eqd 0"))
(use "TotalNatZero")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfTotalNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfTotalNatNc
(set-goal "allnc n^(F -> TotalNatNc n^)")
(assume "n^" "Absurd")
(simp (pf "n^ eqd 0"))
(use "TotalNatNcZero")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfTotalNatNc")

;; TotalNatToCoTotal
(set-goal "allnc n^(TotalNat n^ -> CoTotalNat n^)")
(assume "n^" "Tn")
(coind "Tn")
(assume "n^1" "Tn1")
(assert "n^1 eqd 0 ori exr n^2(TotalNat n^2 andi n^1 eqd Succ n^2)")
 (elim "Tn1")
 (intro 0)
 (use "InitEqD")
 (assume "n^2" "Tn2" "Useless")
 (intro 1)
 (intro 0 (pt "n^2"))
 (split)
 (use "Tn2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "n1=0")
(intro 0)
(use "n1=0")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^2" "n2Prop")
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "n2Prop")
(use "n2Prop")
;; Proof finished.
;; (cp)
(save "TotalNatToCoTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if n0 (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; TotalNatNcToCoTotalNc
(set-goal "allnc n^(TotalNatNc n^ -> CoTotalNatNc n^)")
(assume "n^" "Tn")
(coind "Tn")
(assume "n^1" "Tn1")
(assert "n^1 eqd 0 ornc exnc n^2(TotalNatNc n^2 andi n^1 eqd Succ n^2)")
 (elim "Tn1")
 (intro 0)
 (use "InitEqD")
 (assume "n^2" "Tn2" "Useless")
 (intro 1)
 (intro 0 (pt "n^2"))
 (split)
 (use "Tn2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "n1=0")
(intro 0)
(use "n1=0")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^2" "n2Prop")
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "n2Prop")
(use "n2Prop")
;; Proof finished.
;; (cp)
(save "TotalNatNcToCoTotalNc")

;; EfCoTotalNat
(set-goal "allnc n^(F -> CoTotalNat n^)")
(assume "n^" "Absurd")
(coind "Absurd")
(assume "n^1" "Useless")
(intro 0)
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoTotalNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat)(DummyL nat ysumu)

;; EfCoTotalNatNc
(set-goal "allnc n^(F -> CoTotalNatNc n^)")
(assume "n^" "Absurd")
(coind "Absurd")
(assume "n^1" "Useless")
(intro 0)
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoTotalNatNc")

;; TotalNatMRToEqD
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "TMRn1n2")
(elim "TMRn1n2")
;; 3,4
(use "InitEqD")
;; 4
(assume "n^3" "n^4" "Useless" "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "TotalNatMRToEqD")

;; TotalNatMRToTotalNcLeft
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> TotalNatNc n^1)")
(assume "n^1" "n^2" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cp)
(save "TotalNatMRToTotalNcLeft")

;; TotalNatMRToTotalNcRight
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> TotalNatNc n^2)")
(assume "n^1" "n^2" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cp)
(save "TotalNatMRToTotalNcRight")

;; TotalNatMRRefl
(set-goal "allnc n^(TotalNat n^ -> TotalNatMR n^ n^)")
(assume "n^" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatZeroMR")
;; 4
(assume "n^1" "n^1" "TMRn1n1")
(use "TotalNatSuccMR")
(use "TMRn1n1")
;; Proof finished.
;; (cp)
(save "TotalNatMRRefl")

;; EfCoTotalNatMR
(set-goal "allnc n^1,n^2(F -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoTotalNatMR")

;; TotalNatMRToCoTotalMR
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "Tn1n2")
(coind "Tn1n2")
(assume "n^3" "n^4" "Tn3n4")
(assert "n^3 eqd 0 andnc n^4 eqd0 ornc
         exr n^5,n^6(TotalNatMR n^5 n^6 andnc 
        n^3 eqd Succ n^5 andnc
        n^4 eqd Succ n^6)")
 (elim "Tn3n4")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "n^5" "n^6" "Tn5n6" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "n^5"))
 (intro 0 (pt "n^6"))
 (split)
 (use "Tn5n6")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 22,23
(assume "Conj")
(intro 0)
(use "Conj")
;; 23
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cp)
(save "TotalNatMRToCoTotalMR")

;; EfEqPNat
(set-goal "allnc n^1,n^2(F -> EqPNat n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(use "EqPNatZero")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfEqPNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfEqPNatNc
(set-goal "allnc n^1,n^2(F -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(use "EqPNatNcZero")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfEqPNatNc")

;; EqPNatNcToEqD
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "InitEqD")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPNatNcToEqD")

;; EqPNatSym
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> EqPNat n^2 n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "EqPNatZero")
(assume "n^3" "n^4" "Useless" "EqPn4n3")
(use "EqPNatSucc")
(use "EqPn4n3")
;; Proof finished.
;; (cp)
(save "EqPNatSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp (rename-variables neterm))
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcSym
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "EqPNatNcZero")
(assume "n^3" "n^4" "Useless" "EqPn4n3")
(use "EqPNatNcSucc")
(use "EqPn4n3")
;; Proof finished.
;; (cp)
(save "EqPNatNcSym")

;; EqPNatRefl
(set-goal "allnc n^(TotalNat n^ -> EqPNat n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatZero")
(assume "n^1" "Tn1")
(use "EqPNatSucc")
;; Proof finished.
;; (cp)
(save "EqPNatRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp (rename-variables neterm))
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcRefl
(set-goal "allnc n^(TotalNatNc n^ -> EqPNatNc n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatNcZero")
(assume "n^1" "Tn1" "EqPHyp")
(use "EqPNatNcSucc")
(use "EqPHyp")
;; Proof finished.
;; (cp)
(save "EqPNatNcRefl")

;; EqPNatToTotalLeft
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> TotalNat n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatZero")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPNatToTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcToTotalNcLeft
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatNc n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "EqPn3n4" "IH")
(use "TotalNatNcSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPNatNcToTotalNcLeft")

;; EqPNatToTotalRight
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> TotalNat n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatZero")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPNatToTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcToTotalNcRight
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatNc n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "EqPn3n4" "IH")
(use "TotalNatNcSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPNatNcToTotalNcRight")

;; EqPNatNcTrans
(set-goal
 "allnc n^1,n^2,n^3(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^3 -> EqPNatNc n^1 n^3)")
(assume "n^1" "n^2" "n^3" "EqPn1n2" "EqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "EqPNatNcRefl")
(use "EqPNatNcToTotalNcRight" (pt "n^2"))
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "EqPNatNcTrans")

;; EqPNatNcToEq
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> n^1=n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "Truth")
(assume "n^13" "n^4" "Useless" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPNatNcToEq")

;; EqNatToEqPNc
(set-goal "allnc n^1(TotalNatNc n^1 -> allnc n^2(TotalNatNc n^2 ->
 n^1=n^2 -> EqPNatNc n^1 n^2))")
(assume "n^1" "Tn1")
(elim "Tn1")
;; 3,4
(assume "n^2" "Tn2")
(elim "Tn2")
(assume "Useless")
(use "EqPNatNcZero")
;; 7
(assume "n^3" "Tn3" "Useless" "Absurd")
(use "EfEqPNatNc")
(use "Absurd")
;; 4
(assume "n^2" "Tn2" "IH" "n^3" "Tn3")
(elim "Tn3")
(assume "Absurd")
(use "EfEqPNatNc")
(use "Absurd")
;; 13
(assume "n^4" "Tn4" "Useless" "n2=n4")
(use "EqPNatNcSucc")
(use "IH")
(use "Tn4")
(use "n2=n4")
;; Proof finished.
;; (cp)
(save "EqNatToEqPNc")

;; EfCoEqPNat
(set-goal "allnc n^1,n^2(F -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoEqPNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat)(DummyL nat ysumu)
(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

;; EfCoEqPNatNc
(set-goal "allnc n^1,n^2(F -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoEqPNatNc")

;; CoEqPNatNcToEqD
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> n^1 eqd n^2)")
(use (make-proof-in-aconst-form (finalg-to-bisim-aconst (py "nat"))))
;; Proof finished.
;; (cp)
(save "CoEqPNatNcToEqD")

;; CoEqPNatSym
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoEqPNat n^2 n^1)")
(assume "n^1" "n^2" "n1~n2")
(coind "n1~n2")
(assume "n^3" "n^4" "n4~n3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPNat n^2 n^1"))))
 (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 8,9
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cp)
(save "CoEqPNatSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcSym
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^1)")
(assume "n^1" "n^2" "n1~n2")
(coind "n1~n2")
(assume "n^3" "n^4" "n4~n3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPNatNc n^2 n^1"))))
 (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 8,9
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcSym")

;; CoEqPNatRefl
(set-goal "allnc n^(CoTotalNat n^ -> CoEqPNat n^ n^)")
(assert "allnc n^1,n^2(CoTotalNat n^1 andi n^1 eqd n^2 -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2")
(coind)
(assume "n^3" "n^4" "Conj")
(inst-with-to "Conj" 'left "CoTn3")
(inst-with-to "Conj" 'right "n3=n4")
(drop "Conj")
(simp "<-" "n3=n4")
(drop "n3=n4")
(inst-with-to "CoTotalNatClause" (pt "n^3") "CoTn3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "n3=0")
(intro 0)
(split)
(use "n3=0")
(use "n3=0")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(split)
(use "n5Prop")
(use "InitEqD")
(split)
(use "n5Prop")
(use "n5Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "CoEqPNatRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcRefl
(set-goal "allnc n^(CoTotalNatNc n^ -> CoEqPNatNc n^ n^)")
(assert
 "allnc n^1,n^2(CoTotalNatNc n^1 andi n^1 eqd n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2")
(coind)
(assume "n^3" "n^4" "Conj")
(inst-with-to "Conj" 'left "CoTn3")
(inst-with-to "Conj" 'right "n3=n4")
(drop "Conj")
(simp "<-" "n3=n4")
(drop "n3=n4")
(inst-with-to "CoTotalNatNcClause" (pt "n^3") "CoTn3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "n3=0")
(intro 0)
(split)
(use "n3=0")
(use "n3=0")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(split)
(use "n5Prop")
(use "InitEqD")
(split)
(use "n5Prop")
(use "n5Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcRefl")

;; CoEqPNatToCoTotalLeft
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoTotalNat n^1)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNat n^1 n^3 -> CoTotalNat n^1")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n3~n4")
(inst-with-to "CoEqPNatClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(split)
(intro 1)
(intro 0 (pt "n^6"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^2"))
(use "n1~n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatToCoTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcToCoTotalNcLeft
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatNc n^1)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatNc n^1 n^3 -> CoTotalNatNc n^1")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n3~n4")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(split)
(intro 1)
(intro 0 (pt "n^6"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^2"))
(use "n1~n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcToCoTotalNcLeft")

;; CoEqPNatToCoTotalRight
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoTotalNat n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNat n^3 n^2 -> CoTotalNat n^2")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n4~n3")
(inst-with-to "CoEqPNatClause" (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(split)
(intro 1)
(intro 0 (pt "n^5"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^1"))
(use "n1~n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatToCoTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcToCoTotalNcRight
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatNc n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatNc n^3 n^2 -> CoTotalNatNc n^2")))
;; 3,4
(assume "n^4" "ExHyp3")
(by-assume "ExHyp3" "n^3" "n3~n4")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(split)
(intro 1)
(intro 0 (pt "n^5"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^1"))
(use "n1~n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcToCoTotalNcRight")

;; CoEqPNatNcTrans
(set-goal "allnc n^1,n^2,n^3(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^3 ->
                             CoEqPNatNc n^1 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPn1n2" "CoEqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "CoEqPNatNcRefl")
(use "CoEqPNatNcToCoTotalNcRight" (pt "n^2"))
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn1n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcTrans")

;; EqPNatToCoEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(coind "EqPn1n2")
(assume "n^3" "n^4" "EqPn3n4")
(elim "EqPn3n4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "n^5" "n^6" "EqPn5n6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "Conj")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPNatToCoEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]
;;    (Rec nat=>uysum(nat ysum nat))n0(DummyL nat ysum nat)
;;    ([n1,(uysum(nat ysum nat))]Inr((InR nat nat)n1)))

;; EqPNatNcToCoEqPNc
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(coind "EqPn1n2")
(assume "n^3" "n^4" "EqPn3n4")
(elim "EqPn3n4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "n^5" "n^6" "EqPn5n6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "Conj")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPNatNcToCoEqPNc")

;; EfEqPNatMR
(set-goal "allnc n^1,n^2,n^3(F -> EqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(simp (pf "n^3 eqd 0"))
(use "EqPNatZeroMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfEqPNatMR")

;; EqPNatMRToEqDLeft
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "InitEqD")
(assume "n^4" "n^5" "n^6" "Useless" "EqDHyp")
(simp "EqDHyp")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPNatMRToEqDLeft")

;; EqPNatMRToEqDRight
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> n^2 eqd n^3)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "InitEqD")
(assume "n^4" "n^5" "n^6" "Useless" "EqDHyp")
(simp "EqDHyp")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPNatMRToEqDRight")

;; EqPNatNcToTotalMR
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "TotalNatZeroMR")
(assume "n^3" "n^4" "Useless")
(use "TotalNatSuccMR")
;; Proof finished.
;; (cp)
(save "EqPNatNcToTotalMR")

;; TotalNatMRToEqPNc
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "TMRn1n2")
(elim "TMRn1n2")
(use "EqPNatNcZero")
(assume "n^3" "n^4" "Useless")
(use "EqPNatNcSucc")
;; Proof finished.
;; (cp)
(save "TotalNatMRToEqPNc")

;; EqPNatMRToTotalNc
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> TotalNatNc n^3)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "TotalNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cp)
(save "EqPNatMRToTotalNc")

;; EqPNatMRRefl
(set-goal "allnc n^(TotalNatNc n^ -> EqPNatMR n^ n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatZeroMR")
(assume "n^1" "IH")
(use "EqPNatSuccMR")
;; Proof finished.
;; (cp)
(save "EqPNatMRRefl")

;; EqPNatNcToEqPMR
(set-goal "allnc n^1,n^2,n^3(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^3 ->
                             EqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "EqPn1n2" "EqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "EqPNatMRRefl")
(use "EqPNatNcToTotalNcRight" (pt "n^2"))
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "EqPNatNcToEqPMR")

;; EqPNatMRToEqPNcLeft
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "n^3" "EqPMRHyp")
(elim "EqPMRHyp")
(use "EqPNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless" "EqPn4n5")
(use "EqPNatNcSucc")
(use "EqPn4n5")
;; Proof finished.
;; (cp)
(save "EqPNatMRToEqPNcLeft")

;; EqPNatMRToEqPNcRight
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> EqPNatNc n^2 n^3)")
(assume "n^1" "n^2" "n^3" "EqPMRHyp")
(elim "EqPMRHyp")
(use "EqPNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless" "EqPn5n6")
(use "EqPNatNcSucc")
(use "EqPn5n6")
;; Proof finished.
;; (cp)
(save "EqPNatMRToEqPNcRight")

;; EfCoEqPNatMR
(set-goal "allnc n^1,n^2,n^3(F -> CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Absurd")
(coind "Absurd")
(assume "n^4" "n^5" "n^6" "Useless")
(intro 0)
(simp (pf "n^4 eqd 0"))
(simp (pf "n^5 eqd 0"))
(simp (pf "n^6 eqd 0"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfCoEqPNatMR")

;; EqPNatMRToCoEqPMR
(set-goal "allnc n^1,n^2,n^3(
 EqPNatMR n^1 n^2 n^3 -> CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Tn1n2n3")
(coind "Tn1n2n3")
(assume "n^4" "n^5" "n^6" "Tn4n5n6")
(assert "n^4 eqd 0 andnc n^5 eqd 0 andnc n^6 eqd 0 ornc
         exr n^7,n^8,n^9(EqPNatMR n^7 n^8 n^9 andnc 
         n^4 eqd Succ n^7 andnc
         n^5 eqd Succ n^8 andnc
         n^6 eqd Succ n^9)")
 (elim "Tn4n5n6")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "n^7" "n^8" "n^9" "Tn7n8n9" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "n^7"))
 (intro 0 (pt "n^8"))
 (intro 0 (pt "n^9"))
 (split)
 (use "Tn7n8n9")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 27,28
(assume "Conj")
(intro 0)
(use "Conj")
;; 28
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 0 (pt "n^7"))
(intro 0 (pt "n^8"))
(intro 0 (pt "n^9"))
(split)
(intro 1)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; Proof finished.
;; (cp)
(save "EqPNatMRToCoEqPMR")

;; CoEqPNatNcToCoTotalMR
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (make-proof-in-aconst-form
      (imp-formulas-to-gfp-aconst
       (pf "CoEqPNatNc n^1 n^2 -> CoTotalNatMR n^1 n^2"))))
;; 3,4
(use "n1~n2")
;; 4
(assume "n^3" "n^4" "n3~n4")
;; use the closure axiom for CoEqPNat
;; (pp "CoEqPNatNcClause")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4"
	      "CoEqPNatNcClauseInst")
(elim "CoEqPNatNcClauseInst")
;; 8,9
(drop "CoEqPNatNcClauseInst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "CoEqPNatNcClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcToCoTotalMR")

;; CoTotalNatMRToCoEqPNc
(set-goal "allnc n^1,n^2(CoTotalNatMR n^1 n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "CoTn1n2")
(use (make-proof-in-aconst-form
      (imp-formulas-to-gfp-aconst
       (pf "CoTotalNatMR n^1 n^2 -> CoEqPNatNc n^1 n^2"))))
;; 3,4
(use "CoTn1n2")
;; 4
(assume "n^3" "n^4" "CoTn3n4")
;; use the closure axiom for CoTotalNatMR
(inst-with-to "CoTotalNatMRClause" (pt "n^3") (pt "n^4") "CoTn3n4"
	      "CoTotalNatMRClauseInst")
(elim "CoTotalNatMRClauseInst")
;; 8,9
(drop "CoTotalNatMRClauseInst")
(assume "EqConj")
(intro 0)
(split)
(use "EqConj")
(use "EqConj")
;; 9
(drop "CoTotalNatMRClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cp)
(save "CoTotalNatMRToCoEqPNc")

;; CoEqPNatMRRefl
(set-goal "allnc n^(CoTotalNatNc n^ -> CoEqPNatMR n^ n^ n^)")
(assert
 "allnc n^1,n^2,n^3(CoTotalNatNc n^1 andnc n^1 eqd n^2 andnc n^2 eqd n^3 ->
                    CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3")
(coind)
(assume "n^4" "n^5" "n^6" "Conj")
(inst-with-to "Conj" 'left "CoTn4")
(inst-with-to "Conj" 'right "Conj34")
(inst-with-to "Conj34" 'left "n4=n5")
(inst-with-to "Conj34" 'right "n5=n6")
(drop "Conj" "Conj34")
(simp "<-" "n5=n6")
(simp "<-" "n4=n5")
(drop "n5=n6" "n4=n5")
(inst-with-to "CoTotalNatNcClause" (pt "n^4") "CoTn4" "Inst")
(elim "Inst")
;; 20,21
(drop "Inst")
(assume "n4=0")
(intro 0)
(split)
(use "n4=0")
(split)
(use "n4=0")
(use "n4=0")
;; 21
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(intro 1)
(intro 0 (pt "n^7"))
(intro 0 (pt "n^7"))
(intro 0 (pt "n^7"))
(split)
(intro 1)
(split)
(use "n7Prop")
(split)
(use "InitEqD")
(use "InitEqD")
(split)
(use "n7Prop")
(split)
(use "n7Prop")
(use "n7Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "CoEqPNatMRRefl")

;; CoEqPNatNcToCoEqPMR
(set-goal "allnc n^1,n^2,n^3(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^3 ->
                             CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPn1n2" "CoEqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "CoEqPNatMRRefl")
(use "CoEqPNatNcToCoTotalNcRight" (pt "n^2"))
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn1n2")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcToCoEqPMR")

;; CoEqPNatMRToCoEqPNcLeft
(set-goal "allnc n^1,n^2,n^3(CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "n^3" "CoEqPMRn1n2n3")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^1 n^2")))
;; 3,4
(assume "n^4" "n^5" "ExHyp45")
(by-assume "ExHyp45" "n^6" "CoEqPMRn4n5n6")
;; (pp "CoEqPNatMRClause")
(inst-with-to "CoEqPNatMRClause"
	      (pt "n^4") (pt "n^5") (pt "n^6") "CoEqPMRn4n5n6" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 1)
(intro 0 (pt "n^7"))
(intro 0 (pt "n^8"))
(split)
(intro 1)
(intro 0 (pt "n^9"))
(use "n7n8n9Prop")
(split)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; 4
(intro 0 (pt "n^3"))
(use "CoEqPMRn1n2n3")
;; Proof finished.
;; (cp)
(save "CoEqPNatMRToCoEqPNcLeft")

;; CoEqPNatMRToCoEqPNcRight
(set-goal "allnc n^1,n^2,n^3(CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^2 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPMRn1n2n3")
(use (imp-formulas-to-coind-proof
      (pf "exr n^1 CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^2 n^3")))
;; 3,4
(assume "n^5" "n^6" "ExHyp56")
(by-assume "ExHyp56" "n^4" "CoEqPMRn4n5n6")
;; (pp "CoEqPNatMRClause")
(inst-with-to "CoEqPNatMRClause"
	      (pt "n^4") (pt "n^5") (pt "n^6") "CoEqPMRn4n5n6" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 1)
(intro 0 (pt "n^8"))
(intro 0 (pt "n^9"))
(split)
(intro 1)
(intro 0 (pt "n^7"))
(use "n7n8n9Prop")
(split)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; 4
(intro 0 (pt "n^1"))
(use "CoEqPMRn1n2n3")
;; Proof finished.
;; (cp)
(save "CoEqPNatMRToCoEqPNcRight")

;; This concludes the correction of properties of TotalNat and EqPNat.

;; Program constants
;; =================

(add-program-constant "NatPlus" (py "nat=>nat=>nat"))
(add-program-constant "NatTimes" (py "nat=>nat=>nat"))
(add-program-constant "NatLt" (py "nat=>nat=>boole"))
(add-program-constant "NatLe" (py "nat=>nat=>boole"))
(add-program-constant "Pred" (py "nat=>nat"))
(add-program-constant "NatMinus" (py "nat=>nat=>nat"))
(add-program-constant "NatMax" (py "nat=>nat=>nat"))
(add-program-constant "NatMin" (py "nat=>nat=>nat"))
(add-program-constant "AllBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "ExBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "NatLeast" (py "nat=>(nat=>boole)=>nat"))
(add-program-constant "NatLeastUp" (py "nat=>nat=>(nat=>boole)=>nat"))
(add-program-constant "NatSqrt" (py "nat=>nat"))

;; Tokens used by the parser.

(define (add-nat-tokens)
  (let* ((make-type-string
	  (lambda (type op-string type-strings)
	    (let* ((string (type-to-string type))
		   (l (string->list string)))
	      (if (member string type-strings)
		  (list->string (cons (char-upcase (car l)) (cdr l)))
		  (myerror op-string "unexpected type" type)))))
	 (tc ;term-creator
	  (lambda (op-string . type-strings)
	    (lambda (x y)
	      (let* ((type (term-to-type x))
		     (type-string
		      (make-type-string type op-string type-strings))
		     (internal-name (string-append type-string op-string)))
		(mk-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst internal-name))
		 x y))))))
    (add-token "+" 'add-op (tc "Plus" "nat"))
    (add-token "*" 'mul-op (tc "Times" "nat"))
    (add-token "<" 'rel-op (tc "Lt" "nat"))
    (add-token "<=" 'rel-op (tc "Le" "nat"))
    (add-token "--" 'add-op (tc "Minus" "nat"))
    (add-token "max" 'mul-op (tc "Max" "nat"))
    (add-token "min" 'mul-op (tc "Min" "nat"))))

(add-nat-tokens)

;; (add-nat-display) updates DISPLAY-FUNCTIONS, so that it uses the
;; tokens introduced by (add-nat-tokens).

(define (add-nat-display)
  (let ((dc ;display-creator
	 (lambda (name display-string token-type)
	   (lambda (x)
	     (let ((op (term-in-app-form-to-final-op x))
		   (args (term-in-app-form-to-args x)))
	       (if (and (term-in-const-form? op)
			(string=? name (const-to-name
					(term-in-const-form-to-const op)))
			(= 2 (length args)))
		   (list token-type display-string
			 (term-to-token-tree (term-to-original (car args)))
			 (term-to-token-tree (term-to-original (cadr args))))
		   #f))))))
    (add-display (py "nat") (dc "NatPlus" "+" 'add-op))
    (add-display (py "nat") (dc "NatTimes" "*" 'mul-op))
    (add-display (py "boole") (dc "NatLt" "<" 'rel-op))
    (add-display (py "boole") (dc "NatLe" "<=" 'rel-op))
    (add-display (py "nat") (dc "NatMinus" "--" 'add-op))
    (add-display (py "nat") (dc "NatMax" "max" 'mul-op))
    (add-display (py "nat") (dc "NatMin" "min" 'mul-op))))

(add-nat-display)

;; (remove-nat-tokens) removes all tokens and from DISPLAY-FUNCTIONS
;; all items (nat proc).

(define (remove-nat-tokens)
  (remove-token "+")
  (remove-token "*")
  (remove-token "<")
  (remove-token "<=")
  (remove-token "--")
  (remove-token "max")
  (remove-token "min")
  (set! DISPLAY-FUNCTIONS
	(list-transform-positive DISPLAY-FUNCTIONS
	  (lambda (item)
	    (not (equal? (car item) (py "nat")))))))

;; NatEqToEqD
(set-goal "all n,m(n=m -> n eqd m)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n" "0=Sn")
(use "EfEqD")
(use "0=Sn")
(assume "n" "IH")
(cases)
(assume "Sn=0")
(use "EfEqD")
(use "Sn=0")
(assume "m" "Sn=Sm")
(assert "n eqd m")
 (use "IH")
 (use "Sn=Sm")
(assume "n=m")
(elim "n=m")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "NatEqToEqD")

;; Computation rules for the program constants.

;; For NatPlus
(add-computation-rules
 "n+0" "n"
 "n+Succ m" "Succ(n+m)")

(set-totality-goal "NatPlus")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
;; 5,6
(use "TotalVar")
;; 6
(assume "m" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; For NatTimes
(add-computation-rules
 "n*0" "0"
 "n*Succ m" "(n*m)+n")

(set-totality-goal "NatTimes")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
;; 5,6
(use "TotalVar")
;; 6
(assume "m" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "TotalVar")
;; Proof finished
;; (cp)
(save-totality)

;; For NatLt
(add-computation-rules
 "n<0" "False"
 "0<Succ n" "True"
 "Succ n<Succ m" "n<m")

(set-totality-goal "NatLt")
(assert
 "allnc m^(TotalNat m^ -> allnc n^(TotalNat n^ -> TotalBoole(n^ <m^)))")
(fold-alltotal)
(ind)
;; 5,6
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; 6
(assume "n" "IH")
(fold-alltotal)
(cases)
;; 11,12
(use "TotalVar")
;; 12
(assume "m")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(auto)
;; Proof finished.
;; (cp)
(save-totality)

;; For NatLe
(add-computation-rules
 "0<=n" "True"
 "Succ n<=0" "False"
 "Succ n<=Succ m" "n<=m")

(set-totality-goal "NatLe")
(fold-alltotal)
(ind)
;; 3,4
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; 4
(assume "n" "IH")
(fold-alltotal)
(cases)
;; 9,10
(use "TotalVar")
;; 10
(assume "m")
(use "IH")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; For Pred
(add-computation-rules
 "Pred 0" "0"
 "Pred(Succ n)" "n")

(set-totality-goal "Pred")
(fold-alltotal)
(cases)
;; 3,4
(use "TotalVar")
;; 4
(assume "n")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; For NatMinus
(add-computation-rules
 "n--0" "n"
 "n--Succ m" "Pred(n--m)")

(set-totality-goal "NatMinus")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
;; 5,6
(use "TotalVar")
;; 6
(assume "m" "IH")
(use "PredTotal")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; For NatMax
(add-computation-rules
 "n max 0" "n"
 "0 max Succ n" "Succ n"
 "Succ n max Succ m" "Succ(n max m)")

(set-totality-goal "NatMax")
(assert
 "allnc m^(TotalNat m^ -> allnc n^(TotalNat n^ -> TotalNat(n^ max m^)))")
(fold-alltotal)
(ind)
;; 5,6
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; 6
(assume "n" "IH")
(fold-alltotal)
(cases)
;; 11,12
(use "TotalVar")
;; 12
(assume "m")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(auto)
;; Proof finished.
;; (cp)
(save-totality)

;; For NatMin
(add-computation-rules
 "n min 0" "0"
 "0 min Succ n" "0"
 "Succ n min Succ m" "Succ(n min m)")

(set-totality-goal "NatMin")
(assert
 "allnc m^(TotalNat m^ -> allnc n^(TotalNat n^ -> TotalNat(n^ min m^)))")
(fold-alltotal)
(ind)
;; 5,6
(fold-alltotal)
(assume "n")
(use "TotalVar")
;; 6
(assume "n" "IH")
(fold-alltotal)
(cases)
;; 11,12
(use "TotalVar")
;; 12
(assume "m")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(auto)
;; Proof finished.
;; (cp)
(save-totality)

(add-var-name "w" (py "boole"))
(add-var-name "ws" (py "nat=>boole"))
;; (add-var-name "ps" (py "nat=>boole"))
;; (add-var-name "pf" (py "nat=>boole"))

;; For AllBNat
(add-computation-rules
 "AllBNat 0 ws" "True"
 "AllBNat(Succ n)ws" "[if (AllBNat n ws) (ws n) False]")

(set-totality-goal "AllBNat")
(fold-alltotal)
(ind)
;; 3,4
(strip)
(use "TotalVar")
;; 4
(assume "n" "IH" "ws^" "Tws")
(ng #t)
(use "BooleIfTotal")
(use "IH")
(use "Tws")
(use "Tws")
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; For NatLeast
(add-computation-rules
 "NatLeast 0 ws" "0"
 "NatLeast(Succ n)ws"
 "[if (ws 0) 0 (Succ(NatLeast n([m]ws (Succ m))))]")

(set-totality-goal "NatLeast")
(fold-alltotal)
(ind)
;; 3,4
(strip)
(use "TotalVar")
;; 4
(assume "n" "IH" "ws^" "Tws")
(ng #t)
(use "BooleIfTotal")
(use "Tws")
(use "TotalVar")
(use "TotalVar")
(use "TotalNatSucc")
(use "IH")
(assume "n^" "Tn")
(ng #t)
(use "Tws")
(use "TotalNatSucc")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)=>nat)n([ws]0)
;;  ([n0,((nat=>boole)=>nat),ws]
;;    [if (ws 0) 0 (Succ(((nat=>boole)=>nat)([n1]ws(Succ n1))))])

;; For NatLeastUp
(add-computation-rules
 "NatLeastUp n0 n ws"
 "[if (n0<=n) (NatLeast(n--n0)([m]ws (m+n0))+n0) 0]")

(set-totality-goal "NatLeastUp")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "ws")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; We prove and add some properties of the program constants introduced,
;; either as rewrite rules or as theorems.

;; Properties of NatPlus

;; NatPlusEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> allnc m^1,m^2(EqPNat m^1 m^2 ->
 EqPNat(n^1+m^1)(n^2+m^2)))")
(assume "n^1" "n^2" "EqPn1n2" "m^1" "m^2" "EqPm1m2")
(elim "EqPm1m2")
;; 3,4
(ng #t)
(use "EqPn1n2")
;; 4
(assume "m^3" "m^4" "EqPm3m4" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusEqP")

(set-goal "all n 0+n=n")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "0+n" "n")

(set-goal "all n,m Succ n+m=Succ(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Succ n+m" "Succ(n+m)")

(set-goal "all n,m,l n+(m+l)=n+m+l")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+(m+l)" "n+m+l")
(save "NatPlusAssoc")

;; NatPlusComm
(set-goal "all n,m n+m=m+n")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusComm")

;; NatPlusCancelL
(set-goal "all n,m,l(n+m=n+l -> m=l)")
(ind)
(ng)
(assume "m" "l" "m=l")
(use "m=l")
;; Step
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusCancelL")

;; NatPlusCancelR
(set-goal "all n,m,l(n+m=l+m -> n=l)")
(assert "all m,n,l(n+m=l+m -> n=l)")
(ind)
(assume "n" "l" "n=l")
(use "n=l")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Assertion proved.
(assume "Assertion" "n" "m")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "NatPlusCancelR")

;; NatPlusCancelEqL
(set-goal "all n,m,l (n+m=n+l)=(m=l)")
(ind)
(assume "m" "l")
(use "Truth")
(assume "n" "IH" "m" "l")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusCancelEqL")

;; NatPlusCancelEqR
(set-goal "all n,m,l (n+m=l+m)=(n=l)")
(assume "n")
(ind)
(assume "l")
(use "Truth")
(assume "m" "IH" "l")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusCancelEqR")

;; Properties of NatTimes

(set-goal "all n 0*n=0")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "0*n" "0")

;; NatCompat
(set-goal "all n,m(n=m -> all ws^(ws^ n -> ws^ m))")
(ind)
  (cases)
    (assume "0=0" "ws^" "H1")
    (use "H1")
  (assume "nat" "Absurd" "ws^" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "ws^" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m" "n=m" "ws^")
(use-with "IH" (pt "m") "n=m" (pt "[n]ws^(Succ n)"))
;; Proof finished.
;; (cp)
(save "NatCompat")

(add-var-name "ns" "ms" (py "nat=>nat"))

;; NatEqCompat
(set-goal "all n,m(n=m -> allnc ns(ns n=ns m))")
(ind)
  (cases)
    (assume "Useless" "ns")
    (use "Truth")
  (assume "m" "Absurd" "ns")
  (use "EfAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "ns")
  (use "EfAtom")
  (use "Absurd")
(assume "m" "n=m" "ns")
(use-with "IH" (pt "m") "n=m" (pt "[n]ns(Succ n)"))
;; Proof finished.
;; (cp)
(save "NatEqCompat")

;; NatEqSym
(set-goal "all n,m(n=m -> m=n)")
(assume "n" "m" "n=m")
(simp "n=m")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatEqSym")

;; NatEqTrans
(set-goal "all n,m,l(n=m -> m=l -> n=l)")
(assume "n" "m" "l" "=Hyp")
(simp "<-" "=Hyp")
(assume "n=l")
(use "n=l")
;; Proof finished.
;; (cp)
(save "NatEqTrans")

(set-goal "all n,m Succ n*m=(n*m)+m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "n*m+m+n"))
(use-with "NatEqCompat" (pt "Succ n*m") (pt "n*m+m")
	  "IH" (pt "[nat]nat+n"))
(use-with "NatEqCompat" (pt "m+n") (pt "n+m") "?"
	  (pt "[nat]n*m+nat"))
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Succ n*m" "(n*m)+m")

;; NatTimesPlusDistr
(set-goal "all n,m,l n*(m+l)=(n*m)+(n*l)")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesPlusDistr")
(add-rewrite-rule "n*(m+l)" "n*m+n*l")

;; NatTimesComm
(set-goal "all n,m n*m=m*n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "m*n+n"))
(use-with "NatEqCompat" (pt "n*m") (pt "m*n") "IH"
	  (pt "[nat]nat+n"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesComm")

;; NatTimesPlusDistrLeft
(set-goal "all n,m,l (n+m)*l=(n*l)+(m*l)")
(assume "n" "m" "l")
(simp-with "NatTimesComm" (pt "n+m") (pt "l"))
(ng #t)
(simp-with "NatTimesComm" (pt "n") (pt "l"))
(simp-with "NatTimesComm" (pt "m") (pt "l"))
(use-with "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesPlusDistrLeft")
(add-rewrite-rule "(n+m)*l" "n*l+m*l")

(set-goal "all n,m,l n*(m*l)=(n*m)*l")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH1" "m" "l")
(ng)
(simp-with "IH1" (pt "m") (pt "l"))
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n*(m*l)" "n*m*l")
(save "NatTimesAssoc")

;; NatTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m=n*l -> m=l)")
(assert "all n,m,l((Succ n)*m=(Succ n)*l -> m=l)")
(assume "n")
(ind)
(cases)
(strip)
(use "Truth")
(assume "l" "Absurd")
(use "Absurd")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(assume "Absurd")
(use "Absurd")
(assume "l" "Hyp")
(ng)
(use "IHm")
(use "NatPlusCancelR" (pt "n"))
(use "Hyp")
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "NatTimesCancelL")

;; NatTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m=l*m -> n=l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cp)
(save "NatTimesCancelR")

;; Properties of NatLt

(set-goal "all n n<Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<Succ n" "True")

(set-goal "all n (n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<n" "False")

(set-goal "all n(Succ n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Succ n<n" "False")

;; NatLtTrans
(set-goal "all n,m,l(n<m -> m<l -> n<l)")
(ind)
  (cases)
    (assume "l" "Absurd" "0<l")
    (use "0<l")
  (assume "m")
  (cases)
    (assume "Useless" "Absurd")
    (use "Absurd")
  (assume "l" "Useless" "H1")
  (use "Truth")
(assume "n" "IH1")
(cases)
  (assume "l" "Absurd" "0<l")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
(assume "H1" "Absurd")
(use "Absurd")
(use "IH1")
;; Proof finished
;; (cp)
(save "NatLtTrans")

;; NatNotEqSucc
(set-goal "all n(n=Succ n -> F)")
(ind)
(auto)
;; Proof finished.
;; (cp)
(save "NatNotEqSucc")

;; NatNotLeToLt
(set-goal "all n,m((n<=m -> F) -> m<n)")
(ind)
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatNotLeToLt")

;; NatNotLtToLe
(set-goal "all n,m((n<m -> F) -> m<=n)")
(ind)
(cases)
(assume "Useless")
(use "Truth")
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatNotLtToLe")

;; NatLeToNotLt
(set-goal "all n,m(n<=m -> m<n -> F)")
(ind)
(search)
(assume "n" 1)
(cases)
(search)
(use 1)
;; (cp)
(save "NatLeToNotLt")

;; NatLtToLe
(set-goal "all n,m(n<m -> n<=m)")
(ind)
(assume "m" "Useless")
(use "Truth")
(assume "nat" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtToLe")

;; NatLeAntiSym
(set-goal "all n,m(n<=m -> m<=n -> n=m)")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "n" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "IHn")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m")
(use "IHn")
;; Proof finished.
;; (cp)
(save "NatLeAntiSym")

;; NatLePlusCancelR
(set-goal "all n,m,l(n+l<=m+l -> n<=m)")
(assume "n" "m")
(ind)
;; 3,4
(assume "LeH")
(use "LeH")
;; 4
(assume "l" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLePlusCancelR")

;; NatLePlusCancelL
(set-goal "all n,m,l(n+m<=n+l -> m<=l)")
(assume "n" "m" "l")
(simp "NatPlusComm")
(simp (pf "n+l=l+n"))
(use "NatLePlusCancelR")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(save "NatLePlusCancelL")

;; NatLtPlusCancelR as rewrite rule
(set-goal "all n,m,l(n+m<l+m)=(n<l)")
(assert "all n,l,m(n+m<l+m)=(n<l)")
(assume "n" "l")
(ind)
(use "Truth")
(assume "m" "IH")
(ng)
(use "IH")
;; Assertion proved.
(assume "Assertion" "n" "m" "l")
(use "Assertion")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m<l+m" "n<l")

;; NatLtPlusCancelL
(set-goal "all n,m,l(n+m<n+l)=(m<l)") ;as rewrite rule
(assume "n" "m" "l")
(simp "NatPlusComm")
(simp (pf "n+l=l+n"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m<n+l" "m<l")

;; NatLtTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m<n*l -> m<l)")
(assert "all n,m,l((Succ n)*m<(Succ n)*l -> m<l)")
(assume "n")
(ind)
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "l")
(ng)
(use "IHm")
;; Assertion proved.
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "NatLtTimesCancelL")

;; NatLtTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m<l*m -> n<l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatLtTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cp)
(save "NatLtTimesCancelR")

;; NatPlusCancelLtL
(set-goal "all n,m,l (n+m<n+l)=(m<l)")
(assume "n" "m" "l")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPlusCancelLtL")

;; NatPlusCancelLtR
(set-goal "all n,m,l (n+m<l+m)=(n<l)")
(assume "n" "m" "l")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPlusCancelLtR")

;; Properties of NatLe

;; NatLeToEq
(set-goal "all n (n<=0)=(n=0)")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeToEq")
(add-rewrite-rule "n<=0" "n=0")

(set-goal "all n n<=n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<=n" "True")

(set-goal "all n,m n<=n+m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<=n+m" "True")

(set-goal "all n(Succ n<=n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Succ n<=n" "False")

(set-goal "all n n<=Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<=Succ n" "True")

;; NatLeTrans
(set-goal "all n,m,l(n<=m -> m<=l -> n<=l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeTrans")

;; NatLtLeTrans
(set-goal "all n,m,l(n<m -> m<=l -> n<l)")
(ind)
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtLeTrans")

;; NatLeLtTrans
(set-goal "all n,m,l(n<=m -> m<l -> n<l)")
(ind)
(cases)
  (assume "l" "Useless" "0<l")
  (use "0<l")
(assume "m")
(cases)
  (prop)
(assume "l")
(prop)
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeLtTrans")

;; NatLtSuccToLe
(set-goal "all n,m(n<Succ m -> n<=m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtSuccToLe")

;; NatLtLtSuccTrans
(set-goal "all n,m,l(n<m -> m<Succ l -> n<l)")
(assume "n" "m" "l" "n<m" "m<Succ l")
(use "NatLtLeTrans" (pt "m"))
(use "n<m")
(use "NatLtSuccToLe")
(use "m<Succ l")
;; Proof finished.
;; (cp)
(save "NatLtLtSuccTrans")

;; NatLeToLtSucc
(set-goal "all n,m(n<=m -> n<Succ m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeToLtSucc")

;; NatLtToSuccLe
(set-goal "all n,m(n<m -> Succ n<=m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtToSuccLe")

;; NatSuccLeToLt
(set-goal "all n,m(Succ n<=m -> n<m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatSuccLeToLt")

;; NatLtSuccCases
(set-goal "all n,m(n<Succ m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "LtSuccHyp")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "NatLtSuccToLe")
(use "LtSuccHyp")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
;; (cp)
(save "NatLtSuccCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,beta,beta_0][if (n<n0) beta beta_0]

(animate "NatLtSuccCases")

;; NatLeCases
(set-goal "all n,m(n<=m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "n<=m")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "n<=m")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
;; (cp)
(save "NatLeCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,beta,beta_0][if (n<n0) beta beta_0]

(animate "NatLeCases")

;; NatLeLtCases
(set-goal "all n,m((n<=m -> Pvar) -> (m<n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
;; (cp)
(save "NatLeLtCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,beta,beta_0][if (n<=n0) beta beta_0]

(animate "NatLeLtCases")

;; NatLeLeCases
(set-goal "all n,m((n<=m -> Pvar) -> (m<=n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
;; (cp)
(save "NatLeLin")
(save "NatLeLeCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,beta,beta_0][if (n<=n0) beta beta_0]

(animate "NatLeLin")

;; NatLtToLePred
(set-goal "all n,m(n<m -> n<=Pred m)")
(assume "n")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<Succ m")
(use "NatLtSuccToLe")
(use "n<Succ m")
;; Proof finished.
;; (cp)
(save "NatLtToLePred")

;; NatLePred
(set-goal "all n,m (Pred n<=m)=(n<=Succ m)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLePred")

;; NatSuccPred
(set-goal "all n(Zero<n -> Succ(Pred n)=n)")
(cases)
;; 2,3
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSuccPred")

;; NatLtMonPred
(set-goal "all n,m(0<n -> n<m -> Pred n<Pred m)")
(cases)
(assume "m" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "Useless" "n<m")
(use "n<m")
;; Proof finished.
;; (cp)
(save "NatLtMonPred")

;; NatLePlusCancelR
(set-goal "all n,m,l(n+m<=l+m)=(n<=l)") ;as rewrite rule
(assume "n")
(ind)
(assume "l")
(use "Truth")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m<=l+m" "n<=l")

;; NatLePlusCancelL
(set-goal "all n,m,l(n+m<=n+l)=(m<=l)") ;as rewrite rule
(assume "n" "m" "l")
(simp "NatPlusComm")
(simp (pf "n+l=l+n"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m<=n+l" "m<=l")

;; NatLeTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m<=n*l -> m<=l)")
(assert "all n,m,l((Succ n)*m<=(Succ n)*l -> m<=l)")
(assume "n")
(ind)
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "l")
(ng)
(use "IHm")
;; Assertion proved.
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "NatLeTimesCancelL")

;; NatLeTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m<=l*m -> n<=l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatLeTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cp)
(save "NatLeTimesCancelR")

;; NatPlusCancelLeL
(set-goal "all n,m,l (n+m<=n+l)=(m<=l)")
(assume "n" "m" "l")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPlusCancelLeL")

;; NatPlusCancelLeR
(set-goal "all n,m,l (n+m<=l+m)=(n<=l)")
(assume "n" "m" "l")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPlusCancelLeR")

;; Properties of NatMinus and Pred

;; PredEqP
(set-goal "allnc n^,m^(EqPNat n^ m^ -> EqPNat(Pred n^)(Pred m^))")
(assume "n^" "m^" "EqPnm")
(elim "EqPnm")
;; 3,4
(use "EqPNatZero")
;; 4
(assume "n^1" "m^1" "EqPn1m1" "IH")
(ng)
(use "EqPn1m1")
;; Proof finished.
;; (cp)
(save "PredEqP")

;; NatMinusEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> allnc m^1,m^2(EqPNat m^1 m^2 ->
 EqPNat(n^1--m^1)(n^2--m^2)))")
(assume "n^1" "n^2" "EqPn1n2" "m^1" "m^2" "EqPm1m2")
(elim "EqPm1m2")
;; 3,4
(ng #t)
(use "EqPn1n2")
;; 4
(assume "m^3" "m^4" "EqPm3m4" "IH")
(ng #t)
(use "PredEqP")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinusEqP")

(set-goal "all n,m Pred(Succ n--m)=n--m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(simp-with "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Pred(Succ n--m)" "n--m")

(set-goal "all n n--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n--n" "0")

(set-goal "all n Succ n--n=1")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Succ n--n" "1")

;; Added 2024-10-04:
;; NatPredMinus
(set-goal "all n,m Pred(n--m)=Pred n--m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPredMinus")
;; End of addition 2024-10-04.

;; NatPlusMinusAssoc
(set-goal "all n,m,l(l<=m -> n+(m--l)=n+m--l)")
(assume "n")
(ind)
;; 3,4
(ng #t)
(assume "l" "l=0")
(simp "l=0")
(use "Truth")
;; 4
(assume "m" "IH")
(cases)
;; 9,10
(ng #t)
(assume "Useless")
(use "Truth")
;; 10
(assume "l" "l<=m")
(ng)
(use "IH")
(use "l<=m")
;; Proof finished.
;; (cp)
(save "NatPlusMinusAssoc")

;; NatMinusPlusPlus
(set-goal "all n,m,l n+l--(m+l)=n--m")
(assume "n" "m")
(ind)
;; 3,4
(use "Truth")
(assume "l" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinusPlusPlus")

;; NatMinusPlusPlusR
(set-goal "all n,m,l l+n--(l+m)=n--m")
(assume "n" "m" "l")
(simp (pf "l+n=n+l"))
(simp (pf "l+m=m+l"))
(use "NatMinusPlusPlus")
(use "NatPlusComm")
(use "NatPlusComm")
;; Proof finshed.
;; (cp)
(save "NatMinusPlusPlusR")

;; Properties of NatMax

;; NatMaxEqP
(set-goal "allnc n^1,m^1(EqPNat n^1 m^1 -> allnc n^2,m^2(EqPNat n^2 m^2 ->
 EqPNat(n^1 max n^2)(m^1 max m^2)))")
(assume "n^1" "m^1" "EqPn1m1" "n^2" "m^2" "EqPn2m2")
(simp "<-" (pf "n^1 eqd m^1"))
(simp "<-" (pf "n^2 eqd m^2"))
(use "EqPNatRefl")
(use "NatMaxTotal")
(use "EqPNatToTotalLeft" (pt "m^1"))
(use "EqPn1m1")
(use "EqPNatToTotalLeft" (pt "m^2"))
(use "EqPn2m2")
;; 6
(use "EqPNatNcToEqD")
(use "EqPn2m2")
;; 4
(use "EqPNatNcToEqD")
(use "EqPn1m1")
;; Proof finished.
;; (cp)
(save "NatMaxEqP")

(set-goal "all n 0 max n=n")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "0 max n" "n")

(set-goal "all n n max n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n max n" "n")

(set-goal "all n,m,l(n max (m max l)=n max m max l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule
 "n max (m max l)" "n max m max l")

;; NatMaxComm
(set-goal "all n,m n max m = m max n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMaxComm")

;; NatMaxUB1
(set-goal "all n,m n<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMaxUB1")

;; NatMaxUB2
(set-goal "all n,m m<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMaxUB2")

;; NatMaxLUB
(set-goal "all n,m,l(n<=l -> m<=l -> n max m<=l)")
(ind)
(cases)
(strip)
(use "Truth")
(assume "m" "l" "Useless1" "Hyp")
(use "Hyp")
(assume "n" "IHn")
(cases)
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l" "Hyp" "Useless")
(use "Hyp")
(assume "m")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IHn")
;; Proof finished
;; (cp)
(save "NatMaxLUB")

;; NatMaxEq1
(set-goal "all n,m(m<=n -> n max m=n)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "Truth")
(use "m<=n")
(use "NatMaxUB1")
;; Proof finished.
;; (cp)
(save "NatMaxEq1")

;; NatMaxEq2
(set-goal "all n,m(n<=m -> n max m=m)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "n<=m")
(use "Truth")
(use "NatMaxUB2")
;; Proof finished.
;; (cp)
(save "NatMaxEq2")

;; Properties of NatMin

(set-goal "all n 0 min n=0")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "0 min n" "0")

(set-goal "all n n min n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n min n" "n")

(set-goal "all n,m,l(n min (m min l)=n min m min l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n min (m min l)" "n min m min l")

;; NatMinComm
(set-goal "all n,m n min m = m min n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinComm")

;; NatMinLB1
(set-goal "all n,m n min m<=n")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinLB1")

;; NatMinLB2
(set-goal "all n,m n min m<=m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinLB2")

;; NatMinGLB
(set-goal "all n,m,l(l<=n -> l<=m -> l<=n min m)")
(ind)
(assume "m" "l" "Hyp" "Useless")
(use "Hyp")
(assume "n" "IH")
(cases)
(assume "l" "Useless1" "Hyp")
(use "Hyp")
(assume "m")
(cases)
(strip)
(use "Truth")
(use "IH")
;; Proof finished
;; (cp)
(save "NatMinGLB")

;; NatMinEq1
(set-goal "all n,m(n<=m -> n min m=n)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMinLB1")
(use "NatMinGLB")
(use "Truth")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "NatMinEq1")

;; NatMinEq2
(set-goal "all n,m(m<=n -> n min m=m)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMinLB2")
(use "NatMinGLB")
(use "m<=n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatMinEq2")

;; NatIfTotal
(set-goal "allnc n^(TotalNat n^ ->
 allnc alpha^,(nat=>alpha)^(Total alpha^ ->
 allnc m^(TotalNat m^ -> Total((nat=>alpha)^ m^)) ->
 Total[if n^ alpha^ (nat=>alpha)^]))")
(assume "n^" "Tn" "alpha^" "(nat=>alpha)^" "Talpha" "Tf")
(elim "Tn")
(use "Talpha")
(assume "m^" "Tm" "Useless")
(ng #t)
(use "Tf")
(use "Tm")
;; Proof finished.
;; (cp)
(save "NatIfTotal")

;; NatEqTotal
(set-goal "allnc n^(
 TotalNat n^ -> allnc m^(TotalNat m^ -> TotalBoole(n^ =m^)))")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save "NatEqTotal")

;; The following would fit better into a file lib/boole.scm
;; Renamed into EqFalseToNeg NegToEqFalse and moved to ets.scm

;; ;; EqFalseToNeg
;; (set-goal "all w(w=False -> w -> F)")
;; (cases)
;; (assume "Absurd" "Useless")
;; (use "Absurd")
;; (assume "Useless" "Absurd")
;; (use "Absurd")
;; ;; Proof finished.
;; ;; (cp)
;; (save "EqFalseToNeg")

;; ;; NegToEqFalse
;; (set-goal "all w((w -> F) -> w=False)")
;; (cases)
;; (assume "Absurd")
;; (use-with "Absurd" "Truth")
;; (assume "Useless")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (save "NegToEqFalse")

;; Theorems OrIntroLeft OrIntroRight OrElim IfAndb IfOrb moved here
;; from nat.scm

;; ;; OrIntroLeft
;; (set-goal "all w1,w2(w1 -> w1 orb w2)")
;; (cases)
;; (strip)
;; (use "Truth")
;; (cases)
;; (strip)
;; (use "Truth")
;; (assume "Absurd")
;; (use "Absurd")
;; ;; Proof finished.
;; ;; (cp)
;; (save "OrIntroLeft")

;; ;; OrIntroRight
;; (set-goal "all w1,w2(w2 -> w1 orb w2)")
;; (cases)
;; (strip)
;; (use "Truth")
;; (cases)
;; (strip)
;; (use "Truth")
;; (assume "Absurd")
;; (use "Absurd")
;; ;; Proof finished.
;; ;; (cp)
;; (save "OrIntroRight")

;; ;; OrElim
;; (set-goal "all w1,w2(
;;  w1 orb w2 -> (w1 -> Pvar) -> (w2 -> Pvar) -> Pvar)")
;; (cases)
;; (assume "w1" "Useless1" "Hyp" "Useless2")
;; (use-with "Hyp" "Truth")
;; (cases)
;; (assume "Useless1" "Useless2" "Hyp")
;; (use-with "Hyp" "Truth")
;; (ng #t)
;; (assume "Absurd" "Hyp1" "Hyp2")
;; (use-with "Hyp1" "Absurd")
;; ;; Proof finished.
;; ;; (cp)
;; (save "OrElim")

;; ;; IfAndb
;; (set-goal "all w1,w2 [if w1 w2 False]=(w1 andb w2)")
;; (cases)
;; (assume "w1")
;; (use "Truth")
;; (assume "w1")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (save "IfAndb")

;; ;; IfOrb
;; (set-goal "all w1,w2 [if w1 True w2]=(w1 orb w2)")
;; (cases)
;; (assume "w1")
;; (use "Truth")
;; (assume "w1")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (save "IfOrb")

;; NatNegbLeEqLt
(set-goal "all n,m negb(n<=m)=(m<n)")
(assume "n" "m")
(cases (pt "n<=m"))
(assume "n<=m")
(cases (pt "m<n"))
(assume "m<n")
(use-with "NatLeLtTrans" (pt "n") (pt "m") (pt "n") "?" "?")
(use "n<=m")
(use "m<n")
;; 7
(strip)
(use "Truth")
;; 4
(assume "n<=m -> F")
(inst-with-to "NatNotLeToLt" (pt "n") (pt "m") "n<=m -> F" "m<n")
(cases (pt "m<n"))
(strip)
(use "Truth")
(assume "(m<n -> F)")
(use "(m<n -> F)")
(use "m<n")
;; Proof finished.
;; (cp)
(save "NatNegbLeEqLt")

;; (display-pconst "NegConst")

;; NatNegbLtEqLe
(set-goal "all n,m negb(n<m)=(m<=n)")
(assume "n" "m")
(simp "<-" "NatNegbLeEqLt")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatNegbLtEqLe")

;; Properties of AllBNat

;; We have extensionality of AllBNat:

;; AllBNatExt
(set-goal (rename-variables (term-to-pure-ext-formula (pt "AllBNat"))))

;; allnc n^,n^0(
;;      EqPNat n^ n^0 -> 
;;      allnc ws^,ws^0(
;;       allnc n^1,n^2(EqPNat n^1 n^2 -> EqPBoole(ws^ n^1)(ws^0 n^2)) -> 
;;       EqPBoole(AllBNat n^ ws^)(AllBNat n^0 ws^0)))

(assume "n^1" "n^2" "n1=n2" "ws^1" "ws^2" "ExtHyp")
(elim "n1=n2")
;; 3,4
(ng #t)
(use "EqPBooleTrue")
;; 4
(assume "n^3" "n^4" "n3=n4" "IH")
(ng #t)
(assert "AllBNat n^3 ws^1 eqd AllBNat n^4 ws^2")
 (use "EqPBooleToEqD")
 (use "IH")
(assume "EqDAllBNatHyp")
(simp "EqDAllBNatHyp")
(assert "ws^1 n^3 eqd ws^2 n^4")
 (use "EqPBooleToEqD")
 (use "ExtHyp")
 (use "n3=n4")
(assume "EqDwsHyp")
(simp "EqDwsHyp")
(use "EqPBooleRefl")
(use "BooleIfTotal")
(use "EqPBooleToTotalRight" (pt "AllBNat n^3 ws^1"))
(use "IH")
(use "EqPBooleToTotalRight" (pt "ws^1 n^3"))
(use "ExtHyp")
(use "n3=n4")
(use "TotalBooleFalse")
;; Proof finished.
;; (cp)
(save "AllBNatExt")

(animate "EqPBooleRefl")
;; ok, computation rule cEqPBooleRefl -> [w0]w0 added
(animate "EqPBooleToTotalRight")
;; ok, computation rule cEqPBooleToTotalRight -> [w0]w0 added

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,ws](Rec nat=>boole)n True([n0,w][if w (ws n0) False])

;; AllBNatExtEqD
(set-goal "allnc n^(TotalNatNc n^ -> 
 allnc ws^,ws^0(
  allnc n^0(TotalNatNc n^0 -> ws^ n^0 eqd ws^0 n^0) ->
  AllBNat n^ ws^ eqd AllBNat n^ ws^0))")
(assume "n^" "Tn" "ws^1" "ws^2" "ExtHyp")
(elim "Tn")
;; 3,4
(ng #t)
(use "InitEqD")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(simp "IH")
(simp "ExtHyp")
(use "InitEqD")
(use "Tn1")
;; Proof finished.
;; (cp)
(save "AllBNatExtEqD")

;; Same for nc

;; AllBNatTotalNc
(set-goal (rename-variables (term-to-totalnc-formula (pt "AllBNat"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc ws^(
;;       allnc n^0(TotalNatNc n^0 -> TotalBooleNc(ws^ n^0)) -> 
;;       TotalBooleNc(AllBNat n^ ws^)))

(assume "n^" "Tn" "ws^" "Tws")
(elim "Tn")
;; 3,4
(ng #t)
(use "TotalBooleNcTrue")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(elim "IH")
(ng #t)
(use "Tws")
(use "Tn1")
(ng #t)
(use "TotalBooleNcFalse")
;; Proof finished.
;; (cp)
(save "AllBNatTotalNc")

;; AllBNatExtNc
(set-goal (rename-variables (term-to-pure-extnc-formula (pt "AllBNat"))))

;; allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc ws^,ws^0(
;;       allnc n^1,n^2(EqPNatNc n^1 n^2 -> EqPBooleNc(ws^ n^1)(ws^0 n^2)) -> 
;;       EqPBooleNc(AllBNat n^ ws^)(AllBNat n^0 ws^0)))

(assume "n^1" "n^2" "n1=n2" "ws^1" "ws^2" "ExtHyp")
(elim "n1=n2")
;; 3,4
(ng #t)
(use "EqPBooleNcTrue")
;; 4
(assume "n^3" "n^4" "n3=n4" "IH")
(ng #t)
(assert "AllBNat n^3 ws^1 eqd AllBNat n^4 ws^2")
 (use "EqPBooleNcToEqD")
 (use "IH")
(assume "EqDAllBNatHyp")
(simp "EqDAllBNatHyp")
(assert "ws^1 n^3 eqd ws^2 n^4")
 (use "EqPBooleNcToEqD")
 (use "ExtHyp")
 (use "n3=n4")
(assume "EqDwsHyp")
(simp "EqDwsHyp")
(use "EqPBooleNcRefl")
(use "BooleIfTotal")
(use "EqPBooleNcToTotalNcRight" (pt "AllBNat n^3 ws^1"))
(use "IH")
(use "EqPBooleToTotalRight" (pt "ws^1 n^3"))
(use "ExtHyp")
(use "n3=n4")
(use "TotalBooleFalse")
;; Proof finished.
;; (cp)
(save "AllBNatExtNc")

;; AllBNatIntro
(set-goal "allnc ws,n(all n1(n1<n -> ws n1) -> AllBNat n ws)")
(assume  "ws")
(ind)
(strip)
(use "Truth")
(assume "n" "IH" "Hyp")
(ng)
(simp "IH")
;; 8,9
(ng)
(use "Hyp")
(use "Truth")
;; 9
(assume "n1" "n1<n")
(use "Hyp")
(use "NatLtTrans" (pt "n"))
(use "n1<n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "AllBNatIntro")

;; AllBNatElim
(set-goal "allnc ws,n(AllBNat n ws -> all n1(n1<n -> ws n1))")
(assume  "ws")
(ind)
(assume "Useless" "n1" "Absurd")
(use "EfAtom")
(use "Absurd")
(ng)
(assume "n" "IH")
(cases (pt "AllBNat n ws"))
(ng)
(assume "AllBNatHyp" "wsn" "n1" "n1<Sn")
(use "NatLtSuccCases" (pt "n1") (pt "n"))
(use "n1<Sn")
(use "IH")
(use "AllBNatHyp")
(assume "n1=n")
(simp "n1=n")
(use "wsn")
;; 10
(ng)
(assume "Useless1" "Absurd" "n1" "Useless2")
(use "EfAtom")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "AllBNatElim")

;; For ExBNat
(add-computation-rules
 "ExBNat 0 nat=>boole" "False"
 "ExBNat(Succ n)ws" "[if (ws n) True (ExBNat n ws)]")

(set-totality-goal "ExBNat")
(fold-alltotal)
(ind)
;; 3,4
(strip)
(use "TotalVar")
;; 4
(assume "n" "IH" "ws^" "Tws")
(ng #t)
(use "BooleIfTotal")
(use "Tws")
(use "TotalVar")
(use "TotalVar")
(use "IH")
(use "Tws")
;; Proof finished.
;; (cp)
(save-totality)

;; For efficiency reasons if is preferred over orb (i.e., over the
;; term (ExBNat n nat=>boole orb ws n), since it computes
;; its arguments only when necessary.

;; ExBNatIntro
(set-goal "all ws,m,n(m<n -> ws m -> ExBNat n ws)")
(assume "ws" "m")
(ind)
;; 3,4
(assume "Absurd" "Useless")
(ng #t)
(use "Absurd")
;; 4
(assume "n" "IH" "m<n+1" "ws m")
(ng #t)
(cases (pt "ws n"))
(assume "Useless")
(use "Truth")
(assume "ws n -> F")
(ng #t)
(use "IH" (pt "m"))
(use "NatLtSuccCases" (pt "m") (pt "n"))
(use "m<n+1")
(assume "m<n")
(use "m<n")
(assume "m=n")
(use "EfAtom")
(use "ws n -> F")
(simp "<-" "m=n")
(use "ws m")
(use "ws m")
;; Proof finished.
;; (cp)
(save "ExBNatIntro")

;; IfOrbEq
(set-goal "all w1,w2 [if w1 True w2]=(w2 orb w1)")
(cases)
(assume "w")
(use "Truth")
(assume "w")
(use "Truth")
;; Proof finished.
;; (cp)
(save "IfOrbEq")

;; ExBNatElim
(set-goal "all ws,n(ExBNat n ws -> allnc m(m<n -> ws m -> Pvar) -> Pvar)")
(assume "ws")
(ind)
;; 3,4
(ng #t)
(assume "Absurd" "AllHyp")
(use "AllHyp" (pt "Zero"))
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "n" "IH")
(ng #t)
(simp "IfOrbEq")
(assume "OrHyp" "AllHyp")
(use "OrElim" (pt "ExBNat n ws") (pt "ws n"))
(use "OrHyp")
(assume "ExbHyp")
(use "IH")
(use "ExbHyp")
(assume "m" "m<n")
(use "AllHyp")
(use "NatLtTrans" (pt "n"))
(use "m<n")
(use "Truth")
;; 16
(assume "ws n")
(use "AllHyp" (pt "n"))
(use "Truth")
(use "ws n")
;; Proof finished.
;; (cp)
(save "ExBNatElim")

;; ExBNatToExNc
(set-goal "all ws,n(ExBNat n ws -> exnc m(m<n andnc ws m))")
(assume "ws" "n" "ExBNatHyp")
(use "ExBNatElim" (pt "ws") (pt "n"))
(use "ExBNatHyp")
(assume "m" "m<n" "ws m")
(intro 0 (pt "m"))
(split)
(use "m<n")
(use "ws m")
;; Proof finished.
;; (cp)
(save "ExBNatToExNc")

;; ExNcToExBNat
(set-goal "all ws,n(exnc m(m<n andnc ws m) -> ExBNat n ws)")
(assume "ws" "n" "ExNcHyp")
(by-assume "ExNcHyp" "m" "mProp")
(use "ExBNatIntro" (pt "m"))
(use "mProp")
(use "mProp")
;; Proof finished.
;; (cp)
(save "ExNcToExBNat")

;; We have extensionality of NatLeast:

;; NatLeastExt
(set-goal (rename-variables (term-to-pure-ext-formula (pt "NatLeast"))))

;; allnc n^,n^0(
;;      EqPNat n^ n^0 -> 
;;      allnc ws^,ws^0(
;;       allnc n^1,n^2(EqPNat n^1 n^2 -> EqPBoole(ws^ n^1)(ws^0 n^2)) -> 
;;       EqPNat(NatLeast n^ ws^)(NatLeast n^0 ws^0)))

(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 3,4
(ng #t)
(strip)
(intro 0)
;; 4
(assume "n^3" "n^4" "n3=n4" "IH" "ws^1" "ws^2" "EqPHyp")
(ng #t)
(use "BooleIfEqP")
(use "EqPHyp")
(intro 0)
(intro 0)
(intro 1)
(use "IH")
(ng #t)
(assume "n^5" "n^6" "n5=n6")
(use "EqPHyp")
(intro 1)
(use "n5=n6")
;; Proof finished.
;; (cp)
(save "NatLeastExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)=>nat)n([ws]0)
;;  ([n0,((nat=>boole)=>nat),ws]
;;    (cBooleIfEqP nat)(ws 0)0(Succ(((nat=>boole)=>nat)([n1]ws(Succ n1)))))

(animate "BooleIfEqP")
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)=>nat)n([ws]0)
;;  ([n0,((nat=>boole)=>nat),ws]
;;    [if (ws 0) 0 (Succ(((nat=>boole)=>nat)([n1]ws(Succ n1))))])

;; NatLeastExtEqD
(set-goal "allnc n^(TotalNatNc n^ -> 
 allnc ws^,ws^0(
  allnc n^0(TotalNatNc n^0 -> ws^ n^0 eqd ws^0 n^0) ->
  NatLeast n^ ws^ eqd NatLeast n^ ws^0))")
(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "InitEqD")
;; 4
(assume "n^1" "Tn1" "IH" "ws^1" "ws^2" "EqDHyp")
(ng #t)
(simp "EqDHyp")
(inst-with-to "IH" (pt "[n]ws^1(Succ n)") (pt "[n]ws^2(Succ n)") "Inst")
(simp "Inst")
(use "InitEqD")
(assume "n^2" "Tn2")
(use "EqDHyp")
(use "TotalNatSucc")
(use "Tn2")
(use "TotalNatNcZero")
;; Proof finished.
;; (cp)
(save "NatLeastExtEqD")

;; Same for nc

;; Need BooleIfTotalNc (to be added to ets.scm)

;; BooleIfTotalNc
(set-goal "allnc w^(
 TotalBooleNc w^ -> 
 allnc alpha^0,alpha^1(
  TotalNc alpha^0 -> TotalNc alpha^1 -> TotalNc[if w^ alpha^0 alpha^1]))")
(assume "w^" "Tb" "alpha^1" "alpha^2" "Tx1" "Tx2")
(elim "Tb")
(use "Tx1")
(use "Tx2")
;; Proof finished.
;; (cp)
(save "BooleIfTotalNc")

;; NatLeastTotalNc
(set-goal (rename-variables (term-to-totalnc-formula (pt "NatLeast"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc ws^(
;;       allnc n^0(TotalNatNc n^0 -> TotalBooleNc(ws^ n^0)) -> 
;;       TotalNatNc(NatLeast n^ ws^)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "TotalNatNcZero")
;; 4
(assume "n^1" "Tn1" "IH" "ws^" "Tws")
(ng #t)
(use "BooleIfTotalNc")
(use "Tws")
(use "TotalNatNcZero")
(use "TotalNatNcZero")
(use "TotalNatNcSucc")
(use "IH")
(ng #t)
(assume "n^2" "Tn2")
(use "Tws")
(use "TotalNatSucc")
(use "Tn2")
;; Proof finished.
;; (cp)
(save "NatLeastTotalNc")

;; NatLeastExtNc
(set-goal (rename-variables (term-to-pure-extnc-formula (pt "NatLeast"))))

;; allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc ws^,ws^0(
;;       allnc n^1,n^2(EqPNatNc n^1 n^2 -> EqPBooleNc(ws^ n^1)(ws^0 n^2)) -> 
;;       EqPNatNc(NatLeast n^ ws^)(NatLeast n^0 ws^0)))

(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 3,4
(ng #t)
(strip)
(intro 0)
;; 4
(assume "n^3" "n^4" "n3=n4" "IH" "ws^1" "ws^2" "EqPHyp")
(ng #t)
(use "BooleIfEqP")
(use "EqPHyp")
(intro 0)
(intro 0)
(intro 1)
(use "IH")
(ng #t)
(assume "n^5" "n^6" "n5=n6")
(use "EqPHyp")
(intro 1)
(use "n5=n6")
;; Proof finished.
;; (cp)
(save "NatLeastExtNc")

;; NatLeastBound
(set-goal "all n,ws NatLeast n ws<=n")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "ws")
(ng #t)
(cases (pt "ws 0"))
(assume "ws 0")
(ng #t)
(use "Truth")
(assume "ws 0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeastBound")

;; NatLeastLeIntro
(set-goal "all n,m,ws(ws m -> (NatLeast n ws)<=m)")
(ind)
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
(assume "ws" "g0")
(ng #t)
(simp "g0")
(use "Truth")
(assume "m" "ws" "g(Sn)")
(ng #t)
(cases 'auto)
(strip)
(use "Truth")
(strip)
(ng #t)
(use-with "IH" (pt "m") (pt "[nat](ws(Succ nat))") "?")
(ng #t)
(use "g(Sn)")
;; Proof finished.
;; (cp)
(save "NatLeastLeIntro")

;; NatLeastLtElim
(set-goal "all n,ws(NatLeast n ws<n -> ws(NatLeast n ws))")
(ind)
(assume "ws")
(ng #t)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "IH" "ws")
(ng #t)
(cases (pt "ws 0"))
(assume "g0" "Useless")
(use "g0")
(assume "ws 0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeastLtElim")

;; PropNatLeast
(set-goal "all n,m,ws(m<=n -> ws m -> ws(NatLeast n ws))")
(ind)
;; 2,3
(ng #t)
(assume "m" "ws" "m=0")
(simp "m=0")
(assume "ws0")
(use "ws0")
;; 3
(assume "n" "IH")
(ng #t)
(cases)
;; Zero
(assume "ws" "Useless" "g0")
(simp "g0")
(use "g0")
;; Succ
(assume "m" "ws" "m<=n" "gSm")
(inst-with-to "IH" (pt "m") (pt "[n0]ws(Succ n0)") "m<=n" "gSm" "Inst")
(ng)
(cases (pt "ws Zero"))
(assume "g0")
(use "g0")
(assume "Useless")
(ng #t)
(use "Inst")
;; Proof finished.
;; (cp)
(save "PropNatLeast")

;; EqPNatNcPlus
(set-goal "allnc n^1,n^2,m^(
 TotalNat m^ -> EqPNat n^1 n^2 -> EqPNatNc(n^1+m^)(n^2+m^))")
(assume "n^1" "n^2" "m^" "Tm")
(elim "Tm")
;; 3,4
(ng #t)
(assume "n1=n2")
(use "n1=n2")
;; 4
(assume "m^1" "Tm1" "IH" "n1=n2")
(ng #t)
(use "EqPNatNcSucc")
(use "IH")
(use "n1=n2")
;; Proof finished.
;; (cp)
(save "EqPNatNcPlus")

;; For use in NatLeastUpExt we add NatNatTotalToExt NatNatExtToTotal
;; NatNatBooleTotalToExt NatNatNatTotalToExt.  Same for Nc.

;; NatNatTotalToExt
(set-goal "all ns allnc n^,n^0(EqPNat n^ n^0 -> EqPNat(ns n^)(ns n^0))")
(use
 "AllTotalIntro"
 (py "ns")
 (make-cterm
  (pv "ns^")
  (pf "allnc n^,n^0(EqPNat n^ n^0 -> EqPNat(ns^ n^)(ns^ n^0))"))
 "?")
(assume "ns^" "Tg" "n^1" "n^2" "EqPn1n2")
;; (inst-with-to "EqPNatNcToEqD" (pt "n^1") (pt "n^2") "EqPn1n2" "n1=n2")
(simp (pf "n^1 eqd n^2"))
(use "EqPNatRefl")
(use "Tg")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "EqPNatRefl")
(use "EqPNatToTotalRight" (pt "n^1"))
(use "EqPn1n2")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "NatNatTotalToExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [ns,n]
;;  cEqPNatRefl(ns(cEqPNatToTotalLeft(cEqPNatRefl(cEqPNatToTotalRight n))))

;; NatNatTotalToExtNc
(set-goal "allnc ns,n^,n^0(EqPNatNc n^ n^0 -> EqPNatNc(ns n^)(ns n^0))")
(use-with
 "AllncTotalIntro"
 (py "ns")
 (make-cterm
  (pv "ns^")
  (pf "allnc n^,n^0(EqPNatNc n^ n^0 -> EqPNatNc(ns^ n^)(ns^ n^0))"))
 "?")
(assume "ns^" "Tns" "n^1" "n^2" "EqPn1n2")
(inst-with-to "EqPNatNcToEqD" (pt "n^1") (pt "n^2") "EqPn1n2" "n1=n2")
(simp "<-" "n1=n2")
(use "EqPNatNcRefl")
(use "Tns")
(use "EqPNatNcToTotalNcLeft" (pt "n^2"))
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "NatNatTotalToExtNc")

;; NatNatExtToTotal
(set-goal "all ns(allnc n^,n^0(EqPNat n^ n^0 -> EqPNat(ns n^)(ns n^0)) ->
 all n TotalNat(ns n))")
(assume "ns" "nsExt")
(use "AllTotalIntro")
(assume "n^" "Tn")
(use "EqPNatToTotalLeft" (pt "ns n^"))
(use "nsExt")
(use "EqPNatRefl")
(use "Tn")
;; Proof finished.
;; (cp)
(save "NatNatExtToTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [ns,ns0,n]cEqPNatToTotalLeft(ns0(cEqPNatRefl n))

;; NatNatExtToTotalNc
(set-goal
 "allnc ns^(allnc n^,n^0(EqPNatNc n^ n^0 -> EqPNatNc(ns^ n^)(ns^ n^0)) ->
 allnc n TotalNatNc(ns^ n))")
(assume "ns^" "nsExt")
(use "AllncTotalIntro")
(assume "n^" "Tn")
(use "EqPNatNcToTotalNcLeft" (pt "ns^ n^"))
(use "nsExt")
(use "EqPNatNcRefl")
(use "Tn")
;; Proof finished.
;; (cp)
(save "NatNatExtToTotalNc")

;; NatNatBooleTotalToExt
(set-goal "all nat=>nat=>boole allnc n^,n^0(EqPNat n^ n^0 -> allnc n^1,n^2(
 EqPNat n^1 n^2 -> 
 EqPBoole((nat=>nat=>boole)n^ n^1)((nat=>nat=>boole)n^0 n^2)))")
(use
 "AllTotalIntro"
 (py "nat=>nat=>boole")
 (make-cterm
  (pv "nat=>nat=>boole^")
  (pf "allnc n^,n^0(EqPNat n^ n^0 -> allnc n^1,n^2(EqPNat n^1 n^2 ->
       EqPBoole(nat=>nat=>boole^ n^ n^1)(nat=>nat=>boole^ n^0 n^2)))"))
 "?")
(assume "nat=>nat=>boole^" "Tf" "n^1" "n^2" "EqPn1n2" "n^3" "n^4" "EqPn3n4")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^3 eqd n^4"))
(use "EqPBooleRefl")
(use "Tf")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "EqPNatRefl")
(use "EqPNatToTotalRight" (pt "n^1"))
(use "EqPn1n2")
(use "EqPNatToTotalLeft" (pt "n^4"))
(use "EqPNatRefl")
(use "EqPNatToTotalRight" (pt "n^3"))
(use "EqPn3n4")
(use "EqPNatNcToEqD")
(use "EqPn3n4")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "NatNatBooleTotalToExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [(nat=>nat=>boole),n,n0]
;;  (nat=>nat=>boole)(cEqPNatToTotalLeft(cEqPNatRefl(cEqPNatToTotalRight n)))
;;  (cEqPNatToTotalLeft(cEqPNatRefl(cEqPNatToTotalRight n0)))

;; NatNatBooleTotalToExtNc
(set-goal "allnc nat=>nat=>boole,n^,n^0(EqPNatNc n^ n^0 -> allnc n^1,n^2(
 EqPNatNc n^1 n^2 -> 
 EqPBooleNc((nat=>nat=>boole)n^ n^1)((nat=>nat=>boole)n^0 n^2)))")
(use-with
 "AllncTotalIntro"
 (py "nat=>nat=>boole")
 (make-cterm
  (pv "nat=>nat=>boole^")
  (pf "allnc n^,n^0(EqPNatNc n^ n^0 -> allnc n^1,n^2(EqPNatNc n^1 n^2 ->
       EqPBooleNc(nat=>nat=>boole^ n^ n^1)(nat=>nat=>boole^ n^0 n^2)))"))
 "?")
(assume "nat=>nat=>boole^" "Tf" "n^1" "n^2" "EqPn1n2" "n^3" "n^4" "EqPn3n4")
(inst-with-to "EqPNatNcToEqD" (pt "n^1") (pt "n^2") "EqPn1n2" "n1=n2")
(simp "<-" "n1=n2")
(inst-with-to "EqPNatNcToEqD" (pt "n^3") (pt "n^4") "EqPn3n4" "n3=n4")
(simp "<-" "n3=n4")
(use "EqPBooleNcRefl")
(use "Tf")
(use "EqPNatNcToTotalNcLeft" (pt "n^2"))
(use "EqPn1n2")
(use "EqPNatNcToTotalNcLeft" (pt "n^4"))
(use "EqPn3n4")
;; Proof finished.
;; (cp)
(save "NatNatBooleTotalToExtNc")

;; NatNatNatTotalToExt
(set-goal "all nat=>nat=>nat allnc n^,n^0(EqPNat n^ n^0 -> allnc n^1,n^2(
 EqPNat n^1 n^2 -> 
 EqPNat((nat=>nat=>nat)n^ n^1)((nat=>nat=>nat)n^0 n^2)))")
(use
 "AllTotalIntro"
 (py "nat=>nat=>nat")
 (make-cterm
  (pv "nat=>nat=>nat^")
  (pf "allnc n^,n^0(EqPNat n^ n^0 -> allnc n^1,n^2(EqPNat n^1 n^2 ->
       EqPNat(nat=>nat=>nat^ n^ n^1)(nat=>nat=>nat^ n^0 n^2)))"))
 "?")
(assume "nat=>nat=>nat^" "Tf" "n^1" "n^2" "EqPn1n2" "n^3" "n^4" "EqPn3n4")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^3 eqd n^4"))
(use "EqPNatRefl")
(use "Tf")
(use "EqPNatToTotalLeft" (pt "n^2"))
(use "EqPNatRefl")
(use "EqPNatToTotalRight" (pt "n^1"))
(use "EqPn1n2")
(use "EqPNatToTotalLeft" (pt "n^4"))
(use "EqPNatRefl")
(use "EqPNatToTotalRight" (pt "n^3"))
(use "EqPn3n4")
(use "EqPNatNcToEqD")
(use "EqPn3n4")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cp)
(save "NatNatNatTotalToExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [(nat=>nat=>nat),n,n0]
;;  cEqPNatRefl
;;  ((nat=>nat=>nat)(cEqPNatToTotalLeft(cEqPNatRefl(cEqPNatToTotalRight n)))
;;   (cEqPNatToTotalLeft(cEqPNatRefl(cEqPNatToTotalRight n0))))

;; NatNatNatTotalToExtNc
(set-goal "allnc nat=>nat=>nat,n^,n^0(EqPNatNc n^ n^0 -> allnc n^1,n^2(
 EqPNatNc n^1 n^2 -> 
 EqPNatNc((nat=>nat=>nat)n^ n^1)((nat=>nat=>nat)n^0 n^2)))")
(use-with
 "AllncTotalIntro"
 (py "nat=>nat=>nat")
 (make-cterm
  (pv "nat=>nat=>nat^")
  (pf "allnc n^,n^0(EqPNatNc n^ n^0 -> allnc n^1,n^2(EqPNatNc n^1 n^2 ->
       EqPNatNc(nat=>nat=>nat^ n^ n^1)(nat=>nat=>nat^ n^0 n^2)))"))
 "?")
(assume "nat=>nat=>nat^" "Tf" "n^1" "n^2" "EqPn1n2" "n^3" "n^4" "EqPn3n4")
(inst-with-to "EqPNatNcToEqD" (pt "n^1") (pt "n^2") "EqPn1n2" "n1=n2")
(simp "<-" "n1=n2")
(inst-with-to "EqPNatNcToEqD" (pt "n^3") (pt "n^4") "EqPn3n4" "n3=n4")
(simp "<-" "n3=n4")
(use "EqPNatNcRefl")
(use "Tf")
(use "EqPNatNcToTotalNcLeft" (pt "n^2"))
(use "EqPn1n2")
(use "EqPNatNcToTotalNcLeft" (pt "n^4"))
(use "EqPn3n4")
;; Proof finished.
;; (cp)
(save "NatNatNatTotalToExtNc")

;; We have extensionality of NatLeastUp:

;; NatLeastUpExt
(set-goal (rename-variables (term-to-pure-ext-formula (pt "NatLeastUp"))))

;; allnc n^,n^0(
;;      EqPNat n^ n^0 -> 
;;      allnc n^1,n^2(
;;       EqPNat n^1 n^2 -> 
;;       allnc ws^,ws^0(
;;        allnc n^3,n^4(EqPNat n^3 n^4 -> EqPBoole(ws^ n^3)(ws^0 n^4)) -> 
;;        EqPNat(NatLeastUp n^ n^1 ws^)(NatLeastUp n^0 n^2 ws^0))))

(assume "n^1" "n^2" "n1=n2" "n^3" "n^4" "n3=n4" "ws^1" "ws^2" "EqPws")
(ng)
(use "BooleIfEqP")
;; 4-6
(use "NatNatBooleTotalToExt")
(use "n1=n2")
(use "n3=n4")
;; 5
(use "NatNatNatTotalToExt")
(use "NatLeastExt")
(use "NatNatNatTotalToExt")
(use "n3=n4")
(use "n1=n2")
(ng)
(assume "n^5" "n^6" "n5=n6")
(use "EqPws")
(use "NatNatNatTotalToExt")
(use "n5=n6")
(use "n1=n2")
(use "n1=n2")
;; 6
(intro 0)
;; Proof finished.
;; (cp)
(save "NatLeastUpExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n,n0,ws]
;;  [if (cNatNatBooleTotalToExt NatLe n n0)
;;    (cNatNatNatTotalToExt NatPlus
;;    (cNatLeastExt(cNatNatNatTotalToExt NatMinus n0 n)
;;     ([n1]ws(cNatNatNatTotalToExt NatPlus n1 n)))
;;    n)
;;    0]

;; Same for nc

;; NatLeastUpTotalNc
(set-goal (rename-variables (term-to-totalnc-formula (pt "NatLeastUp"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc n^0(
;;       TotalNatNc n^0 -> 
;;       allnc ws^(
;;        allnc n^1(TotalNatNc n^1 -> TotalBooleNc(ws^ n^1)) -> 
;;        TotalNatNc(NatLeastUp n^ n^0 ws^))))

(assume "n^1" "Tn1" "n^2" "Tn2" "ws^" "Tws")
(ng #t)
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tn1")
(use "Tn2")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn2")
(use "Tn1")
(ng #t)
(assume "n^3" "Tn3")
(use "Tws")
(use "NatPlusTotal")
(use "Tn3")
(use "Tn1")
(use "Tn1")
(use "TotalNatZero")
;; Proof finished.
;; (cp)
(save "NatLeastUpTotalNc")

;; NatLeastUpExtNc
(set-goal (rename-variables (term-to-pure-extnc-formula (pt "NatLeastUp"))))

;; allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc n^1,n^2(
;;       EqPNatNc n^1 n^2 -> 
;;       allnc ws^,ws^0(
;;        allnc n^3,n^4(EqPNatNc n^3 n^4 -> EqPBooleNc(ws^ n^3)(ws^0 n^4)) -> 
;;        EqPNatNc(NatLeastUp n^ n^1 ws^)(NatLeastUp n^0 n^2 ws^0))))

(assume "n^1" "n^2" "n1=n2" "n^3" "n^4" "n3=n4" "ws^1" "ws^2" "EqPws")
(ng)
(use "BooleIfEqPNc")
;; 4-6
(use "NatNatBooleTotalToExtNc")
(use "n1=n2")
(use "n3=n4")
;; 5
(use "NatNatNatTotalToExtNc")
(use "NatLeastExtNc")
(use "NatNatNatTotalToExtNc")
(use "n3=n4")
(use "n1=n2")
(ng)
(assume "n^5" "n^6" "n5=n6")
(use "EqPws")
(use "NatNatNatTotalToExtNc")
(use "n5=n6")
(use "n1=n2")
(use "n1=n2")
;; 6
(intro 0)
;; Proof finished.
;; (cp)
(save "NatLeastUpExtNc")

;; We postpone proofs of the NatLeastUpBound NatLeastUpLBound
;; NatLeastUpLeIntro NatLeastUpLtElim NatLeastUpZero since they use
;; monotonicity properties of NatLt which are only proved later.

;; We add some further rewrite rules and theorems.  The order is
;; somewhat delicate, since the proofs can depend on which rewrite
;; rules are present, and also which program constants have been proved
;; to be total.

(set-goal "all n,m n<=m+n")
(ind)
  (assume "n")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<=m+n" "True")

(set-goal "all n,m (n+m<n)=False")
(assert "all l,l0(l+l0<l -> F)")
 (ind)
 (assume "l" "Absurd")
 (use "Absurd")
 (assume "l" "IH")
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "l0")
 (ng #t)
 (assume "Succ(l+l0)<l")
 (use "IH" (pt "l0"))
 (use "NatLtTrans" (pt "Succ(l+l0)"))
 (use "Truth")
 (use "Succ(l+l0)<l")
(assume "Prop" "n" "m")
(use "AtomFalse")
(use "Prop")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m<n" "False")

(set-goal "all n Pred n<=n")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Pred n<=n" "True")

(set-goal "all n 0--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "0--n" "0")

(set-goal "all n,m n--m<=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "NatLeTrans" (pt "n--m"))
(use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n--m<=n" "True")

(set-goal "all n,m n+m--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n+m--m" "n")

(set-goal "all n,m m+n--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "m+n--m" "n")

(set-goal "all n,m n*Pred m=n*m--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n*Pred m" "n*m--n")

(set-goal "all n,m Pred m*n=m*n--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Pred m*n" "m*n--n")

(set-goal "all n,m,l n--m--l=n--(m+l)")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n--m--l" "n--(m+l)")

(set-goal "all n,m,l n*(m--l)=n*m--n*l")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n*(m--l)" "n*m--n*l")

(set-goal "all n,m,l (m--l)*n=m*n--l*n")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "(m--l)*n" "m*n--l*n")

;; SuccNatMinus
(set-goal "all m,n(m<=n -> Succ(n--m)=Succ(n)--m)")
(ind)
(assume "n" "Useless")
(use "Truth")
(assume "m" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n")
(use "IH")
;; Proof finished.
;; (cp)
(save "SuccNatMinus")

;; NatLeMonPlus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n+l<=m+l0)")
(assume "n" "m")
(ind)
(ind)
(assume "n<=m" "Useless")
(use "n<=m")
(assume "l0" "IHl0")
(assume "n<=m" "Useless")
(use "NatLeTrans" (pt "m+l0"))
(use "IHl0")
(use "n<=m")
(use "Truth")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(use "IHl")
;; Proof finished.
;; (cp)
(save "NatLeMonPlus")

;; Added 2024-10-04

;; NatLtMonPlus1
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> n+l<m+l0)")
(ind)
(cases)
(assume "l" "l0")
(ng #t)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m" "l" "l0" "Useless" "l<=l0")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "l0"))
(use "l<=l0")
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(cases)
(assume "l" "l0")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtMonPlus1")

;; NatLtMonPlus2
(set-goal "all n,m,l,l0(n<=m -> l<l0 -> n+l<m+l0)")
(assume "n" "m")
(ind)
(cases)
(ng #t)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "l" "n<=m" "Useless")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "m"))
(use "n<=m")
(ng #t)
(use "Truth")
(assume "l" "IH")
(ng #t)
(cases)
(assume "n<=m")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtMonPlus2")

;; NatLtTimesPos
(set-goal "all n,l,m(0<n -> m<l -> m<n*l)")
(cases)
(search)
(assume "n" "l" "m" 2 3)
(ng)
(simp (pf "m=0+m"))
(use "NatLtMonPlus2")
(use "Truth")
(use 2)
(use "Truth")
;; (cp)
(save "NatLtTimesPos")

;; NatLeTimesPos
(set-goal "all n,l,m(0<n -> m<=l -> m<=n*l)")
(cases)
(strip)
(use "EfAtom")
(use 1)
(strip)
(ng)
(simp (pf "m=0+m"))
(use "NatLeMonPlus")
(use "Truth")
(use 2)
(use "Truth")
;; (cp)
(save "NatLeTimesPos")

;; NatLtMonTimes
(set-goal "all n1,n2,m1,m2(n1<n2-> m1<m2 -> n1*m1<n2*m2)")
(ind)
(strip)
(use "NatLtTimesPos")
(use 1)
(use "NatLeLtTrans" (pt "m1"))
(use "Truth")
(use 2)
(assume "n1" 1)
(ind)
(search)
(assume "n2" 2 "m1" "m2" 3 4)
(ng)
(use "NatLtMonPlus1")
(use 1)
(use 3)
(use 4)
(use "NatLtToLe")
(use 4)
;; (cp)
(save "NatLtMonTimes")

;; NatLeMonTimes
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n*l<=m*l0)")
(assume "n" "m")
(ind)
(ind)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l0" "IHl0")
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "l0" "n<=m" "l<=l0")
(ng)
(use "NatLeMonPlus")
(use "IHl")
(use "n<=m")
(use "l<=l0")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "NatLeMonTimes")

;; NatLeMonPred
(set-goal "all n,m(n<=m -> Pred n<=Pred m)")
(cases)
(assume "m" "Useless")
(use "Truth")
(assume "n")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<=m")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "NatLeMonPred")

;; NatLeMonMinus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n--l0<=m--l)")
(assume "n" "m" "l" "l0" "n<=m" "l<=l0")
(use "NatLeTrans" (pt "m--l0"))
;; ?_3: n--l0<=m--l0
(ind (pt "l0"))
(use "n<=m")
(assume "nat" "IH")
(ng #t)
(use "NatLeMonPred")
(use "IH")
;; ?_4: m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
;; (cp)
(save "NatLeMonMinus")

;; NatLeMonMinusLeft
(set-goal "all n,m,l(m<=l -> m--n<=l--n)")
(ind)
(ng #t)
(assume "m" "l" "m<=l")
(use "m<=l")
(assume "n" "IH")
(cases)
(ng #t)
(strip)
(use "Truth")
(assume "m")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeMonMinusLeft")

;; NatLeMonSquare
(set-goal "all n,m(n<=m -> n*n<=m*m)")
(strip)
(use "NatLeMonTimes")
(auto)
;; (cp)
(save "NatLeMonSquare")

;; NatLeMonSquareInv
(set-goal "all n,m(n*n<=m*m -> n<=m)")
(strip)
(use "NatNotLtToLe")
(assume 2)
(assert "n*n<n*n")
(use "NatLeLtTrans" (pt "m*m"))
(use 1)
(use "NatLtMonTimes")
(use 2)
(use 2)
(search)
;; (cp)
(save "NatLeMonSquareInv")

;; NatLeSquarePred
(set-goal "all n(2<n -> n<=Pred n*Pred n)")
(cases)
(search)
(cases)
(search)
(cases)
(search)
(assume "n" 1)
(ng)
(use "NatLeTrans" (pt "n*n+n+n+n+n"))
(use "Truth")
(use "Truth")
;; (cp)
(save "NatLeSquarePred")

;; NatSuccPlusLtTimes
(set-goal "all n,m(2<n -> 2<m -> Succ(m+n)<n*m)")
(cases)
(search)
(cases)
(strip)
(use "EfAtom")
(use 1)
(cases)
(strip)
(use "EfAtom")
(use 1)
(assume "n")
(cases)
(search)
(cases)
(strip)
(use "EfAtom")
(use 2)
(cases)
(strip)
(use "EfAtom")
(use 2)
(assume "m" 1 2)
(ng)
(use "NatLeLtTrans" (pt "Succ(n*m+m+m+m+n+n+n)"))
(use "NatLeTrans" (pt "n*m+m+m+m+n+n+n"))
(ng)
(use "NatLeTrans" (pt "n*m+m+m+m"))
(use "Truth")
(use "NatLeTrans" (pt "n*m+m+m+m+n"))
(auto)
;; (cp)
(save "NatSuccPlusLtTimes")

;; NatLePlusToLeMax
(set-goal "all n,m,l,l0(l0+l0<=l -> l<=n+m -> l0<=n max m)")
(assume "n" "m" "l" "l0" "2l0<=n" "lBd")
(assert "l0+l0<=n+m")
(use "NatLeTrans" (pt "l"))
(use "2l0<=n")
(use "lBd")
;; Assertion proved.
(assume "A1")
(use "NatNotLtToLe")
(assume "nmaxm<l0")
(assert "n+m<n+m")
(use "NatLtLeTrans" (pt "l0+l0"))
(use "NatLeLtTrans" (pt "(n max m)+(n max m)"))
(use "NatLeMonPlus")
(use "NatMaxUB1")
(use "NatMaxUB2")
(use "NatLtMonPlus1")
(use "nmaxm<l0")
(use "NatLtToLe")
(use "nmaxm<l0")
(use "A1")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "NatLePlusToLeMax")

;; NatLtPlusToLtMax
(set-goal "all n,m,l,l0(l0+l0<=l -> l<n+m -> l0<n max m)")
(assume "n" "m" "l" "l0" "2l0<=l" "lBd")

(assert "l0*2<n+m")
(use "NatLeLtTrans" (pt "l"))
(use "2l0<=l")
(use "lBd")
;; Assertion proved.
(assume "A1")

(assert "n+m<=(n max m)*2")
(use "NatLeMonPlus")
(use "NatMaxUB1")
(use "NatMaxUB2")
;; Assertion proved.
(assume "A2")

(use "NatLtTimesCancelR" (pt "Succ(Succ Zero)"))
(use "Truth")
(use "NatLtLeTrans" (pt "n+m"))
(use "A1")
(use "A2")
;; Proof finished.
;; (cp)
(save "NatLtPlusToLtMax")

;; End of additions 2024-10-04

;; NatLeMonMax
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n max l<=m max l0)")
(ind)
;; 2,3
(assume "m")
(cases)
(strip)
(use "Truth")
(assume "n" "l" "Useless" "Sn<=l")
(ng)
(use "NatLeTrans" (pt "l"))
(use "Sn<=l")
(use "NatMaxUB2")
;; 3
(assume "n" "IH")
(cases)
;; 13,14
(assume "l" "l0" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n1")
(cases)
(cases)
(ng)
(assume "n<=n1" "Useless")
(use "n<=n1")
(ng)
(assume "n2" "n<=n1" "Useless")
(use "NatLeTrans" (pt "n1"))
(use "n<=n1")
(use "NatMaxUB1")
(assume "n2")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeMonMax")

;; NatLtMax
(set-goal "all n,m,l(l+l<n+m -> l<n max m)")
(assume "n" "m" "l" "LtHyp")
(use "NatNotLeToLt")
(assume "LeHyp")

(assert "n<=l")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB1")
(use "LeHyp")
(assume "n<=l")

(assert "m<=l")
(use "NatLeTrans" (pt "n max m"))
(use "NatMaxUB2")
(use "LeHyp")
(assume "m<=l")

(assert "n+m<=l+l")
(use "NatLeMonPlus")
(auto)
(assume "n+m<=l+l")

(assert "l+l<l+l")
(use "NatLtLeTrans" (pt "n+m"))
(auto)
;; Proof finished.
;; (cp)
(save "NatLtMax")

;; ;; NatPlusMinus removed: it is the same as NatPlusMinusAssoc
;; No, it operates differently
;; NatPlusMinus
(set-goal "all n,m,l(l<=m -> n+(m--l)=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=m")
(ng #t)
(assert "all l0,l1(0<l1 -> l0+Pred l1=Pred(l0+l1))")
 (assume "l0")
 (cases)
 (assume "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "l1" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=m")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=m")
;; Proof finished.
;; (cp)
(save "NatPlusMinus")

;; NatMinusPlus
(set-goal "all n,m,l(l<=n -> n--l+m=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=n")
(ng #t)
(assert "all l1,l0(0<l0 -> Pred l0+l1=Pred(l0+l1))")
 (assume "l1")
 (cases)
 (assume "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "l0" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=n")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=n")
;; Proof finished.
;; (cp)
(save "NatMinusPlus")

;; NatPlusMinusMinus
(set-goal "all n,m,l(n<=m -> m<=l -> m--n+(l--m)=l--n)")
(assume "n" "m" "l" "n<=m" "m<=l")
(simp "NatPlusMinus")
(simp "NatMinusPlus")
(simp "<-" "NatPlusMinusAssoc")
(ng #t)
(use "Truth")
(use "NatLeTrans" (pt "m"))
(use "n<=m")
(use "m<=l")
(use "n<=m")
(use "m<=l")
;; Proof finished.
;; (cp)
(save "NatPlusMinusMinus")

;; NatMinusPlusEq
(set-goal "all n,m(m<=n -> n--m+m=n)")
(assume "n" "m" "m<=n")
(simp "NatMinusPlus")
(use "Truth")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "NatMinusPlusEq")

;; NatMinusEq
(set-goal "all n1,m1,n2,m2(m1<=n1 -> m2+n1=m1+n2 -> n1--m1=n2--m2)")
(assume "n1" "m1" "n2" "m2" "m1<=n1" "EqH")
(assert "m2<=n2")
(use "NatLePlusCancelR" (pt "n1"))
(simp "EqH")
(simp "NatPlusComm")
(use "NatLeMonPlus")
(use "Truth")
(use "m1<=n1")
;; Assertion proved.
(assume "m2<=n2")
(use "NatPlusCancelR" (pt "m2"))
(simp "NatMinusPlusEq")
(simp "NatMinusPlus")
(simp "NatPlusComm")
(simp "EqH")
(use "Truth")
(use "m1<=n1")
(use "m2<=n2")
;; Proof finished.
;; (cp)
(save "NatMinusEq")

;; NatMinusMinus
(set-goal  "all n,m,l(l<=m -> m<=n+l -> n--(m--l)=n+l--m)")
(assume "n")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "m" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m" "IHm")
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "l<=m" "m<=n+l")
(ng)
(use "IHm")
(use "l<=m")
(use "m<=n+l")
;; Proof finished.
;; (cp)
(save "NatMinusMinus")

;; NatLtMonMinusLeft
(set-goal "all n,m,l(m<l -> n<=m -> m--n<l--n)")
(ind)
(ng #t)
(assume "m" "l" "m<l" "Useless")
(use "m<l")
(assume "n" "IH")
(cases)
(ng #t)
(assume "l" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtMonMinusLeft")

;; NatLtMonMinusRight
(set-goal "all n,m,l(l<m -> m<=n -> n--m<n--l)")
(ind)
;; 2,3
(assume "m" "l" "l<m" "m<=0")
(assert "l<Zero")
(use "NatLtLeTrans" (pt "m"))
(use "l<m")
(use "m<=0")
;; Assertion proved.
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
;; 12,13
(assume "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 13
(assume "m")
(cases)
;; 17,18
(assume "Useless1" "Useless2")
(ng #t)
(use "NatLeLtTrans" (pt "n"))
(use "Truth")
(use "Truth")
;; 18
(assume "l")
;; ?^23:Succ l<Succ m -> Succ m<=Succ n -> Succ n--Succ m<Succ n--Succ l
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtMonMinusRight")

;; NatLtMonMinus
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> l0<=n -> n--l0<m--l)")
(assume "n" "m" "l" "l0" "n<m" "l<=l0" "l0<=n")
(use "NatLtLeTrans" (pt "m--l0"))
;; n--l0<m--l0
(use "NatLtMonMinusLeft")
(use "n<m")
(use "l0<=n")
;; m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
;; (cp)
(save "NatLtMonMinus")

;; NatMinusZero
(set-goal "all n,m(n<=m -> n--m=0)")
(ind)
;; Base
(strip)
(use "Truth")
;; Step
(assume "n" "IH")
(cases)
;; Zero
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; Succ
(assume "m" "n<=m")
(use "IH")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "NatMinusZero")

;; NatLeMinusZero
(set-goal "all n,m (n<=m)=(n--m=0)")
(ind)
;; Base
(strip)
(use "Truth")
;; Step
(assume "n" "IH")
(cases)
;; Zero
(use "Truth")
;; Succ
(assume "m")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeMinusZero")

;; NatLtMinusZero
(set-goal "all n,m (n<m)=(0<m--n)")
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

;; NatMinusPlusLe
(set-goal "all n, m n<=n--m+m")
(assume "n" "m")
(cases (pt "n<=m"))
(assume "n<=m")
(simp "NatMinusZero")
(use "n<=m")
(use "n<=m")
(assume "n</=m")
(simp "NatMinusPlusEq")
(use "Truth")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "n</=m")
;; Proof finished.
;; (cp)
(save "NatMinusPlusLe")

;; Added 2024-10-04

;; NatLtPlusMinus1
(set-goal "all n,m,l(n<=l -> l<m+n -> l--n<m)")
(assume "n" "m" "l" "n<=l" "l<n+m")
(simp "<-" "NatPlusCancelLtR" (pt "n"))
(simp "NatMinusPlusEq")
(use "l<n+m")
(use "n<=l")
;; Proof finished.
;; (cp)
(save "NatLtPlusMinus1")

;; NatLtPlusMinus2
(set-goal "all n,m,l(n<=l -> l--n<m -> l<m+n)")
(assume "n" "m" "l" "A1" "A2")
(simp (pf "l=l--n+n"))
(ng #t)
(use "A2")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "A1")
;; Proof finished.
;; (cp)
(save "NatLtPlusMinus2")

;; NatLtPlusMinus
(set-goal "all n,m,l(n<=l -> (l<m+n)=(l--n<m))")
(assume "n" "m" "l" "A1")
(use "BooleAeqToEq")
;; 3,4
(use "NatLtPlusMinus1")
(use "A1")
;; 4
(use "NatLtPlusMinus2")
(use "A1")
;; Proof finished.
;; (cp)
(save "NatLtPlusMinus")

;; NatLtMinusPlus1 (was NatLtMinusPlusEq1 NatLtMinusRToLtPlusL)
(set-goal "all n,m,l(l<n--m -> m+l<n)")
(assume "n" "m" "l" "LtH")
(use "NatLeLtCases" (pt "n") (pt "m"))
;; 3,4
(assume "n<=m")

(assert "n--m<=m--m")
(use "NatLeMonMinusLeft")
(use "n<=m")
;; Assertion proved.
(assume "LeH")

(assert "l<Zero")
(use "NatLtLeTrans" (pt "n--m"))
(use "LtH")
(use "LeH")
;; Assertion proved.
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "m<n")
(use "NatLtLeTrans" (pt "m+(n--m)"))
(use "NatLtMonPlus2")
(use "Truth")
(use "LtH")
(simp "NatPlusComm")
(simp "NatMinusPlus")
(use "Truth")
(use "NatLtToLe")
(use "m<n")
;; Proof finished.
;; (cp)
(save "NatLtMinusPlus1")

;; NatLtMinusPlus2 (was NatLtPlusLToLtMinusR)
(set-goal "all n,m,l(m+l<n -> l<n--m)")
(assume "n" "m" "l" "LtH")
(simp (pf "l=l+m--m"))
(use "NatLtMonMinusLeft")
(simp "NatPlusComm")
(use "LtH")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtMinusPlus2")

;; NatLtMinusPlus (was NatLtMinusPlusEq)
(set-goal "all n,m,l (l<n--m)=(m+l<n)")
(assume "n" "m" "l")
(use "BooleAeqToEq")
;; 3,4
(use "NatLtMinusPlus1")
;; 4
(use "NatLtMinusPlus2")
;; Proof finished.
;; (cp)
(save "NatLtMinusPlus")

;; End of additions 2024-10-04

;; NatMinusMax
(set-goal "all n,m n max m--n=m--n")
(assume "n" "m")
(use "NatLeLtCases" (pt "n") (pt "m"))
;; 3,4
(assume "Lenm")
(simp "NatMaxEq2")
(use "Truth")
(use "Lenm")
;; 4
(assume "Ltmn")
(simp "NatMaxEq1")
(simp (pf "m--n=Zero"))
(use "Truth")
(use "NatMinusZero")
(use "NatLtToLe")
(use "Ltmn")
(use "NatLtToLe")
(use "Ltmn")
;; Proof finished.
;; (cp)
(save "NatMinusMax")

(set-goal "all n,m n<=n--m+m")
(ind)
(assume "m")
(use "Truth")
(assume "n" "IH")
(cases)
(use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n<=n--m+m" "True")

;;  NatLeastUpBound
(set-goal "all n0,n,ws NatLeastUp n0 n ws<=n")
(assume "n0" "n" "ws")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(use "NatLeTrans" (pt "n--n0+n0"))
(use "NatLeMonPlus")
(use "NatLeastBound")
(use "Truth")
(simp "NatMinusPlus")
(use "Truth")
(use "n0<=n")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeastUpBound")

;; NatLeastUpLBound
(set-goal "all n0,n,ws(n0<=n -> n0<=NatLeastUp n0 n ws)")
(assume "n0" "n" "ws" "n0<=n")
(ng #t)
(simp "n0<=n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeastUpLBound")

;; NatLeastUpLeIntro
(set-goal "all n0,n,m,ws(
 n0<=m -> ws m -> NatLeastUp n0 n ws<=m)")
(assume "n0" "n" "m" "ws" "n0<=m" "ws m")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(assert "NatLeast(n--n0)([nat]ws(nat+n0))<=m--n0")
 (use "NatLeastLeIntro")
 (ng #t)
 (simp "NatMinusPlus")
 (use "ws m")
 (use "n0<=m")
(assume "Assertion")
(assert
 "NatLeast(n--n0)([nat]ws(nat+n0))+n0<=m--n0+n0")
 (use "NatLeMonPlus")
 (use "Assertion")
 (use "Truth")
 (simp "NatMinusPlus")
(assume "Hyp")
(use "Hyp")
(use "n0<=m")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeastUpLeIntro")

;; NatLeastUpLtElim
(set-goal "all n0,n,ws(
 n0<=NatLeastUp n0 n ws ->
 NatLeastUp n0 n ws<n ->
 ws(NatLeastUp n0 n ws))")
(assume "n0" "n" "ws" "n0<=m" "m<n")
(ng #t)
(assert "n0<=n")
 (use "NatLeTrans" (pt "NatLeastUp n0 n ws"))
 (use "n0<=m")
 (use "NatLtToLe")
 (use "m<n")
(assume "n0<=n")
(simp "n0<=n")
(ng #t)
(use-with "NatLeastLtElim"
	  (pt "n--n0")
	  (pt "[nat](ws(nat+n0))") "?")
(ng "m<n")
(simphyp-with-to "m<n" "n0<=n" "SimpHyp")
(ng "SimpHyp")
(assert
 "NatLeast(n--n0)([nat]ws(nat+n0))+n0--n0<n--n0")
 (use "NatLtMonMinusLeft")
 (use "SimpHyp")
 (ng #t)
 (use "Truth")
(ng #t)
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cp)
(save "NatLeastUpLtElim")

;; NatLeastUpZero
(set-goal "all n,ws
 NatLeastUp Zero n ws=NatLeast n ws")
(assume "n" "nat=>boole")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeastUpZero")
(add-rewrite-rule "NatLeastUp Zero n ws" "NatLeast n ws")

;; Added 2025-02-15

;; NatThirdBinom
(set-goal "all n,m(m*m--n*n=(m+n)*(m--n))")
(assume "n" "m")
(cases (pt "n<=m"))
(assume 1)
(ng)
(simp (pf "m*n=n*m"))
(simp "NatPlusMinusAssoc")
(simp "NatMinusPlus")
(simp "<-" "NatPlusMinusAssoc")
(use "Truth")
(use "Truth")
(use "NatLeMonTimes")
(use 1)
(use "Truth")
(use "NatLeMonTimes")
(use "Truth")
(use 1)
(use "NatTimesComm")
(assume 1)
(assert "m<=n")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use 1)
(assume 2)
(simp "NatMinusZero")
(simp "NatMinusZero")
(use "Truth")
(use 2)
(use "NatLeMonTimes")
(use 2)
(use 2)
;; (cp)
(save "NatThirdBinom")

;; NatLtPosToLtTimes
(set-goal "all m,n(1<m -> 0<n -> n<n*m)")
(assume "m" "n" 1 2)
(cases (pt "n"))
(assume 3)
(simphyp 2 3)
(use "EfAtom")
(use 4)
(assume "n0" 4)
(cases (pt "m"))
(assume 4)
(simphyp 1 4)
(use "EfAtom")
(use 5)
(assume "m0" 4)
(cases (pt "m0"))
(assume 5)
(simphyp 4 5)
(simphyp 1 6)
(use "EfAtom")
(use 7)
(assume "m1" 5)
(simp (pf "Succ n0*Succ(Succ m1)=Succ n0*Succ m1+Succ n0"))
(use "NatLeLtTrans" (pt "0+Succ n0"))
(use "Truth")
(use "NatLtMonPlus1")
(use "Truth")
(use "Truth")
(use "Truth")
;; (cp)
(save "NatLtPosToLtTimes")

;; NatLtMonTimesLeft
(set-goal "all l,n,m(Zero<l -> n<m -> l*n<l*m)")
(ind)
(search)
(assume "l" 1 "n" "m" 2 3)
(ng)
(use "NatLtMonPlus2")
(cases (pt "l"))
(search)
(assume "l0" 2)
(use "NatLtToLe")
(simp "<-" 4)
(use 1)
(simp 4)
(use "Truth")
(use 3)
(use 3)
;; (cp)
(save "NatLtMonTimesLeft")

;; NatLtMonTimesRight
(set-goal "all l,n,m(Zero<l -> n<m -> n*l<m*l)")
(strip)
(simp (pf "n*l=l*n"))
(simp (pf "m*l=l*m"))
(use "NatLtMonTimesLeft")
(use 1)
(use 2)
(use "NatTimesComm")
(use "NatTimesComm")
;; (cp)
(save "NatLtMonTimesRight")

;; NatTimesEqualOneToOne
(set-goal "all n, m(n*m=1 -> n=1)")
(cases)
(search)
(cases)
(assume "m" 1)
(use "Truth")
(assume "n")
(cases)
(auto)
;; (cp)
(save "NatTimesEqualOneToOne")

;; NatPosTimes
(set-goal "all n, m(0<n -> 0<m -> 0<n*m)")
(cases)
(strip)
(use "EfAtom")
(use 1)
(assume "n")
(cases)
(strip)
(use "EfAtom")
(use 2)
(search)
;; (cp)
(save "NatPosTimes")

;; NatLeNotEqToLt
(set-goal "all n, m(n<=m -> (n=m -> F) -> n<m)")
(ind)
(cases)
(auto)
(assume "n" 1)
(cases)
(search)
(use 1)
;; (cp)
(save "NatLeNotEqToLt")

;; NatLtSuccNotEqToLt
(set-goal "all n, m(n<Succ m -> (n=m -> F) -> n<m)")
(ind)
(cases)
(auto)
(assume "n" 1)
(cases)
(search)
(use 1)
;; (cp)
(save "NatLtSuccNotEqToLt")

;; End of additions 2025-02-15

;; For totality of (Rec nat=>alpha) we need a general forms (with
;; alpha for nat) of

;; (pp "EqPNatRefl")
;; allnc n^(TotalNat n^ -> EqPNat n^ n^)

;; This is provable for closed finitary types (Lemma 3.3.1 ss19/ml).
;; We could take the general forms as global assumption, where alpha
;; ranges over closed finitary types.

;; (term-to-t-deg (pt "(Rec nat=>alpha)"))
;; 1

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "nat=>alpha"))
(add-var-name "f" (py "nat=>alpha=>alpha"))

(set-goal (rename-variables (term-to-totality-formula (pt "(Rec nat=>alpha)"))))
(assume "n^" "Tn" "x^" "Tx" "f^" "Tf")
(elim "Tn")
;; 3,4
(ng #t)
(use "Tx")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(use "Tf")
(use "Tn1")
(use "IH")
;; Proof finished.
;; (cp)
;; (save-totality) ;does not work here
(save "NatRecTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

(animate "NatRecTotal")

;; 2020-07-16.  We prove (pure) n.c. extensionality theorems for the
;; constructors, recursion, cases, destructor and corecursion in nat.

;; ExtNc theorems for constructors are superfluous: they are the
;; clauses of EqPNatNc

(pp "EqPNatNcSucc")
;; allnc n^,n^0(EqPNatNc n^ n^0 -> EqPNatNc(Succ n^)(Succ n^0))

;; NatRecExtNc
(set-goal
 (rename-variables (term-to-pure-extnc-formula (pt "(Rec nat=>alpha)"))))
;; ?^1:allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc alpha^,alpha^0(
;;       EqPNc alpha^ alpha^0 -> 
;;       allnc (nat=>alpha=>alpha)^,(nat=>alpha=>alpha)^0(
;;        allnc n^1,n^2(
;;         EqPNatNc n^1 n^2 -> 
;;         allnc alpha^1,alpha^2(
;;          EqPNc alpha^1 alpha^2 -> 
;; 	       EqPNc((nat=>alpha=>alpha)^ n^1 alpha^1)
;; 	       ((nat=>alpha=>alpha)^0 n^2 alpha^2))) -> 
;;        EqPNc((Rec nat=>alpha)n^ alpha^(nat=>alpha=>alpha)^)
;;        ((Rec nat=>alpha)n^0 alpha^0(nat=>alpha=>alpha)^0))))
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(ng #t)
(assume "alpha^1" "alpha^2" "EqPx1x2")
(strip)
(use "EqPx1x2")
;; 4
(assume "n^3" "n^4" "EqPn3n4" "IH" "alpha^1" "alpha^2" "EqPx1x2"
	"(nat=>alpha=>alpha)^1" "(nat=>alpha=>alpha)^2" "EqPf1f2")
(ng #t)
(use "EqPf1f2")
(use "EqPn3n4")
(use "IH")
(use "EqPx1x2")
(use "EqPf1f2")
;; Proof finished.
;; (cp)
(save "NatRecExtNc")

;; NatCasesExtNc
(set-goal (rename-variables
	   (nf (term-to-pure-extnc-formula
		(pt "[n,x,nat=>alpha][if n x nat=>alpha]")))))

;; allnc n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      allnc x^,x^0(
;;       EqPNc x^ x^0 -> 
;;       allnc (nat=>alpha)^,(nat=>alpha)^0(
;;        allnc n^1,n^2(
;;         EqPNatNc n^1 n^2 -> EqPNc((nat=>alpha)^ n^1)((nat=>alpha)^0 n^2)) -> 
;;        EqPNc[if n^ x^ (nat=>alpha)^][if n^0 x^0 (nat=>alpha)^0])))

(assert "allnc x^,x^0(
     EqPNc x^ x^0 -> 
     allnc (nat=>alpha)^,(nat=>alpha)^0(
      allnc n^,n^0(
       EqPNatNc n^ n^0 -> EqPNc((nat=>alpha)^ n^)((nat=>alpha)^0 n^0)) -> 
      allnc n^,n^0(
       EqPNatNc n^ n^0 -> 
       EqPNc[if n^ x^ (nat=>alpha)^][if n^0 x^0 (nat=>alpha)^0])))")

(assume "x^1" "x^2" "x1=x2" "(nat=>alpha)^1" "(nat=>alpha)^2" "xs1=xs2"
	"n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 5,6
(ng #t)
(use "x1=x2")
;; 6
(assume "n^3" "n^4" "n3=n4" "IH")
(ng #t)
(use "xs1=xs2")
(use "n3=n4")
;; Assertion proved.
(assume "Assertion"
	"n^1" "n^2" "n1=n2" "x^1" "x^2" "x1=x2"
	"(nat=>alpha)^1" "(nat=>alpha)^2" "xs1=xs2")
(use "Assertion")
(use "x1=x2")
(use "xs1=xs2")
(use "n1=n2")
;; Proof finished.
;; (cp)
(save "NatCasesExtNc")

;; NatDestrExtNc
(set-goal
 (rename-variables
  (term-to-pure-extnc-formula
   (pt "(Destr nat)")
   (make-arrow (make-alg "conat") (make-alg "uysum" (make-alg "conat"))))))
;; ?^1:allnc n^,n^0(
;;      CoEqPNatNc n^ n^0 -> 
;;      (REqPUysumNc (cterm (n^1,n^2) CoEqPNatNc n^1 n^2))(Des n^)(Des n^0))
(assume "n^1" "n^2" "n1~~n2")
(inst-with-to "CoEqPNatNcClause" (pt "n^1") (pt "n^2") "n1~~n2" "Inst")
(elim "Inst")
;; 5,6
(drop "Inst")
(assume "Conj")
(elim "Conj")
(drop "Conj")
(assume "n1=0" "n2=0")
(simp "n1=0")
(simp "n2=0")
(ng #t)
(intro 0)
;; 6
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^3" "n3Prop")
(by-assume "n3Prop" "n^4" "n3n4Prop")
(elim "n3n4Prop")
(drop "n3n4Prop")
(assume "n3=n4" "Conj")
(elim "Conj")
(drop "Conj")
(assume "n1=Sn3" "n2=Sn4")
(simp "n1=Sn3")
(simp "n2=Sn4")
(ng #t)
(intro 1)
(use "n3=n4")
;; Proof finished.
;; (cp)
(save "NatDestrExtNc")

;; For NatCoRecExtNc we apply term-to-pure-extnc-formula to the term
;; (CoRec gamma=>nat) and the cotype obtained from the type of (CoRec
;; gamma=>nat) by changing the final nat to conat.  Then the
;; conclusion has CoEqPNatNc with two arguments (CoRec gamma=>nat).
;; This blocks the application of coinduction, which needs variable
;; arguments.  We therefore prove NatCoRecExtNcAux first where this
;; does not happen, and from it the original goal.  This needs
;; NatCoRec0 NatCoRec1L NatCoRec1R.

(add-var-name "gam" (py "gamma"))
;;(add-var-name "w" (py "gamma"))
(add-var-name "g" (py "gamma=>uysum(nat ysum gamma)"))

;; NatCoRec0
(set-goal "all g^,gam^(g^ gam^ eqd(DummyL nat ysum gamma) ->
 (CoRec gamma=>nat)gam^ g^ eqd Zero)")
(assume "g^" "gam^" "EqHyp")
(simp-with (make-proof-in-aconst-form
	    (alg-or-arrow-types-to-corec-aconst (py "gamma=>nat"))))
(ng)
(simp-with "EqHyp")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "NatCoRec0")

;; NatCoRec1L
(set-goal "all g^,gam^,n^(g^ gam^ eqd((Inr((InL nat gamma)n^))) ->
 (CoRec gamma=>nat)gam^ g^ eqd Succ n^)")
(assume "g^" "gam^" "n^" "EqHyp")
(simp-with (make-proof-in-aconst-form
	    (alg-or-arrow-types-to-corec-aconst (py "gamma=>nat"))))
(ng)
(simp-with "EqHyp")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "NatCoRec1L")

;; NatCoRec1R
(set-goal "all g^,gam^,gam^1(g^ gam^ eqd((Inr((InR gamma nat)gam^1))) ->
 (CoRec gamma=>nat)gam^ g^ eqd Succ((CoRec gamma=>nat)gam^1 g^))")
(assume "g^" "gam^" "gam^1" "EqHyp1")
(assert "all n^(Succ((CoRec gamma=>nat)gam^1 g^) eqd n^ ->
 (CoRec gamma=>nat)gam^ g^ eqd n^)")
 (assume "n^" "EqHyp2")
 (simp-with (make-proof-in-aconst-form
 	    (alg-or-arrow-types-to-corec-aconst (py "gamma=>nat"))))
 (ng)
 (simp "EqHyp1")
 (ng)
 (use "EqHyp2")
(assume "Assertion")
(use "Assertion")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "NatCoRec1R")

;; (add-var-name "h" (py "gamma=>uysum(nat ysum gamma)"))

;; NatCoRecExtNcAux
(set-goal "allnc g^1,g^2(
     allnc gam^1,gam^2(
      EqPNc gam^1 gam^2 -> 
      g^1 gam^1 eqd(DummyL nat ysum gamma) andnc 
      g^2 gam^2 eqd(DummyL nat ysum gamma) ornc
      exnc n^1,n^2(
       g^1 gam^1 eqd Inr((InL nat gamma)n^1) andnc 
       g^2 gam^2 eqd Inr((InL nat gamma)n^2) andnc CoEqPNatNc n^1 n^2) ornc
      exnc gam^3,gam^4(
       g^1 gam^1 eqd Inr((InR gamma nat)gam^3) andnc
       g^2 gam^2 eqd Inr((InR gamma nat)gam^4) andnc EqPNc gam^3 gam^4)) -> 
     allnc n^1,n^2(
      exnc gam^1,gam^2(
       n^1 eqd(CoRec gamma=>nat)gam^1 g^1 andnc
       n^2 eqd(CoRec gamma=>nat)gam^2 g^2 andnc EqPNc gam^1 gam^2) -> 
      CoEqPNatNc n^1 n^2))")
(assume "g^1" "g^2" "g1=g2" "n^1" "n^2")
(use (imp-formulas-to-coind-proof
   (pf "exnc gam^1,gam^2(n^1 eqd(CoRec gamma=>nat)gam^1 g^1 andnc
                     n^2 eqd(CoRec gamma=>nat)gam^2 g^2 andnc EqPNc gam^1 gam^2) ->
        CoEqPNatNc n^1 n^2")))
(assume "n^3" "n^4" "ExHyp")
(by-assume "ExHyp" "gam^1" "gam1Prop")
(by-assume "gam1Prop" "gam^2" "gam1gam2Prop")
(assert "EqPNc gam^1 gam^2")
(use "gam1gam2Prop")
(assume "gam1=gam2")
(inst-with-to "g1=g2" (pt "gam^1") (pt "gam^2")  "gam1=gam2" "g1=g2Inst")
(drop "g1=g2")
(elim "g1=g2Inst")
;; 17,18
(drop "g1=g2Inst")
(assume "Conj")
(intro 0)
(split)
;; 22,23
(simp "gam1gam2Prop")
(use "NatCoRec0")
(use "Conj")
;; 23
(simp "gam1gam2Prop")
(use "NatCoRec0")
(use "Conj")
;; 18
(drop "g1=g2Inst")
(assume "Disj")
(intro 1)
(elim "Disj")
;; 31,32
(drop "Disj")
(assume "ExHypL")
(by-assume "ExHypL" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(simp "gam1gam2Prop")
(simp "gam1gam2Prop")
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 0)
(use "n5n6Prop")
(split)
(use "NatCoRec1L")
(use "n5n6Prop")
(use "NatCoRec1L")
(use "n5n6Prop")
;; 32
(drop "Disj")
(assume "ExHypR")
(by-assume "ExHypR" "gam^3" "gam3Prop")
(by-assume "gam3Prop" "gam^4" "gam3gam4Prop")
(simp "gam1gam2Prop")
(simp "gam1gam2Prop")
(intro 0 (pt "(CoRec gamma=>nat)gam^3 g^1"))
(intro 0 (pt "(CoRec gamma=>nat)gam^4 g^2"))
(split)
(intro 1)
(intro 0 (pt "gam^3"))
(intro 0 (pt "gam^4"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "gam3gam4Prop")
(split)
(use "NatCoRec1R")
(use "gam3gam4Prop")
(use "NatCoRec1R")
(use "gam3gam4Prop")
;; Proof finished.
;; (cp)
(save "NatCoRecExtNcAux")

(add-var-name "ngam" (py "nat ysum gamma"))

;; 2020-06-19.  Want gamma=>uysum(conat ysum gamma) rather than
;; gamma=>uysum(nat ysum gamma).  We can keep ngam as it is, but only
;; correct the cotype of (CoRec gamma=>nat)

;; NatCoRecExtNc
(set-goal (rename-variables (term-to-pure-extnc-formula
			     (pt "(CoRec gamma=>nat)")
			     (make-arrow
			      (py "gamma")
			      (make-arrow
			       (make-arrow
				(py "gamma")
				(make-alg "uysum"
					  (make-alg "ysum" (make-alg "conat")
						    (py "gamma"))))
			       (make-alg "conat"))))))
;; allnc gam^,gam^0(
;;      EqPNc gam^ gam^0 -> 
;;      allnc g^,g^0(
;;       allnc gam^1,gam^2(
;;        EqPNc gam^1 gam^2 -> 
;;        (REqPUysumNc (cterm (ngam^,ngam^0) 
;;                       (REqPYsumNc (cterm (n^,n^0) CoEqPNatNc n^ n^0)
;;                         (cterm (gam^3,gam^4) EqPNc gam^3 gam^4))
;;                       ngam^ 
;;                       ngam^0))
;;        (g^ gam^1)
;;        (g^0 gam^2)) -> 
;;       CoEqPNatNc((CoRec gamma=>nat)gam^ g^)((CoRec gamma=>nat)gam^0 g^0)))
(assert "allnc g^,g^0(
     allnc gam^,gam^0(
      EqPNc gam^ gam^0 -> 
      (REqPUysumNc (cterm (ngam^,ngam^0) 
                     (REqPYsumNc (cterm (n^,n^0) CoEqPNatNc n^ n^0)
                       (cterm (gam^1,gam^2) EqPNc gam^1 gam^2))
                     ngam^ 
                     ngam^0))
      (g^ gam^)
      (g^0 gam^0)) -> 
     allnc gam^,gam^0(
      EqPNc gam^ gam^0 -> 
     allnc n^1,n^2(
      exnc gam^1,gam^2(
       n^1 eqd(CoRec gamma=>nat)gam^1 g^ andnc
       n^2 eqd(CoRec gamma=>nat)gam^2 g^0 andnc EqPNc gam^1 gam^2) -> 
      CoEqPNatNc n^1 n^2)))")
(assume "g^1" "g^2" "g1=g2" "gam^1" "gam^2" "gam1=gam2")
(use  "NatCoRecExtNcAux")
(assume "gam^" "gam^0" "gam=gam0")
(inst-with-to "g1=g2" (pt "gam^") (pt "gam^0") "gam=gam0" "Inst")
(drop "g1=g2")
(elim "Inst")
;; 10,11
(drop "Inst")
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 11
(drop "Inst")
(assume "ngam^1" "ngam^2" "YsumHyp")
(intro 1)
(elim "YsumHyp")
;; 19,20
(drop "YsumHyp")
(assume "n^1" "n^2" "n1=n2")
(intro 0)
(intro 0 (pt "n^1"))
(intro 0 (pt "n^2"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
;; (use "EqPNatNcToCoEqPNc")
(use "n1=n2")
;; 20
(drop "YsumHyp")
(assume "gam^3" "gam^4" "gam3=gam4")
(intro 1)
(intro 0 (pt "gam^3"))
(intro 0 (pt "gam^4"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "gam3=gam4")
;; Assertion proved.
(assume "Assertion" "gam^1" "gam^2" "gam1=gam2" "g^1" "g^2" "g1g2Prop")
(inst-with-to
 "Assertion"
 (pt "g^1") (pt "g^2") "g1g2Prop" (pt "gam^1") (pt "gam^2") "gam1=gam2" "AInst")
(drop "Assertion" "g1g2Prop")
(use "AInst")
(drop "AInst")
(intro 0 (pt "gam^1"))
(intro 0 (pt "gam^2"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "gam1=gam2")
;; Proof finished.
;; (cp)
(save "NatCoRecExtNc")

;; NatDouble
(add-program-constant "NatDouble" (py "nat=>nat"))

(add-computation-rules
 "NatDouble Zero" "Zero"
 "NatDouble(Succ n)" "Succ(Succ(NatDouble n))")

(set-totality-goal "NatDouble")
(fold-alltotal)
(ind)
;; 3,4
(use "TotalVar")
;; 4
(assume "n" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; NatMaxDouble
(set-goal "all n,m NatDouble n max NatDouble m=NatDouble(n max m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMaxDouble")

;; NatMinDouble
(set-goal "all n,m NatDouble n min NatDouble m=NatDouble(n min m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatMinDouble")

(add-program-constant "NatEven" (py "nat=>boole"))

(add-computation-rules
 "NatEven Zero" "True"
 "NatEven(Succ Zero)" "False"
 "NatEven(Succ(Succ n))" "NatEven n")

(set-totality-goal "NatEven")
(assert "allnc n^(TotalNat n^ ->
         TotalBoole(NatEven(Succ n^)) andd
         TotalBoole(NatEven(Succ(Succ n^))))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalBooleFalse")
 (use "TotalBooleTrue")
 (assume "m^" "Tm" "IH")
 (ng)
 (split)
 (use "IH")
 (use "IH")
(assume "NatEvenTotalAux")
(ng)
(assume "n^" "Tn")
(use "NatEvenTotalAux")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

;; NatEvenDouble
(set-goal "all n NatEven(NatDouble n)")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatEvenDouble")

;; NatEvenToOddSucc  (was NatEvenSucc)
(set-goal "all n(NatEven n -> NatEven(Succ n) -> F)")
(ind)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "IH" "ESn" "ESSn")
(ng "ESSn")
(use "IH")
(use "ESSn")
(use "ESn")
;; Proof finished.
;; (cp)
(save "NatEvenToOddSucc")

;; NatOddSuccToEven
(set-goal "all n((NatEven(Succ n) -> F) -> NatEven n)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "OSSn")
(cases (pt "NatEven(Succ n)"))
(strip)
(use "Truth")
(assume "OSn")
(use "OSSn")
(ng #t)
(use "IH")
(use "OSn")
;; Proof finished
;; (cp)
(save "NatOddSuccToEven")

;; NatOddToEvenSucc 
(set-goal "all n((NatEven n -> F) -> NatEven(Succ n))")
(ind)
;; 2,3
(ng)
(assume "Absurd")
(use "Absurd")
(use "Truth")
;; 3
(assume "n" "IH" "NESnF")
(assert "(NatEven n -> F) -> F")
(assume "NEnF")
(use "NESnF")
(use "IH")
(use "NEnF")
;; Assertion proved.
(assume "NEFF")
(ng #t)
(use "StabAtom")
(use "NEFF")
;; Proof finished.
;; (cp)
(save "NatOddToEvenSucc")

;; NatEvenMinus
(set-goal "all n,m(NatEven n -> NatEven m -> NatEven(m--n))")
(assert "all l,n,m(n+m<l->NatEven n -> NatEven m -> NatEven(m--n))")
(ind)
(strip)
(use "EfAtom")
(use 1)
(assume "l" 1)
(cases)
(strip)
(use 4)
(cases)
(strip)
(use "EfAtom")
(use 3)
(assume "n")
(cases)
(search)
(cases)
(strip)
(use "EfAtom")
(use 4)
(assume "m" 2 3 4)
(ng)
(use 1)
(use "NatLeLtTrans" (pt "n+m+3"))
(use "NatLeTrans" (pt "n+m+0"))
(use "Truth")
(use "NatLeMonPlus")
(auto)
(strip)
(use 1 (pt "n+m+1"))
(auto)
;; (cp)
(save "NatEvenMinus")

;; NatEvenOrOdd
(set-goal "all n(NatEven n oru NatEven(Succ n))")
(ind)
(intro 0)
(use "Truth")
(assume "n")
(elim)
(assume 2)
(intro 1)
(use 2)
(assume 2)
(intro 0)
(use 2)
;; (cp)
(save "NatEvenOrOdd")

(add-program-constant "NatHalf" (py "nat=>nat"))

(add-computation-rules
 "NatHalf Zero" "Zero"
 "NatHalf(Succ Zero)" "Zero"
 "NatHalf(Succ(Succ n))" "Succ(NatHalf n)")

(set-totality-goal "NatHalf")
(assert "allnc n^(TotalNat n^ -> TotalNat(NatHalf n^) andd
                                 TotalNat(NatHalf(Succ n^)))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalNatZero")
 (use "TotalNatZero")
 (assume "m^" "Tm" "IH")
 (split)
 (use "IH")
 (ng #t)
 (use "TotalNatSucc")
 (use "IH")
(assume "NatHalfTotalAux")
(assume "n^" "Tn")
(use "NatHalfTotalAux")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

;; NatHalfDouble
(set-goal "all n NatHalf(NatDouble n)=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatHalfDouble")

;; NatHalfSuccDouble
(set-goal "all n NatHalf(Succ(NatDouble n))=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatHalfSuccDouble")

;; NatLeMonHalf
(set-goal "all n,m(n<=m -> NatHalf n<=NatHalf m)")
(assert "all l,n,m(n+m<l -> n<=m -> NatHalf n<=NatHalf m)")
(ind)
(strip)
(use "EfAtom")
(use 1)
(assume "l" 1)
(cases)
(search)
(cases)
(search)
(assume "n")
(cases)
(search)
(cases)
(search)
(assume "m" 3 4)
(ng)
(use 1)
(use "NatLeLtTrans" (pt "n+m+3"))
(use "NatLeTrans" (pt "n+m+0"))
(use "Truth")
(use "NatLeMonPlus")
(use "Truth")
(use "Truth")
(use 2)
(use 3)
(strip)
(use 1 (pt "Succ(n+m)"))
(auto)
;; (cp)
(save "NatLeMonHalf")

;; NatDoubleHalfEven
(set-goal "all n(NatEven n -> NatDouble(NatHalf n)=n)")
(assert "all n((NatEven n -> NatDouble(NatHalf n)=n) andnc
               (NatEven(Succ n) -> NatDouble(NatHalf(Succ n))=Succ n))")
(ind)
(split)
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfEvenAux" "n")
(use "NatDoubleHalfEvenAux")
;; Proof finished.
;; (cp)
(save "NatDoubleHalfEven")

;; NatDoubleHalfOdd
(set-goal "all n((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n)")
(assert "all n(
   ((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n) andnc
   ((NatEven(Succ n) -> F) -> Succ(NatDouble(NatHalf(Succ n)))=Succ n))")
(ind)
(split)
(ng #t)
(assume "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfOddAux" "n")
(use "NatDoubleHalfOddAux")
;; Proof finished.
;; (cp)
(save "NatDoubleHalfOdd")

;; EvenNotEqOdd
(set-goal "all m,n(2*m=Succ(2*n) -> F)")
(ind)
(search)
(assume "m" 1)
(ind)
(search)
(assume "n" 1 2)
(ng)
(use 1 (pt "n"))
(use 3)
;; (cp)
(save "EvenNotEqOdd")

;; NatPlusDouble
(set-goal "all n,m NatDouble n+NatDouble m=NatDouble(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatPlusDouble")

;; NatDoubleEq
(set-goal "all n,m (NatDouble n=NatDouble m)=(n=m)")
(ind)
;; 2,3
(cases)
(use "Truth")
;; 5
(assume "n")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 8,9
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoubleEq")

;; NatDoubleLt
(set-goal "all n,m (NatDouble n<NatDouble m)=(n<m)")
(ind)
(ng)
(cases)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoubleLt")

;; NatDoubleLe
(set-goal "all n,m (NatDouble n<=NatDouble m)=(n<=m)")
(ind)
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoubleLe")

;; NatLt0Double
(set-goal "all n(Zero<n -> Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Proof finished
;; (cp)
(save "NatLt0Double")

;; NatLeDouble
(set-goal "all n n<=NatDouble n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLeTrans" (pt "NatDouble n"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeDouble")

;; NatLtDouble
(set-goal "all n(Zero<n -> n<NatDouble n)")
(ind)
(assume "Absurd")
(use "Absurd")
;; Step
(assume "n" "IH" "Useless")
(ng)
(use "NatLeLtTrans" (pt "NatDouble n"))
(use "NatLeDouble")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtDouble")

;; NatDoubleMinus
(set-goal "all n,m NatDouble(n--m)=NatDouble n--NatDouble m")
(ind)
;; 2-3
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 7,8
(ng)
(use "Truth")
;; 8
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoubleMinus")

;; NatHalfMinus
(set-goal "all n,m(NatEven n -> NatEven m ->
 NatHalf n--NatHalf m=NatHalf(n--m))")
(strip)
(simp "<-" "NatDoubleEq")
(simp "NatDoubleMinus")
(simp "NatDoubleHalfEven")
(simp "NatDoubleHalfEven")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "NatEvenMinus")
(auto)
;; (cp)
(save "NatHalfMinus")

;; NatMinusPred
(set-goal "all m,n (0<m -> m<n -> n--Pred m=Succ(n--m))")
(cases)
(strip)
(use "EfAtom")
(use 1)
(assume "m" "n" 2 3)
(ng)
(cases (pt "n--m"))
(assume 4)
(use "EfAtom")

(inst-with "NatLtMinusZero" (pt "m") (pt "n"))
(assert "m<n")
(use "NatLtTrans" (pt "Succ m"))
(use "Truth")
(use 2)
(simp 4)
(simp 3)
(auto)
;;(cp)
(save "NatMinusPred")

;;NatMinusNatMinus
(set-goal "all m,n(m<n -> n+m--(n--m)=m+m)")
(ind)
(search)
(assume "n" 1 "m" 2)
(ng)
(simp "NatMinusPred")
(ng)
(use "NatEqTrans" (pt "Succ(m+n--(m--n))"))
(use "NatEqSym")
(use "SuccNatMinus")
(use "NatLeTrans" (pt "m"))
(auto)
(simp 1)
(auto)
(use "NatLtTrans" (pt "Succ n"))
(auto)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "m"))
(auto)
(simp "<-" "NatLtMinusZero")
(use "NatLtTrans" (pt "Succ n"))
(use "Truth")
(use 2)
;;(cp)
(save "NatMinusNatMinus")

;; NatEvenOrOdd
;; NatHalfLtMonEven
(set-goal "all n,m(NatEven n -> NatEven m -> n<m -> NatHalf n<NatHalf m)")
(strip)
(simp "<-" "NatDoubleLt")
(simp "NatDoubleHalfEven")
(simp "NatDoubleHalfEven")
(use 3)
(use 2)
(use 1)
;; (cp)
(save "NatHalfLtMonEven")

;; NatLtSZeroSOne 
;; NatLtSOneSZero
;; NatLtSOneSOne

;; NatLeSZeroSOne
;; NatLeSOneSZero
;; NatLeSOneSOne

;; NatLtOneSZero
;; NatLtOneSOne

;; NatLeSZeroOne
;; NatLtSZeroOne

;; moved here from numbers.scm.  The terminology comes from pos: Double
;; for NatDouble, SOne for Succ(NatDouble)

;; NatLtDoubleSuccDouble
(set-goal "all n,m (NatDouble n<Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtDoubleSuccDouble")

;; NatLtSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtSuccDoubleDouble")

;; NatLtSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<Succ(NatDouble m))=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(strip)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLtSuccDoubleSuccDouble")

;; NatLeDoubleSuccDouble
(set-goal "all n,m (NatDouble n<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeDoubleSuccDouble")

;; NatLeSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<=NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeSuccDoubleDouble")

;; NatLeSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(ng #t)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeSuccDoubleSuccDouble")

;; NatLtOneDouble
(set-goal "all n(Zero<n -> Succ Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtOneDouble")

;; NatLtOneSuccDouble
(set-goal "all n(Zero<n -> Succ Zero<Succ(NatDouble n))")
(assume "n" "0<n")
(use "NatLtTrans" (pt "NatDouble n"))
(use "NatLtOneDouble")
(use "0<n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtOneSuccDouble")

;; NatLeDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<=Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "NatLeDoubleOne")

;; NatLtDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "NatLtDoubleOne")

;; NatDoubleToTwoTimes
(set-goal "NatDouble n=2*n")
(ind)
(auto)
;; (cp)
(save "NatDoubleToTwoTimes")

;; Reason to have a local efq assumption in CVIndPvar: soundness proof
;; does not normalize for Efq a global assumption.  Check

;; CVIndPvar
(set-goal "(F -> allnc n^(Pvar nat)n^) ->
  all n(all m(m<n -> (Pvar nat)m) -> (Pvar nat)n) ->
  all n (Pvar nat)n")
(assume "efq" "Prog")
(assert "all n,m(m<n -> (Pvar nat)m)")
 (ind)
 (assume "m" "Absurd")
 (use "efq")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "CVIndPvar")

;; In CVInd we do not need an Efq assumption since EfEqD is avaiable
;; (pp "EfEqD")
;; F -> all alpha^,alpha^0 alpha^ eqd alpha^0

;; CVInd
(set-goal "all ws(all n(all m(m<n -> ws m) -> ws n) -> all n ws n)")
(assume "ws" "Prog")
(assert "all n,m(m<n -> ws m)")
 (ind)
 (assume "m" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "CVInd")

;; NatHalfLt
(set-goal "all n(Zero<n -> NatHalf n<n)")
(assert "all n((Zero<n -> NatHalf n<n) andnc NatHalf(Succ n)<Succ n)")
(use "CVIndPvar")
(assume "Absurd" "n^")
(split)
(strip)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog")
(split)
(cases (pt "n"))
(assume "Useless" "Absurd")
(use "Absurd")
(assume "l" "n=Sl" "Useless")
(use-with "Prog" (pt "l") "?" 'right)
(simp "n=Sl")
(use "Truth")
;; 14
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "n=Sl")
(ng #t)
(cases (pt "l"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "l=Sm")
(simp "<-" "l=Sm")
(use "NatLtTrans" (pt "l"))
(use "Prog")
(simp "n=Sl")
(use "Truth")
(simp "l=Sm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "NatHalfLtAux" "n")
(use "NatHalfLtAux")
;; Proof finished.
;; (cp)
(save "NatHalfLt")

;; NatHalfLtSucc
(set-goal "all n NatHalf n<Succ n")
(use "CVInd")
(assume "n" "Prog")
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "n=Sm")
(cases (pt "m"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "m=Sl")
(ng #t)
(use "NatLtTrans" (pt "Succ l"))
(use "Prog")
(use "NatLtTrans" (pt "m"))
(simp "m=Sl")
(use "Truth")
(simp "n=Sm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatHalfLtSucc")

;; NatHalfLe
(set-goal "all n NatHalf n<=n")
(assume "n")
(use "NatLtSuccToLe")
(use "NatHalfLtSucc")
;; Proof finished.
;; (cp)
(save "NatHalfLe")

;; NatLtZeroHalfEven
(set-goal "all n(Zero<n -> NatEven n -> Zero<NatHalf n)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroHalfEven")

;; NatLtZeroHalfFinally
(set-goal "all n(Zero<n -> (n=Succ Zero -> F) -> Zero<NatHalf n)")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroHalfFinally")

;; NatDoublePlus
(set-goal "all n,m NatDouble(n+m)=NatDouble n+NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoublePlus")

;; NatDoublePlusEq
(set-goal "all n n+n=NatDouble n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "NatDoublePlusEq")

;; NatEvenPlus
(set-goal "all n,m(NatEven n -> NatEven m -> NatEven(n+m))")
(assume "n" "m" "En" "Em")
(inst-with-to "NatDoubleHalfEven" (pt "n") "En" "DHn=n")
(inst-with-to "NatDoubleHalfEven" (pt "m") "Em" "DHm=m")
(simp "<-" "DHn=n")
(simp "<-" "DHm=m")
(simp "<-" "NatDoublePlus")
(use "NatEvenDouble")
;; Proof finished.
;; (cp)
(save "NatEvenPlus")

;; NatOddTimesToOdd0
(set-goal "all n,m (NatEven(Succ(n*m)) -> NatEven(Succ n))")
(assert "all l,n,m(n+m<l -> NatEven(Succ(n*m)) -> NatEven(Succ n))")
(ind)
(strip)
(use "EfAtom")
(use 1)
(assume "l" 1)
(cases)
(search)
(cases)
(search)
(assume "n")
(cases)
(strip)
(use "EfAtom")
(use 3)
(cases)
(search)
(assume "m" 2 3)
(ng)
(use 1 (pt "m"))
(use "NatLeLtTrans" (pt "n+m+3"))
(use "NatLeTrans" (pt "n+m+0"))
(use "Truth")
(use "NatLeMonPlus")
(auto)
(simp (pf "Succ(n*m)=Succ(n*m+m+m+n+n)--(NatDouble m+NatDouble n)"))
(use "NatEvenMinus")
(use "NatEvenPlus")
(use "NatEvenDouble")
(use "NatEvenDouble")
(use 3)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "NatDoublePlusEq")
(ng)
(simp (pf "Succ(n*m+m+m+n+n)=Succ(n*m)+(m+m+n+n)"))
(simp "<-" "NatPlusMinusAssoc")
(auto)
(strip)
(use 1 (pt "n+m+1") (pt "m"))
(auto)
;; (cp)
(save "NatOddTimesToOdd0")

;;  NatOddTimesToOdd1
(set-goal "all n,m(NatEven(Succ(n*m)) -> NatEven(Succ m))")
(assume "n" "m")
(simp "NatTimesComm")
(use "NatOddTimesToOdd0")
;; (cp)
(save "NatOddTimesToOdd1")

;; NatTimesDouble
(set-goal "all n,m NatDouble n*NatDouble m=NatDouble(NatDouble(n*m))")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "IH")
(assert "NatDouble(n*m+n)=NatDouble(n*m)+NatDouble n")
 (use "NatDoublePlus")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "NatDouble(NatDouble(n*m)+NatDouble n)=
         NatDouble(NatDouble(n*m))+NatDouble(NatDouble(n))")
 (use "NatDoublePlus")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "NatDouble(NatDouble n)=NatDouble n+NatDouble n")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesDouble")

;; NatDoubleTimes2
(set-goal "all n,m NatDouble(n*m)=n*NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "NatDoublePlus")
(simp "IH")
(assert "NatDouble n=n+n")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatDoubleTimes2")

;; NatEvenTimes
(set-goal "all n,m(NatEven n -> NatEven(n*m))")
(assume "n")
(ind)
;; 3,4
(assume "Useless")
(use "Truth")
;; 4
(assume "m" "IH" "En")
(ng #t)
(use "NatEvenPlus")
(use "IH")
(use "En")
(use "En")
;; Proof finished
;; (cp)
(save "NatEvenTimes")

;; NatHalfPlus
(set-goal "all n,m(NatEven n -> NatEven m -> NatHalf(n+m)=NatHalf n+NatHalf m)")
(assume "n" "m" "En" "Em")
(simp "<-" "NatDoubleEq")
(simp "NatDoubleHalfEven")
(simp "NatDoublePlus")
(simp "NatDoubleHalfEven")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "Em")
(use "En")
(use "NatEvenPlus")
(use "En")
(use "Em")
;; Proof finished.
;; (cp)
(save "NatHalfPlus")

;; (pp "CasesNot")
;; all w((w -> Pvar) -> ((w -> F) -> Pvar) -> Pvar)

;; NatEvenTimesSucc
(set-goal "all n NatEven(n*Succ n)")
(assume "n")
(use "CasesNot" (pt "NatEven n"))
;; 3,4
(use "NatEvenTimes")
;; 4
(assume "NotEn")
(simp "NatTimesComm")
(use "NatEvenTimes")
(use "NatOddToEvenSucc")
(use "NotEn")
;; Proof finished.
;; (cp)
(save "NatEvenTimesSucc")

;; NatHalfTimes
(set-goal "all n,m(NatEven n -> NatEven m ->
 NatHalf n*NatHalf m=NatHalf(NatHalf(n*m)))")
(assert "all l,n,m(n+m<l -> NatEven n -> NatEven m ->
 NatHalf n*NatHalf m=NatHalf(NatHalf(n*m)))")
(ind)
(strip)
(use "EfAtom")
(use 1)
(assume "l" 1)
(cases)
(assume "m" 2 3 4)
(use "Truth")
(cases)
(strip)
(use "EfAtom")
(use 3)
(assume "n")
(cases)
(strip)
(use "Truth")
(cases)
(strip)
(use "EfAtom")
(use 4)
(assume "m" 2 3 4)	
(simp "NatHalf2CompRule")
(simp "NatHalf2CompRule")
(use "NatEqTrans" (pt "NatHalf n*NatHalf m+NatHalf m+NatHalf n+1"))
(use "Truth")
(simp 1)
(ng)
(assert "NatEven(NatHalf(n*m))")
(simp (pf "m=NatDouble(NatHalf m)"))
(simp "<-" "NatDoubleTimes2")
(simp "NatHalfDouble")
(simp (pf "n=NatDouble(NatHalf n)"))
(simp "NatTimesComm")
(simp "<-" "NatDoubleTimes2")
(use "NatEvenDouble")
(use "NatEqSym")
(use "NatDoubleHalfEven")
(use 3)
(use "NatEqSym")
(use "NatDoubleHalfEven")
(use 4)
(assume 5)
(assert "NatEven(n*m)")
(use "NatEvenTimes")
(use 3)
(assume 6)
(simp (pf "NatHalf(n*m+m+m+n+n)=
           NatHalf(n*m)+NatDouble(NatHalf m)+NatDouble(NatHalf n)"))
(simp "NatHalfPlus")
(simp "NatHalfPlus")
(simp "NatHalfDouble")
(simp "NatHalfDouble")
(use "Truth")
(use "NatEvenDouble")
(use 5)
(use "NatEvenDouble")
(use "NatEvenPlus")
(use 5)
(use "NatEvenDouble")
(simp "NatHalfPlus")
(simp "NatHalfPlus")
(simp "<-" "NatPlusAssoc")
(simp "NatDoublePlusEq")
(simp (pf "NatHalf(n*m+m+m)=NatHalf(n*m)+NatDouble(NatHalf m)"))
(use "Truth")
(simp "NatHalfPlus")
(simp "NatHalfPlus")
(simp "<-" "NatPlusAssoc")
(simp "NatDoublePlusEq")
(use "Truth")
(auto)
(use "NatEvenPlus")
(auto)
(use "NatEvenPlus")
(use "NatEvenPlus")
(auto)
(use "NatEvenPlus")
(use "NatEvenPlus")
(use "NatEvenPlus")
(auto)
(ng 2)
(use "NatLtTrans" (pt "(n+m)+3"))
(use "NatLeLtTrans" (pt "(n+m)+0"))
(use "Truth")
(use "NatLtMonPlus2")
(use "Truth")
(use "Truth")
(use 2)
(strip)
(use 1 (pt "n+m+1"))
(use "Truth")
(use 2)
(use 3)
;; (cp)
(save "NatHalfTimes")

;; For use with grec we add

(define natlt-obj (nbe-term-to-object (pt "NatLt") '()))

;; For the translation to Haskell we add

(add-program-constant "TranslationNatMinusPosDiff" (py "nat=>nat=>nat"))

;; SuccTotalFPFalseR
(set-goal "all n (n=Succ n)=False")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "SuccTotalFPFalseR")

;; SuccTotalFPFalseL
(set-goal "all n (Succ n=n)=False")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "SuccTotalFPFalseL")

;; CoEqPNatNcSuccNotZero
(set-goal "allnc n^(CoEqPNatNc(Succ n^)Zero -> F)")
(assume "n^" "Sn=0")
(inst-with-to "CoEqPNatNcClause" (pt "Succ n^") (pt "Zero") "Sn=0" "Inst")
(drop "Sn=0")
(elim "Inst")
;; 6,7
(assume "Absurd")
(assert "Succ n^ eqd Zero")
(use "Absurd")
(assume "SnEqD0")
(drop "Absurd")
(inst-with-to
(constructors-overlap-imp-falsity-proof (pf "Succ n^ eqd Zero"))
(pt "n^") "SnEqD0" "SnInst")
(ng "SnInst")
(use (make-proof-in-aconst-form eqd-true-to-atom-aconst))
(use "SnInst")
;; 7
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^1" "n1Prop")
(by-assume "n1Prop" "m^1" "n1m1Prop")
(assert "Zero eqd Succ m ^1")
(use "n1m1Prop")
(assume "0=Sn1")
(inst-with-to
(constructors-overlap-imp-falsity-proof (pf "Zero eqd Succ m^1"))
(pt "m^1") "0=Sn1" "0SnInst")
(ng "0SnInst")
(use (make-proof-in-aconst-form eqd-true-to-atom-aconst))
(use "0SnInst")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcSuccNotZero")

;; CoEqPNatNcSuccInj
(set-goal "allnc n^,m^(CoEqPNatNc(Succ n^)(Succ m^) -> CoEqPNatNc n^ m^)")
(assume "n^" "m^" "Sn=Sm")
(inst-with-to "CoEqPNatNcClause" (pt "Succ n^") (pt "Succ m^") "Sn=Sm" "Inst")
(drop "Sn=Sm")
(elim "Inst")
;; 6,7
(assume "Absurd")
(use "EfCoEqPNatNc")
(assert "Succ n^ eqd Zero")
(use "Absurd")
(assume "Sn=0")
(drop "Absurd")
(inst-with-to
(constructors-overlap-imp-falsity-proof (pf "Succ n^ eqd Zero"))
(pt "n^") "Sn=0" "SnInst")
(ng "SnInst")
(use (make-proof-in-aconst-form eqd-true-to-atom-aconst))
(use "SnInst")
;; 7
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^1" "n1Prop")
(by-assume "n1Prop" "m^1" "n1m1Prop")
(assert "Succ n^ eqd Succ n^1")
(use "n1m1Prop")
(assume "Sn=Sn1")
(inst-with-to
(constructor-eqd-imp-args-eqd-proof (pf "Succ n^ eqd Succ n^1")) "Sn=Sn1"
"nEqDInst")
(ng "nEqDInst")
(simp "nEqDInst")
(assert "Succ m^ eqd Succ m^1")
(use "n1m1Prop")
(assume "Sm=Sm1")
(inst-with-to
(constructor-eqd-imp-args-eqd-proof (pf "Succ m^ eqd Succ m^1")) "Sm=Sm1"
"mEqDInst")
(ng "mEqDInst")
(simp "mEqDInst")
(use "n1m1Prop")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcSuccInj")

;; CoEqPNatNcSuccCompat
(set-goal "allnc n^,m^(CoEqPNatNc n^ m^ -> CoEqPNatNc(Succ n^)(Succ m^))")
(assume "n^" "m^" "n=m")
(assert
"allnc n^1,m^1(n^1 eqd Succ n^ andnc m^1 eqd Succ m^ -> CoEqPNatNc n^1 m^1)")
(assume "n^1" "m^1" "n1m1Prop")
(coind "n1m1Prop")
(assume "n^2" "m^2" "n2m2Prop")
(intro 1)
(intro 0 (pt "n^"))
(intro 0 (pt "m^"))
(split)
(intro 0)
(use "n=m")
(use "n2m2Prop")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcSuccCompat")

;; CoEqPNatNcZeroZero
(set-goal "CoEqPNatNc Zero Zero")
(assert "allnc n^,m^(n^ eqd Zero andnc m^ eqd Zero -> CoEqPNatNc n^ m^)")
(assume "n^" "m^" "Conj")
(coind "Conj")
(assume "n^1" "m^1" "n1m1Prop")
(intro 0)
(use "n1m1Prop")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "CoEqPNatNcZeroZero")

;; 2023-04-16.  Choose (binomial coefficients) added

(add-program-constant "Choose" (py "nat=>nat=>nat"))

(add-computation-rules
 "Choose Zero Zero" "Succ Zero"
 "Choose Zero(Succ m)" "Zero"
 "Choose(Succ n)Zero" "Succ Zero"
 "Choose(Succ n)(Succ m)" "Choose n m+Choose n(Succ m)")

(set-totality-goal "Choose")
(fold-alltotal)
(ind)
;; 3,4
(fold-alltotal)
(cases)
(use "NatTotalVar")
(assume "n")
(use "NatTotalVar")
;; 4
(assume "n" "IH")
(fold-alltotal)
(cases)
(use "NatTotalVar")
(assume "m")
(use "NatPlusTotal")
(use "IH")
(use "NatTotalVar")
(use "IH")
(use "NatTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

(set-goal "all n Choose n Zero=Succ Zero")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Choose n Zero" "Succ Zero")

(set-goal "all n Choose n(Succ Zero)=n")
(cases)
(use "Truth")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Choose n(Succ Zero)" "n")

;; NatLtToChooseZero
(set-goal "all n,m(n<m -> Choose n m=Zero)")
(ind)
;; 2,3
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(assume "m" "n<m")
(simp "IH")
(ng #t)
(use "IH")
(use "NatLtTrans" (pt "m"))
(use "n<m")
(use "Truth")
(use "n<m")
;; Proof finished.
;; (cp)
(save "NatLtToChooseZero")

(set-goal "all n Choose n(Succ n)=Zero")
(assume "n")
(use "NatLtToChooseZero")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Choose n(Succ n)" "Zero")

(set-goal "all n Choose n n=Succ Zero")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Choose n n" "Succ Zero")

(set-goal "all n Choose(Succ n)n=Succ n")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "Choose(Succ n)n" "Succ n")

;; NatLeToLtZeroChoose
(set-goal "all n,m(m<=n -> Zero<Choose n m)")
(ind)
;; 2,3
(cases)
;; 4,5
(assume "Useless")
(use "Truth")
;; 5
(assume "n" "Absurd")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
;; 9,10
(assume "Useless")
(use "Truth")
(assume "m" "m<=n")
(ng #t)
(use "NatLeLtTrans" (pt "Zero+Choose n(Succ m)"))
(use "Truth")
(simp "NatLt3RewRule")
(use "IH")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "NatLeToLtZeroChoose")

;; NatLeToLeOneChoose
(set-goal "all n,m(m<=n -> Succ Zero<=Choose n m)")
(assume "n" "m" "m<=n")
(use "NatLtToSuccLe")
(use  "NatLeToLtZeroChoose")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "NatLeToLeOneChoose")

;; NatPosToChooseSuccPred
(set-goal "all n,m(Zero<m ->  Choose(Succ n)m=Choose n(Pred m)+Choose n m)")
(ind)
;; 2,3
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 5
(assume "n")
(ng #t)
(assume "Useless")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "Useless")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPosToChooseSuccPred")

;; 2023-03-05.  Factorial added.  Relation between Choose and NatF proved.

(add-program-constant "NatF" (py "nat=>nat"))
(add-computation-rules
 "NatF Zero" "Succ Zero"
 "NatF(Succ n)" "NatF n*(Succ n)")

(set-totality-goal "NatF")
(fold-alltotal)
(ind)
(use "TotalVar")
(assume "n" "Tn")
(ng #t)
(use "NatPlusTotal")
(use "NatTimesTotal")
(use "Tn")
(use "TotalVar")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

;; NatTimesChooseNatF
(set-goal "all n,m(m<=n -> Choose n m*NatF(n--m)*NatF m=NatF n)")
(ind)
;; 2,3
(cases)
;; 4,5
(assume "Useless")
(use "Truth")
;; 5
(assume "n" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
;; 10,11
(assume "Useless")
(use "Truth")
;; 11
(assume "m" "m<=n")
(use "NatLeCases" (pt "m")(pt "n"))
(use "m<=n")
;; 15
(assume "m<n")
(defnc "n0" "NatF(Succ n)")
(defnc "m0" "NatF(Succ m)")
(simp "<-" "n0Def")
(simp "<-" "m0Def")
(ng #t)
(simp (pf "Choose n m*NatF(n--m)*m0=Choose n m*NatF(n--m)*(NatF m)*(Succ m)"))
(simp "IH")
(simp (pf "NatF(n--m)=NatF(n--(Succ m))*(n--m)"))
(simp (pf "Choose n(Succ m)*(NatF(n--Succ m)*(n--m))*m0=
           Choose n(Succ m)*NatF(n--Succ m)*m0*(n--m)"))
(simp "m0Def")
(assert "Succ m<=n")
(use "NatLtToSuccLe")
(use "m<n")
(assume "Sm<=n")
(inst-with-to "IH" (pt "Succ m") "Sm<=n" "Inst")
(simp "Inst")
(simp "<-" "NatTimesPlusDistr")
;; ?^51:NatF n*(Succ m+(n--m))=n0
(simp "NatPlusMinus")
(simp "NatPlusComm")
(simp "<-" "NatPlusMinusAssoc")
(simp "NatMinus1RewRule")
(simp "n0Def")
(use "Truth")
;; 56
(use "Truth")
;; 53
(use "NatLtToLe")
(use "m<n")
;; 42
(simp "<-" "NatTimesAssoc")
(simp "<-" "NatTimesAssoc")
(simp (pf "(n--m)*m0=m0*(n--m)"))
(use "Truth")
(use "NatTimesComm")
;; 40
(simp (pf "n--m=Succ(n--Succ m)"))
(use "Truth")
(ng #t)
(simp "NatSuccPred")
(use "Truth")
(simp (pf "Zero=m--m"))
(use "NatLtMonMinusLeft")
(use "m<n")
(use "Truth")
(use "Truth")
;; 38
(use "m<=n")
;; 36
(simp "m0Def")
(use "Truth")
;; 16
(assume "m=n")
(simp "m=n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesChooseNatF")

;; NatLtZeroNatF
(set-goal "all n Zero<NatF n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "NatLtLeTrans" (pt "Zero+NatF n"))
(use "IH")
(use "NatLeMonPlus")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroNatF")
 
;; NatLeMonIf
(set-goal
 "all n,n0,m,m0(n<=n0 -> m<=m0 -> all w [if w n m]<=[if w n0 m0])")
(assume "n" "n0" "m" "m0" "n<=n0" "m<=m0")
(cases)
(use "n<=n0")
(use "m<=m0")
;; Proof finished.
;; (cp)
(save "NatLeMonIf")

(add-program-constant "NatLub" (py "nat=>nat=>(nat=>nat)=>nat"))

(add-computation-rules
 "NatLub l Zero ms" "Zero"
 "NatLub l(Succ n)ms" "NatLub l n ms max ms(l+n)")

;; (pp (nt (pt "NatLub l(PosToNat 3)ms")))
;; ms l max ms(Succ l)max ms(Succ(Succ l))

(set-totality-goal "NatLub")
(assert "all ms,l,n TotalNat(NatLub l n ms)")
(assume "ms" "l")
(ind)
;; 5,6
(use "TotalVar")
;; 6
(assume "n" "IH")
(ng #t)
(use "NatMaxTotal")
(use "IH")
(use "TotalVar")
;; 2
;; Assertion proved.
(assume "Assertion")
(fold-alltotal)
(assume "l")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "ms")
(use "Assertion")
;; Proof finished.
;; (cp)
(save-totality)

;; NatLubLUB
(set-goal "all ms,l,n,n0(all m(m<n0 -> ms(l+m)<=n) -> NatLub l n0 ms<=n)")
(assume "ms" "l" "n")
(ind)
;; 3,4
(ng #t)
(auto)
;; 4
(assume "n0" "IH" "n0lnProp")
(ng #t)
(use "NatMaxLUB")
;; 8,9
(use "IH")
(assume "m" "m<n0")
(use "n0lnProp")
(use "NatLtTrans" (pt "n0"))
(use "m<n0")
(use "Truth")
;; 9
(use "n0lnProp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLubLUB")

;; NatLubSplit
(set-goal "all ms,l,n,n0(
 NatLub l n ms max NatLub(l+n)n0 ms=NatLub l(n+n0)ms)")
(assume "ms" "l" "n")
(ind)
;; 3,4
(ng #t)
(use "Truth")
;; 4
(assume "n0" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLubSplit")

;; NatLtPred
(set-goal "all n(Zero<n -> Pred n<n)")
(cases)
;; 2,3
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtPred")

;; We define an inductive predicate (AllLtNat n ws) as alternative to
;; the boolean constant (AllBNat n ws).  Both are equivalent.

;; Advantages of the inductive predicate: no unwanted unfoldings, and
;; one avoids logical arguments with boolean connectives.

;; Advantages of the boolean constant: unfolding can simplify proofs,
;; and one can compute closed terms.

;; (set! COMMENT-FLAG #t)
;; (remove-pvar-name "AllLtNat")
(add-ids
 (list (list "AllLtNat" (make-arity (py "nat") (py "nat=>boole"))))
 '("all ws AllLtNat Zero ws" "InitAllLtNat")
 '("all n,ws(AllLtNat n ws -> ws n -> AllLtNat(Succ n)ws)" "GenAllLtNat"))

;; AllLtNatIntro
(set-goal "all ws,n(all n1(n1<n -> ws n1) -> AllLtNat n ws)")
(assume  "ws")
(ind)
(assume "Useless")
(use "InitAllLtNat")
(assume "n" "IH" "Hyp")
(use "GenAllLtNat")
(use "IH")
(assume "n0" "n0<n")
(use "Hyp")
(use "NatLtTrans" (pt "n"))
(use "n0<n")
(use "Truth")
(use "Hyp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "AllLtNatIntro")

;; AllLtNatElim
(set-goal "all ws,n(AllLtNat n ws -> all n1(n1<n -> ws n1))")
(assume  "ws" "n" "Hyp")
(elim "Hyp")
;; 3,4
(assume "ws0" "n0" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "n0" "ws0" "Useless" "LtH" "ws n0")
(assume "m" "m<Sn0")
(use "NatLtSuccCases" (pt "m") (pt "n0"))
;; 9-11
(use "m<Sn0")
;; 10
(use "LtH")
;; 11
(assume "m=n0")
(simp "m=n0")
(use "ws n0")
;; Prof finished.
;; (cp)
(save "AllLtNatElim")

(add-program-constant "NatSum" (py "nat=>nat=>(nat=>nat)=>nat"))

(add-computation-rules
 "NatSum n Zero ns" "Zero"
 "NatSum n(Succ m)ns" "NatSum n m ns+ns(n+m)")

(set-totality-goal "NatSum")
(assert "all ns,n,m TotalNat(NatSum n m ns)")
(assume "ns" "n")
(ind)
;; 5,6
(ng #t)
(use "TotalVar")
;; 6
(assume "m" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(assume "Assertion")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "ns")
(use "Assertion")
;; Proof finished.
;; (cp)
(save-totality)

;; NatSumCompat
(set-goal "all ns,ms,n,m(all l(n<=l -> l<n+m -> ns l=ms l) ->
 NatSum n m ns=NatSum n m ms)")
(assume "ns" "ms" "n")
(ind)
;; 3,4
(assume "Useless")
(use "Truth")
;; 4
(assume "m" "IH" "EqHyp")
(ng #t)
(simp "<-" (pf "ns(n+m)=ms(n+m)"))
(simp "IH")
(use "Truth")
(assume "l" "n<=l" "l<n+m")
(use "EqHyp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
(use "EqHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSumCompat")

;; NatSumAssoc (new, with n for 0)
(set-goal "all ns,n,m ns n+NatSum n m([l]ns(Succ l))=NatSum n(Succ m)ns")
(assume "ns" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSumAssoc")

;; NatSumShiftOne
(set-goal "all ns,n,m NatSum(Succ n)m ns=NatSum n m([n0]ns(Succ n0))")
(assume "ns" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(simp "NatSum1CompRule")
(simp "NatSum1CompRule")
(bpe-ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSumShiftOne")

;; NatSumShift
(set-goal "all ns,n,n1,m NatSum(n+n1)m ns=NatSum n m([n0]ns(n0+n1))")
(assume "ns" "n" "n1")
(ind)
(use "Truth")
(assume "m" "IH")
(simp "NatSum1CompRule")
(simp "NatSum1CompRule")
(bpe-ng #t)
(simp "IH")
(simp (pf "n+n1+m=(n+m)+n1"))
(use "Truth")
(simp "<-" "NatPlusAssoc")
(simp "<-" "NatPlusAssoc")
(simp (pf "m+n1=n1+m"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
(cp)
(save "NatSumShift")

;; NatSumMonBd
(set-goal "all n,m,l,ns(m<=l -> NatSum n m ns<=NatSum n l ns)")
(assert "all n,m0,ns,m(NatSum n m0 ns<=NatSum n(m0+m)ns)")
(assume "n" "m0" "ns")
(ind)
;; 5,6
(use "Truth")
;; 6
(assume "m" "IH")
(ng #t)
(use "NatLeTrans" (pt "NatSum n(m0+m)ns"))
(use "IH")
(use "Truth")
;; Assertion proved.
(assume "Assertion" "n" "m" "l" "ns" "m<=l")

(assert "l=m+(l--m)")
(simp "NatPlusComm")
(simp "NatMinusPlus")
(use "Truth")
(use "m<=l")
;; Assertion proved.
(assume "LeH")

(simp "LeH")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "NatSumMonBd")

;; NatLeMonSum
(set-goal "all ns,ms,n,m(all l(n<=l -> l<n+m -> ns l<=ms l) ->
 NatSum n m ns<=NatSum n m ms)")
(assume "ns" "ms" "n")
(ind)
;; 3,4
(strip)
(use "Truth")
;; 4
(assume "m" "IH" "LeHyp")
(ng #t)
(use "NatLeMonPlus")
(use "IH")
(assume "l" "n<=l" "l<n+m")
(use "LeHyp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
(use "LeHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeMonSum")

;; We prove that the order of a sum (indexed from 0) can be reverted.

;; NatSumComm
(set-goal "all ns,m NatSum Zero m ns=NatSum Zero m([n]ns(Pred(m--n)))")
(assume "ns")
(ind)
(use "Truth")
(assume "m" "IH")
(simp "NatSum1CompRule")
(simp "<-" "NatSumAssoc")
(bpe-ng #t)
(simp "NatPlusComm")
(ng #t)
(simp "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSumComm")

;; NatSumSplit
(set-goal "all ns,n,m,l(NatSum n m ns+NatSum(n+m)l ns=NatSum n(m+l)ns)")
(assume "ns" "n" "m")
(ind)
;; 3,4
(ng #t)
(use "Truth")
;; 4
(assume "l" "IH")
(ng #t)
(simp "NatPlusCancelEqR")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatSumSplit")

;; NatSumPlus
(set-goal "all ns,ms,m,n(NatSum n m ns+NatSum n m ms=NatSum n m([l]ns l+ms l))")
(assume "ns" "ms")
(ind)
;; 3,4
(assume "n")
(use "Truth")
;; 4
(assume "m" "IH" "n")
(ng #t)
(simp "<-" "IH")
(simp "NatPlusCancelEqR")
(simp "<-" "NatPlusAssoc")
(simp "<-" "NatPlusAssoc")
(simp "NatPlusCancelEqL")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(save "NatSumPlus")

;; NatTimesSum
(set-goal "all n,m n*m=NatSum Zero m([n0]n)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesSum")

;; Now we can prove the Gauss trick

;; NatTimesDoubleSum
(set-goal "all n Succ n*n=NatDouble(NatSum Zero n Succ)")
(assume "m")
(simp "NatTimesSum")
(simp "<-" "NatDoublePlusEq")
(simp (pf "NatSum Zero m Succ+NatSum Zero m Succ=
           NatSum Zero m Succ+NatSum Zero m([n]Succ(Pred(m--n)))"))
;; 5,6
(inst-with-to
 "NatSumPlus"
 (pt "Succ") (pt "[n]Succ(Pred(m--n))") (pt "m") (pt "Zero") "Inst")
(simp "Inst")
(drop "Inst")
(bpe-ng #t)
;; ?^11:NatSum Zero m([n]Succ m)=NatSum Zero m([n]Succ n+Succ(Pred(m--n)))
(use "NatSumCompat")
;; 12
(assume "n" "Useless" "n<m")
(bpe-ng #t)
(simp "NatSuccPred")
(ng #t)
(simp "NatPlusComm")
(simp "NatMinusPlus")
(use "Truth")
(use "NatLtToLe")
(use "n<m")
;; ?^16:Zero<m--n
(simp (pf "Zero=n--n"))
(use "NatLtMonMinusLeft")
(use "n<m")
(use "Truth")
(use "Truth")
;; ?^6:NatSum 0 m Succ+NatSum 0 m Succ=
;;     NatSum 0 m Succ+NatSum 0 m([n]Succ(Pred(m--n)))
(inst-with-to "NatSumComm" (pt "Succ") (pt "m") "Inst")
(simp "<-" "Inst")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesDoubleSum")

(add-program-constant "NatProd" (py "nat=>nat=>(nat=>nat)=>nat"))

(add-computation-rules
 "NatProd n Zero ns" "Succ Zero"
 "NatProd n(Succ m)ns" "NatProd n m ns*ns(n+m)")

(set-totality-goal "NatProd")
(assert "all ns,n,m TotalNat(NatProd n m ns)")
(assume "ns" "n")
(ind)
;; 5,6
(ng #t)
(use "TotalVar")
;; 6
(assume "m" "IH")
(ng #t)
(use "NatTimesTotal")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(assume "Assertion")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "ns")
(use "Assertion")
;; Proof finished.
;; (cp)
(save-totality)

;; NatProdCompat
(set-goal "all ns,ms,n,m(all l(n<=l -> l<n+m -> ns l=ms l) ->
 NatProd n m ns=NatProd n m ms)")
(assume "ns" "ms" "n")
(ind)
;; 3,4
(strip)
(use "Truth")
;; 4
(assume "m" "IH" "EqHyp")
(ng #t)
(simp "<-" (pf "ns(n+m)=ms(n+m)"))
(simp "IH")
(use "Truth")
(assume "l" "n<=l" "l<n+m")
(use "EqHyp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
(use "EqHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatProdCompat")

;; NatProdAssoc
(set-goal "all ns,m ns Zero*NatProd Zero m([n]ns(n+1))=NatProd Zero(Succ m)ns")
(assume "ns")
(ind)
;; 3,4
(ng #t)
(use "Truth")
;; 4
(assume "m" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatProdAssoc")

;; NatLeMonProd
(set-goal "all ns,ms,n,m(all l(n<=l -> l<n+m -> ns l<=ms l) ->
 NatProd n m ns<=NatProd n m ms)")
(assume "ns" "ms" "n")
(ind)
;; 3,4
(strip)
(use "Truth")
;; 4
(assume "m" "IH" "LeHyp")
(ng #t)
(use "NatLeMonTimes")
(use "IH")
(assume "l" "n<=l" "l<n+m")
(use "LeHyp")
(use "n<=l")
(use "NatLtTrans" (pt "n+m"))
(use "l<n+m")
(use "Truth")
(use "LeHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeMonProd")

;; We prove that the order of a product (indexed from 0) can be reverted.

;; NatProdComm
(set-goal "all ns,m NatProd Zero m ns=NatProd Zero m([n]ns(Pred(m--n)))")
(assume "ns")
(ind)
(use "Truth")
(assume "m" "IH")
(simp "NatProd1CompRule")
(simp "<-" "NatProdAssoc")
(bpe-ng #t)
(simp "NatTimesComm")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatProdComm")

;; We want to use the Gauss trick for products

;; NatTimesProd (general version)
(set-goal
 "all ns,ms,m,n NatProd n m ns*NatProd n m ms=NatProd n m([l]ns l*ms l)")
(assume "ns" "ms")
(ind)
(assume "n")
(use "Truth")
(assume "m" "IH" "n")
(ng #t)
(simp "<-" "IH")
(use "NatLeAntiSym")
;; 9,10
(use "NatLeMonTimes")
(simp "<-" "NatTimesAssoc")
(simp "<-" "NatTimesAssoc")
(use "NatLeMonTimes")
(use "Truth")
(simp "NatTimesComm")
(use "Truth")
(use "Truth")
;; 10
(use "NatLeMonTimes")
(simp "<-" "NatTimesAssoc")
(simp "<-" "NatTimesAssoc")
(use "NatLeMonTimes")
(use "Truth")
(simp "NatTimesComm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatTimesProd")

;; NatProdSplit (generalizes NatTimesProdBound)
(set-goal "all ns,n,m,l NatProd n m ns*NatProd(n+m)l ns=NatProd n(m+l)ns")
(assume "ns" "m" "n")
(ind)
;; 3,4
(ng #t)
(use "Truth")
;; 4
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; (cp)
(save "NatProdSplit")

;; NatProdSplitZero (was NatTimesProdBound)
(set-goal "all ns,m,l NatProd Zero m ns*NatProd m l ns=NatProd Zero(m+l)ns")
(strip)
(simp "<-" "NatProdSplit")
(use "Truth")
;; (cp)
(save "NatProdSplitZero")

;; NatProdShiftZero
(set-goal "all n,ns,m NatProd 0 m ns=NatProd n m([l]ns(l--n))")
(assume "n" "ns")
(ind)
(search)
(assume "m" 1)
(ng)
(simp 1)
(use "Truth")
;; (cp)
(save "NatProdShiftZero")

;; NatProdShift
(set-goal "all ns,n,n0,m NatProd(n+n0)m ns=NatProd n m([n1]ns(n1+n0))")
(assume "ns" "n" "n1")
(ind)
(use "Truth")
(assume "m" "IH")
(simp "NatProd1CompRule")
(simp "NatProd1CompRule")
(bpe-ng #t)
(simp "IH")
(simp (pf "n+n1+m=(n+m)+n1"))
(use "Truth")
(simp "<-" "NatPlusAssoc")
(simp "<-" "NatPlusAssoc")
(simp (pf "m+n1=n1+m"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cp)
(save "NatProdShift")

;; NatProdShiftZeroDown
(set-goal "all n,ms,m NatProd 0 m ms=NatProd n m([l]ms(l--n))")
(assume "n" "ms")
(ind)
(search)
(assume "m" 1)
(ng)
(simp 1)
(use "Truth")
;; (cp)
(save "NatProdShiftZeroDown")

;; NatProdOne
(set-goal "all m NatProd 0 m([n]1)=1")
(ind)
(use "Truth")
(assume "n" 1)
(ng)
(simp 1)
(use "Truth")
;; (cp)
(save "NatProdOne")

;; the factorial NatF is a special case of NatProd.

;; NatFProd
(set-goal "all n NatF n=NatProd Zero n Succ")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatFProd")

;; Added 2024-10-04
  
;; We now deal with sequences of objects of an arbitrary type.

(add-var-name "alphas" (py "nat=>alpha"))

;; SeqShiftBdElim
(set-goal "all alphas,n,m(all l(l<m -> (Pvar alpha)^(alphas(n+l))) ->
 all l(n<=l -> l<n+m -> (Pvar alpha)^ (alphas l)))")
(assume "alphas" "n" "m" "H1" "l" "LBd" "UBd")
(simp (pf "l=n+(l--n)"))
(use "H1")
;; ?^5:l--n<m
(simp (pf "m=n+m--n"))
(use "NatLtMonMinusLeft")
(use "UBd")
(use "LBd")
(simp "NatPlusComm")
(use "Truth")
;; ?^4:l=n+(l--n)
(simp "NatPlusMinusAssoc")
(use "Truth")
(use "LBd")
;; Proof finished.
;; (cp)
(save "SeqShiftBdElim")

;; SeqShiftBdIntro
(set-goal "all alphas,n,m(
 all l(n<=l -> l<n+m -> (Pvar alpha)^ (alphas l)) ->
 all l(l<m -> (Pvar alpha)^(alphas(n+l))))")
(assume "alphas" "n" "m" "H1" "l" "UBd")
(use "H1")
(use "Truth")
(use "UBd")
;; Proof finished.
;; (cp)
(save "SeqShiftBdIntro")

;; SeqShiftElim
(set-goal "all alphas,n(all l((Pvar alpha)^(alphas(n+l))) ->
 all l(n<=l -> (Pvar alpha)^(alphas l)))")
(assume "alphas" "n" "H1" "l" "n<=l")
(simp (pf "l=n+(l--n)"))
(use "H1")
;; ?^4:l=n+(l--n)
(simp "NatPlusComm")
;; ?^5:l=l--n+n
(simp "<-" "NatPlusMinusAssoc")
(simp "NatMinusPlusEq")
(use "Truth")
(use "n<=l")
;; Proof finished.
;; (cp)
(save "SeqShiftElim")

;; SeqShiftIntro
(set-goal "all alphas,n(
 all l(n<=l -> (Pvar alpha)^(alphas l)) ->
 all l (Pvar alpha)^(alphas(n+l)))")
(assume "alphas" "n" "H1" "l")
(use "H1")
(use "Truth")
;; Proof finished.
;; (cp)
(save "SeqShiftIntro")

(add-var-name "k" "j" "i" (py "nat"))
(add-var-name "ml" "ij" (py "nat yprod nat"))

;; YprodNatNatEqToEqD
(set-goal "all ml,ml0(ml=ml0 -> ml eqd ml0)")
(cases)
(assume "m" "l")
(cases)
(assume "m0" "l0")
(ng #t)
(assume "andbH")

(assert "m=m0")
(use "AndbElim0" (pt "l=l0"))
(use "andbH")
(assume "m=m0")

(assert "l=l0")
(use "AndbElim1" (pt "m=m0"))
(use "andbH")
(assume "l=l0")

(simp "m=m0")
(simp "l=l0")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "YprodNatNatEqToEqD")

;; NatPairEqD
(set-goal "all ml ml eqd(lft ml pair rht ml)")
(assume "ml")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "NatPairEqD")

;; NatPairEq
(set-goal "all ml ml=(lft ml pair rht ml)")
(assume "ml")
(simp "<-" "NatPairEqD")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPairEq")

;; NatPairEqToConj
(set-goal "all m,l,ml((m pair l)=ml -> m=lft ml andnc l=rht ml)")
(assume "m" "l")
(cases)
(assume "m0" "l0" "EqH")
(ng)
(split)
(use "AndbElim0" (pt "l=l0"))
(use "EqH")
(use "AndbElim1" (pt "m=m0"))
(use "EqH")
;; Proof finished.
;; (cp)
(save "NatPairEqToConj")

;; End of additions 2024-10-04
  
;; For NatSqrt
(add-computation-rules
 "NatSqrt n" "NatLeast(Succ n)([m]n<=m*m)")

(set-totality-goal "NatSqrt")
(fold-alltotal)
(assume "n")
(ng)
(use "TotalVar")
;; (cp)
(save-totality)

;; NatLtSqrtToSquareLt
(set-goal "all n,m(m<NatSqrt n -> m*m<n)")
(assume "n" "m")
(simp "NatSqrt0CompRule")
(assume 1)
(use "NatNotLeToLt")
(assume 2)
(inst-with "NatLeastLeIntro" (pt "Succ n") (pt "m") (pt "[m]n<=m*m") 2)
(assert "m<m")
(use "NatLtLeTrans" (pt "NatLeast(Succ n)([m0]n<=m0*m0)"))
(auto)
;; (cp)
(save "NatLtSqrtToSquareLt")

;; NatSqrtLeToLeSquare
(set-goal "all n,m(NatSqrt n<=m -> n<=m*m)")
(assume "n" "m")
(simp "NatSqrt0CompRule")
(assume 1)
(cases (pt "n<m"))
(assume 2)
(use "NatLeTrans" (pt "m*1"))
(use "NatLtToLe")
(use 2)
(use "NatLeMonTimes")
(use "Truth")
(cases (pt "m"))
(assume 3)
(simphyp 2 3)
(use 4)
(search)
(assume 2)
(inst-with "PropNatLeast" (pt "Succ n") (pt "n") (pt "[m0]n<=m0*m0") "?" "?")
(use "NatLeTrans"
     (pt "(NatLeast(Succ n)([m]n<=m*m))*(NatLeast(Succ n)([m]n<=m*m))"))
(use 3)
(use "NatLeMonTimes")
(use 1)
(use 1)
(use "NatLeTrans" (pt "n"))
(use "NatNotLtToLe")
(auto)
(cases (pt "n"))
(assume 4)
(use "Truth")
(search)
;; (cp)
(save "NatSqrtLeToLeSquare")

;; NatSquareSqrtId
(set-goal "all n NatSqrt(n*n)=n")
(cases)
(use "Truth")
(assume "n")
(use "NatLeAntiSym")
(simp "NatSqrt0CompRule")
(use "NatLeastLeIntro")
(use "Truth")
(assert "Succ n*Succ n<=NatSqrt(Succ n*Succ n)*NatSqrt(Succ n*Succ n)")
(simp "NatSqrt0CompRule")
(use-with "PropNatLeast"
 (pt "Succ(Succ n*Succ n)") (pt "Succ n") (pt "[m]Succ n*Succ n<=m*m")
 "?" "?")
(use "NatLeTrans" (pt "Succ n*Succ n"))
(use "NatLeTrans" (pt "Succ n*1"))
(use "Truth")
(use "NatLeMonTimes")
(auto)
(assume 1)
(use "NatNotLtToLe")
(assume "2")
(use "NatLeToNotLt" (pt "Succ n*Succ n")
 (pt "NatSqrt(Succ n*Succ n)*NatSqrt(Succ n*Succ n)"))
(use 1)
(use "NatLtMonTimes")
(use 2)
(use 2)
;; (cp)
(save "NatSquareSqrtId")

;; NatSqrtBound
(set-goal "all n NatSqrt n<=n")
(assume "n")
(simp "NatSqrt0CompRule")
(use "NatLeastLeIntro")
(cases (pt "n"))
(auto)
;; (cp)
(save "NatSqrtBound")

;; NatSqrtBoundPred
(set-goal "all n (2<n -> NatSqrt n<=Pred n)")
(cases)
(search)
(cases)
(search)
(cases)
(search)
(assume "n" 1)
(simp "NatSqrt0CompRule")
(use "NatLeastLeIntro")
(use "NatLeTrans" (pt "n*n+n+n+n+n"))
(auto)
;; (cp)
(save "NatSqrtBoundPred")

;; NatSqr
(set-goal "all n exl m m=NatSqrt n")
(assume "n")
(intro 0 (pt "NatSqrt n"))
(use "Truth")
;; (cp)
(save "NatSqr")

(animate "NatSqr")

;; NatSqrExFree
(set-goal "all n cNatSqr n=NatSqrt n")
(assume "n")
(use "Truth")
;; (cp)
(save "NatSqrExFree")

(deanimate "NatSqr")

;; (display-default-varnames)

;; nw: 	nat ysum gamma
;; g: 	gamma=>uysum(nat ysum gamma)
;; w: 	gamma
;; f: 	nat=>alpha=>alpha
;; xs: 	nat=>alpha
;; x: 	alpha
;; ns: 	nat=>nat
;; ws: 	nat=>boole
;; n: 	nat

(remove-var-name "nw")
(remove-var-name "g")
(remove-var-name "w")
(remove-var-name "f")
(remove-var-name "xs")
(remove-var-name "x")
;; (remove-var-name "ns")
;; (remove-var-name "ws")

(remove-var-name "k")
(remove-var-name "j")
(remove-var-name "i")
(remove-var-name "ml")
(remove-var-name "ij")

;; We keep the var names
;; n m l of type nat
;; ns of type nat=>nat
;; ws of type nat=> boole

