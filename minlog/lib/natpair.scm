;; 2025-07-28.  natpair.scm

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
;; (set! COMMENT-FLAG #t)
|#

(display "loading natpair.scm ...") (newline)

(add-var-name "k" "j" "i" (py "nat"))
(add-var-name "ml" "ij" (py "nat yprod nat"))

;; 1.  Quotient and remainder coding
;; =================================

;;  2    5    8
;;  1    4    7
;;  0    3    6   9

;; We define a decoding function QrD (was QrCToIj)

;; (remove-program-constant "QrD")
(add-program-constant "QrD" (py "nat=>nat=>nat yprod nat"))
(add-computation-rules
 "QrD n Zero" "Zero pair Zero"
 "QrD n(Succ k)"
 "([ij][if (rht ij<n)
           (lft ij pair Succ rht ij)
           (Succ lft ij pair Zero)])
  (QrD n k)")

;; (pp (nt (pt "QrD 2 Zero")))
;; (pp (nt (pt "QrD 2 1")))
;; (pp (nt (pt "QrD 2 2")))
;; (pp (nt (pt "QrD 2 3")))
;; (pp (nt (pt "QrD 2 4")))
;; (pp (nt (pt "QrD 2 5")))
;; (pp (nt (pt "QrD 2 6")))
;; (pp (nt (pt "QrD 2 7")))
;; (pp (nt (pt "QrD 2 8")))
;; (pp (nt (pt "QrD 2 9")))

;; > 0 pair 0
;; > 0 pair 1
;; > 0 pair 2
;; > 1 pair 0
;; > 1 pair 1
;; > 1 pair 2
;; > 2 pair 0
;; > 2 pair 1
;; > 2 pair 2
;; > 3 pair 0

;; (pp (nt (pt "QrD 6 754")))
;; 107 pair 5
;; (+ (* 107 7) 5)
;; 754

(set-totality-goal "QrD")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
(ng #t)
(use "TotalVar")
(assume "k" "IH")
(simp "QrD1CompRule")
(use "TotalApp")
(fold-alltotal)
(assume "ij")
(use "TotalVar")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; QrDStep
(set-goal "all n,i,j,k((i pair j)=QrD n k ->
 QrD n(Succ k)=[if (j<n) (i pair Succ j) (Succ i pair Zero)])")
(assume "n" "i" "j" "k" "PairEq")
(inst-with-to "NatPairEqToConj"
	      (pt "i") (pt "j") (pt "QrD n k") "PairEq" "Inst")
(ng #t)
(simp "<-" "Inst")
(simp "<-" "Inst")
(use "Truth")
;; Proof finished.
;; (cp)
(save "QrDStep")

;; QrDPropAux
(set-goal "all n,k(
 k=Succ n*lft(QrD n k)+rht(QrD n k) andnc rht(QrD n k)<=n)")
(assume "n")
(ind)
;; 3,4
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 4
(assume "k")
(ng #t)
(def "ij" "QrD n k")
(def "i" "lft ij")
(def "j" "rht ij")
(simp "<-" "ijDef")
(simp "<-" "iDef")
(simp "<-" "jDef")
(assume "IH")
(use "NatLeCases" (pt "j") (pt "n"))
;; 35-37
(use "IH")
;; 36
(assume "j<n")
(simp "j<n")
(ng #t)
(split)
(use "IH")
(use "NatLtToSuccLe")
(use "j<n")
;; 37
(assume "j=n")
(simp "j=n")
(ng #t)
(split)
(simp "<-" "NatPlusAssoc")
(simp (pf "n+i=i+j"))
(use "IH")
(simp "j=n")
(use "NatPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(save "QrDPropAux")

;; QrDProp1
(set-goal "all n,k,j,i((i pair j)=QrD n k -> k=Succ n*i+j andnc j<=n)")
(assume "n" "k" "j" "i" "EqH")
(inst-with-to "NatPairEqToConj" (pt "i") (pt "j") (pt "QrD n k") "EqH" "Conj")
(simp "Conj" 'left)
(simp "Conj" 'right)
(use "QrDPropAux")
;; Proof finished.
;; (cp)
(save "QrDProp1")

;; We now prove the inverse of "QrDProp1

;; QrDProp2
(set-goal "all n,k,j,i(k=Succ n*i+j -> j<=n -> (i pair j)=QrD n k)")
(assume "n")
(ind)
;; 3,4
(cases)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
;; 8
(assume "i")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 6
(assume "j" "i")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 4
(assume "k" "IH")
(cases)
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 20
(assume "i")
(simp (pf "Succ n*Succ i+Zero=Succ(Succ n*i+n)"))
(assume "EqH" "Useless")
(inst-with-to "IH" (pt "n") (pt "i") "EqH" "Truth" "Inst")
(inst-with-to "QrDStep" (pt "n") (pt "i") (pt "n") (pt "k") "Inst" "InstStep")
(simp "InstStep")
(use "Truth")
;; 26
(use "Truth")
;; 18
(assume "j" "i" "kEq" "j+1<=n")
(assert "(i pair j)=QrD n k")
(use "IH")
(use "kEq")
(use "NatLeTrans" (pt "Succ j"))
(use "Truth")
(use "j+1<=n")
;; Assertion proved.
(assume "PairEq")

(inst-with-to "QrDStep" (pt "n") (pt "i") (pt "j") (pt "k") "PairEq" "Inst")
(simp "Inst")
(simp (pf "j<n"))
(use "Truth")
(use "NatSuccLeToLt")
(use "j+1<=n")
;; Proof finished.
;; (cp)
(save "QrDProp2")

;; QrDUniq
(set-goal "all n,i,j,i0,j0(Succ n*i+j=Succ n*i0+j0 -> j<=n -> j0<=n ->
 i=i0 andnc j=j0)")
(assume "n" "i" "j" "i0" "j0")
(def "m" "Succ n")
(simp "<-" "mDef")
(assume "EqH" "jBd" "j0Bd")

(assert "i=i0")
(use "NatLeAntiSym")
;; 14,15
;; ?^14:i<=i0
(use "NatNotLtToLe")
(assume "LtH")
(assert "m*i0+j0<m*i+j")
(use "NatLtLeTrans" (pt "m*i0+m"))
;; 20,21
(ng #t)
(simp "mDef")
(use "NatLeToLtSucc")
(use "j0Bd")
;; 21
(use "NatLeTrans" (pt "m*(Succ i0)"))
(use "Truth")
(use "NatLeTrans" (pt "m*i"))
(use "NatLeMonTimes")
(use "Truth")
(use "NatLtToSuccLe")
(use "LtH")
(use "Truth")
;; Assertion proved.
(simp "EqH")
(assume "Absurd")
(use "Absurd")

;; ?^15:i0<=i symmetric 
(use "NatNotLtToLe")
(assume "LtH")
(assert "m*i+j<m*i0+j0")
(use "NatLtLeTrans" (pt "m*i+m"))
;; 38,39
(ng #t)
(simp "mDef")
(use "NatLeToLtSucc")
(use "jBd")
;; 39
(use "NatLeTrans" (pt "m*(Succ i)"))
(use "Truth")
(use "NatLeTrans" (pt "m*i0"))
(use "NatLeMonTimes")
(use "Truth")
(use "NatLtToSuccLe")
(use "LtH")
(use "Truth")
;; Assertion proved.
(simp "EqH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved
(assume "i=i0")
(split)
(use "i=i0")
;; ?^54:j=j0
(simphyp-with-to "EqH" "i=i0" "EqHS")
(simp "<-" "NatPlusCancelEqL" (pt "m*i0"))
(use "EqHS")
;; Proof finished.
;; (cp)
(save "QrDUniq")

;; (pp "QrDUniq")

;; (remove-program-constant "QrC")
(add-program-constant "QrC" (py "nat=>nat=>nat=>nat"))
(add-computation-rules
 "QrC n i j" "Succ n*i+j")

(set-totality-goal "QrC")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "i")
(fold-alltotal)
(assume "j")
(ng #t)
(use "TotalVar")
;; Prove finished.
;; (cp)
(save-totality)

;; (pp "QrDStep")

;; Need the converse of QrDProp1

;; (pp "QrDProp1")
;; all n,k,j,i((i pair j)=QrD n k -> k=Succ n*i+j andnc j<=n)
;; (pp "QrDProp2")
;; all n,k,j,i(k=Succ n*i+j -> j<=n -> (i pair j)=QrD n k)

;; (display-pconst "QrC")
;; QrC n i j	Succ n*i+j

;; QrCCDId
(set-goal "all n,k,j,i((i pair j)=QrD n k -> QrC n i j=k)")
(assume "n" "k" "j" "i" "PairEq")
(ng #t)
(use "NatEqSym")
(use "QrDProp1")
(use "PairEq")
;; Proof finished.
;; (cp)
(save "QrCDId")

;; QrDCId
(set-goal "all n,i,j(j<=n -> QrD n(QrC n i j)=(i pair j))")
(assume "n" "i" "j" "j<=n")
(simp "QrC0CompRule")
(simp "QrDProp2" (pt "n") (pt "Succ n*i+j"))
(use "Truth")
(use "j<=n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "QrDCId")

;; 2.  Root coding
;; ===============

;; Root coding is based on the observation that every number k can be
;; written uniquely in the form k=m*m+l with l<=m+m.  From the pair (m,l)
;; we obtain the coordinates (i,j) as follows.

;; 12   13   14   15
;;  6    7    8   11
;;  2    3    5   10
;;  0    1    4    9   16

;; If l<m take (m*m,l)
;; If m<=l<=2m take (m*m+l,m)

;;  "RtCToMlUniq
(set-goal
 "all m,l,m0,l0(m*m+l=m0*m0+l0 -> l<=m+m -> l0<=m0+m0 -> m=m0 andi l=l0)")

(assert "all m,l,m0,l0(m*m+l=m0*m0+l0 -> l<=m+m -> l0<=m0+m0 -> m0<=m)")
(assume "m" "l" "m0" "l0" "EqH" "lBd" "l0Bd")
(use "NatNotLtToLe")
(assume "m<m0")

(assert "m*m+l<m0*m0+l0")
(use "NatLeLtTrans" (pt "m*m+(m+m)"))
;; 9,10
(simp "NatLe6RewRule")
(use "lBd")
;; 10
(use "NatLtLeTrans" (pt "(m+1)*(m+1)"))
;; 12,13
(ng #t)
(use "Truth")
;; 13
(use "NatLeTrans" (pt "m0*m0"))
(use "NatLeMonTimes")
;; 17,18
(use "NatLtToSuccLe")
(use "m<m0")
;; 18
(use "NatLtToSuccLe")
(use "m<m0")
;; 16
(use "Truth")
;; Assertion proved.
(assume "A1")

(simphyp-with-to "A1" "EqH" "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "Aux")

;; ?^24:m=m0 andnc l=l0
(assume "m" "l" "m0" "l0" "EqH" "lBd" "l0Bd")

(assert "m=m0")
(use "NatLeAntiSym")
;; 28,29
(use "Aux" (pt "l0") (pt "l"))
;; 30-32
(use "NatEqSym")
(use "EqH")
;; 31
(use "l0Bd")
;; 32
(use "lBd")
;; 29
(use "Aux" (pt "l") (pt "l0"))
;; 34-36
(use "EqH")
;; 35
(use "lBd")
;; 36
(use "l0Bd")
;; Assertion proved.
(assume "m=m0")
(split)
;; 38,39
(use "m=m0")
;; 16
(simphyp-with-to "EqH" "m=m0" "EqHS")
(use "NatPlusCancelL" (pt "m0*m0"))
(use "EqHS")
;; Proof finished.
;; (cp)
(save "RtCToMlUniq")

;; (remove-program-constant "RtCToMl")
(add-program-constant "RtCToMl" (py "nat=>nat yprod nat"))
(add-computation-rules
 "RtCToMl Zero" "Zero pair Zero"
 "RtCToMl(Succ k)"
 "([ml][if (rht ml<lft ml+lft ml)
           (lft ml pair Succ rht ml)
           (Succ lft ml pair Zero)])(RtCToMl k)")

;; (pp (nt (pt "RtCToMl 1")))
;; (pp (nt (pt "RtCToMl 2")))
;; (pp (nt (pt "RtCToMl 3")))
;; (pp (nt (pt "RtCToMl 4")))
;; (pp (nt (pt "RtCToMl 5")))

;; > 1 pair 0
;; > 1 pair 1
;; > 1 pair 2
;; > 2 pair 0
;; > 2 pair 1

(set-totality-goal "RtCToMl")
(fold-alltotal)
(ind)
(ng #t)
(use "TotalVar")
(assume "k" "IH")
(simp "RtCToMl1CompRule")
(use "TotalApp")
(fold-alltotal)
(assume "ml")
(use "TotalVar")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; RtCToMlStep
(set-goal "all m,l,k((m pair l)=RtCToMl k ->
 RtCToMl(Succ k)=[if (l<m+m) (m pair Succ l) (Succ m pair Zero)])")
(assume "m" "l" "k" "PairEq")
(inst-with-to "NatPairEqToConj"
	      (pt "m") (pt "l") (pt "RtCToMl k") "PairEq" "Inst")
(ng #t)
(simp "<-" "Inst")
(simp "<-" "Inst")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCToMlStep")

;; RtCToMlPropAux
(set-goal "all k(k=lft(RtCToMl k)*lft(RtCToMl k)+rht(RtCToMl k) andnc
 rht(RtCToMl k)<=lft(RtCToMl k)+lft(RtCToMl k))")
(ind)
;; 2,3
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 3
(ng #t)
(assume "k")
(def "ml" "RtCToMl k")
(def "m" "lft ml")
(def "l" "rht ml")
(simp "<-" "mlDef")
(simp "<-" "mDef")
(simp "<-" "lDef")
(assume "IH")
(use "NatLeCases" (pt "l") (pt "m+m"))
;; 34-36
(use "IH")
;; 35
(assume "l<m+m")
(simp "l<m+m")
(ng #t)
(split)
(use "IH")
(use "NatLtToSuccLe")
(use "l<m+m")
;; 36
(assume "l=m+m")
(simp "l=m+m")
(ng #t)
(split)
(simp "<-" "NatPlusAssoc")
(simp "<-" "l=m+m")
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCToMlPropAux")

;; RtCToMlProp1
(set-goal "all k,m,l((m pair l)=RtCToMl k -> k=m*m+l andnc l<=m+m)")
(assume "k" "m" "l" "EqH")
(inst-with-to "NatPairEqToConj" (pt "m") (pt "l") (pt "RtCToMl k") "EqH" "Conj")
(simp "Conj" 'left)
(simp "Conj" 'right)
(use "RtCToMlPropAux")
;; Proof finished.
;; (cp)
(save "RtCToMlProp1")

;; We now prove the inverse of RtCToMlProp1

;; RtCToMlProp2
(set-goal "all k,l,m(k=m*m+l -> l<=m+m -> (m pair l)=RtCToMl k)")
(ind)
;; 2,3
(cases)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
;; 7
(assume "m")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 5
(assume "l" "m")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(assume "k" "IH")
(cases)
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 19
(assume "m")
(simp (pf "Succ m*Succ m+Zero=Succ(m*m+m+m)"))
(assume "EqH" "Useless")
(inst-with-to "IH" (pt "m+m") (pt "m") "EqH" "Truth" "Inst")
(inst-with-to "RtCToMlStep" (pt "m") (pt "m+m") (pt "k") "Inst" "InstStep")
(simp "InstStep")
(use "Truth")
;; 25
(use "Truth")
;; 17
(assume "l" "m" "kEq" "l+1<=m+m")
(assert "(m pair l)=RtCToMl k")
(use "IH")
(use "kEq")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=m+m")
;; Assertion proved.
(assume "PairEq")

(inst-with-to "RtCToMlStep" (pt "m") (pt "l") (pt "k") "PairEq" "Inst")
(simp "Inst")
(simp (pf "l<m+m"))
(use "Truth")
(use "NatSuccLeToLt")
(use "l+1<=m+m")
;; Proof finished.
;; (cp)
(save "RtCToMlProp2")

;; (pp "RtCToMlProp2")
;; all k,l,m(k=m*m+l -> l<=m+m -> (m pair l)=RtCToMl k)

;; Together with (pp "RtCToMlUniq")
;; all m,l,m0,l0(m*m+l=m0*m0+l0 -> l<=m+m -> l0<=m0+m0 -> m=m0 andnc l=l0)
;; we have shown that every k can uniquely be written in the form
;; k=m*m+l with l<=m+m.

;; The inverse of RtCToMl can be easily defined:

(add-program-constant "RtMlToC" (py "nat yprod nat=>nat"))
(add-computation-rules
 "RtMlToC(m pair l)" "m*m+l")

(set-totality-goal "RtMlToC")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; We have the expected properties RtMlToCToMlId and RtCToMlToCId:

;; RtMlToCToMlId
(set-goal "all k RtMlToC(RtCToMl k)=k")
(assume "k")
(def "ml" "RtCToMl k")
(def "m" "lft ml")
(def "l" "rht ml")
(simp "<-" "mlDef")
(simp "NatPairEq")
(simp "<-" "mDef")
(simp "<-" "lDef")
(ng #t)
(use "NatEqSym")
(use "RtCToMlProp1")
(simp (pf "(m pair l)=ml"))
(simp "mlDef")
(use "Truth")
(simp "mDef")
(simp "lDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtMlToCToMlId")

;; (pp "RtMlToCToMlId")
;; all k RtMlToC(RtCToMl k)=k

;; RtCToMlToCId
(set-goal "all ml(rht ml<=lft ml+lft ml -> RtCToMl(RtMlToC ml)=ml)")
(cases)
(assume "m" "l" "lBd")
(ng)
(simp "RtCToMlProp2" (pt "m*m+l"))
(use "Truth")
(use "lBd")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCToMlToCId")

;; We need the formulation with ml rather than (m pair l), since then
;; we can simplify with RtCToMl(RtMlToC ml)=ml for arbitrary arguments
;; ml of pair type, not only pairs.

;; ;; RtMlToCToMlId
;; (set-goal "all m,l(l<=m+m -> RtCToMl(RtMlToC(m pair l))=(m pair l))")
;; (assume "m" "l" "lBd")
;; (simp "RtMlToC0CompRule")
;; (simp "RtCToMlProp2" (pt "m*m+l"))
;; (use "Truth")
;; (use "lBd")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (save "RtMlToCToMlId")
;; (pp "RtMlToCToMlId")
;; all ml(rht ml<=lft ml+lft ml -> RtCToMl(RtMlToC ml)=ml)

;; From ml we can read off the coordinates ij of k's position (i.e.,
;; decode k).

;; (remove-program-constant "RtMlToIj")
(add-program-constant "RtMlToIj" (py "nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "RtMlToIj(m pair l)" "[if (l<m) (m pair l) (l--m pair m)]")

;; (pp (nt (pt "RtMlToIj(3 pair 0)")))
;; (pp (nt (pt "RtMlToIj(3 pair 1)")))
;; (pp (nt (pt "RtMlToIj(3 pair 2)")))
;; (pp (nt (pt "RtMlToIj(3 pair 3)")))
;; (pp (nt (pt "RtMlToIj(3 pair 4)")))
;; (pp (nt (pt "RtMlToIj(3 pair 5)")))
;; (pp (nt (pt "RtMlToIj(3 pair 6)")))

;; > 3 pair 0
;; > 3 pair 1
;; > 3 pair 2
;; > 0 pair 3
;; > 1 pair 3
;; > 2 pair 3
;; > 3 pair 3

(set-totality-goal "RtMlToIj")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "RtIjToMl")
(add-program-constant "RtIjToMl" (py "nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "RtIjToMl(i pair j)" "i max j pair[if (j<i) j (j+i)]")

(set-totality-goal "RtIjToMl")
(fold-alltotal)
(cases)
(assume "i" "j")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "RtIjToMl(3 pair 0)")))
;; (pp (nt (pt "RtIjToMl(3 pair 1)")))
;; (pp (nt (pt "RtIjToMl(3 pair 2)")))
;; (pp (nt (pt "RtIjToMl(0 pair 3)")))
;; (pp (nt (pt "RtIjToMl(1 pair 3)")))
;; (pp (nt (pt "RtIjToMl(2 pair 3)")))
;; (pp (nt (pt "RtIjToMl(3 pair 3)")))

;; > 3 pair 0
;; > 3 pair 1
;; > 3 pair 2
;; > 3 pair 3
;; > 3 pair 4
;; > 3 pair 5
;; > 3 pair 6

;; (display-pconst "RtIjToMl")
;; (pp "NatPairEqToConj")

;; RtIjToMlEst
(set-goal "all m,l,ij((m pair l)=RtIjToMl ij -> l<=m+m)")
(assume "m" "l")
(cases)
(assume "i" "j" "PairEq")
(ng "PairEq")
(assert "m=i max j")
(use "PairEq")
(assume "mDef")
(assert "l=[if (j<i) j (j+i)]")
(use "PairEq")
(assume "lDef")
(simp "mDef")
(simp "lDef")
(use "NatLeTrans" (pt "j+i"))
;; 14,15
(cases 'auto)
;; 16,17
(assume "Useless")
(ng #t)
(use "Truth")
;; 17
(assume "Useless")
(ng #t)
(use "Truth")
;; 15
(use "NatLeMonPlus")
(use "NatMaxUB2")
(use "NatMaxUB1")
;; Proof finished.
;; (cp)
(save "RtIjToMlEst")

;; RtMlToIjToMlId
(set-goal "all ij RtMlToIj(RtIjToMl ij)=ij")
(cases)
(assume "i" "j")
(ng)
(use "NatLeLtCases" (pt "i") (pt "j"))
;; 5,6
(assume "i<=j")
(simp "NatMaxEq2")
(simp (pf "j<i -> F"))
(ng #t)
(use "Truth")
(assume "j<i")
(assert "i<i")
(use "NatLeLtTrans" (pt "j"))
(use "i<=j")
(use "j<i")
(assume "Absurd")
(use "Absurd")
(use "i<=j")
;; 6
(assume "j<i")
(simp "j<i")
(ng #t)
(simp "NatMaxEq1")
(simp "j<i")
(use "Truth")
(use "NatLtToLe")
(use "j<i")
;; Proof finished.
;; (cp)
(save "RtMlToIjToMlId")

;; RtIjToMlToIjId
(set-goal "all ml(rht ml<=lft ml+lft ml -> RtIjToMl(RtMlToIj ml)=ml)")
(cases)
(assume "m" "l" "lBd")
(ng #t)
(use "NatLeLtCases" (pt "m") (pt "l"))
;; 5,6
(assume "m<=l")
(simp (pf "l<m -> F"))
(ng #t)
(simp (pf "(l--m)max m=m"))
(split)
(use "Truth")
(simp (pf "m<l--m -> F"))
(ng #t)
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "m<=l")
;; ?^16:m<l--m -> F
(assume "m<l--m")
(assert "m+m<l--m+m")
(use "m<l--m")
;; Assertion proved.
(simp "NatMinusPlusEq")
(assume "m+m<l")
(assert "l<l")
(use "NatLeLtTrans" (pt "m+m"))
(use "lBd")
(use "m+m<l")
(assume "Absurd")
(use "Absurd")
(use "m<=l")
;; ?^12:(l--m)max m=m
(use "NatMaxEq2")
(use "NatLeTrans" (pt "m+m--m"))
(use "NatLeMonMinusLeft")
(use "lBd")
(use "Truth")
;; 9
(assume "l<m")
(assert "l<l")
(use "NatLtLeTrans" (pt "m"))
(use "l<m")
(use "m<=l")
(assume "Absurd")
(use "Absurd")
;; 6
(assume "l<m")
(simp "l<m")
(ng #t)
(split)
(use "NatMaxEq1")
(use "NatLtToLe")
(use "l<m")
(simp "l<m")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtIjToMlToIjId")

(add-program-constant "RtC" (py "nat yprod nat=>nat"))
(add-computation-rules
 "RtC ij" "RtMlToC(RtIjToMl ij)")

(set-totality-goal "RtC")
(fold-alltotal)
(assume "ij")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

(add-program-constant "RtD" (py "nat=>nat yprod nat"))
(add-computation-rules
 "RtD k" "RtMlToIj(RtCToMl k)")

(set-totality-goal "RtD")
(fold-alltotal)
(assume "k")
(ng #t)
(use "TotalApp")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; RtDCId
(set-goal "all ij RtD(RtC ij)=ij")
(cases)
(assume "i" "j")
(simp "RtC0CompRule")
(simp "RtD0CompRule")
(simp "RtCToMlToCId")
(use "RtMlToIjToMlId")
;; ?^7:rht(RtIjToMl(i pair j))<=lft(RtIjToMl(i pair j))+lft(RtIjToMl(i pair j))
(ng #t)
;; [if (j<i) j (j+i)]<=i max j+i max j
(def "m" "i max j")
(simp "<-" "mDef")
(use "NatLeLtCases" (pt "i") (pt "j"))
;; 17,18
(assume "i<=j")
(assert "j<i -> F")
(assume "j<i")
(assert "i<i")
(use "NatLeLtTrans" (pt "j"))
(use "i<=j")
(use "j<i")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "A1")
(simp "A1")
(ng #t)
(simp "mDef")
(simp "NatMaxEq2")
(ng #t)
(use "i<=j")
(use "i<=j")
;; 18
(assume "j<i")
(simp "j<i")
(ng #t)
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "Truth")
;; Proof finished,
;; (cp)
(save "RtDCId")

;; RtCDId
(set-goal "all k RtC(RtD k)=k")
(assume "k")
(simp "RtD0CompRule")
(simp "RtC0CompRule")
(simp "RtIjToMlToIjId")
;; 5,6
(use "RtMlToCToMlId")
;; ?^6:rht(RtCToMl k)<=lft(RtCToMl k)+lft(RtCToMl k)
(use "RtCToMlPropAux")
;; Proof finished.
;; (cp)
(save "RtCDId")

;; RtDUp
(set-goal "all n,l(l<n -> RtD(n*n+l)=(n pair l))")
(assume "n" "l" "lBd")
(ng #t)
(def "ml0" "RtCToMl(n*n+l)")
(simp "<-" "ml0Def")
(def "m0" "lft ml0")
(def "l0" "rht ml0")

(assert "n*n+l=m0*m0+l0 andnc l0<=m0+m0")
(simp "m0Def")
(simp "l0Def")
(simp "ml0Def")
(use "RtCToMlPropAux")
;; Assertion proved.
(assume "A1")

(assert "n=m0 andnc l=l0")
(use "RtCToMlUniq")
(use "A1")
(use "NatLeTrans" (pt "n"))
(use "NatLtToLe")
(use "lBd")
(use "Truth")
(use "A1")
;; Assertion proved.
(assume "A2")

(simp (pf "ml0=(m0 pair l0)"))
(ng #t)
(simp "<-" "A2")
(simp "<-" "A2")
(simp "lBd")
(use "Truth")
;; 42
(simp "m0Def")
(simp "l0Def")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "RtDUp")

;; RtDFlat
(set-goal "all n,l(l<=n -> RtD(n*n+n+l)=(l pair n))")
(assume "n" "l" "lBd")
(ng #t)
(def "ml0" "RtCToMl(n*n+n+l)")
(simp "<-" "ml0Def")
(def "m0" "lft ml0")
(def "l0" "rht ml0")

(assert "n*n+(n+l)=m0*m0+l0 andnc l0<=m0+m0")
(simp "m0Def")
(simp "l0Def")
(simp "ml0Def")
(use "RtCToMlPropAux")
;; Assertion proved.
(assume "A1")

(assert "n=m0 andnc n+l=l0")
(use "RtCToMlUniq")
(use "A1")
(use "lBd")
(use "A1")
;; Assertion proved.
(assume "A2")

(simp (pf "ml0=(m0 pair l0)"))
(ng #t)
(simp "<-" "A2")
(simp "<-" "A2")
(ng #t)
(use "Truth")
;; 39
(simp "m0Def")
(simp "l0Def")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "RtDFlat")

;; RtCProp1
(set-goal "all n,i,j(n=i max j -> RtC(i pair j)<=n*n+n+n)")
(assume "n" "i" "j" "nEq")
(ng #t)
(simp "<-" "nEq")
(simp "<-" "NatPlusAssoc")
(simp "NatLe6RewRule")
(cases 'auto)
;; 7,8
(assume "j<i")
(ng #t)
(use "NatLeTrans" (pt "n"))
(simp "nEq")
(use "NatMaxUB2")
(use "Truth")
;; 8
(assume "NegH")
(ng #t)
(use "NatLeMonPlus")
(simp "nEq")
(use "NatMaxUB2")
(simp "nEq")
(use "NatMaxUB1")
;; Proof finished.
;; (cp)
(save "RtCProp1")

;; ;; RtCProp1
;; (set-goal "all n,i,j(n=i max j -> RtC(i pair j)<Succ n*Succ n)")
;; (assume "n" "i" "j" "nEq")
;; (ng #t)
;; (simp "<-" "nEq")
;; (use "NatLeLtTrans" (pt "n*n+(n+n)"))
;; (simp "NatLe6RewRule")
;; (cases 'auto)
;; ;; 8,9
;; (assume "j<i")
;; (ng #t)
;; (use "NatLeTrans" (pt "n"))
;; (simp "nEq")
;; (use "NatMaxUB2")
;; (use "Truth")
;; ;; 9
;; (assume "NegH")
;; (ng #t)
;; (use "NatLeMonPlus")
;; (simp "nEq")
;; (use "NatMaxUB2")
;; (simp "nEq")
;; (use "NatMaxUB1")
;; ;; 6
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (save "RtCProp1")

;; RtCProp2
(set-goal "all i,j,n(n=i max j ->  n*n<=RtC(i pair j))")
(assume "i" "j" "n" "nEq")
(ng #t)
(cases 'auto)
;; 4,5
(assume "j<i")
(ng #t)
(simp "nEq")
(use "Truth")
;; 5
(assume "NegH")
(ng #t)
(simp "nEq")
(simp "<-" "NatPlusAssoc")
(simp "NatLe2RewRule")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCProp2")

;; (pp "RtCProp1")
;; all n,i,j(n=i max j -> RtC(i pair j)<=n*n+n+n)
;; (pp "RtCProp2")
;; all i,j,n(n=i max j -> n*n<=RtC(i pair j))

;; LeSqRtCChar1
(set-goal "all n,i,j(n*n<=RtC(i pair j) -> n<=i max j)")
(assume "n" "i" "j" "SqLeHyp")
(def "m" "i max j")
(simp "<-" "mDef")
(use "NatNotLtToLe")
(assume "LtMaxHyp")
(assert "RtC(i pair j)<RtC(i pair j)")
(use "NatLtLeTrans" (pt "n*n"))
(use "NatLeLtTrans" (pt "m*m+m+m"))
(use "RtCProp1")
(simp "mDef")
(use "Truth")
(use "NatLtLeTrans" (pt "Succ m*Succ m"))
(use "Truth")
(use "NatLeMonTimes")
(use "NatLtToSuccLe")
(use "LtMaxHyp")
(use "NatLtToSuccLe")
(use "LtMaxHyp")
;; 16
(use "SqLeHyp")
;; 13
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "LeSqRtCChar1")

;; LeSqRtCChar2
(set-goal "all n,i,j(n<=i max j -> n*n<=RtC(i pair j))")
(assume "n" "i" "j" "LeH")
(use "NatLeTrans" (pt "i max j*(i max j)"))
;; 3,4
(use "NatLeMonTimes")
(use "LeH")
(use "LeH")
;; 4
(use "RtCProp2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "LeSqRtCChar2")

;; As consequences of LeSqRtCChar1 and LeSqRtCChar2 we obtain similar
;; implications with Lt.

;; LtRtCSqChar1
(set-goal "all n,i,j(i max j<n -> RtC(i pair j)<n*n)")
(assume "n" "i" "j" "LtH")
(use "NatNotLeToLt")
(assume "LeH")
(assert "n<n")
(use "NatLeLtTrans" (pt "i max j"))
(use "LeSqRtCChar1")
(use "LeH")
(use "LtH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "LtRtCSqChar1")

;; LtRtCSqChar2
(set-goal "all n,i,j(RtC(i pair j)<n*n -> i max j<n)")
(assume "n" "i" "j" "LtH")
(use "NatNotLeToLt")
(assume "LeH")
(assert "n*n<n*n")
(use "NatLeLtTrans" (pt "RtC(i pair j)"))
(use "LeSqRtCChar2")
(use "LeH")
(use "LtH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "LtRtCSqChar2")

;; ;; As a consequence of LeSqRtCChar1 we obtain an upper bound for
;; ;; RtC(i pair j) on the n-square, i.e., in case i max j<=n

;; ;; RtCUB
;; (set-goal "all n,i,j(i max j<=n -> RtC(i pair j)<=n*n+n+n)")
;; (assume "n" "i" "j" "LeH")
;; (use "NatLtSuccToLe")
;; (use "NatNotLeToLt")
;; (simp (pf "Succ(n*n+n+n)=Succ n*Succ n"))
;; (assert "Succ n<=i max j -> F")
;; ;; 7,8
;; ;; ?^8:Succ n<=i max j -> F
;; (assume "Succ n<=i max j")
;; (assert "i max j<i max j")
;; (use "NatLeLtTrans" (pt "n"))
;; (use "LeH")
;; (use "NatLtLeTrans" (pt "Succ n"))
;; (use "Truth")
;; (use "Succ n<=i max j")
;; (assume "Absurd")
;; (use "Absurd")
;; ;; ?^7:(Succ n<=i max j -> F) -> Succ n*Succ n<=RtC(i pair j) -> F
;; (assume "H1" "H2")
;; (use "H1")
;; (use "LeSqRtCChar1")
;; (use "H2")
;; ;; 6
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (remove-theorem "RtCUB")

;; As a consequence of LeSqRtCChar2 we obtain

;; LeIdMaxRtDLRToLeSqId
(set-goal "all k,n(n<=lft(RtD k)max rht(RtD k) -> n*n<=k)") 
(assume "k" "n")
(def "i" "lft(RtD k)")
(def "j" "rht(RtD k)")
(simp "<-" "iDef")
(simp "<-" "jDef")
(simp (pf "k=RtC(i pair j)"))
(use "LeSqRtCChar2")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "NatEqSym")
(use "RtCDId")
;; Proof finished.
;; (cp)
(save "LeIdMaxRtDLRToLeSqId")

;; RtCBd
(set-goal "all n,i,j(i<=n -> j<=n -> RtC(i pair j)<=n*n+n+n)")
(assume "n" "i" "j" "i<=n" "j<=n")
(use "NatLtSuccToLe")
(simp (pf "Succ(n*n+n+n)=Succ n*Succ n"))
(use "LtRtCSqChar1")
(use "NatLeToLtSucc")
(use "NatMaxLUB")
(use "i<=n")
(use "j<=n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCBd")

;; RtCBdMod
(set-goal "all n,ij(lft ij<=n -> rht ij<=n -> RtC ij<=n*n+n+n)")
(assume "n")
(cases)
(assume "i" "j" "i<=n" "j<=n")
(use "RtCBd")
(use "i<=n")
(use "j<=n")
;; Proof finished.
;; (cp)
(save "RtCBdMod")

;; 2024-08-20

;; RtDBd
(set-goal "all n,i,j,k(k<=n*n+n+n -> (i pair j)=RtD k -> (i max j)<=n)")
(assume "n" "i" "j" "k" "kBd")
(ng "ijDef")
(def "ml" "RtCToMl k")
(def "m" "lft ml")
(def "l" "rht ml")

(assert "(m pair l)=RtCToMl k")
(simp "<-" "mlDef")
(simp "mDef")
(simp "lDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "A0")

(inst-with-to "RtCToMlProp1" (pt "k") (pt "m") (pt "l") "A0" "Conj")
(assert "m*m+l<=n*n+n+n")
(simp "<-" "Conj")
(use "kBd")
;; Assertion proved.
(assume "A1")

(assert "m<=n")
(use "NatNotLtToLe")
(assume "n<m")
(assert "k<k")
(use "NatLtLeTrans" (pt "Succ n*Succ n"))
(use "NatLeToLtSucc")
(use "kBd")
(use "NatLeTrans" (pt "m*m"))
(use "NatLeMonTimes")
(use "NatLtToSuccLe")
(use "n<m")
(use "NatLtToSuccLe")
(use "n<m")
(simp "Conj")
(use "Truth")
;; Assertion proved.
;; 42
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "A2")

(ng #t)
(simp "<-" "A0")
(ng #t)
;; ?^58:(i pair j)=[if (l<m) (m pair l) (l--m pair m)] -> i max j<=n
(cases (pt "l<m"))
;; 59,60
(assume "l<m")
(ng #t)
(assume "ijDef")
(simp (pf "i=m"))
(simp (pf "j=l"))
(use "NatMaxLUB")
;; 68,69
(use "A2")
;; 69
(use "NatLtToLe")
(use "NatLtLeTrans" (pt "m"))
(use "l<m")
(use "A2")
(use "ijDef")
(use "ijDef")
;; 60
(assume "NegH")
(ng #t)
(assume "ijDef")
(simp (pf "i=l--m"))
(simp (pf "j=m"))
(use "NatMaxLUB")
;; 80,81
(use "NatLeTrans" (pt "m+m--m"))
(use "NatLeMonMinusLeft")
(use "Conj")
(use "A2")
;; 81
(use "A2")
;; 79
(use "ijDef")
;; 77
(use "ijDef")
;; Proof finished.
;; (cp)
(save "RtDBd")

;; End 2024-08-20

;; 2024-10-02

(set-goal "all n,k(n*n<=k -> k<n*n+n -> lft(RtD k)=n)")
(assume "n" "k" "LeH" "LtH")
(ng #t)

(display-pconst "RtCToMl")
(display-pconst "RtMlToIj")
;; RtMlToIj(m pair l)	[if (l<m) (m pair l) (l--m pair m)]
(pp "RtCToMlProp1")
;; all k,m,l((m pair l)=RtCToMl k -> k=m*m+l andnc l<=m+m)
(pp "RtCToMlProp2")
;; all k,l,m(k=m*m+l -> l<=m+m -> (m pair l)=RtCToMl k)

;; RtCToMlProp
(set-goal "all m,l,k ((m pair l)=RtCToMl k)=(l<=m+m andb(m pair l)=RtCToMl k)")
(assume "m" "l" "k")
(use "BooleAeqToEq")
;; 3,4
(assume "EqH")
(use "AndbIntro")
(use "RtCToMlProp1" (pt "k"))
(use "RtCToMlProp2")
(use "RtCToMlProp1")
(use "EqH")
(use "RtCToMlProp1" (pt "k"))
(use "EqH")
(use "EqH")
;; 4
(assume "Conj")
(use "Conj")
;; Proof finished.
;; (cp)
(save "RtCToMlProp")

;; 2024-10-03
;; End 2024-10-02

;; 3.  Gauss sum based coding
;; ==========================

;; 36
;; 28  37
;; 21  29  38
;; 15  22  30  39
;; 10  16  23  31  40
;;  6  11  17  24  32
;;  3   7  12  18  25  33
;;  1   4   8  13  19  26  34
;;  0   2   5   9  14  20  27  35

;; The Gauss sum (Gs n) is the sum of the first n natural numbers.

(add-program-constant "Gs" (py "nat=>nat"))
(add-computation-rules
 "Gs Zero" "Zero"
 "Gs(Succ n)" "Succ(Gs n)+n")

(set-totality-goal "Gs")
(fold-alltotal)
(ind)
(ng #t)
(intro 0)
;; 3
(assume "n" "IH")
(ng #t)
(use "NatPlusTotal")
(intro 1)
(use "IH")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; Before going into Gauss sum based coding we prove the main property
;; of Gauss sums called here GsChar: Gs n=NatHalf(n*Succ n).  This
;; requires some preparations.

;; GsEq
(set-goal "all n Gs(Succ n)=Gs n+Succ n")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsEq")

;; GsChar
(set-goal "all n Gs n=NatHalf(n*Succ n)")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(simp "GsEq")
(simp "IH")
(simp "<-" "NatDoubleEq")
(simp "NatDoublePlus")
(simp "NatDoubleHalfEven")
(simp "NatDoubleHalfEven")
(ng #t)
(simp "<-" "NatDoublePlusEq")
(use "Truth")
(use "NatEvenTimesSucc")
(use "NatEvenTimesSucc")
;; Proof finished.
;; (cp)
(save "GsChar")

;; GsProp
(set-goal "all n Gs(Succ n)+Gs n=(Succ n)*(Succ n)")
(ng)
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "<-" "IH")
(simp "NatPlusCancelEqR")
(simp "<-" "NatPlusAssoc")
(simp (pf "Gs n+n+Gs n+n=Gs n+n+(Gs n+n)"))
(simp "NatPlusCancelEqL")
(use "NatPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsProp")

;; For monotonicity of Gs we use NatSumMonBd together with a
;; characterization of Gs via NatSum:

;; NatSumGs
(set-goal "all n NatSum Zero n Succ=Gs n")
(ind)
(use "Truth")
(assume "n" "IH")
(simp "GsEq")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatSumGs")

;; GsMon
(set-goal "all n,m(n<=m -> Gs n<=Gs m)")
(assume "n" "m" "n<=m")
(simp "<-" "NatSumGs")
(simp "<-" "NatSumGs")
(use "NatSumMonBd")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "GsMon")

;; GsIncr
(set-goal "all n n<=Gs n")
(cases)
(use "Truth")
(assume "n")
(simp "GsEq")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsIncr")

;; GsCToMlUniq
(set-goal "all m,l,m0,l0(Gs m+l=Gs m0+l0 -> l<=m -> l0<=m0 -> m=m0 andnc l=l0)")

(assert "all m,l,m0,l0(Gs m+l=Gs m0+l0 -> l<=m -> m0<=m)")
(assume "m" "l" "m0" "l0" "EqH" "lBd")
(use "NatNotLtToLe")
(assume "m<m0")
(assert "Gs m+l<Gs m0+l0")
(use "NatLtLeTrans" (pt "Gs m+Succ m"))
;; 7,8
(simp "NatLt4RewRule")
(use "NatLeToLtSucc")
(use "lBd")
;; 8
(simp "<-" "GsEq")
(use "NatLeTrans" (pt "Gs m0"))
;; 12,13
(use "GsMon")
(use "NatLtToSuccLe")
(use "m<m0")
;; 13
(use "Truth")
;; Assertion proved.
(simp "EqH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.

(assume "Aux" "m" "l" "m0" "l0" "EqH" "lBd" "l0Bd")

(assert "m=m0")
(use "NatLeAntiSym")
;; 23,24
(use "Aux" (pt "l0") (pt "l"))
;; 25,26
(use "NatEqSym")
(use "EqH")
(use "l0Bd")
;; 24
(use "Aux" (pt "l") (pt "l0"))
;; 28,29
(use "EqH")
(use "lBd")
;; Assertion proved.
;; 21
(assume "m=m0")
(simp "m=m0")
(split)
(use "Truth")
(simphyp-with-to "EqH" "m=m0" "EqHS")
(use "NatPlusCancelL" (pt "Gs m0"))
(use "EqHS")
;; Proof finished.
;; (cp)
(save "GsCToMlUniq")

(add-program-constant "GsCToMl" (py "nat=>nat yprod nat"))
(add-computation-rules
 "GsCToMl Zero" "Zero pair Zero"
 "GsCToMl(Succ k)"
 "([ml][if (rht ml<lft ml)
           (lft ml pair Succ rht ml)
           (Succ lft ml pair Zero)])(GsCToMl k)")

;; (pp (nt (pt "GsCToMl 1")))
;; (pp (nt (pt "GsCToMl 2")))
;; (pp (nt (pt "GsCToMl 3")))
;; (pp (nt (pt "GsCToMl 4")))
;; (pp (nt (pt "GsCToMl 5")))
;; (pp (nt (pt "GsCToMl 6")))

;; > 1 pair 0
;; > 1 pair 1
;; > 2 pair 0
;; > 2 pair 1
;; > 2 pair 2
;; > 3 pair 0

(set-totality-goal "GsCToMl")
(fold-alltotal)
(ind)
(ng #t)
(use "TotalVar")
(assume "k" "IH")
(simp "GsCToMl1CompRule")
(use "TotalApp")
(fold-alltotal)
(assume "ml")
(use "TotalVar")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp "RtCToMlProp2")
;; all k,l,m(k=m*m+l -> l<=m+m -> (m pair l)=RtCToMl k)

;; GsCToMlStep
(set-goal "all m,l,k(
 (m pair l)=GsCToMl k -> 
 GsCToMl(Succ k)=[if (l<m) (m pair Succ l) (Succ m pair Zero)])")
(assume "m" "l" "k" "PairEq")
(inst-with-to "NatPairEqToConj"
	      (pt "m") (pt "l") (pt "GsCToMl k") "PairEq" "Inst")
(ng #t)
(simp "<-" "Inst")
(simp "<-" "Inst")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCToMlStep")

;; GsCToMlProp2
(set-goal "all k,l,m(k=Gs m+l -> l<=m -> (m pair l)=GsCToMl k)")
(ind)
;; 2,3
(cases)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
;; 7
(assume "m")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 5
(assume "l" "m")
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(assume "k" "IH")
(cases)
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 19
(assume "m")
(simp (pf "Gs(Succ m)+Zero=Succ(Gs m+m)"))
(assume "EqH" "Useless")
(inst-with-to "IH" (pt "m") (pt "m") "EqH" "Truth" "Inst")
(inst-with-to "GsCToMlStep" (pt "m") (pt "m") (pt "k") "Inst" "InstStep")
(simp "InstStep")
(use "Truth")
;; 25
(use "Truth")
;; 17
(assume "l" "m" "kEq" "l+1<=m")
(assert "(m pair l)=GsCToMl k")
(use "IH")
(use "kEq")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=m")
;; Assertion proved.
(assume "PairEq")
(inst-with-to "GsCToMlStep" (pt "m") (pt "l") (pt "k") "PairEq" "Inst")
(simp "Inst")
(simp (pf "l<m"))
(use "Truth")
(use "NatSuccLeToLt")
(use "l+1<=m")
;; Proof finished.
;; (cp)
(save "GsCToMlProp2")

;; GsCToMlPropAux
(set-goal "all k(
     k=Gs lft(GsCToMl k)+rht(GsCToMl k) andnc 
     rht(GsCToMl k)<=lft(GsCToMl k))")
(ind)
;; 2,3
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 4
(assume "k")
(def "ml" "GsCToMl k")
(def "m" "lft ml")
(def "l" "rht ml")
(simp "<-" "mlDef")
(simp "<-" "mDef")
(simp "<-" "lDef")
(assume "IH")
(pp "NatLeCases")
(use "NatLeCases" (pt "l") (pt "m"))
;; 33-35
(use "IH")
;; 34
(assume "l<m")
(ng #t)
(simp "<-" "mlDef")
(simp "<-" "mDef")
(simp "<-" "lDef")
(simp "l<m")
(ng #t)
(split)
(use "IH")
(use "NatLtToSuccLe")
(use "l<m")
;; 35
(assume "l=m")
(ng #t)
(simp "<-" "mlDef")
(simp "<-" "mDef")
(simp "<-" "lDef")
(simp "<-" "l=m")
(ng #t)
(split)
(simp (pf "Gs l=Gs m"))
(use "IH")
(simp "l=m")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCToMlPropAux")

;; GsCToMlProp1
(set-goal "all k,m,l((m pair l)=GsCToMl k -> k=Gs m+l andnc l<=m)")
(assume "k" "m" "l" "EqH")
(inst-with-to "NatPairEqToConj" (pt "m") (pt "l") (pt "GsCToMl k") "EqH" "Conj")
(simp "Conj" 'left)
(simp "Conj" 'right)
(use "GsCToMlPropAux")
;; Proof finished.
;; (cp)
(save "GsCToMlProp1")

;; (pp "GsCToMlProp1")
;; all k,m,l((m pair l)=GsCToMl k -> k=Gs m+l andnc l<=m)
;; (pp "GsCToMlProp2")
;; all k,l,m(k=Gs m+l -> l<=m -> (m pair l)=GsCToMl k)

;; Together with (pp "GsCToMlUniq")
;; all m,l,m0,l0(Gs m+l=Gs m0+l0 -> l<=m -> l0<=m0 -> m=m0 andnc l=l0)
;; we have shown that every k can uniquely be written in the form
;; k=Gs m+l with l<=m.

;; From ml we can read off the coordinates ij of k's position (i.e.,
;; decode k).

(add-program-constant "GsMlToC" (py "nat yprod nat=>nat"))
(add-computation-rules
 "GsMlToC(m pair l)" "Gs m+l")

(set-totality-goal "GsMlToC")
(fold-alltotal)
(cases)
(assume "m" "l")
(simp "GsMlToC0CompRule")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GsMlToCToMlId
(set-goal "all k GsMlToC(GsCToMl k)=k")
(assume "k")
(simp (pf "GsCToMl k=(lft(GsCToMl k)pair rht(GsCToMl k))"))
(ng #t)
(use "NatEqSym")
(use "GsCToMlPropAux")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "GsMlToCToMlId")

;; (search-about "Qr" "Id")
;; (search-about "Rt" "Id")
;; (search-about "Gs" "Id")
;; Names: AToBToAId means x= AToB(BToA x) "AToB past BtoA

;; (pp "GsCToMlPropAux")
;; all k(
;;  Gs lft(GsCToMl k)+rht(GsCToMl k)=k andnc 
;;  rht(GsCToMl k)<=lft(GsCToMl k))

;; GsCToMlToCId
(set-goal "all ml(rht ml<=lft ml -> GsCToMl(GsMlToC ml)=ml)")
(cases)
(assume "m" "l" "lBd")
(ng)
(simp "GsCToMlProp2" (pt "Gs m+l"))
(use "Truth")
(use "lBd")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCToMlToCId")

;; (pp "GsCToMlToCId")
;; all ml(rht ml<=lft ml -> GsCToMl(GsMlToC ml)=ml)
;; (pp "GsMlToCToMlId")
;; all k GsMlToC(GsCToMl k)=k

;; In addition we have a bijection between (nat yprod nat) and the set
;; of all pairs (m pair l) such that l<=m.

;; (remove-program-constant "GsMlToIj")
(add-program-constant "GsMlToIj" (py "nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "GsMlToIj(m pair l)" "l pair m--l")

(set-totality-goal "GsMlToIj")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "GsIjToMl")
(add-program-constant "GsIjToMl" (py "nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "GsIjToMl(i pair j)" "i+j pair i")

(set-totality-goal "GsIjToMl")
(fold-alltotal)
(cases)
(assume "i" "j")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; An immediate consequence of this definition is

;; GsIjToMlEst
(set-goal "all m,l,ij((m pair l)=GsIjToMl ij -> l<=m)")
(assume "m" "l")
(cases)
(assume "i" "j" "PairEq")
(ng "PairEq")
(simp (pf "m=i+j"))
(simp (pf "l=i"))
(use "Truth")
(use "PairEq")
(use "PairEq")
;; Proof finished.
;; (cp)
(save "GsIjToMlEst")

;; GsMlToIjToMlId
(set-goal "all ij GsMlToIj(GsIjToMl ij)=ij")
(cases)
(assume "i" "j")
(ng)
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsMlToIjToMlId")

;; GsIjToMlToIlId
(set-goal "all ml(rht ml<=lft ml -> GsIjToMl(GsMlToIj ml)=ml)")
(cases)
(assume "m" "l" "lBd")
(simp "GsMlToIj0CompRule")
(simp "GsIjToMl0CompRule")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(use "lBd")
;; Proof finished.
;; (cp)
(save "GsIjToMlToIjId")

;; ;; GsIjToMlToIlId
;; (set-goal "all m,l(l<=m -> GsIjToMl(GsMlToIj(m pair l))=(m pair l))")
;; (assume "m" "l" "lBd")
;; (simp "GsMlToIj0CompRule")
;; (simp "GsIjToMl0CompRule")
;; (simp "NatPlusComm")
;; (simp "NatMinusPlusEq")
;; (use "Truth")
;; (use "lBd")
;; ;; Proof finished.
;; ;; (cp)
;; (save "GsIjToMlToIjId")

(add-program-constant "GsD" (py "nat=>nat yprod nat"))
(add-computation-rules
 "GsD k" "GsMlToIj(GsCToMl k)")

(set-totality-goal "GsD")
(fold-alltotal)
(assume "k")
(simp "GsD0CompRule")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "GsC")
(add-program-constant "GsC" (py "nat yprod nat=>nat"))
(add-computation-rules
 "GsC(i pair j)" "GsMlToC(GsIjToMl(i pair j))")

(set-totality-goal "GsC")
(fold-alltotal)
(cases)
(assume "i" "j")
(simp "GsC0CompRule")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp "GsMlToCToMlId")
;; all k GsMlToC(GsCToMl k)=k
;; (pp "GsCToMlToCId")
;; all ml(rht ml<=lft ml -> GsCToMl(GsMlToC ml)=ml)

;; GsDCId
(set-goal "all ij GsD(GsC ij)=ij")
(cases)
(assume "i" "j")
(simp "GsC0CompRule")
(simp "GsD0CompRule")
(simp "GsCToMlToCId")
;; 6,7
(use "GsMlToIjToMlId")
;; ?^7:rht(GsIjToMl(i pair j))<=lft(GsIjToMl(i pair j))
(simp "GsIjToMl0CompRule")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsDCId")

;; GsCDId
(set-goal "all k GsC(GsD k)=k")
(assert "all ij GsC ij=GsMlToC(GsIjToMl ij)")
(cases)
(assume "i" "j")
(simp "GsC0CompRule")
(use "Truth")
;; Assertion proved.
(assume "A1" "k")
(ng)
(simp "A1")
(simp "GsIjToMlToIjId")
(use "GsMlToCToMlId")
;; ?^11:rht(GsCToMl k)<=lft(GsCToMl k)
(use "GsCToMlPropAux")
;; Proof finished.
;; (cp)
(save "GsCDId")

;; ;; GsCEq
;; (set-goal "all ij GsC ij=GsMlToC(GsIjToMl ij)")
;; (cases)
;; (assume "i" "j")
;; (simp "GsC0CompRule")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (remove-theorem "GsCEq")

;; ;; GsCDId
;; (set-goal "all k GsC(GsD k)=k")
;; (assume "k")
;; (ng)
;; (simp "GsCEq")
;; (simp "GsIjToMlToIjId")
;; (use "GsMlToCToMlId")
;; ;; ?^6:rht(GsCToMl k)<=lft(GsCToMl k)
;; (use "GsCToMlPropAux")
;; ;; Proof finished.
;; ;; (cp)
;; (save "GsCDId")

;; From the definitions of (display-pconst "GsMlToIj") and
;; (display-pconst "GsIjToMl") we obtain by normalization

;; GsCEq
(set-goal "all i,j GsC(i pair j)=Gs(i+j)+i")
(assume "i" "j")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCEq")

;; GsCD1
(set-goal "all i,j,k (GsC(i pair j)=k -> (i pair j)=GsD k)")
(assume "i" "j" "k" "EqH")
(simp "<-" "EqH")
(simp "GsDCId")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCD1")

;; GsCD2
(set-goal "all i,j,k ((i pair j)=GsD k -> GsC(i pair j)=k)")
(assume "i" "j" "k" "EqH")
(simp "EqH")
(simp "GsCDId")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCD2")

;; GsCD
(set-goal "all i,j,k (GsC(i pair j)=k)=((i pair j)=GsD k)")
(assume "i" "j" "k")
(use "BooleAeqToEq")
;; 3,4
(use "GsCD1")
;; 4
(use "GsCD2")
;; Proof finished.
;; (cp)
(save "GsCD")

;; (pp "GsCEq")
;; (pp "GsCProp")

;; 2024-09-29.  Done up to this point.  Next: s. 26. Sep/1

;; GsCL1
(set-goal "all n,i,j (i+j<n -> GsC(i pair j)<Gs n)")
(assume "n" "i" "j" "LtH")
(ng)
(use "NatLtLeTrans" (pt "Gs(i+j)+Succ(i+j)"))
;; 4,5
(ng #t)
(use "NatLeToLtSucc")
(use "Truth")
;; ?^5:Gs(i+j)+Succ(i+j)<=Gs n
(simp (pf "Gs(i+j)+Succ(i+j)=Gs(Succ(i+j))"))
;; 8,9
(use "GsMon")
(use "NatLtToSuccLe")
(use "LtH")
;; ?^9:Gs(i+j)+Succ(i+j)=Gs(Succ(i+j))
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCL1")

;; GsCL2
(set-goal "all n,i,j(GsC(i pair j)<Gs n -> i+j<n)")
(assume "n" "i" "j" "LtH")
(use "NatNotLeToLt")
(assume "LeH")
(assert "Gs n<Gs n")
(use "NatLeLtTrans" (pt "Gs(i+j)"))
;; 7,8
(use "GsMon")
(use "LeH")
;; ?^8:Gs(i+j)<Gs n
(use "NatLeLtTrans" (pt "Gs(i+j)+i"))
;; 10,11
(use "Truth")
;; ?^11:Gs(i+j)+i<Gs n
(use "NatLeLtTrans" (pt "GsC(i pair j)"))
;; 12,13
;; ?^12:Gs(i+j)+i<=GsC(i pair j)
(use "Truth")
(use "LtH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCL2")

;; GsCL
(set-goal "all n,i,j (i+j<n)=(GsC(i pair j)<Gs n)")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
(use "GsCL1")
;; 4
(use "GsCL2")
;; Proof finished.
;; (cp)
(save "GsCL")

;; GsCM1
(set-goal
 "all n,i,j(i+j=n -> Gs n<=GsC(i pair j) andnc GsC(i pair j)<Gs(Succ n))")
(assume "n" "i" "j" "EqH")
(simp "<-" "EqH")
(ng #t)
(split)
(use "Truth")
(use "NatLeToLtSucc")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsCM1")

;; GsCM2
(set-goal
 "all n,i,j(Gs n<=GsC(i pair j) -> GsC(i pair j)<Gs(Succ n) -> i+j=n)")
(assume "n" "i" "j" "LeH" "LtH")
(use "NatLeAntiSym")
;; 3,4
;; ?^3:i+j<=n
(use "NatNotLtToLe")
(assume "n<i+j")
(assert "Gs(Succ n)<Gs(Succ n)")
;; 7,8
(use "NatLeLtTrans" (pt "Gs(i+j)"))
;; 9,10
(use "GsMon")
(use "NatLtToSuccLe")
(use "n<i+j")
;; ?^10:Gs(i+j)<Gs(Succ n)
(use "NatLeLtTrans" (pt "GsC(i pair j)"))
;; 13,14
(use "Truth")
;; 14
(use "LtH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; ?^4:n<=i+j
(use "NatNotLtToLe")
(assume "i+j<n")
(assert "Gs(Succ(i+j))<Gs(Succ(i+j))")
(use "NatLeLtTrans" (pt "Gs n"))
(use "GsMon")
(use "NatLtToSuccLe")
(use "i+j<n")
(use "NatLeLtTrans" (pt "GsC(i pair j)"))
(use "LeH")
(ng #t)
(use "NatLeToLtSucc")
(use "Truth")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCM2")

;; GsCM
(set-goal
 "all n,i,j(i+j=n)=(Gs n<=GsC(i pair j) andb GsC(i pair j)<Gs(Succ n))")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
(assume "EqH")
(inst-with-to "GsCM1" (pt "n") (pt "i") (pt "j") "EqH" "Conj")
(split)
(use "Conj")
(use "Conj")
;; 4
(assume "Conj")
(use "GsCM2")
(use "Conj")
(use "Conj")
;; Proof finished.
;; (cp)
(save "GsCM")

;; GsCLM1
(set-goal "all n,i,j(i+j<=n -> GsC(i pair j)<Gs(Succ n))")
(assume "n" "i" "j" "LeH")
(simp "GsEq")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeMonPlus")
(use "GsMon")
(use "LeH")
(use "NatLeTrans" (pt "i+j"))
(use "Truth")
(use "LeH")
;; Proof finished.
;; (cp)
(save "GsCLM1")

;; GsCLM2
(set-goal "all n,i,j(GsC(i pair j)<Gs(Succ n)-> i+j<=n)")
(assume "n" "i" "j" "LtH")
(use "NatLeLtCases" (pt "Gs n") (pt "GsC(i pair j)"))
;; 3,4
(assume "LeH")
(assert "i+j=n")
(use "GsCM2")
(use "LeH")
(use "LtH")
(assume "EqH")
(simp "EqH")
(use "Truth")
;; 4
(assume "A1")
(assert "i+j<n")
(use "GsCL2")
(use "A1")
;; Assertion proved.
(assume "A2")
(use "NatLtToLe")
(use "A2")
;; Proof finished.
;; (cp)
(save "GsCLM2")

;; GsCLM
(set-goal "all n,i,j (i+j<=n)=(GsC(i pair j)<Gs(Succ n))")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
(use "GsCLM1")
;; 4
(use "GsCLM2")
;; Proof finished.
;; (cp)
(save "GsCLM")

;; 2024-10-01.  Done up to this point.


;; GsCR1
(set-goal "all n,i,j(n<i+j -> Gs(Succ n)<=GsC(i pair j))")
(assume "n" "i" "j" "LtH")
(use "NatNotLtToLe")
(assume "H1")
(assert "i+j<=n")
(use "GsCLM2")
(use "H1")
;; Assertion proved.
(assume "A1")
(assert "n<n")
(use "NatLtLeTrans" (pt "i+j"))
(use "LtH")
(use "A1")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCR1")

;; GsCR2
(set-goal "all n,i,j(Gs(Succ n)<=GsC(i pair j) -> n<i+j)")
(assume "n" "i" "j" "LeH")
(use "NatNotLeToLt")
(assume "H1")
(assert "GsC(i pair j)<Gs(Succ n)")
(use "GsCLM1")
(use "H1")
;; Assertion proved.
(assume "A1")
(assert "Gs(Succ n)<Gs(Succ n)")
(use "NatLeLtTrans" (pt "GsC(i pair j)"))
(use "LeH")
(use "A1")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCR2")

;; GsCR
(set-goal "all n,i,j (n<i+j)=(Gs(Succ n)<=GsC(i pair j))")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
(use "GsCR1")
;; 4
(use "GsCR2")
;; Proof finished.
;; (cp)
(save "GsCR")

;; GsCRM1
(set-goal "all n,i,j(n<=i+j -> Gs n<=GsC(i pair j))")
(assume "n" "i" "j" "LeH")
(use "NatNotLtToLe")
(assume "LtH")
(assert "i+j<n")
(use "GsCL2")
(use "LtH")
;; Assertion proved.
(assume "A1")
(assert "n<n")
(use "NatLeLtTrans" (pt "i+j"))
(use "LeH")
(use "A1")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCRM1")

;; GsCRM2
(set-goal "all n,i,j(Gs n<=GsC(i pair j) -> n<=i+j)")
(assume "n" "i" "j" "LeH")
(use "NatNotLtToLe")
(assume "LtH")
(assert "GsC(i pair j)<Gs n")
(use "GsCL1")
(use "LtH")
;; Assertion proved.
(assume "A1")
(assert "Gs n<Gs n")
(use "NatLeLtTrans" (pt "GsC(i pair j)"))
(use "LeH")
(use "A1")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GsCRM2")

;; GsCRM
(set-goal "all n,i,j (n<=i+j)=(Gs n<=GsC(i pair j))")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
(use "GsCRM1")
;; 4
(use "GsCRM2")
;; Proof finished.
;; (cp)
(save "GsCRM")

;; 4.  Quadratic Gauss sum based coding
;; ====================================

;; The quadratic Gauss based coding is necessary to relate the square
;; root based coding with the Gauss sum based coding.  It requires a
;; parameter $n$ to determine the size of the square.

;;  6  10  13  15
;;  3   7  11  14
;;  1   4   8  12
;;  0   2   5   9

;; To obtain the position $\pair{i}{j}$ from the code, we first need
;; auxiliary data $\pair{m}{l}$, where $m$ enumerates the diagonals and
;; $l$ determines the distance from the beginning of the diagonal.  If
;; the code $k$ is in the lower triangle (i.e., $k<\Gs(n+1)$) we can use
;; what has been done for Gauss code.  Otherwise the lengths of the
;; diagonals are decreasing from $n$.  Again we need auxiliary data
;; $\pair{m}{l}$, where $m$ enumerates the diagonals and $l$ determines
;; the distance from the beginning of the diagonal.  However, this time
;; the lengths of the diagonals decrease from $n$.  To describe this
;; setup we need a treatment of decreasing Gauss sums, whose first
;; summand is the parameter $n$.  We define $\Gds_n(m)$ as the decreasing
;; sum of the first $m$ numbers starting with $n$:

;; (remove-program-constant "Gds")
(add-program-constant "Gds" (py "nat=>nat=>nat"))
(add-computation-rules
 "Gds n Zero" "Zero"
 "Gds n(Succ m)" "Gds n m+(n--m)")

(set-totality-goal "Gds")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
(use "TotalVar")
(assume "m" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; NatEqGdsSum
(set-goal "all n,m Gds n m=NatSum Zero m(NatMinus n)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatEqGdsSum")

;; GdsMonBd
(set-goal "all n,m,l(m<=l -> Gds n m<=Gds n l)")
(assume "n" "m" "l")
(simp "NatEqGdsSum")
(simp "NatEqGdsSum")
(use "NatSumMonBd")
;; Proof finished.
;; (cp)
(save "GdsMonBd")

;; GdsSucc
(set-goal "Gds n(Succ m)=Gds n m+(n--m)")
(assume "n" "m")
(simp "NatEqGdsSum")
(ng #t)
(simp "<-" "NatEqGdsSum")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GdsSucc")

;; NatEqGdsGs
(set-goal "all n Gds n n=Gs n")
(assume "n")
(assert "all m,l(n=l+m -> Gds n m+Gs l=Gs n)")
(ind)
;; Basis
(assume "l")
(ng #t)
(assume "n=l")
(simp "n=l")
(use "Truth")
;; Step
(assume "m" "IH" "l" "n=l+m+1")
(inst-with-to "IH" (pt "Succ l") "n=l+m+1" "IHInst")
(ng #t)
(simp "<-" "IHInst")
(simp "<-" "NatPlusAssoc")
(simp "NatPlusCancelEqL")
(simp "NatPlusComm")
(ng #t)
(ng "n=l+m+1")
(simp "n=l+m+1")
(simp (pf "Succ(l+m)=Succ l+m"))
(simp "<-" "NatPlusMinusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "Assertion")
(inst-with-to "Assertion" (pt "n") (pt "Zero") "Truth" "Inst")
(use "Inst")
;; Proof finished.
;; (cp)
(save "NatEqGdsGs")

;; GdsUniq
(set-goal "all n,m,l,m0,l0(
     Gds n m+l=Gds n m0+l0 -> l<n--m -> l0<n--m0 -> m=m0 andnc l=l0)")

;; We prove an auxiliary proposition which will be used twice.
(assert "all n,l,l0,m,m0(
 m<m0 -> l<n--m -> l0<n--m0 -> Gds n m+l<Gds n m0+l0)")
(assume "n" "l" "l0" "m" "m0" "m<m0" "lH" "l0H")
(use "NatLtLeTrans" (pt "Gds n m+(n--m)"))
;; 5,6
(ng #t)
(use "lH")
;; 6
(use "NatLeTrans" (pt "Gds n(Succ m)"))
;; 8,9
(use "Truth")
;; 9
(use "NatLeTrans" (pt "Gds n m0"))
;; 10,11
(use "GdsMonBd")
(use "NatLtToSuccLe")
(use "m<m0")
;; 11
(use "Truth")
;; Assertion proved.
(assume "Aux")

(assume "n" "m" "l" "m0" "l0" "EqH" "lH" "l0H")

(assert "m=m0")
(use "NatLeAntiSym")
;; ?^18:m<=m0
(use "NatNotLtToLe")
(assume "m0<m")

(assert "Gds n m0+l0<Gds n m+l")
(use "Aux")
;; 24-26
(use "m0<m")
(use "l0H")
(use "lH")
(simp "EqH")
(assume "Absurd")
(ng "Absurd")
(use "Absurd")

;; ?^19:m0<=m
(use "NatNotLtToLe")
(assume "m<m0")

(assert "Gds n m+l<Gds n m0+l0")
(use "Aux")
;; 34-36
(use "m<m0")
(use "lH")
(use "l0H")
(simp "EqH")
(assume "Absurd")
(ng "Absurd")
(use "Absurd")

(assume "m=m0")
(split)
(use "m=m0")

(simphyp-with-to "EqH" "m=m0" "SEqH")
(use "NatPlusCancelL" (pt "Gds n m"))
(simp "m=m0")
(use "SEqH")
;; Proof finished.
;; (cp)
(save "GdsUniq")

;; GdsBd
(set-goal "all n,m,l(m<n -> l<n--m -> Gds n m+l<Gs n)")
(assume "n" "m" "l" "m<n" "lBd")
(use "NatLtLeTrans" (pt "Gds n m+(n--m)"))
(use "lBd")
(simp "<-" "GdsSucc")
(simp "<-" "NatEqGdsGs")
(use "GdsMonBd")
(use "NatLtToSuccLe")
(use "m<n")
;; Proof finished.
;; (cp)
(save "GdsBd")

;; Now assume that a given $k<(n+1)^2$ is in the upper triangle (i.e.,
;; $\Gs(n+1) \le k$).  Let $k_0 \defeq k-\Gs(n+1)$ (hence $k_0<\Gs(n)$).
;; We want to define from $n$ and $k_0$ the auxiliary data $\pair{m}{l}$
;; described above.  This means that we want a function $\GdsCToMl$
;; mapping $n$ and $k_0$ to $\pair{m}{l}$.  To define $\GdsCToMl$ we need
;; to distinguish cases whether $k_0+1<\Gds_n(m)$ or $k_0+1=\Gds_n(m)$.
;; To deal with these cases we define $\GdsCToMlLt$ and $\GdsCToMlEq$.
;; (remove-program-constant "GdsCToMlLt")

(add-program-constant "GdsCToMlLt" (py "nat=>nat=>nat yprod nat"))
(add-computation-rules
 "GdsCToMlLt n Zero" "Zero pair Zero"
 "GdsCToMlLt n(Succ k)"
 "([ml][if (Succ rht ml<n--lft ml)
        (lft ml pair Succ rht ml)
        (Succ lft ml pair Zero)])
  (GdsCToMlLt n k)")

(set-totality-goal "GdsCToMlLt")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(ind)
(ng #t)
(use "TotalVar")
;; 6
(assume "k" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatLtTotal")
(use "TotalNatSucc")
(use "PairTwoTotal")
(use "IH")
(use "NatMinusTotal")
(use "TotalVar")
(use "PairOneTotal")
(use "IH")
;; 11
(intro 0)
(use "PairOneTotal")
(use "IH")
(use "TotalNatSucc")
(use "PairTwoTotal")
(use "IH")
;; 12
(intro 0)
(use "TotalNatSucc")
(use "PairOneTotal")
(use "IH")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "GdsCToMlLt 3 0")))
;; (pp (nt (pt "GdsCToMlLt 3 1")))
;; (pp (nt (pt "GdsCToMlLt 3 2")))
;; (pp (nt (pt "GdsCToMlLt 3 3")))
;; (pp (nt (pt "GdsCToMlLt 3 4")))
;; (pp (nt (pt "GdsCToMlLt 3 5")))

;; > 0 pair 0
;; > 0 pair 1
;; > 0 pair 2
;; > 1 pair 0
;; > 1 pair 1
;; > 2 pair 0

;; GdsCToMlLtProp
(set-goal "all n,k(Succ k<Gs n ->
 Gds n(lft(GdsCToMlLt n k))+rht(GdsCToMlLt n k)=k andnc
 rht(GdsCToMlLt n k)<n--lft(GdsCToMlLt n k))")
(assume "n")
(ind)
;; 3,4
(assume "nH")

(assert "Zero<n")
(cases (pt "n"))
;; 8,9
(assume "n=0")
(simphyp-with-to "nH" "n=0" "Absurd")
(ng "Absurd")
(use "Absurd")
;; 9
(assume "n0" "Useless")
(use "Truth")
;; Assertion proved.
(assume "0<n")
;; 15
(ng #t)
(split)
(use "Truth")
(use "0<n")
;; 4
(assume "k")
(simp "GdsCToMlLt1CompRule") 

(def "ml" "GdsCToMlLt n k")
(def "m" "lft ml")
(def "l" "rht ml")
(simp "<-" "mlDef")
(simp "<-" "mDef")
(simp "<-" "lDef")

(bpe-ng #t)
(simp "<-" "mDef")
(simp "<-" "lDef")

(assume "ImpH" "LtH")
(assert "Gds n m+l=k andnc l<n--m")
(use "ImpH")
(use "NatLeLtTrans" (pt "Succ(Succ k)"))
(use "Truth")
(use "LtH")
;; Assertion proved.
(assume "mlProp")
(use "NatLtSuccCases" (pt "Succ l") (pt "n--m"))
;; 55-57
(use "mlProp")
;; 56
(assume "Sl<n--m")
(simp "Sl<n--m")
(ng #t)
(split)
(use "mlProp")
(use "Sl<n--m")
;; 57
(assume "Sl=n-m")
(simp "<-" "Sl=n-m")
(ng #t)
(simp "<-" "Sl=n-m")
(ng #t)
(split)
(use "mlProp")
;; ?^69:0<l
(cases (pt "l"))
;; 70,71
(assume "l=0")
(simphyp-with-to "Sl=n-m" "l=0" "1=n-m")
(simphyp-with-to "mlProp" "l=0" "mlPropS")
(ng "mlPropS")

(assert "m<n")
(simp "NatLtMinusZero")
(use "mlPropS")
;; Assertion proved.
(assume "m<n")

(assert "m+(n--m)=n")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "NatLtToLe")
(use "m<n")
;; Assertion proved.
(assume "nEq")

(assert "Succ(Succ k)<Gds n(m+(n--m))")
(simp "nEq")
(simp "NatEqGdsGs")
(use "LtH")
;; Assertion proved.
(assume "H")

(assert "Gds n m=k")
(use "mlPropS")
;; Assertion proved.
(assume "kEq")

(simphyp-with-to "H" "<-" "1=n-m" "HS")
(ng "HS")
(simphyp-with-to "HS" "<-" "kEq" "HSS")
(simphyp-with-to "HSS" "<-" "1=n-m" "Absurd")
(ng "Absurd")
(use "Absurd")
;; 71
(assume "n0" "Useless")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GdsCToMlLtProp")

;; (remove-program-constant "GdsCToMlEq")
(add-program-constant "GdsCToMlEq" (py "nat=>nat yprod nat"))
(add-computation-rules
 "GdsCToMlEq Zero" "Zero pair Zero"
 "GdsCToMlEq(Succ n)" "n pair Zero")

(set-totality-goal "GdsCToMlEq")
(fold-alltotal)
(cases)
(use "TotalVar")
(assume "n")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GdsCToMlEqProp
(set-goal "all k,n(Gds n n=Succ k ->
 Gds n lft(GdsCToMlEq n)+rht(GdsCToMlEq n)=k andnc
 rht(GdsCToMlEq n)<n--lft(GdsCToMlEq n))")
(assume "k")
(cases)
;; 3,4
(ng #t)
(assume "Absurd")
(split)
(use "EfAtom")
(use "Absurd")
(use "Absurd")
;; 4
(assume "n" "EqH")
(ng #t)
(split)
(ng)
(use "EqH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GdsCToMlEqProp")

;; (remove-program-constant "GdsCToMl")
(add-program-constant "GdsCToMl" (py "nat=>nat=>nat yprod nat"))
(add-computation-rules
 "GdsCToMl n k" 
 "[if (Succ k<Gs n)
      (GdsCToMlLt n k)
      (GdsCToMlEq n)]")

(set-totality-goal "GdsCToMl")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "k")
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GdsCToMlProp
(set-goal "all n,k(k<Gs n ->
  Gds n lft(GdsCToMl n k)+rht(GdsCToMl n k)=k andnc
  rht(GdsCToMl n k)<n--lft(GdsCToMl n k))")
(assume "n" "k" "kBd")
(use "NatLeCases" (pt "Succ k") (pt "Gs n"))
;; 3-5
(use "NatLtToSuccLe")
(use "kBd")
;; 4
(assume "LtH")
(inst-with-to "GdsCToMlLtProp" (pt "n") (pt "k") "LtH" "GdsCToMlLtPropInst")
(ng #t)
(simp "LtH")
(ng #t)
(use "GdsCToMlLtPropInst")
;; 5
(assume "EqH")
(simphyp-with-to "EqH" "<-" (pf "Gds n n=Gs n") "EqHS")
(assert "Gds n n=Succ k")
(use "NatEqSym")
(use "EqHS")
;; Assertion proved.
(assume "EqHSS")
(inst-with-to "GdsCToMlEqProp" (pt "k") (pt "n") "EqHSS" "GdsCToMlEqPropInst")
(ng #t)
(simp "EqH")
(ng #t)
(use "GdsCToMlEqPropInst")
;; ?^15:Gds n n=Gs n
(use "NatEqGdsGs")
;; Proof finished.
;; (cp)
(save "GdsCToMlProp")

;; GdsCToMlPropMod
(set-goal "all n,k,ml,m,l(
  ml=GdsCToMl n k ->
  m=lft ml -> l=rht ml -> k<Gs n -> Gds n m+l=k andnc l<n--m)")
(assume "n" "k" "ml" "m" "l" "mlDef" "mDef" "lDef")
(simp "lDef")
(simp "mDef")
(simp "mlDef")
(use "GdsCToMlProp")
;; Proof finished.
;; (cp)
(save "GdsCToMlPropMod")

(add-program-constant "GdsMlToC" (py "nat=>nat yprod nat=>nat"))
(add-computation-rules
 "GdsMlToC n(m pair l)" "Gds n m+l")

(set-totality-goal "GdsMlToC")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GdsMlToCBd
(set-goal "all n,m,l(m<n -> l<n--m -> GdsMlToC n(m pair l)<Gs n)")
(assume "n" "m" "l" "m<n" "lBd")
(ng #t)
(use "NatLtLeTrans" (pt "Gds n m+(n--m)"))
(use "lBd")
(simp "<-" "GdsSucc")
(simp "<-" "NatEqGdsGs")
(use "GdsMonBd")
(use "NatLtToSuccLe")
(use "m<n")
;; Proof finished.
;; (cp)
(save "GdsMlToCBd")

;; GdsCToMlToCId (was GdsCDId)
(set-goal
 "all m,n,l(m<n -> l<n--m -> GdsCToMl n(GdsMlToC n(m pair l))=(m pair l))")
(assume "m" "n" "l" "m<n" "lBd")
(inst-with-to
 "GdsMlToCBd" (pt "n") (pt "m") (pt "l") "m<n" "lBd" "Inst")
(def "k" "(GdsMlToC n(m pair l))")
(simphyp-with-to "Inst" "<-" "kDef" "InstS")
(simp "<-" "kDef")
(inst-with-to "GdsCToMlProp" (pt "n") (pt "k") "InstS" "Conj")
(ng "kDef")

(assert "m=lft(GdsCToMl n k) andnc l=rht(GdsCToMl n k)")
(use "GdsUniq" (pt "n"))
(simp "Conj")
(simp "kDef")
(use "Truth")
(use "lBd")
(use "Conj")
;; Assertion proved.
(assume "A")
(simp "A")
(simp "A")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "GdsCToMlToCId")

;; GdsMlToCToMlId (was GdsDCId)
(set-goal "all n,k(k<Gs n -> GdsMlToC n(GdsCToMl n k)=k)")
(assume "n" "k" "kBd")
(def "ml" "lft(GdsCToMl n k) pair rht(GdsCToMl n k)")
(inst-with-to "NatPairEq" (pt "GdsCToMl n k") "PairEqInst")
(simphyp-with-to "mlDef" "<-" "PairEqInst" "mlDef1")
(simp "<-" "mlDef1")
(simp "mlDef")
(ng #t)
(simp "<-" "mlDef")
(def "m" "lft ml")
(def "l" "rht ml")
(simp "<-" "mDef")
(simp "<-" "lDef")

(use "GdsCToMlPropMod" (pt "GdsCToMl n k"))
(use "Truth")
(simp "<-" "mlDef1")
(simp "<-" "mDef")
(use "Truth")
(simp "<-" "mlDef1")
(simp "<-" "lDef")
(use "Truth")
(use "kBd")
;; Proof finished.
;; (cp)
(save "GdsMlToCToMlId")

;; 2024-05-06.  We define GqIjToMl, GqMlToIj as IjToMl, MlToIj were
;; defined in libnatgausspair.scm

;; (remove-program-constant "GqMlToIj")
(add-program-constant "GqMlToIj" (py "nat=>nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "GqMlToIj n(m pair l)" "Succ(m+l)pair n--l")

(set-totality-goal "GqMlToIj")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "GqIjToMl")
(add-program-constant "GqIjToMl" (py "nat=>nat yprod nat=>nat yprod nat"))
(add-computation-rules
 "GqIjToMl n(i pair j)" "Pred(i+j--n)pair n--j")

(set-totality-goal "GqIjToMl")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(cases)
(assume "i" "j")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GqIjToMlToIjId
(set-goal "all n,i,j(i max j<=n -> n<i+j -> 
 GqMlToIj n(GqIjToMl n(i pair j))=(i pair j))")
(assume "n" "i" "j" "LeH" "n<i+j")
(ng #t)
(split)
;; 4,5
(simp "<-" "NatPlus1RewRule")
(simp "NatSuccPred")
;; 7,8
(simp "NatPlusMinusAssoc")
(simp "NatMinusPlusEq")
(use "Truth")
(use "NatLtToLe")
(use "n<i+j")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "i max j"))
(use "Truth")
(use "LeH")
;; 8
(simp "<-" "NatLtMinusZero")
(use "n<i+j")
;; 5
(use "NatPlusCancelR" (pt "n--j"))
(assert "j<=n")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
;; Assertion proved.
(assume "j<=n")
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(use "NatEqSym")
(use "NatMinusPlusEq")
(use "j<=n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqIjToMlToIjId")

;; GqMlToIjToMlId
(set-goal "all n,m,l(l<=n -> GqIjToMl n(GqMlToIj n(m pair l))=(m pair l))")
(assume "n" "m" "l" "l<=n")
(ng #t)
(split)
(simp (pf "m+l+(n--l)=m+n"))
(use "Truth")
(simp "<-" "NatPlusAssoc")
(simp (pf "l+(n--l)=n"))
(use "Truth")
(simp "NatPlusComm")
(use "NatMinusPlusEq")
(use "l<=n")
;; ?^5:n--(n--l)=l
(simp "NatMinusMinus")
(simp "NatPlusComm")
(use "Truth")
(use "Truth")
(use "l<=n")
;; Proof finished.
;; (cp)
(save "GqMlToIjToMlId")

;; GqMlToIjToMlIdMod
(set-goal "all n,ml(rht ml<=n -> GqIjToMl n(GqMlToIj n ml)=ml)")
(assume "n")
(cases)
(assume "m" "l")
(use "GqMlToIjToMlId")
;; Peroof finished.
;; (cp)
(save "GqMlToIjToMlIdMod")

;; GqMlToIjBd
(set-goal "all n,ml,ij(ij=GqMlToIj n ml -> n<lft ij+rht ij)")
(assume "n")
(cases)
(assume "m" "l")
(cases)
(assume "i" "j")
(ng #t)
(assume "Conj")
(assert "i=Succ(m+l)")
(use "Conj")
(assume "iEq")
(assert "j=n--l")
(use "Conj")
(assume "jEq")
(simp "iEq")
(simp "jEq")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "l+(n--l)"))
;; 19,20
(use "NatLeLeCases" (pt "n") (pt "l"))
;; 21,22
(assume "n<=l")
(use "NatLeTrans" (pt "l"))
(use "n<=l")
(use "Truth")
;; 22
(assume "l<=n")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(use "l<=n")
;; 20
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqMlToIjBd")

;; GqIjToMlBd
(set-goal "all n,i,j,m,l(i<=n -> j<=n -> n<i+j ->
 m=i+j--n--1 -> l=n--j -> m+l<n)")
(assume "n" "i" "j" "m" "l" "iBd" "jBd" "nBd" "mEq" "lEq")
(simp "mEq")
(simp "lEq")
(ng #t)
(simp "NatPredMinus")
(simp "NatPlusMinusAssoc")
(simp "NatMinusPlusEq")
(simp "<-" "NatPredMinus")
(ng #t)
(use "NatSuccLeToLt")
;; 12,13
(simp "NatSuccPred")
(use "iBd")
;; ?^15:0<i
(simp "<-" "NatPlusCancelLtR" (pt "j"))
(ng #t)
(use "NatLeLtTrans" (pt "n"))
(use "jBd")
(use "nBd")
;; ?^10:n<=Pred(i+j)
(use "NatLtToLePred")
(use "nBd")
;; 8
(use "jBd")
;; Proof finished.
;; (cp)
(save "GqIjToMlBd")

;; (remove-program-constant "GqC")
(add-program-constant "GqC" (py "nat=>nat yprod nat=>nat"))

(add-computation-rules
 "GqC n(i pair j)"
 "[if (i+j<=n) (GsC(i pair j))
      (Gs(Succ n)+Gds n(lft(GqIjToMl n(i pair j)))+rht(GqIjToMl n(i pair j)))]")

;; (pp (nt (pt "GqC 4(1 pair 4)")))
;; (pp (nt (pt "GqC 4(4 pair 3)")))
;; (pp (nt (pt "GqC 4(4 pair 4)")))

;; > 15
;; > 23
;; > 24

(set-totality-goal "GqC")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(cases)
(assume "m" "l")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "GqD")
(add-program-constant "GqD" (py "nat=>nat=>nat yprod nat"))
(add-computation-rules
 "GqD n k"
 "[if (k<Gs(Succ n))
      (GsD k)
      (GqMlToIj n(GdsCToMl n(k--Gs(Succ n))))]")

;; (pp (nt (pt "GqD 4 15")))
;; (pp (nt (pt "GqD 4 23")))
;; (pp (nt (pt "GqD 4 24")))

;; > 1 pair 4
;; > 4 pair 3
;; > 4 pair 4

(set-totality-goal "GqD")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "k")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; GqDLe
(set-goal
 "all n,k(Gs(Succ n)<=k -> GqD n k=GqMlToIj n(GdsCToMl n(k--Gs(Succ n))))")
(assume "n" "k" "kBd")
(simp "GqD0CompRule")
(assert "k<Gs(Succ n) -> F")
(assume "LtH")
(assert "k<k")
(use "NatLtLeTrans" (pt "Gs(Succ n)"))
(use "LtH")
(use "kBd")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "NegH")
(simp "GdsCToMl0CompRule")
(simp "NegH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqDLe")

;; GqCLt
(set-goal "all n,ij(n<lft ij+rht ij -> 
 GqC n ij=Gs(Succ n)+GdsMlToC n(GqIjToMl n ij))")
(assume "n")
(cases)
(assume "i" "j" "nBd")
(ng "nBd")
(simp "GqC0CompRule")
(assert "i+j<=n -> F")
(assume "LeH")
(assert "n<n")
(use "NatLtLeTrans" (pt "i+j"))
(use "nBd")
(use "LeH")
(assume "n<n")
(use "n<n")
;; Assertion proved.
(assume "NegH")
(simp "NegH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqCLt")

;; GqCDId
(set-goal "all n,k(k<=n*n+n+n -> GqC n(GqD n k)=k)")
(assume "n" "k" "kLeBd")
(assert "k<Succ n*Succ n")
(use "NatLeToLtSucc")
(use "kLeBd")
;; Assertion proved.
(assume "kBd")
(use "NatLeLtCases" (pt "Gs(Succ n)") (pt "k"))
;; 7,8
(assume "GsSn<=k")
(def "k0" "k--Gs(Succ n)")

(assert "k0<Gs n")
(simp "k0Def")
(simphyp-with-to "kBd" "<-" (pf "Gs(Succ n)+Gs n=(Succ n)*(Succ n)")  "kBdS")
(use "NatLtLeTrans" (pt "Gs(Succ n)+Gs n--Gs(Succ n)"))
(use "NatLtMonMinusLeft")
(use "kBdS")
(use "GsSn<=k")
(simp "NatMinus4RewRule")
(use "Truth")
;; 21
(use "GsProp")
;; ?^17:k0<Gs n -> GqC n(GqD n k)=k
;; Assertion proved.
(assume "k0Bd")

(simp "GqDLe")
;; 29,30
;; ?^29:GqC n(GqMlToIj n(GdsCToMl n(k--Gs(Succ n))))=k
(simp "<-" "k0Def")
;; ?^31:GqC n(GqMlToIj n(GdsCToMl n k0))=k

(def "ij" "GqMlToIj n(GdsCToMl n k0)")

(simp "<-" "ijDef")
;; (pp "GqCLt")
;; all n,ij(n<lft ij+rht ij -> GqC n ij=Gs(Succ n)+GdsMlToC n(GqIjToMl n ij))

(assert "n<lft ij+rht ij")
(use "GqMlToIjBd" (pt "GdsCToMl n k0"))
(simp "ijDef")
(use "Truth")
;; Assertion proved.
(assume "nBd")

(simp "GqCLt")
(simp "ijDef")
(simp (pf "GqIjToMl n(GqMlToIj n(GdsCToMl n k0))=GdsCToMl n k0"))
;; 48,49
(simp "GdsMlToCToMlId")
;; 50,51
(simp "k0Def")
(simp "NatPlusMinusAssoc")
;; 53,54
(simp "NatPlusComm")
(simp "NatMinus3RewRule")
(use "Truth")
;; 54
(use "GsSn<=k")
;; 51
(use "k0Bd")
;; ?^49:GqIjToMl n(GqMlToIj n(GdsCToMl n k0))=GdsCToMl n k01
(use "GqMlToIjToMlIdMod")
;; ?^57:rht(GdsCToMl n k0)<=n

(inst-with-to "GdsCToMlProp" (pt "n") (pt "k0") "k0Bd" 'right "Inst")
;;   Inst:rht(GdsCToMl n k0)<n--lft(GdsCToMl n k0)
;; -----------------------------------------------------------------------------
;; ?^59:rht(GdsCToMl n k0)<=n
(use "NatLtToLe")
(def "ml" "GdsCToMl n k0")
(simphyp-with-to "Inst" "<-" "mlDef" "InstS")
(simp "<-" "mlDef")
(use "NatLtLeTrans" (pt "n--lft ml"))
(use "InstS")
(use "Truth")
;; ?^46:n<lft ij+rht ij
(use "nBd")
;; ?^30:Gs(Succ n)<=k
(use "GsSn<=k")
;; ?^8:k<Gs(Succ n) -> GqC n(GqD n k)=k
(assume "k<GsSn")
(def "i" "lft(GqD n k)")
(def "j" "rht(GqD n k)")
(simp (pf "GqD n k=(i pair j)"))
(simp "GqC0CompRule")
(assert "(i pair j)=GqD n k")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(simp (pf "GqD n k=GsD k"))
(get 97)
(simp "GqD0CompRule")
(simp "k<GsSn")
(use "Truth")
;; 96
(assume "ijEq")
(assert "i+j<=n")
(simp "GsCLM")
(simp "ijEq")
(simp "GsCDId")
(use "k<GsSn")
;; Assertion proved.
(assume "A1")
(simp "A1")
(simp "IfTrue")
(simp "ijEq")
(use "GsCDId")
;; 89
(simp "iDef")
(simp "jDef")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "GqCDId")

;; Now the converse.

;; GqDCIdAux
(set-goal "all n,i,j(i<=n ->j<=n -> GqD n(GqC n(i pair j))=(i pair j))")
(assume "n" "i" "j" "i<=n" "j<=n")
(simp "GqC0CompRule")
(cases 'auto)
;; 4,5
(simp (pf "[if True
      (GsC(i pair j))
      (Gs(Succ n)+Gds n lft(GqIjToMl n(i pair j))+rht(GqIjToMl n(i pair j)))]=
      GsC(i pair j)"))
;; 6,7
(assume "i+j<=n")
(def "k" "GsC(i pair j)")
(simp "<-" "kDef")
;; (simp "GqC0CompRule") ;does not work for pair types
(inst-with-to "GqD0CompRule" (pt "n") (pt "k") "Inst")
(simp "Inst")
(drop "Inst")
(simp "kDef")
(simp "<-" "GsCLM")
(simp "i+j<=n")
(simp "IfTrue")
(simp "GsDCId")
(use "Truth")
;; 7
(use "Truth")
;; 5
;; Continue on L2578 of libnatgausspair.scm
(assume "NegH")
(assert "n<i+j")
(use "NatNotLeToLt")
(use "NegH")
;; Assertion proved.
(assume "nBd")
(drop "NegH")
(def "m" "lft(GqIjToMl n(i pair j))")
(simp "<-" "mDef")
(def "l" "rht(GqIjToMl n(i pair j))")
(simp "<-" "lDef")
(def "k" "(Gs(Succ n)+Gds n m+l)")
(simp "<-" "kDef")
(simp (pf "[if False (GsC(i pair j)) k]=k"))
(def "k0" "Gds n m+l")
(ng "mDef")
(ng "lDef")
(simp "GqDLe")
;; 69
(assert "m+l<n")
(use "GqIjToMlBd" (pt "i") (pt "j"))
(use "i<=n")
(use "j<=n")
(use "nBd")
(simp "mDef")
(use "Truth")
(simp "lDef")
(use "Truth")
;; Assertion proved.
(assume "m+l<n")
;; 80
(assert "l<n--m")
(simp (pf "l=l+m--m"))
(use "NatLtMonMinusLeft")
(simp "NatPlusComm")
(use "m+l<n")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "l<n--m")
;; 88
(assert "k0<Gs n")
(simp "k0Def")
(use "GdsBd")
;; ?^92:m<n
(use "NatLeLtTrans" (pt "m+l"))
(use "Truth")
(use "m+l<n")
(use "l<n--m")
;; Assertion proved.
(assume "k0Bd")
;; 96
(assert "m=lft(GdsCToMl n k0) andnc l=rht(GdsCToMl n k0)")
(use "GdsUniq" (pt "n"))
(simp "<-" "k0Def")
(use "NatEqSym")
(use-with "GdsCToMlProp" (pt "n") (pt "k0") "k0Bd" 'left)
(use "l<n--m")
(use-with "GdsCToMlProp" (pt "n") (pt "k0") "k0Bd" 'right)
;; Assertion proved.
(assume "Conj")
;; 104
(simp "kDef")
(simp (pf "Gs(Succ n)+Gds n m+l=Gds n m+l+Gs(Succ n)"))
(simp (pf "Gds n m+l+Gs(Succ n)--Gs(Succ n)=Gds n m+l"))
(simp "<-" "k0Def")
;; 110
(inst-with-to "NatPairEq" (pt "GdsCToMl n k0") "Inst")
(simp "Inst")
(inst-with-to "Conj" 'left "mEq")
(simp "<-" "mEq")
(inst-with-to "Conj" 'right "lEq")
(simp "<-" "lEq")
(ng #t)
(simp "lDef")
(split)
(simp "mDef")
(simp "NatPredMinus")
(simp "NatPlusMinusAssoc")
(simp "NatMinusPlusEq")
(simp "<-" "NatPredMinus")
(ng #t)
(use "NatSuccPred") 
;; ?^132:0<i
(use "NatNotLeToLt")
(ng #t)
(assume "i=0")
(simphyp-with-to "nBd" "i=0" "n<j")
(assert "n<n")
(use "NatLtLeTrans" (pt "j"))
(use "n<j")
(use "j<=n")
(assume "Absurd")
(use "Absurd")
;; ?^129:n<=Pred(i+j)
(use "NatLtToLePred")
(use "nBd")
;; 127
(use "j<=n")
;; 123
(simp "NatMinusMinus")
(simp "NatPlusComm")
(use "Truth")
(use "Truth")
(use "j<=n")
;; ?^109:Gds n m+l+Gs(Succ n)--Gs(Succ n)=Gds n m+l
(def "k1" "Gs(Succ n)")
(simp "<-" "k1Def")
(use "Truth")
;; ?^107:Gs(Succ n)+Gds n m+l=Gds n m+l+Gs(Succ n)
(simp "<-" "NatPlusAssoc")
(use "NatPlusComm")
;; ?^70:Gs(Succ n)<=k
(simp "kDef")
(simp "<-" "NatPlusAssoc")
(def "k1" "Gs(Succ n)")
(simp "<-" "k1Def")
(simp "NatLe2RewRule")
(use "Truth")
;; ?^59:[if False (GsC(i pair j)) k]=k
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqDCIdAux")

;; GqDCId
(set-goal "all n,ij(lft ij<=n ->rht ij<=n -> GqD n(GqC n ij)=ij)")
(assume "n")
(cases)
(assume "i" "j")
(use "GqDCIdAux")
;; Proof finished.
;; (cp)
(save "GqDCId")

;; GqCBd
(set-goal "all n,i,j(i<=n -> j<=n -> GqC n(i pair j)<=n*n+n+n)")
(cases)
;; 2,3
(ng #t)
(assume "i" "j" "i=0" "j=0")
(simp "i=0")
(simp "j=0")
(use "Truth")
;; 3
(assume "n0" "i" "j")
(def "n" "Succ n0")
(simp "<-" "nDef")
(assume "i<=n" "j<=n")
(simp "GqC0CompRule")
(cases 'auto)
;; 19,20
(get 20)
(simp "IfFalse")
(assume "NegH")
(inst-with-to "NatNotLeToLt" (pt "i+j") (pt "n") "NegH" "n<i+j")
(drop "NegH")
;;   n  i  j  i<=n:i<=n
;;   j<=n:j<=n
;;   n<i+j:n<i+j
;; -----------------------------------------------------------------------------
;; ?^25:Gs(Succ n)+Gds n lft(GqIjToMl n(i pair j))+rht(GqIjToMl n(i pair j))<=
;;      n*n+n+n
(assert "Gds n lft(GqIjToMl n(i pair j))+rht(GqIjToMl n(i pair j))<Gs n")
;; 26,27
;; suffices by GsProp
(def "m" "lft(GqIjToMl n(i pair j))")
(def "l" "rht(GqIjToMl n(i pair j))")
(simp "<-" "mDef")
(simp "<-" "lDef")
(use "GdsBd")
;; 44,45
;; ?^44:m<n
(ng "mDef")
(simp "mDef")
(use "NatLeLtTrans" (pt "Pred(n+j--j)"))
(use "NatLeMonPred")
(use "NatLeMonMinus")
(use "NatLeMonPlus")
(use "i<=n")
(use "Truth")
(use "j<=n")
(ng #t)
(use "NatLtPred")
(simp "nDef")
(use "Truth")
;; ?^45:l<n--m
(ng "lDef")
(simp "lDef")
(ng "mDef")
(simp "mDef")
;; ?^61:n--j<n--Pred(i+j--n)
(simp "<-" "NatMinus1CompRule")
;; ?^62:n--j<n--(i+j--Succ n)
(use "NatLtMonMinusRight")
(simp (pf "(i+j--Succ n<j)=(i+j--Succ n+Succ n<j+Succ n)"))
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(simp "NatLt4RewRule")
(use "NatLeToLtSucc")
(use "i<=n")
;; ?^68:Succ n<=i+j
(use "NatLtToSuccLe")
(use "n<i+j")
(simp "NatPlusCancelLtR")
(use "Truth")
(use "j<=n")
;; 26
;; Assertion proved.
(assume "A1")
(use "NatLtSuccToLe")
(use "NatLtLeTrans" (pt "Gs(Succ n)+Gs n"))
(simp "<-" "NatPlusAssoc")
(simp "NatLt4RewRule")
(use "A1")
(simp "GsProp")
(use "Truth")
;; 19
(assume "i+j<=n")
(simp "IfTrue")
(ng #t)
;; ?^83:Gs(i+j)+i<=n*n+n+n
(use "NatLeTrans" (pt "Gs n+i"))
(use "GsMon")
(use "i+j<=n")
(use "NatLeTrans" (pt "Gs n+n"))
(use "i<=n")
(use "NatLeTrans" (pt "Gs n+Gs n"))
(use "GsIncr")
(simp "GsChar")
(simp "NatDoublePlusEq")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "NatEvenTimesSucc")
;; Proof finished.
;; (cp)
(save "GqCBd")

;; 2024-08-26

;; GqCBdMod
(set-goal "all n,ij(lft ij<=n -> rht ij<=n -> GqC n ij<=n*n+n+n)")
(assume "n")
(cases)
(assume "i" "j" "i<=n" "j<=n")
(use "GqCBd")
(use "i<=n")
(use "j<=n")
;; Proof finished.
;; (cp)
(save "GqCBdMod")

;; End 2024-08-26

;; 2024-08-25

;; GqDBd
(set-goal "all n,k,i,j(k<=n*n+n+n -> (i pair j)=GqD n k -> i max j<=n)")
(assume "n" "k" "i" "j" "kLeBd" "ijDef")
(assert "k<Succ n*Succ n")
(use "NatLeToLtSucc")
(use "kLeBd")
;; Assertion proved.
(assume "kBd")
(use "NatLeLtCases" (pt "Gs(Succ n)") (pt "k"))
;; 7,8
(assume "LeH")
(inst-with-to "GqD0CompRule" (pt "n") (pt "k") "Inst")
(def "k0" "k--Gs(Succ n)")
(simphyp-with-to "Inst" "<-" "k0Def" "InstS")
(simphyp-with-to "ijDef" "InstS" "ijDefS")
(drop "Inst" "InstS")
(assert "(i pair j)=GqMlToIj n(GdsCToMl n k0)")
(simp "ijDefS")
(simp (pf "k<Gs(Succ n) -> F"))
(use "Truth")
(assume "LtH")
(assert "k<k")
(use "NatLtLeTrans" (pt "Gs(Succ n)"))
(use "LtH")
(use "LeH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "ijEq")
(def "ml" "GdsCToMl n k0")
(def "m" "lft ml")
(def "l" "rht ml")

(assert "k0<Gs n")
(simp "k0Def")
(simp "<-" "NatPlusCancelLtR" (pt "Gs(Succ n)"))
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(simp "GsProp")
(use "kBd")
(use "LeH")
;; Assertion proved.
(assume "k0Bd")

(inst-with-to "GdsCToMlProp" (pt "n") (pt "k0") "k0Bd" "Conj")
(simphyp-with-to "Conj" "<-" "mlDef" "ConjS")
(simphyp-with-to "ConjS" "<-" "mDef" "ConjSS")
(simphyp-with-to "ConjSS" "<-" "lDef" "ConjSSS")
(drop "Conj" "ConjS" "ConjSS")

(simphyp-with-to "ijEq" "<-" "mlDef" "ijEqS")
(simphyp-with-to "ijEqS" (pf "ml=(m pair l)") "ijEqSS")
(ng "ijEqSS")

(simp (pf "j=n--l"))
(simp (pf "i=Succ(m+l)"))
(use "NatMaxLUB")
;; 85,86
(use "NatLtSuccToLe")
(ng #t)
(use "NatLtLeTrans" (pt "m+(n--m)"))
(ng #t)
(use "ConjSSS")
;; ?^90:m+(n--m)<=n
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
;; ?^94:m<=n
(use "NatLeTrans" (pt "m+l"))
(use "Truth")
(use "NatLtToLe")
(simp "<-" "NatLtMinusPlus")
(use "ConjSSS")
;; 86
(use "Truth")
;; 84
(use "ijEqSS")
;; 82
(use "ijEqSS")
;; 78
(simp "mDef")
(simp "lDef")
(use "NatPairEq")
;; 8
(assume "LtH")
(use "NatLeTrans" (pt "i+j"))
;; 102,103
(use "NatMaxLUB")
(use "Truth")
(use "Truth")
;; ?^103:i+j<=n
(simp "GsCLM")
(simp "ijDef")

(assert "GqD n k=GsD k")
(simp "GqD0CompRule")
(simp "LtH")
(use "Truth")
;; Assertion proved.
(assume "EqH")
(simp "EqH")
(simp "GsCDId")
(use "LtH")
;; Proof finished.
;; (cp)
(save "GqDBd")

;; GqDBdMod
(set-goal "all n,k,ij(k<=n*n+n+n -> ij=GqD n k -> lft ij max rht ij<=n)")
(assume "n" "k" "ij" "kBd" "ijDef")
(use "GqDBd" (pt "k"))
(use "kBd")
(simp "<-" "ijDef")
(use "NatPairEq")
;; Proof finished.
;; (cp)
(save "GqDBdMod")

;; End 2024-08-25

;; 5.  Relating root and quadratic Gauss coding
;; ============================================

;; For a fixed $n$, the numbers $k<(n+1)^2$ can be viewed as
;; -- root or
;; -- quadratic Gauss
;; codes of the positions $\pair{i}{j}$ with $i,j \le n$.  Going via
;; these positions, we can define bijections on the set of numbers
;; $k<(n+1)^2$:

;; (display-pconst "RtC")

;; (remove-program-constant "GqCRtD")
(add-program-constant "GqCRtD" (py "nat=>nat=>nat"))
(add-computation-rules
 "GqCRtD n k" "[if (k<=n*n+n+n) (GqC n(RtD k)) k]")

(set-totality-goal "GqCRtD")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "k")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; (remove-program-constant "RtCGqD")
(add-program-constant "RtCGqD" (py "nat=>nat=>nat"))
(add-computation-rules
 "RtCGqD n k" "[if (k<=n*n+n+n) (RtC(GqD n k)) k]")

(set-totality-goal "RtCGqD")
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "k")
(ng #t)
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; RtCGqDGqCRtDId (was GqCToRtCToGqCId)
(set-goal "all n,k RtCGqD n(GqCRtD n k)=k")
(assume "n" "k")
(use "NatLeLtCases" (pt "k") (pt "n*n+n+n"))
;; 3,4
(assume "kBd")
(simp "RtCGqD0CompRule")
(simp "GqCRtD0CompRule")
(simp "kBd")
(simp "IfTrue")
;; 9
(def "ij" "RtD k")
(def "i" "lft(RtD k)")
(def "j" "rht(RtD k)")

(assert "i max j<=n")
(use "RtDBd" (pt "k"))
(use "kBd")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "LeH")

(simp "GqDCId")
;; 39-41
(simp "RtCDId")
;; ?^42:[if (GqC n(RtD k)<=n*n+n+n) k (GqC n(RtD k))]=k
(simp (pf "GqC n(RtD k)<=n*n+n+n"))
;; 43,44
(use "Truth")
;; ?^44:GqC n(RtD k)<=n*n+n+n
(simp "<-" "ijDef")
(use "GqCBdMod")
(simp "ijDef")
(simp "<-" "iDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB1")
(use "LeH")
(simp "ijDef")
(simp "<-" "jDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
(simp "<-" "jDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
(simp "<-" "iDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB1")
(use "LeH")
;; ?^4:n*n+n+n<k -> RtCGqD n(GqCRtD n k)=k
(assume "LtH")

(assert "k<=n*n+n+n -> F")
(assume "LeH")
(assert "k<k")
(use "NatLeLtTrans" (pt "n*n+n+n"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "NegH")

(simp "GqCRtD0CompRule")
(simp "NegH")
(simp "IfFalse")
(simp "RtCGqD0CompRule")
(simp "NegH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "RtCGqDGqCRtDId")

;; GqCRtDRtCGqDId (was RtCToGqCToRtCId)
(set-goal "all n,k GqCRtD n(RtCGqD n k)=k")
(assume "n" "k")
(use "NatLeLtCases" (pt "k") (pt "n*n+n+n"))
;; 3,4
(assume "kBd")
(simp "GqCRtD0CompRule")
(simp "RtCGqD0CompRule")
(simp "kBd")
(simp "IfTrue")
;; 9
(simp "RtDCId")
(simp "GqCDId")
;; 11
(simp (pf "RtC(GqD n k)<=n*n+n+n"))
;; 13,14
(use "Truth")
;; ?^14:RtC(GqD n k)<=n*n+n+n
(def "ij" "GqD n k")
(def "i" "lft(GqD n k)")
(def "j" "rht(GqD n k)")

(assert "i max j<=n")
(use "GqDBd" (pt "k"))
(use "kBd")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "LeH")
(use "RtCBdMod")
;; 44,45
(simp "<-" "iDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB1")
(use "LeH")
;; 45
(simp "<-" "jDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
;; 12
(use "kBd")
;; ?^4:n*n+n+n<k -> GqCRtD n(RtCGqD n k)=k
(assume "LtH")

(assert "k<=n*n+n+n -> F")
(assume "LeH")
(assert "k<k")
(use "NatLeLtTrans" (pt "n*n+n+n"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "NegH")

(simp "RtCGqD0CompRule")
(simp "NegH")
(simp "IfFalse")
(simp "GqCRtD0CompRule")
(simp "NegH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqCRtDRtCGqDId")

;; GqCRtDBd
(set-goal "all n,k(k<=n*n+n+n -> GqCRtD n k<=n*n+n+n)")
(assume "n" "k" "kBd")
(simp "GqCRtD0CompRule")
(simp "kBd")
(simp "IfTrue")
(def "ij" "RtD k")
(def "i" "lft(RtD k)")
(def "j" "rht(RtD k)")
(simp "<-" "ijDef")

(assert "i max j<=n")
(use "RtDBd" (pt "k"))
(use "kBd")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "LeH")

(simp "<-" "ijDef")
(simp "NatPairEq")
(simp "ijDef")
(simp "<-" "iDef")
(simp "<-" "jDef")

(use "GqCBd")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB1")
(use "LeH")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
;; Proof finished.
;; (cp)
(save "GqCRtDBd")

;; RtCGqDBd
(set-goal "all n,k(k<=n*n+n+n -> RtCGqD n k<=n*n+n+n)")
(assume "n" "k" "kBd")
(simp "RtCGqD0CompRule")
(simp "kBd")
(simp "IfTrue")
(def "ij" "GqD n k")
(def "i" "lft(GqD n k)")
(def "j" "rht(GqD n k)")
(simp "<-" "ijDef")

(assert "i max j<=n")
(use "GqDBd" (pt "k"))
(use "kBd")
(simp "iDef")
(simp "jDef")
(simp "<-" "NatPairEq")
(use "Truth")
;; Assertion proved.
(assume "LeH")

(use "RtCBdMod")
(simp "ijDef")
(simp "<-" "iDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB1")
(use "LeH")
(simp "ijDef")
(simp "<-" "jDef")
(use "NatLeTrans" (pt "i max j"))
(use "NatMaxUB2")
(use "LeH")
;; Proof finished.
;; (cp)
(save "RtCGqDBd")

;; GqLtChar
(set-goal "all i,j,n (i+j<n)=(GqC n(i pair j)<Gs n)")
(assume "i" "j" "n")
(use "BooleAeqToEq")
;; 3,4
;; ?^3:i+j<n -> GqC n(i pair j)<Gs n
(assume "i+j<n")
(simp "GqC0CompRule")
(simp (pf "i+j<=n"))
(simp "IfTrue")
(simp "<-" "GsCL")
(use "i+j<n")
(use "NatLtToLe")
(use "i+j<n")
;; ?^4:GqC n(i pair j)<Gs n -> i+j<n
(assert "n<=i+j -> Gs n<=GqC n(i pair j)")
(simp "GqC0CompRule")
;; Need (i+j=n) -> Gs n<=GsC(i pair j)
;; This is part of GqEqChar, and easily provable: (?)
(assume "n<=i+j")
(use "NatLeCases" (pt "n") (pt "i+j"))
;; 16-18
(use "n<=i+j")
;; 17
(assume "n<i+j")
(simp (pf "i+j<=n -> F"))
(simp "IfFalse")
(simp "<-" "NatPlusAssoc")
(use "NatLeTrans" (pt "Gs(Succ n)"))
(use "GsMon")
(use "Truth")
(simp "NatLe2RewRule")
(use "Truth")
;; 21
(assume "i+j<=n")
(assert "n<n")
(use "NatLtLeTrans" (pt "i+j"))
(use "n<i+j")
(use "i+j<=n")
(assume "Absurd")
(use "Absurd")
;; 18
(assume "n=i+j")
(simp "n=i+j")
(ng #t)
(use "Truth")
;; 12
(assume "Imp" "LtH")
(use "NatNotLeToLt")
(assume "n<=i+j")
(inst-with-to "Imp" "n<=i+j" "ImpInst")
(assert "Gs n<Gs n")
(use "NatLeLtTrans" (pt "GqC n(i pair j)"))
(use "ImpInst")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GqLtChar")

;; GqLtCharCor
(set-goal "all n,i,j (n<=i+j)=(Gs n<=GqC n(i pair j))")
(assume "n" "i" "j")
(use "BooleAeqToEq")
;; 3,4
;; ?^3:n<=i+j -> Gs n<=GqC n(i pair j)
(assume "n<=i+j")
(use "NatNotLtToLe")
(simp "<-" "GqLtChar")
(assume "i+j<n")
(assert "n<n")
(use "NatLeLtTrans" (pt "i+j"))
(use "n<=i+j")
(use "i+j<n")
(assume "Absurd")
(use "Absurd")
;; ?^4:Gs n<=GqC n(i pair j) -> n<=i+j
(assume "LeH")
(use "NatNotLtToLe")
(simp "GqLtChar")
(assume "LtH")
(assert "Gs n<Gs n")
(use "NatLeLtTrans" (pt "GqC n(i pair j)"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GqLtCharCor")

;; GqGtChar
(set-goal "all i,j,n (n<i+j)=(Gs(Succ n)<=GqC n(i pair j))")
(assume "i" "j" "n")
(use "BooleAeqToEq")
;; 3,4
;; ?^3:n<i+j -> Gs(Succ n)<=GqC n(i pair j)
(assume "n<i+j")
(simp "GqC0CompRule")
(simp (pf "i+j<=n -> F"))
(simp "IfFalse")
(simp "<-" "NatPlusAssoc")
(simp "NatLe2RewRule")
(use "Truth")
(assume "i+j<=n")
(use (pf "n<n"))
(use "NatLtLeTrans" (pt "i+j"))
(use "n<i+j")
(use "i+j<=n")
;; ?^4:Gs(Succ n)<=GqC n(i pair j) -> n<i+j
(simp "GqC0CompRule")
(assume "LeH")
(use "NatNotLeToLt")
(assume "i+j<=n")
(simphyp-with-to "LeH" "i+j<=n" "LeHS")
(drop "LeH")
(ng "LeHS")
(assert "Succ(Gs n+n)<=Gs n+n")
(use "NatLeTrans" (pt "Gs(i+j)+n"))
(use "NatLeTrans" (pt "Gs(i+j)+i"))
(use "LeHS")
(use "NatLeMonPlus")
(use "Truth")
(use "NatLeTrans" (pt "i+j"))
(use "Truth")
(use "i+j<=n")
(ng #t)
(use "GsMon")
(use "i+j<=n")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GqGtChar")

;; GqGtCharCor
(set-goal "all i,j,n (i+j<=n)=(GqC n(i pair j)<Gs(Succ n))")
(assume "i" "j" "n")
(use "BooleAeqToEq")
;; 3,4
(assume "i+j<=n")
(use "NatNotLeToLt")
(simp "<-" "GqGtChar")
(assume "n<i+j")
(assert "n<n")
(use "NatLtLeTrans" (pt "i+j"))
(use "n<i+j")
(use "i+j<=n")
(assume "Absurd")
(use "Absurd")
;; ?^4:GqC n(i pair j)<Gs(Succ n) -> i+j<=n
(assume "LtH")
(use "NatNotLtToLe")
(simp "GqGtChar")
(assume "LeH")
(assert "Gs(Succ n)<Gs(Succ n)")
(use "NatLeLtTrans" (pt "GqC n(i pair j)"))
(use "LeH")
(use "LtH")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "GqGtCharCor")

;; GqEqChar
(set-goal "all i,j,n (i+j=n)=
 (Gs n<=GqC n(i pair j)andb GqC n(i pair j)<Gs(Succ n))")
(assume "i" "j" "n")
(use "BooleAeqToEq")
;; 3,4
;; ?^3:i+j=n ->
;; Gs n<=GqC n(i pair j)andb GqC n(i pair j)<Gs(Succ n)
(assume "i+j=n")
(split)
;; 6,7
;; ?^6:Gs n<=GqC n(i pair j)
(ng #t)
(simp "i+j=n")
(use "Truth")
;; ?^7:GqC n(i pair j)<Gs(Succ n)
(ng #t)
(simp "i+j=n")
(ng #t)
(use "NatLeLtTrans" (pt "Gs n+(i+j)"))
(use "Truth")
(simp "i+j=n")
(use "Truth")
;; ?^4:Gs n<=GqC n(i pair j)andb
;; GqC n(i pair j)<Gs(Succ n) -> i+j=n
(assume "Conj")
(simp "<-" "GqGtCharCor")
(use "NatLeAntiSym")
;; 17,18
(simp "GqGtCharCor")
(use "Conj")
;; 18
(simp "GqLtCharCor")
(use "Conj")
;; Proof finished.
;; (cp)
(save "GqEqChar")

;; (search-about "Gq" "Char")

;; Theorems with name containing Gq and Char
;; GqEqChar
;; all i,j,n (i+j=n)=
;; (Gs n<=GqC n(i pair j)andb GqC n(i pair j)<Gs(Succ n))

;; GqLtCharCor
;; all n,i,j (n<=i+j)=(Gs n<=GqC n(i pair j))

;; GqLtChar
;; all i,j,n (i+j<n)=(GqC n(i pair j)<Gs n)

;; GqGtCharCor
;; all i,j,n (i+j<=n)=(GqC n(i pair j)<Gs(Succ n))

;; GqGtChar
;; all i,j,n (n<i+j)=(Gs(Succ n)<=GqC n(i pair j))

;; GqCGsCEq
(set-goal "all i,j,n(i+j<=n -> GqC n(i pair j)=GsC(i pair j))")
(assume "i" "j" "n" "LeH")
(simp "GqC0CompRule")
(simp "LeH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GqCGsCEq")

;; 2025-01-25

;; GsMlEx
(set-goal "all k exd m exl l(k=Gs m+l andnc l<=m)")
(ind)
(intro 0 (pt "Zero"))
(intro 0 (pt "Zero"))
(split)
(use "Truth")
(use "Truth")

(assume "k" "IH")
(by-assume-with "IH" "m" "mProp")
(by-assume-with "mProp" "l" "mlProp")
(use "NatLeCases" (pt "l") (pt "m"))
;; 15-17
(use "mlProp")
;; 16
(assume "l<m")
(intro 0 (pt "m"))
(intro 0 (pt "Succ l"))
(split)
(use "mlProp")
(use "NatLtToSuccLe")
(use "l<m")
;; 17
(assume "l=m")
(intro 0 (pt "Succ m"))
(intro 0 (pt "Zero"))
(split)
(simp "mlProp")
(simp "l=m")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsMlEx")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp (rename-variables neterm))

;; [n]
;;  (Rec nat=>nat yprod nat)n(Zero pair Zero)
;;  ([n0,ml][if ml ([n1,n2][if (n2<n1) (n1 pair Succ n2) (Succ n1 pair Zero)])])

;; This way to obtain the ml-pair for a Gs code number k is the same as
;; the explicit definition by GsCToMl, with computation rules

;; 0	GsCToMl Zero	Zero pair Zero
;; 1	GsCToMl(Succ k)	([ml][if (rht ml<lft ml)
;; 				 (lft ml pair Succ rht ml)
;; 				 (Succ lft ml pair Zero)])(GsCToMl k)

;; Similarly we prove

;; GsIjEx
(set-goal "all k exd i exl j k=Gs(i+j)+i")
(ind)
(intro 0 (pt "Zero"))
(intro 0 (pt "Zero"))
(use "Truth")

(assume "k" "IH")
(by-assume-with "IH" "i" "iProp")
(by-assume-with "iProp" "j" "ijProp")
(cases (pt "j"))
;; 13,14
(assume "j=0")
(intro 0 (pt "Zero"))
(intro 0 (pt "Succ i"))
(simp "ijProp")
(simp "j=0")
(use "Truth")
;; 14
(assume "j0" "j=Sj0")
(intro 0 (pt "Succ i"))
(intro 0 (pt "j0"))
(simp "ijProp")
(simp "j=Sj0")
(use "Truth")
;; Proof finished.
;; (cp)
(save "GsIjEx")

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
;; (pp (rename-variables neterm))

;; [n]
;;  (Rec nat=>nat yprod nat)n(Zero pair Zero)
;;  ([n0,ml]
;;   [if ml ([n1,n2][if n2 (Zero pair Succ n1)
;; 		     ((PairConstr nat nat)(Succ n1))])])

;; (ppc (rename-variables neterm))

;; [n]
;;  (Rec nat=>nat yprod nat)n(Zero pair Zero)
;;  ([n0,ml]
;;    [case ml
;;      (n1 pair n2 -> 
;;      [case n2 (Zero -> Zero pair Succ n1) (Succ n -> Succ n1 pair n)])])

;; Recall that for Gs we also can go directly from  ml-codes to ij-codes
;; and conversely.

;; (display-pconst "GsMlToIj" "GsIjToMl")
;; GsMlToIj
;;   comprules
;; 0	GsMlToIj(m pair l)	l pair m--l
;; GsIjToMl
;;   comprules
;; 0	GsIjToMl(i pair j)	i+j pair i

;; (pp (nt (pt "GqD 3 Zero")))
;; (pp (nt (pt "GqD 3 1")))
;; (pp (nt (pt "GqD 3 2")))
;; (pp (nt (pt "GqD 3 3")))
;; (pp (nt (pt "GqD 3 4")))
;; (pp (nt (pt "GqD 3 5")))
;; (pp (nt (pt "GqD 3 6")))
;; (pp (nt (pt "GqD 3 9")))
;; (pp (nt (pt "GqD 3 10")))
;; (pp (nt (pt "GqD 3 10")))
;; (pp (nt (pt "GqD 3 11")))
;; (pp (nt (pt "GqD 3 12")))
;; (pp (nt (pt "GqD 3 13")))
;; (pp (nt (pt "GqD 3 14")))
;; (pp (nt (pt "GqD 3 15")))
;; ;; Succ(Succ(Succ Zero))pair Succ(Succ(Succ Zero))
;; (pp (nt (pt "GqD 3 16")))
;; ;; Succ(Succ(Succ Zero))pair Succ(Succ(Succ Zero))
;; (pp (nt (pt "GqD 3 17")))
;; (pp (nt (pt "GqD 3 24")))
;; (pp (nt (pt "GqD 3 25")))
;; (pp (nt (pt "GqD 3 26")))
;; always
;; Succ(Succ(Succ Zero))pair Succ(Succ(Succ Zero))

;; (pp (nt (pt "GqD 4 24")))
;; (pp (nt (pt "GqD 4 25")))
;; (pp (nt (pt "GqD 4 26")))

;; (display-pconst "GqD")
;; GqD n k=[if (k<Gs(Succ n)) (GsD k) (GqMlToIj n(GdsCToMl n(k--Gs(Succ n))))]

;; (display-pconst "GqMlToIj")
;; GqMlToIj n(m pair l)	Succ(m+l)pair n--l
;; The sum of the components is m+n+1, which is >n.


