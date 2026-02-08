;; 2025-07-28.  examples/analysis/JK.scm

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
;; (set! COMMENT-FLAG #t)
|#

(display "loading JK.scm ...") (newline)

;; We define JKTwo: int=>int and JKOne: int=>int and such that
;; (1) for abs k<=6 we have abs(JKTwo k)<=1
;; (2) abs(JKOne k)<=2
;; (3) k=(JKTwo k)*4+(JKOne k).

(add-program-constant "JKTwo" (py "int=>int"))
(add-computation-rules
 "JKTwo p" "lft(PosQR(PosS p)4)"
 "JKTwo 0" "0"
 "JKTwo(IntN p)" "~lft(PosQR(PosS p)4)")

(set-totality-goal "JKTwo")
(fold-alltotal)
(cases)
;; 3-5
(assume "p")
(use "TotalVar")
;; 4
(use "TotalVar")
;; 5
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

(add-program-constant "JKOne" (py "int=>int"))
(add-computation-rules
 "JKOne p" "IntPred rht(PosQR(PosS p)4)"
 "JKOne 0" "0"
 "JKOne(IntN p)" "IntS~rht(PosQR(PosS p)4)")

(set-totality-goal "JKOne")
(fold-alltotal)
(cases)
;; 3-5
(assume "p")
(use "TotalVar")
;; 4
(use "TotalVar")
;; 5
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; KProp
(set-goal "all k(abs k<=6 -> abs(JKTwo k)<=1)")
(assert "all p(2<=lft(PosQR p 4) -> 2*IntP 4<=p)")
(assume "p" "2<=Qp4")
(assert "2*IntP 4<=lft(PosQR p 4)*4+rht(PosQR p 4)")
(use "IntLeTrans" (pt "lft(PosQR p 4)*4"))
(use "IntLeMonTimes")
(use "Truth")
(use "2<=Qp4")
(use "IntLeTrans" (pt "lft(PosQR p 4)*4+0"))
(use "Truth")
(use "IntLeMonPlus")
(use "Truth")
(use "PosQRCorrAux" (pt "p") (pt "4") (pt "lft(PosQR p 4)"))
(simp "PairConstrOneTwoInt")
(use "Truth")
(assume "Assertion")
(assert "p=lft(PosQR p 4)*4+rht(PosQR p 4)")
(use "PosQRCorrAux")
(simp "PairConstrOneTwoInt")
(use "Truth")
(assume "pProp")
(simp "pProp")
(simp "<-" "Assertion")
(use "Truth")
;; Assertion proved.
(assume "KPosAux1")
(assert "all p(IntP p<=7 -> lft(PosQR p 4)<=1)")
(assume "p" "p<=7")
(use "IntNotLtToLe")
(simp "<-" "IntLeIntS")
(assume "2<=Qp4")
(inst-with-to "KPosAux1" (pt "p") "2<=Qp4" "KPosAux1Inst")
(assert "IntP 8<=7")
 (use "IntLeTrans" (pt "IntP p"))
 (use "KPosAux1Inst")
 (use "p<=7")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "KPosAux2")
(assert "all p(p<=6 -> lft(PosQR(PosS p)4)<=1)")
(assume "p" "p<=6")
(use "KPosAux2")
(ng #t)
(simp (pf "7=PosS 6"))
(simp "PosLe9RewRule")
(use "p<=6")
(use "Truth")
;; Assertion proved.
(assume "KPosProp")
(assert "all p,q 0<=lft(PosQR p q)")
(ind)
;; 2-4
(cases)
;; 5-7
(use "Truth")
;; 6
(assume "p")
(use "Truth")
;; 7
(assume "p")
(use "Truth")
;; 3
(assume "p" "IH" "q")
(ng)
(inst-with-to "PairConstrOneTwoInt"
	      (py "int") (py "int") (pt "PosQR p q") "PairConstrOneTwoIntInst")
(simp "<-" "PairConstrOneTwoIntInst")
(drop "PairConstrOneTwoIntInst")
(ng)
(cases (pt "(2*rht(PosQR p q)<q)"))
(assume "Useless")
(ng)
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
;; 18
(assume "Useless")
(ng)
(use "IntLeTrans" (pt "2*lft(PosQR p q)"))
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; 4
(assume "p" "IH" "q")
(ng)
(inst-with-to "PairConstrOneTwoInt"
	      (py "int") (py "int") (pt "PosQR p q") "PairConstrOneTwoIntInst")
(simp "<-" "PairConstrOneTwoIntInst")
(drop "PairConstrOneTwoIntInst")
(ng)
(cases (pt "(2*rht(PosQR p q)+1<q)"))
(assume "Useless")
(ng)
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
;; 41
(assume "Useless")
(ng)
(use "IntLeTrans" (pt "2*lft(PosQR p q)"))
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "PosQRPairOneNNeg")
;; Now we are ready to prove KProp: all k(abs k<=6 -> abs(JKTwo k)<=1)")
(cases)
;; 11-13
(assume "p")
(ng)
(simp "IntAbsId")
(use "KPosProp")
(use "PosQRPairOneNNeg")
;; 12
(strip)
(use "Truth")
;; 13
(assume "p")
(ng)
(simp "IntAbsId")
(use "KPosProp")
(use "PosQRPairOneNNeg")
;; Proof finished.
;; (cp)
(save "KProp")

;; JProp
(set-goal "all k abs(JKOne k)<=2")
(cases)
;; 2-4
(assume "p")
(use "IntLeAbs")
;; 6,7
(ng)
(simp "<-" "IntLe6RewRule")
(ng)
(simp "<-" "IntLtIntS")
(use "PosQRCorr")
;; 7
(ng)
(use "IntLeTrans" (pt "IntS~0"))
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(use "PosQRCorr")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(ng)
(use "IntLeAbs")
;; 19,20
(use "IntLeTrans" (pt "IntS~0"))
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(use "PosQRCorr")
(use "Truth")
;; 20
(simp (pf "2= ~(IntS~3)"))
(simp "IntLe5RewRule")
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(simp "<-" "IntLtIntS")
(use "PosQRCorr")
(use "Truth")
;; Proof finished.
;; (cp)
(save "JProp")

;; KJProp
(set-goal "all k k=JKTwo k*4+JKOne k")
(cases)
;; 2-4
(ng)
(assume "p")
(simp "<-" "IntSInj")
(use "Truth")
(ng)
(simp (pf "all k,j IntS(k+j)=k+IntS j"))
(ng)
(use "PosQRCorr")
;; ?_11:all k,j IntS(k+j)=k+IntS j
(strip)
(use "Truth")
;; 3
(use "Truth")
;; 4
(ng)
(assume "p")
(simp "<-" "IntUMinusInj")
(ng)
(simp "<-" "PosQRCorr")
(use "Truth")
;; Proof finished.
;; (cp)
(save "KJProp")

