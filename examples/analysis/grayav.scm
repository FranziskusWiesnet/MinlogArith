;; 2025-11-21.  examples/analysis/grayav.scm

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "str.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
(load "~/git/minlog/examples/analysis/digits.scm")
(load "~/git/minlog/examples/analysis/sdcode.scm")
;; (load "~/temp/graycode2.scm")
(load "~/git/minlog/examples/analysis/graycode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/grayavaux.scm")
;; (set! COMMENT-FLAG #t)
|#

;; Haskell translation
;; ===================

;; terms-to-haskell-program (written by Fredrik Nordvall-Forsberg)
;; generates a Haskell file (here sdavtest.hs).  To run it, in a
;; terminal type ghci sdavtest.hs.  Then in *Main> one can evaluate
;; the Haskell functions in grayavtest.hs.  To quit type *Main> :q.

(dep-tree "CoGAverage")

#|
("CoGAverage"
  ("CoGAvcToCoG" ("Id") ("IntTimesSdtwoPsdToSdtwo") ("PsdUMinus")
    ("CoGPsdTimes"
      ("CoGCompat"
        ("CoGClauseInv" ("Lft") ("Rht"))
        ("Lft")
        ("Rht")
        ("CoGClause"))
      ("CoGUMinus"
        ("PsdUMinus")
        ("CoHCompat"
          ("CoHClauseInv" ("Lft") ("Rht"))
          ("Lft")
          ("Rht")
          ("CoHClause"))
        ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
        ("CoHClosure" ("Lft") ("Rht") ("CoHClause"))))
    ("SdDisj") ("Lft") ("Rht")
    ("CoGAvcSatCoICl"
      ("CoGAvcSatCoIClAuxJ"
        ("SdtwoInjElim")
        ("SdtwoInjIntro")
        ("PsdInjIntro"))
      ("Lft")
      ("CoGAvcSatCoIClAuxK"
        ("SdInjElim")
        ("SdtwoInjIntro")
        ("PsdInjIntro"))
      ("CoGPsdTimes"
        ("CoGCompat"
          ("CoGClauseInv" ("Lft") ("Rht"))
          ("Lft")
          ("Rht")
          ("CoGClause"))
        ("CoGUMinus"
          ("PsdUMinus")
          ("CoHCompat"
            ("CoHClauseInv" ("Lft") ("Rht"))
            ("Lft")
            ("Rht")
            ("CoHClause"))
          ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
          ("CoHClosure" ("Lft") ("Rht") ("CoHClause"))))
      ("Rht") ("PsdUMinus") ("SdtwoPsdToSdtwoJ") ("SdtwoPsdToSdK")
      ("CoHToCoG" ("Lft")
        ("CoGUMinus"
          ("PsdUMinus")
          ("CoHCompat"
            ("CoHClauseInv" ("Lft") ("Rht"))
            ("Lft")
            ("Rht")
            ("CoHClause"))
          ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
          ("CoHClosure" ("Lft") ("Rht") ("CoHClause")))
        ("CoGCompat"
          ("CoGClauseInv" ("Lft") ("Rht"))
          ("Lft")
          ("Rht")
          ("CoGClause"))
        ("Rht") ("CoHClosure" ("Lft") ("Rht") ("CoHClause"))
        ("CoGClosure" ("Lft") ("Rht") ("CoGClause")))
      ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
      ("SdtwoToSdtwoJ") ("SdtwoToSdK")))
  ("CoGAvToAvc" ("IntPlusPsdToSdtwo") ("Lft")
    ("CoGPsdTimes"
      ("CoGCompat"
        ("CoGClauseInv" ("Lft") ("Rht"))
        ("Lft")
        ("Rht")
        ("CoGClause"))
      ("CoGUMinus"
        ("PsdUMinus")
        ("CoHCompat"
          ("CoHClauseInv" ("Lft") ("Rht"))
          ("Lft")
          ("Rht")
          ("CoHClause"))
        ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
        ("CoHClosure" ("Lft") ("Rht") ("CoHClause"))))
    ("Rht") ("PsdUMinus") ("PsdToSdtwo")
    ("CoHToCoG" ("Lft")
      ("CoGUMinus"
        ("PsdUMinus")
        ("CoHCompat"
          ("CoHClauseInv" ("Lft") ("Rht"))
          ("Lft")
          ("Rht")
          ("CoHClause"))
        ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))
        ("CoHClosure" ("Lft") ("Rht") ("CoHClause")))
      ("CoGCompat"
        ("CoGClauseInv" ("Lft") ("Rht"))
        ("Lft")
        ("Rht")
        ("CoGClause"))
      ("Rht") ("CoHClosure" ("Lft") ("Rht") ("CoHClause"))
      ("CoGClosure" ("Lft") ("Rht") ("CoGClause")))
    ("CoGClosure" ("Lft") ("Rht") ("CoGClause"))))
|#

;; (display-animation)
(deanimate-all)

(terms-to-haskell-program
 "~/temp/grayavtestmod.hs"
 (list (list CoGAverage-eterm "cogav")
       (list CoIToCoG-eterm "coitocog")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))

;; We animate theorems in the order of "undefined" messages in graytestmod.hs

(animate "CoGAvcToCoG")
(animate "CoGAvToAvc")
(animate "CoIUMinus")
(animate "CoICompat")
(animate "Rht")
(animate "PsdToDisj")
(animate "SdToPsd")
(animate "Lft")
(animate "CoIClause")
(animate "SdInjElim")
(animate "RealToCoIAux")
(animate "RealToCoI")

(terms-to-haskell-program
 "~/temp/grayavtestmod.hs"
 (list (list CoGAverage-eterm "cogav")
       (list CoIToCoG-eterm "coitocog")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))

;; We animate theorems in the order of "undefined" messages in graytestmod.hs
;; This gives many warnings: warning: program constant cApproxSplitZeroPtFive
;; has no computation rules [try (animate "ApproxSplitZeroPtFive") ]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; We animate theorems in the order proposed by terms-to-haskell-program

(animate "RealToCoIAux")
(animate "RealToCoI")
(animate "ApproxSplitZeroPtFive")
(animate "SdInjElim")
(animate "ApproxSplitZeroMinusPtFive")
(animate "CoIClause")
(animate "ApproxSplit")
(animate "ApproxSplitPos")
(animate "PsdToDisj")
(animate "SdToPsd")
(animate "CoIUMinus")
(animate "CoICompat")
(animate "CoIClosure")
(animate "CoIClauseInv")
(animate "SdUMinus")
(animate "CoGAvcToCoG")
(animate "CoGAvToAvc")
(animate "CoGAvcSatCoICl")
(animate "SdDisj")
(animate "IntTimesSdtwoPsdToSdtwo")
(animate "SdtwoToSdtwoJ")
(animate "SdtwoToSdK")
(animate "SdtwoPsdToSdtwoJ")
(animate "SdtwoPsdToSdK")
(animate "CoGAvcSatCoIClAuxJ")
(animate "CoGAvcSatCoIClAuxK")
(animate "SdtwoInjElim")
(animate "SdtwoInjIntro")
(animate "IntPlusPsdToSdtwo")
(animate "PsdInjIntro")
(animate "PsdToSdtwo")
(animate "CoHToCoG")
(animate "CoGCompat")
(animate "CoHClosure")
(animate "CoGUMinus")
(animate "CoHCompat")
(animate "CoHClause")
(animate "CoHClauseInv")
(animate "CoGClause")
(animate "CoGClauseInv")
(animate "CoGPsdTimes") ;long
(animate "PsdUMinus")
(animate "CoGClosure")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Guided by this dependence tree of computationally relevant theorems
;; we animate them, working from the root CoGAverage upwards.

;; Apply simultaneously (terms-to-haskell-program ...) here and
;; in grayavtest.scm (on the old laptop), stepwise

(terms-to-haskell-program
 "~/temp/grayavtest.hs"
 (list (list CoGAverage-eterm "cogav")
       (list CoIToCoG-eterm "coitocog")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))



;; warning: program constant cRealToCoIAux has no computation rules [try (animate "RealToCoIAux") ]...

(animate "RealToCoIAux")

;; ok, computation rule cRealToCoIAux -> [x0][if x0 ([as1,M2][if (cApproxSplitZeroMinusPtFive x0) (SdL pair RealConstr([n3]2*as1 n3+1)([p3]M2(PosS p3))) [if (cApproxSplitZeroPtFive x0) (SdM pair RealConstr([n3]2*as1 n3)([p3]M2(PosS p3))) (SdR pair RealConstr([n3]2*as1 n3+IntN 1)([p3]M2(PosS p3)))]])] added

;; warning: program constant cRealToCoI has no computation rules [try (animate "RealToCoI") ]

(animate "RealToCoI")

;; ok, computation rule cRealToCoI -> [x0](CoRec sd yprod rea=>ai)[if x0 ([as1,M2][if (cApproxSplitZeroMinusPtFive x0) (SdL pair RealConstr([n3]2*as1 n3+1)([p3]M2(PosS p3))) [if (cApproxSplitZeroPtFive x0) (SdM pair RealConstr([n3]2*as1 n3)([p3]M2(PosS p3))) (SdR pair RealConstr([n3]2*as1 n3+IntN 1)([p3]M2(PosS p3)))]])]([sx1][if sx1 ([s2,x3][if [if x3 ([as4,M5][if (cApproxSplitZeroMinusPtFive x3) (SdL pair RealConstr([n6]2*as4 n6+1)([p6]M5(PosS p6))) [if (cApproxSplitZeroPtFive x3) (SdM pair RealConstr([n6]2*as4 n6)([p6]M5(PosS p6))) (SdR pair RealConstr([n6]2*as4 n6+IntN 1)([p6]M5(PosS p6)))]])] ([s4,x5]cSdInjElim s2 pair(InR (sd yprod rea) ai)(s4 pair x5))])]) added

;; warning: program constant cApproxSplitZeroPtFive has no computation rules [try (animate "ApproxSplitZeroPtFive") ]

(animate "ApproxSplitZeroPtFive")

;; ok, computation rule cApproxSplitZeroPtFive -> [x0]cApproxSplit 0(1#2)x0 1 added

;; warning: program constant cSdInjElim has no computation rules [try (animate "SdInjElim") ]

(animate "SdInjElim")

;; ok, computation rule cSdInjElim -> [s0]s0 added

;; warning: program constant cApproxSplitZeroMinusPtFive has no computation rules [try (animate "ApproxSplitZeroMinusPtFive") ]

(animate "ApproxSplitZeroMinusPtFive")

;; ok, computation rule cApproxSplitZeroMinusPtFive -> [x0]cApproxSplit(IntN 1#2)0 x0 1 added

;; warning: program constant cCoIClause has no computation rules [try (animate "CoIClause") ]

(animate "CoIClause")

;; ok, computation rule cCoIClause -> (Destr ai) added

;; warning: program constant cApproxSplit has no computation rules [try (animate "ApproxSplit") ]

(animate "ApproxSplit")

;; ok, computation rule cApproxSplit -> cApproxSplitPos added

;; warning: program constant cApproxSplitPos has no computation rules [try (animate "ApproxSplitPos") ]

(animate "ApproxSplitPos")

;; ok, computation rule cApproxSplitPos -> [x0,x1,x2,p3][if x0 ([as4,M5][if x1 ([as6,M7][if x2 ([as8,M9]as8(M7(PosS(PosS p3))max M5(PosS(PosS p3))max M9(PosS(PosS p3)))<=(1#2)*(as4(M7(PosS(PosS p3))max M5(PosS(PosS p3)))+as6(M7(PosS(PosS p3))max M5(PosS(PosS p3)))))])])] added

;; warning: program constant cPsdToDisj has no computation rules [try (animate "PsdToDisj") ] ...













;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The rest is obsolete.

;; '(
;; (animate "RealToCoI")
;; (animate "RealToCoIAux")
;; (animate "ApproxSplitZeroMinusPtFive")
;; (animate "ApproxSplitZeroPtFive")
;; (animate "ApproxSplit")
;; (animate "CoGAvcToCoG")
;; (animate "CoGAvToAvc")
;; (animate "CoGAvcSatCoICl")
;; (animate "SdDisj")
;; (animate "IntTimesSdtwoPsdToSdtwo")
;; (animate "SdtwoToSdtwoJ")
;; (animate "SdtwoToSdK")
;; (animate "SdtwoPsdToSdtwoJ")
;; (animate "SdtwoPsdToSdK")
;; (animate "CoGAvcSatCoIClAuxJ")
;; (animate "CoGAvcSatCoIClAuxK")
;; (animate "PsdToSdtwo")
;; (animate "CoHToCoG")
;; (animate "CoGCompat")
;; (animate "CoGUMinus")
;; (animate "CoHClosure")
;; (animate "CoGClauseInv")
;; (animate "CoHCompat")
;; (animate "CoHClauseInv")
;; (animate "Rht")
;; (animate "PsdUMinus")
;; (animate "Lft")
;; (animate "CoGPsdTimes")
;; (animate "CoGClosure")
;; (animate "IntPlusPsdToSdtwo")
;; (animate "SdToPsd")
;; (animate "CoICompat")
;; (animate "PsdToDisj")
;; (animate "CoIUMinus")
;; (animate "SdUMinus")
;; (animate "CoIClosure")
;; (animate "CoIClauseInv")
;; (animate "CoGClause")
;; (animate "CoHClause")
;; (animate "SdInjElim")
;; (animate "PsdInjIntro")
;; (animate "SdtwoInjIntro")
;; (animate "SdtwoInjElim")
;; (animate "CoIClause")
;; (animate "ApproxSplitPos")
;; )

;; (terms-to-haskell-program
;;  "~/temp/grayavtest.hs"
;;  (list (list CoGAverage-eterm "cogav")
;;        (list CoIToCoG-eterm "coitocog")
;;        (list RealToCoI-eterm "realtocoi")
;;        (list RatToCoI-eterm "rattocoi")
;;        (list (pt "SdMs") "sdms")
;;        (list (pt "PtFive") "ptfive")
;;        (list (pt "MPtFive") "mptfive")
;;        (list (pt "OneSdR") "onesdr")
;;        (list (pt "OneSdL") "onesdl")
;;        (list (pt "SqrtTwoOverTwo") "stot")
;;        (list (pt "TakeStr") "takestr")
;;        (list (pt "ListSdToRat") "listsdtorat")))

;; ;; ok, output written to file ~/temp/grayavtest.hs
;; ;; 647 lines

;; ;; ghci grayavtest.hs

;; ;; Error: Left (,)

(deanimate-all)

(animate "CoGAvToAvc")
(animate "IntPlusPsdToSdtwo")
(animate "CoGClosure")
(animate "CoGClause")
(animate "CoGPsdTimes")
(animate "CoGUMinus")
(animate "CoHCompat")
(animate "CoHClauseInv")
(animate "CoHClause")
(animate "PsdUMinus")
(animate "CoGCompat")
(animate "CoGClauseInv")
(animate "CoHClosure")
(animate "CoHToCoG") ;3 pages!
(animate "PsdToSdtwo")
(animate "CoGAvcToCoG") ;9 pages!
(animate "SdDisj")
(animate "IntTimesSdtwoPsdToSdtwo")
(animate "CoGAvcSatCoICl") ;19 pages!
(animate "CoIUMinus")
(animate "CoGAvcSatCoIClAuxK")
(animate "SdInjElim")
(animate "PsdInjIntro")
(animate "CoGAvcSatCoIClAuxJ")
(animate "SdtwoInjIntro")
(animate "SdtwoInjElim")
(animate "SdtwoPsdToSdK")
(animate "SdtwoPsdToSdtwoJ")
(animate "SdtwoToSdK")
(animate "SdtwoToSdtwoJ")
(animate "SdUMinus")
(animate "CoICompat")
(animate "CoIClauseInv")
(animate "CoIClause")
(animate "CoIClosure")
(animate "PsdToDisj")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplit")
(animate "ApproxSplitPos")
(animate "SdToPsd")
(animate "ApproxSplitZeroPtFive")
(animate "RealToCoI")

(terms-to-haskell-program
 "~/temp/grayavtest.hs"
 (list (list CoGAverage-eterm "cogav")
       (list CoIToCoG-eterm "coitocog")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))

;; ok, output written to file ~/temp/grayavtest.hs
;; 2295 lines

;; ghci grayavtest.hs

;; Error: Left (,)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
(deanimate "CoGAvcToCoG")
(deanimate "CoGAvToAvc")
(deanimate "CoGAvcSatCoICl")
(deanimate "SdDisj")
(deanimate "IntTimesSdtwoPsdToSdtwo")
(deanimate "SdtwoToSdtwoJ")
(deanimate "SdtwoToSdK")
(deanimate "SdtwoPsdToSdtwoJ")
(deanimate "SdtwoPsdToSdK")
(deanimate "CoGAvcSatCoIClAuxJ")
(deanimate "CoGAvcSatCoIClAuxK")
(deanimate "PsdToSdtwo")
(deanimate "CoHToCoG")
(deanimate "CoGCompat")
(deanimate "CoGUMinus")
(deanimate "CoHClosure")
(deanimate "CoGClauseInv")
(deanimate "CoHCompat")
(deanimate "CoHClauseInv")
(deanimate "Rht")
(deanimate "PsdUMinus")
(deanimate "Lft")
(deanimate "CoGPsdTimes")
(deanimate "CoGClosure")
(deanimate "IntPlusPsdToSdtwo")
(deanimate "SdToPsd")
(deanimate "CoICompat")
(deanimate "PsdToDisj")
(deanimate "CoIUMinus")
(deanimate "SdUMinus")
(deanimate "CoIClosure")
(deanimate "CoIClauseInv")
)

;; ghci grayavtest.hs

;; cogav (coitocog (rattocoi (1 % 3))) (coitocog (rattocoi (4 % 7)))
;; LR True (U (D (Fin True (U (Fin False (U (D (D (Fin False (U (Fin False (U

;; cogav (coitocog (realtocoi stot)) (coitocog (rattocoi (4 % 7)))
;; LR True (LR False (LR True (U (D (Fin True (U (D (Fin False (U (Fin False 

