;; 2025-07-28.  sdav.scm

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(libload "rea.scm")
(load "~/git/minlog/examples/analysis/digits.scm")
(load "~/git/minlog/examples/analysis/sdcode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/sdavaux.scm")
;; (set! COMMENT-FLAG #t)
|#

;; Haskell translation
;; ===================

;; terms-to-haskell-program (written by Fredrik Nordvall-Forsberg)
;; generates a Haskell file (here sdavtest.hs).  To run it, in a
;; terminal type ghci sdavtest.hs.  Then in *Main> one can evaluate
;; the Haskell functions in sdavtest.hs.  To quit type *Main> :q

;; (dep-tree "CoIAverage")

;; ("CoIAverage"
;;   ("Id")
;;   ("CoIAvcToCoI"
;;     ("Id")
;;     ("CoIAvcSatCoICl"
;;       ("CoIAvcSatCoIClAuxJ"
;;         ("SdtwoInjElim")
;;         ("SdtwoInjIntro")
;;         ("SdInjIntro"))
;;       ("CoIAvcSatCoIClAuxK"
;;         ("SdInjElim")
;;         ("SdtwoInjIntro")
;;         ("SdInjIntro"))
;;       ("CoIClosure" ("CoIClause"))))
;;   ("CoIAvToAvc"
;;     ("IntPlusSdToSdtwo" ("SdtwoInjElim") ("SdInjIntro"))
;;     ("CoIClosure" ("CoIClause"))))

;; Guided by this dependence tree of computationally relevant theorems
;; we animate them, working from the root CoIAverage upwards.

;; (display-animation)
(deanimate-all)

'(
(animate "CoIAverage")

(animate "Id")
(animate "CoIAvcToCoI")
(animate "CoIAvToAvc")

(animate "CoIAvcSatCoICl")
(animate "IntPlusSdToSdtwo")
(animate "CoIClosure")

(animate "CoIAvcSatCoIClAuxJ")
(animate "CoIAvcSatCoIClAuxK")
(animate "SdtwoInjElim")
(animate "SdtwoInjIntro")
(animate "CoIClause")

(animate "SdInjElim")
(animate "SdInjIntro")

;; We also need
(animate "RealToCoIAux")
(animate "RealToCoI")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplit")
(animate "ApproxSplitPos")

(terms-to-haskell-program
 "~/temp/sdavtest.hs"
 (list (list CoIAverage-eterm "coiav")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "IrrStr") "irrstr")
       (list (pt "AiToReal") "aitoreal")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))
)

;; ghci sdavtest.hs
;; takestr 10 (coiav (realtocoi stot) ptfive)
;; [SdR,SdM,SdR,SdM,SdL,SdR,SdL,SdM,SdR,SdM]

;; listsdtorat (takestr 10 (coiav (realtocoi stot) ptfive))
;; 309 % 512

;; (exact->inexact 309/512)
;; 0.603515625

;; (/ (+ (* (sqrt 2) 0.5) 0.5) 2)
;; 0.6035533905932737

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) (onesdl 1))

;; SdM,SdR,SdM,SdL,SdM,SdM,SdR,SdM,SdM,SdM,SdR,SdM,SdM,SdM,SdM,SdR,SdM,SdM

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) mptfive)

;; SdM,SdM,SdM,SdR,SdM,SdM,SdR,SdM,SdM,SdM,SdR,SdM,SdM,SdM,SdM,SdR,SdM,SdM

;; takestr 18 (coiav (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 1))))

;; SdR,SdM,SdR,SdM,SdL,SdM,SdR,SdM,SdR,SdM,SdR,SdM,SdM,SdR,SdM,SdR,SdM,SdM
