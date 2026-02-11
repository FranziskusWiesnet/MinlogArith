;; 2025-07-28.  sqrt2.scm.

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
(libload "rseq.scm")
(libload "cont.scm")
(load "~/git/minlog/examples/analysis/ivt.scm")
;; (set! COMMENT-FLAG #t)
|#

(if (not (member "lib/cont.scm" LOADED-FILES))
    (myerror "First load lib/cont.scm"))

;; 1.  SqMTwo
;; ==========

;; We want to instantiate IVTFinal to SqMTwo: x \mapsto x^2-2.  Then
;; the resulting real is the square root of 2.  Via RealApprox we can
;; then compute a rational approximation of a given accuracy.

(add-program-constant "SqMTwo" (py "cont"))

(add-computation-rules
 "SqMTwo" "ContConstr 1 2([a,n](a*a+ RatUMinus 2))
                      ([p]Zero)
                      ([p](PosS(PosS(PosS p))))
                      (IntN 1#1)
                      (2#1)")

(set-totality-goal "SqMTwo")
(intro 0)
(use "RatTotalVar")
(use "RatTotalVar")
(fold-alltotal)
(assume "a")
(fold-alltotal)
(assume "n")
(use "RatTotalVar")
;; 5
(fold-alltotal)
(assume "p")
(use "NatTotalVar")
;; 6
(fold-alltotal)
(assume "p")
(use "PosTotalVar")
;; 7
(use "RatTotalVar")
;; 8
(use "RatTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; ContSqMTwo
(set-goal "Cont SqMTwo")
(intro 0)
;; 2-7
(assume "a" "1<=a" "a<=2")
(intro 0)
(ng #t)
(assume "p" "n" "m" "Useless1" "Useless2")
(simprat (pf "IntN 2==RatUMinus 2"))
(simprat "RatEqvPlusMinusPlus")
(simprat (pf "a*a+ ~(a*a)==0"))
(use "Truth")
(use "Truth")
(use "Truth")
;; 3
(ng #t)
(assume "a" "b" "p" "n" "1<=a" "a<=2" "1<=b" "b<=2" "Useless" "|a-b|Bd")
(simprat (pf "IntN 2==RatUMinus 2"))
(simprat "RatEqvPlusMinusPlus")
(simprat "<-" "RatEqvTimesPlusMinus")
(simp "RatAbsTimes")
(use "RatLeTrans" (pt "abs(a+b)*(1#2**PosS(PosS p))"))
;; 24,25
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "Truth")
(use "|a-b|Bd")
;; 25
(use "RatLeTrans" (pt "(1+1)*((1+1)*(1#2**PosS(PosS p)))"))
(simp "RatTimesAssoc")
(use "RatLeMonTimes")
(use "Truth")
(ng #t)
(simp "RatAbsId")
(use "RatLeTrans" (pt "RatPlus 2 2"))
(use "RatLeMonPlus")
(use "a<=2")
(use "b<=2")
(use "Truth")
(use "RatLeTrans" (pt "RatPlus 1 1"))
(use "Truth")
(use "RatLeMonPlus")
(use "1<=a")
(use "1<=b")
(simp (pf "1+1=RatPlus 1 1"))
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimes1RewRule")
(simp "RatTimes1RewRule")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
(use "Truth")
(use "Truth")
;; 4
(ng #t)
(strip)
(use "Truth")
;; 5
(ng #t)
(search)
;; 6
(ng #t)
(assume "a" "n" "1<=a" "a<=2")
(use "RatLeTrans" (pt "(RatTimes 1 1)+IntN 2"))
(use "Truth")
(use "RatLeMonPlus")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "1<=a")
(use "1<=a")
(use "Truth")
;; 7
(ng #t)
(assume "a" "n" "1<=a" "a<=2")
(use "RatLeTrans" (pt "(RatTimes 2 2)+IntN 2"))
(use "RatLeMonPlus")
(use "RatLeMonTimesTwo")
(use "RatLeTrans" (pt "(1#1)"))
(use "Truth")
(use "1<=a")
(use "RatLeTrans" (pt "(1#1)"))
(use "Truth")
(use "1<=a")
(use "a<=2")
(use "a<=2")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "ContSqMTwo")

;; 2.  IVTInst
;; ===========

;; IVTInst
(set-goal
 "exr x(Real x andr SqMTwo x===0 andr all r exl c abs(c+ ~x)<<=(1#2**r))")
(use "IVTApprox" (pt "1") (pt "1"))
;; 2-7
(use "ContSqMTwo")
;; 3
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 4
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
;; 5
(ng #t)
(use "Truth")
;; 6
(ng #t)
(use "Truth")
;; 7
(ng #t)
(assume "c" "d" "p" "1<=c" "d<=2" "c+1/2^p<=d")
(assert "c<=d")
(use "RatLeTrans" (pt "c+(1#2**p)"))
(use "RatLeTrans" (pt "c+0"))
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "c+1/2^p<=d")
;; Assertion proved.
(assume "c<=d")
(simp (pf "c max 1 min 2=c"))
(simp (pf "d max 1 min 2=d"))
(simp (pf "IntN 2=RatUMinus 2"))
(simprat "RatEqvPlusMinusPlus")
(simprat "<-" "RatEqvTimesPlusMinus")
(use "RatLeTrans" (pt "(1#2)*(1#2**p)"))
(simprat "<-" (pf "(1#2**PosS p)+(1#2**PosS p)==(1#2**p)"))
(simprat "<-" "RatTwoTimes")
(ng #t)
(use "Truth")
(use "RatPlusHalfExpPosS")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "RatPlus 1 1"))
(use "Truth")
(use "RatLeMonPlus")
(use "RatLeTrans" (pt "c"))
(use "1<=c")
(use "c<=d")
(use "1<=c")
(use "RatLeTrans" (pt "c+(1#2**p)+ ~c"))
(simp "RatPlusComm")
(ng #t)
(simprat (pf "~c+c==0"))
(use "Truth")
(use "Truth")
(use "RatLeMonPlus")
(use "c+1/2^p<=d")
(use "Truth")
(use "Truth")
(simp "RatMaxMinEq")
(use "Truth")
(use "d<=2")
(use "RatLeTrans" (pt "c"))
(use "1<=c")
(use "c<=d")
(simp "RatMaxMinEq")
(use "Truth")
(use "RatLeTrans" (pt "d"))
(use "c<=d")
(use "d<=2")
(use "1<=c")
;; Proof finished.
;; (cp)
(save "IVTInst")

;; 3.  Extracted term
;; ==================

;; (dep-tree "IVTInst")

;; ("IVTInst"
;;   ("IVTApprox"
;;     ("RealApprox")
;;     ("IVTFinal"
;;       ("IVTcds"
;;         ("DC")
;;         ("IVTAux"
;;           ("Id")
;;           ("ApproxSplitBoole" ("ApproxSplit" ("ApproxSplitPos"))))))))

;; Guided by this dependence tree of computationally relevant theorems
;; we animate them, working from the root IVTInst upwards.

;; (display-animation)
;; (deanimate-all)

;; Annimate from the leaves to the root

(animate "ApproxSplitPos")
(pp "cApproxSplitPos0CompRule")

;; cApproxSplitPos eqd
;; ([x,x0,x1,p]
;;   [if x
;;     ([as,M]
;;      [if x0
;;        ([as0,M0]
;;         [if x1
;;           ([as1,M1]
;;            as1(M0(PosS(PosS p))max M(PosS(PosS p))max M1(PosS(PosS p)))<=
;;            (1#2)*
;;            (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;             as0(M0(PosS(PosS p))max M(PosS(PosS p)))))])])])

(animate "ApproxSplit")
(pp "cApproxSplit0CompRule")

;; cApproxSplit eqd
;; ([x,x0,x1,p]
;;   [if x
;;     ([as,M]
;;      [if x0
;;        ([as0,M0]
;;         [if x1
;;           ([as1,M1]
;;            as1(M0(PosS(PosS p))max M(PosS(PosS p))max M1(PosS(PosS p)))<=
;;            (1#2)*
;;            (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;             as0(M0(PosS(PosS p))max M(PosS(PosS p)))))])])])

(animate "ApproxSplitBoole")
(pp "cApproxSplitBoole0CompRule")

;; cApproxSplitBoole eqd
;; ([x,x0,x1,p]
;;   [if x
;;     ([as,M]
;;      [if x0
;;        ([as0,M0]
;;         [if x1
;;           ([as1,M1]
;;            as1(M0(PosS(PosS p))max M(PosS(PosS p))max M1(PosS(PosS p)))<=
;;            (1#2)*
;;            (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;             as0(M0(PosS(PosS p))max M(PosS(PosS p)))))])])])

(animate "Id")

(animate "IVTAux")
(pp "cIVTAux0CompRule")

;; cIVTAux eqd
;; ([f,p,p0,cd]
;;   [if (0<=
;;         (1#2)*
;;         (f approx((1#3)*(lft cd+lft cd+rht cd)max f doml min f domr)
;;          (f uMod(PosS(PosS(PosS(2+p0+p)))))+
;;          f approx((1#3)*(lft cd+rht cd+rht cd)max f doml min f domr)
;;          (f uMod(PosS(PosS(PosS(2+p0+p)))))))
;;     (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;     ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)])

(animate "DC")
(pp "cDC0CompRule")
;; (cDC alpha)eqd([xx,g,n](Rec nat=>alpha)n xx g)

(animate "IVTcds")
(pp "cIVTcds0CompRule")

;; cIVTcds eqd
;; ([f,p,p0,n]
;;   (Rec nat=>rat yprod rat)n(f doml pair f domr)
;;   ([n0,cd]
;;     [if (0<=
;;           (1#2)*
;;           (f approx((1#3)*(lft cd+lft cd+rht cd)max f doml min f domr)
;;            (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n0)+p)))))+
;;            f approx((1#3)*(lft cd+rht cd+rht cd)max f doml min f domr)
;;            (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n0)+p)))))))
;;       (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;       ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)]))

(animate "IVTFinal")
(pp "cIVTFinal0CompRule")

;; cIVTFinal eqd
;; ([f,p,p0]
;;   RealConstr
;;   ([n]
;;     lft((Rec nat=>rat yprod rat)n(f doml pair f domr)
;;         ([n0,cd]
;;           [if (0<=
;;                 (1#2)*
;;                 (f approx((1#3)*(lft cd+lft cd+rht cd)max f doml min f domr)
;;                  (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n0)+p)))))+
;;                  f approx((1#3)*(lft cd+rht cd+rht cd)max f doml min f domr)
;;                  (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n0)+p)))))))
;;             (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;             ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)])))
;;   ([p1]TwoThirdExpBd(p1+p0)))

(animate "RealApprox")
(pp "cRealApprox0CompRule")
;; cRealApprox eqd([x,p]x seq(x mod p))

(animate "IVTApprox")
(pp "cIVTApprox0CompRule")

;; cIVTApprox eqd
;; ([f,p,p0,p1]
;;   lft((Rec nat=>rat yprod rat)(TwoThirdExpBd(p1+p0))(f doml pair f domr)
;;       ([n,cd]
;;         [if (0<=
;;               (1#2)*
;;               (f approx((1#3)*(lft cd+lft cd+rht cd)max f doml min f domr)
;;                (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n)+p)))))+
;;                f approx((1#3)*(lft cd+rht cd+rht cd)max f doml min f domr)
;;                (f uMod(PosS(PosS(PosS(2+NatToPos(p0+n)+p)))))))
;;           (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;           ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)])))

(animate "IVTInst")
(pp "cIVTInst0CompRule")

;; cIVTInst eqd
;; ([p]
;;   lft((Rec nat=>rat yprod rat)(TwoThirdExpBd(PosS p))(1 pair 2)
;;       ([n,cd]
;;         [if (0<=
;;               (1#2)*
;;               ((1#3)*(lft cd+lft cd+rht cd)max 1 min 2*
;;                ((1#3)*(lft cd+lft cd+rht cd)max 1 min 2)+
;;                IntN 2+
;;                (1#3)*(lft cd+rht cd+rht cd)max 1 min 2*
;;                ((1#3)*(lft cd+rht cd+rht cd)max 1 min 2)+
;;                IntN 2))
;;           (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;           ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)])))

;; 3.  Extracted term
;; ==================

(define IVTInst-eterm
  (proof-to-extracted-term (theorem-name-to-proof "IVTInst")))

(pp IVTInst-eterm)
;; cIVTApprox SqMTwo 1 1

;; (time (pp (nt (make-term-in-app-form IVTInst-eterm (pt "16")))))

(define IVTInst-neterm (rename-variables (nt IVTInst-eterm)))
(pp IVTInst-neterm)

;; [p]
;;  lft((Rec nat=>rat yprod rat)(TwoThirdExpBd(PosS p))(1 pair 2)
;;      ([n,cd]
;;        [if (0<=
;;              (1#2)*
;;              ((1#3)*(lft cd+lft cd+rht cd)max 1 min 2*
;;               ((1#3)*(lft cd+lft cd+rht cd)max 1 min 2)+
;;               IntN 2+
;;               (1#3)*(lft cd+rht cd+rht cd)max 1 min 2*
;;               ((1#3)*(lft cd+rht cd+rht cd)max 1 min 2)+
;;               IntN 2))
;;          (lft cd pair(1#3)*(lft cd+rht cd+rht cd))
;;          ((1#3)*(lft cd+lft cd+rht cd)pair rht cd)]))

;; Recall that TwoThirdExpBd is a program constant with the property
;; all p TwoThirdExpBd p=2*p

;; 4.  Numerical tests
;; ===================

;; 4.1.  Normalization
;; ===================

;; (time (pp (nt (make-term-in-app-form IVTInst-eterm (pt "16")))))

;; 23585087634298163#16677181699666569
;; 90 ms

(exact->inexact (/ 23585087634298163 16677181699666569))
;; 1.4142130282582281

(sqrt 2)
;; 1.4142135623730951

;; We might hope to get some speed-up by providing external code for
;; rational functions.  For instance, we want to view RatPlus as a
;; program constant with external code, using add-external-code.  The
;; external code - after evaluation and application to tsubst and the
;; arguments - should give either the final value (e.g., the numeral
;; for the sum) or else #f, in which case the rules are tried next on
;; the arguments.

;; However, it turns out that there is no speed-up. The reason
;; probably is that rational functions do not play an essential role
;; here.

(define ratplus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (sum (+ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator sum))
			  (denom (denominator sum))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratminus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (diff (- (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator diff))
			  (denom (denominator diff))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define rattimes-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (prod (* (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator prod))
			  (denom (denominator prod))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratdiv-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (quot (/ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator quot))
			  (denom (denominator quot))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratlt-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (< (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratle-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (<= (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(add-external-code "RatPlus" ratplus-code)
(add-external-code "RatMinus" ratminus-code)
(add-external-code "RatTimes" rattimes-code)
(add-external-code "RatDiv" ratdiv-code)
(add-external-code "RatLt" ratlt-code)
(add-external-code "RatLe" ratle-code)

;; (time (pp (nt (make-term-in-app-form IVTInst-eterm (pt "16")))))
;; No speedup

;; 4.2.  Scheme evaluation
;; =======================

;; We now translate terms into scheme expressions, for faster
;; evaluation (no conversions between internal and external numbers)

;; (term-to-scheme-expr IVTInst-neterm)

;; (lambda (p)
;;   (car (((natRec (TwoThirdExpBd (+ p 1))) (cons 1 2))
;;          (lambda (n)
;;            (lambda (cd)
;;              (if (<= 0
;;                      (* 1/2
;;                         (+ (+ (+ (* (min (max (* 1/3
;;                                                  (+ (+ (car cd) (car cd))
;;                                                     (cdr cd)))
;;                                               1)
;;                                          2)
;;                                     (min (max (* 1/3
;;                                                  (+ (+ (car cd) (car cd))
;;                                                     (cdr cd)))
;;                                               1)
;;                                          2))
;;                                  -2)
;;                               (* (min (max (* 1/3
;;                                               (+ (+ (car cd) (cdr cd))
;;                                                  (cdr cd)))
;;                                            1)
;;                                       2)
;;                                  (min (max (* 1/3
;;                                               (+ (+ (car cd) (cdr cd))
;;                                                  (cdr cd)))
;;                                            1)
;;                                       2)))
;;                            -2)))
;;                  (cons (car cd) (* 1/3 (+ (+ (car cd) (cdr cd)) (cdr cd))))
;;                  (cons
;;                    (* 1/3 (+ (+ (car cd) (car cd)) (cdr cd)))
;;                    (cdr cd))))))))

(define |TwoThirdExpBd| (lambda (x) (* 2 x)))

;; (time ((ev (term-to-expr (nt IVTInst-neterm))) 16))

;; 23585087634298163/16677181699666569
;; 7ms

(exact->inexact (/ 23585087634298163 16677181699666569))
;; 1.4142130282582281

(sqrt 2)
;; 1.4142135623730951

;; (time ((ev (term-to-expr (nt IVTInst-neterm))) 32))

;; 43703660048002085261730517567667/30903154382632612361920641803529
;; 10ms

(exact->inexact
 (/ 43703660048002085261730517567667 30903154382632612361920641803529))
;; 1.4142135623722374

(sqrt 2)
;; 1.4142135623730951

;; (time ((ev (term-to-expr (nt IVTInst-neterm))) 64))
;; 150064550394480063920178032994112167045534641638298508651753395/106111661199647248543687855752712667991103904330482569981872649
;; 17ms

(exact->inexact
 (/ 150064550394480063920178032994112167045534641638298508651753395
    106111661199647248543687855752712667991103904330482569981872649))
;; 1.4142135623730951

(sqrt 2)
;; 1.4142135623730951
