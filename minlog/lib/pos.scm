;; 2025-10-11.  pos.scm

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)
|#

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading pos.scm ...") (newline)

;; (remove-nat-tokens) removes all tokens added in nat.scm and from
;; DISPLAY-FUNCTIONS all items (nat proc).  The reason is that they
;; will be reintroduced here, with a different assigned procedure.

(remove-nat-tokens)
(add-display (py "nat") (make-display-creator1 "ListLength" "Lh" 'prefix-op))

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take pos as default.

(set! NAT-NUMBERS #f)

;; 1.  Positive numbers
;; ====================

;; We want to overload operators like +,*,/,<=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.
;; Moreover, a number should be displayed at the lowest possible level.
;; ppn (pretty print with names) displays the actually used functions.

(add-algs "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-var-name "p" "q" "r" (py "pos"))

(add-totality "pos")
(add-totalnc "pos")
(add-co "TotalPos")
(add-co "TotalPosNc")

(add-eqp "pos")
(add-co "EqPPos")
(add-eqpnc "pos")
(add-co "EqPPosNc")

;; PosTotalVar
(set-goal "all p TotalPos p")
(use "AllTotalIntro")
(assume "p^" "Tp")
(use "Tp")
;; Proof finished.
;; (cp)
(save "PosTotalVar")

;; Alternative proof:
;; (set-goal "all p TotalPos p")
;; (ind)
;; (use "TotalPosOne")
;; (assume "p" "Tp")
;; (use "TotalPosSZero")
;; (use "Tp")
;; (assume "p" "Tp")
;; (use "TotalPosSOne")
;; (use "Tp")

;; We collect properties of TotalPos and EqPPos, including the Nc, Co
;; and MR variants.  These are

;; PosEqToEqD
(set-goal "all p,q(p=q -> p eqd q)")
(ind) ;2-4
(cases) ;5-7
(assume "Useless")
(use "InitEqD")
;; 6
(assume "p" "1=SZero p")
(use "EfEqD")
(use "1=SZero p")
;; 7
(assume "p" "1=SOne p")
(use "EfEqD")
(use "1=SOne p")
;; 3
(assume "p" "IH1")
(cases) ;14-16
(assume "SZero p=1")
(use "EfEqD")
(use "SZero p=1")
;; 15
(assume "q" "SZero p=SZero q")
(assert "p eqd q")
 (use "IH1")
 (use "SZero p=SZero q")
(assume "p eqd q")
(elim "p eqd q")
(strip)
(use "InitEqD")
;; 18
(assume "q" "SZero p=SOne q")
(use "EfEqD")
(use "SZero p=SOne q")
;; 4
(assume "p" "IH1")
(cases) ;29-31
(assume "SOne p=1")
(use "EfEqD")
(use "SOne p=1")
;; 30
(assume "q" "SOne p=SZero q")
(use "EfEqD")
(use "SOne p=SZero q")
;; 31
(assume "q" "SOne p=SOne q")
(assert "p eqd q")
 (use "IH1")
 (use "SOne p=SOne q")
(assume "p eqd q")
(elim "p eqd q")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "PosEqToEqD")

;; PosIfTotal
(set-goal "all p^(TotalPos p^ ->
 all alpha^,(pos=>alpha)^1,(pos=>alpha)^2(
 Total alpha^ ->
 all p^1(TotalPos p^1 -> Total((pos=>alpha)^1 p^1)) ->
 all p^1(TotalPos p^1 -> Total((pos=>alpha)^2 p^1)) ->
 Total[if p^ alpha^ (pos=>alpha)^1 (pos=>alpha)^2]))")
(assume "p^" "Tp" "alpha^" "(pos=>alpha)^1" "(pos=>alpha)^2"
	"Talpha" "Tf1" "Tf2")
(elim "Tp")
(use "Talpha")
(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "Tf1")
(use "Tp1")
(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "Tf2")
(use "Tp1")
;; Proof finished.
;; (cp)
(save "PosIfTotal")

;; To prove extensionality of pconsts of level >=2 we will need
;; properties of EqPPos.  There are collected here.

;; EqPPosRefl
(set-goal "all p^(TotalPos p^ -> EqPPos p^ p^)")
(assume "p^" "Tp")
(elim "Tp")
(use "EqPPosOne")
(assume "p^1" "Tp1")
(use "EqPPosSZero")
(assume "p^1" "Tp1")
(use "EqPPosSOne")
;; Proof finished.
;; (cp)
(save "EqPPosRefl")

;; EqPPosToTotalLeft
(set-goal "all p^,q^(EqPPos p^ q^ -> TotalPos p^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "TotalPosOne")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSZero")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSOne")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPPosToTotalLeft")

;; EqPPosToTotalRight
(set-goal "all p^,q^(EqPPos p^ q^ -> TotalPos q^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "TotalPosOne")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSZero")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(use "TotalPosSOne")
(use "IH")
;; Proof finished.
;; (cp)
(save "EqPPosToTotalRight")

;; EqPPosToEqD
(set-goal "all p^,q^(EqPPos p^ q^ -> p^ eqd q^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(use "InitEqD")
;; 4
(assume "p^1" "q^1" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; 5
(assume "p^1" "q^1" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "EqPPosToEqD")

;; EqPPosSym
(set-goal "all p^,q^(EqPPos p^ q^ -> EqPPos q^ p^)")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
(use "EqPPosOne")
(assume "p^1" "q^1" "EqPp1q1" "EqPq1p1")
(use "EqPPosSZero")
(use "EqPq1p1")
(assume "p^1" "q^1" "EqPp1q1" "EqPq1p1")
(use "EqPPosSOne")
(use "EqPq1p1")
;; Proof finished.
;; (cp)
(save "EqPPosSym")

(add-var-name "f" (py "pos=>alpha=>alpha"))

;; PosRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec pos=>alpha)"))))
(assume "p^" "Tp" "alpha^" "Talpha" "f^1" "Tf1" "f^2" "Tf2")
(elim "Tp") 
;; 3-5
(ng #t)
(use "Talpha")
;; 4
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "Tf1")
(use "Tp1")
(use "IH")
;; 5
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "Tf2")
(use "Tp1")
(use "IH")
;; Proof finished.
;; (cp)
(save "PosRecTotal")

(remove-var-name "f")

;; make-numeric-term-wrt-pos produces a pos object for a positive
;; integer.

(define (make-numeric-term-wrt-pos n)
  (cond ((= n 1) (pt "One"))
	((even? n) (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "SZero"))
		    (make-numeric-term-wrt-pos (/ n 2))))
	((odd? n) (make-term-in-app-form
		   (make-term-in-const-form (constr-name-to-constr "SOne"))
		   (make-numeric-term-wrt-pos (/ (- n 1) 2))))
	(else
	 (myerror "make-numeric-term-wrt-pos" "positive integer expected" n))))

(define (make-numeric-term n)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat n)
      (make-numeric-term-wrt-pos n)))

;; (define (make-numeric-term n)
;;   (if (not (and (integer? n) (positive? n)))
;;       (myerror "make-numeric-term" "positive integer expected" n)
;;       (make-numeric-term-wrt-pos n)))
(define is-numeric-term? is-numeric-term-wrt-pos?)
(define numeric-term-to-number numeric-term-wrt-pos-to-number)

;; To use external code in a pconst, we provide tests for numeral
;; values and conversion operations from numerals values to numbers,
;; for pos and nat.

(define (pos-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "One" name)
	     (and (or (string=? "SZero" name) (string=? "SOne" name))
		  (pair? vals)
		  (pos-numeral-value? (car vals)))))))

(define (pos-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "One" name)
	1
	(let ((prev (pos-numeral-value-to-number (car vals))))
	  (if (string=? "SZero" name) (* 2 prev) (+ (* 2 prev) 1))))))

(define (nat-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "Zero" name)
	     (and (string=? "Succ" name)
		  (pair? vals)
		  (nat-numeral-value? (car vals)))))))

(define (nat-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "Zero" name)
	1
	(+ 1 (nat-numeral-value-to-number (car vals))))))

;; Instead of the converse use pt.

;; 2. Parsing and display for arithmetical operations
;; ==================================================

;; We have the subtype relation pos < nat.

(add-program-constant "PosToNat" (py "pos=>nat"))

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "PosToNat"))
         (make-term-in-var-form var)))))

;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))

(add-program-constant "PosS" (py "pos=>pos"))
(add-program-constant "PosPred" (py "pos=>pos"))
(add-program-constant "PosHalf" (py "pos=>pos"))

;; We define an overloaded addition.

(add-program-constant "PosPlus" (py "pos=>pos=>pos"))

;; We define a cut-off subtraction for pos (as we have it for nat).

(add-program-constant "PosMinus" (py "pos=>pos=>pos"))

;; We define an overloaded multiplication.

(add-program-constant "PosTimes" (py "pos=>pos=>pos"))

;; We define the exponential with values in pos and nat

(add-program-constant "PosExp" (py "pos=>nat=>pos"))
(add-program-constant "NatExp" (py "nat=>nat=>nat"))

;; We define the overloaded maximum function, written infix:

(add-program-constant "PosMax" (py "pos=>pos=>pos"))

;; We define the overloaded minimum function, written infix:

(add-program-constant "PosMin" (py "pos=>pos=>pos"))

;; We define an overloaded less-than relation.

(add-program-constant "PosLt" (py "pos=>pos=>boole"))

;; We define an overloaded less-than-or-equal relation.

(add-program-constant "PosLe" (py "pos=>pos=>boole"))

;; We define the logarithm os a positive number

(add-program-constant "PosLog" (py "pos=>nat"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;
;; must be transformed into
;;    f n | even n = ... TranslationPosHalfEven n ...
;;
;; etc.  Notice that we always know that n is an even number, so that
;; the remainder is zero, and similarly for minus and predecessor. Not
;; meant to be used directly by the user.

(add-program-constant "TranslationPosHalfEven" (py "pos=>pos"))
(add-program-constant "TranslationPosNegForInt" (py "pos=>pos"))
(add-program-constant "TranslationPosPredNonOne" (py "pos=>pos"))

;; We define the tokens that are used by the parser

(add-token "+" 'add-op (make-term-creator "+" "pos"))
(add-token-and-type-to-name "+" (py "pos") "PosPlus")
(add-token-and-type-to-name "+" (py "nat") "NatPlus")

(add-token "--" 'add-op (make-term-creator "--" "pos"))
(add-token-and-type-to-name "--" (py "pos") "PosMinus")
(add-token-and-type-to-name "--" (py "nat") "NatMinus")

(add-token "*" 'mul-op (make-term-creator "*" "pos"))
(add-token-and-type-to-name "*" (py "pos") "PosTimes")
(add-token-and-type-to-name "*" (py "nat") "NatTimes")

(add-token "**" 'exp-op (make-term-creator-exp "**"))

(add-token-and-types-to-name "**" (list (py "pos") (py "pos")) "PosExp")
(add-token-and-types-to-name "**" (list (py "pos") (py "nat")) "PosExp")

(add-token-and-types-to-name "**" (list (py "nat") (py "pos")) "NatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "nat")) "NatExp")

(add-token "max" 'mul-op (make-term-creator "max" "pos"))
(add-token-and-type-to-name "max" (py "pos") "PosMax")
(add-token-and-type-to-name "max" (py "nat") "NatMax")

(add-token "min" 'mul-op (make-term-creator "min" "pos"))
(add-token-and-type-to-name "min" (py "pos") "PosMin")
(add-token-and-type-to-name "min" (py "nat") "NatMin")

(add-token "<" 'rel-op (make-term-creator "<" "pos"))
(add-token-and-type-to-name "<" (py "pos") "PosLt")
(add-token-and-type-to-name "<" (py "nat") "NatLt")

(add-token "<=" 'rel-op (make-term-creator "<=" "pos"))
(add-token-and-type-to-name "<=" (py "pos") "PosLe")
(add-token-and-type-to-name "<=" (py "nat") "NatLe")

(add-token "||" 'rel-op (make-term-creator "||" "pos"))
(add-token-and-type-to-name "||" (py "pos") "PosDiv")
(add-token-and-type-to-name "||" (py "nat") "NatDiv")

(add-display (py "pos") (make-display-creator "PosPlus" "+" 'add-op))
(add-display (py "nat") (make-display-creator "NatPlus" "+" 'add-op))

(add-display (py "pos") (make-display-creator "PosMinus" "--" 'add-op))
(add-display (py "nat") (make-display-creator "NatMinus" "--" 'add-op))

(add-display (py "pos") (make-display-creator "PosTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator "NatTimes" "*" 'mul-op))

(add-display (py "pos") (make-display-creator "PosExp" "**" 'exp-op))
(add-display (py "nat") (make-display-creator "NatExp" "**" 'exp-op))

(add-display (py "pos") (make-display-creator "PosMax" "max" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMax" "max" 'mul-op))

(add-display (py "pos") (make-display-creator "PosMin" "min" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMin" "min" 'mul-op))

(add-display (py "boole") (make-display-creator "PosLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLt" "<" 'rel-op))

(add-display (py "boole") (make-display-creator "PosLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLe" "<=" 'rel-op))

(add-display (py "boole") (make-display-creator "PosDiv" "||" 'rel-op))
(add-display (py "boole") (make-display-creator "NatDiv" "||" 'rel-op))

;; 3. Arithmetic for positive numbers
;; ==================================

;; BooleEqTotal is proved in ets.scm.  NatEqTotal is proved in nat.scm

;; EfTotalPos
(set-goal "all p^(F -> TotalPos p^)")
(assume "p^" "Absurd")
(simp (pf "p^ eqd 1"))
(use "TotalVar")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "EfTotalPos")

;; PosEqTotal
(set-goal "all p^(
 TotalPos p^ -> all q^(TotalPos q^ -> TotalBoole(p^ =q^)))")
(assume "p^" "Tp")
(elim "Tp")
(assume "q^" "Tq")
(elim "Tq")
(use "TotalBooleTrue")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cp)
(save "PosEqTotal")

;; Rules for PosS

(add-computation-rules
 "PosS One" "SZero One"
 "PosS(SZero p)" "SOne p"
 "PosS(SOne p)" "SZero(PosS p)")

;; PosSTotal
(set-totality-goal "PosS")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosS 1)
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")
;; ?_4:all p^(
;;      TotalPos p^ -> TotalPos(PosS p^) -> TotalPos(PosS(SZero p^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSOne")
(use "Tq")
;; ?_5:all p^(
;;      TotalPos p^ -> TotalPos(PosS p^) -> TotalPos(PosS(SOne p^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSZero")
(use "TSq")
;; Proof finished.
;; (cp)
(save-totality)

;; PosSEqP
(set-goal "all p^,q^(EqPPos p^ q^ -> EqPPos(PosS p^)(PosS q^))")
(assume "p^" "q^" "EqPpq")
(simp "<-" (pf "p^ eqd q^"))
(use "EqPPosRefl")
(use "PosSTotal")
(use "EqPPosToTotalLeft" (pt "q^"))
(use "EqPpq")
;; 4
(use "EqPPosToEqD")
(use "EqPpq")
;; Proof finished.
;; (cp)
(save "PosSEqP")

;; Rules for PosPred

(add-computation-rules
 "PosPred One" "One"
 "PosPred(SZero One)" "One"
 "PosPred(SZero(SZero p))" "SOne(PosPred(SZero p))"
 "PosPred(SZero(SOne p))" "SOne(SZero p)"
 "PosPred(SOne p)" "SZero p")

;; PosPredTotal
(set-totality-goal "PosPred")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosPred 1)
(ng #t)
(use "TotalPosOne")
;; all p^(TotalPos p^ -> TotalPos(PosPred p^) -> TotalPos(PosPred(SZero p^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(elim "Tq")
;; ?_9:TotalPos(PosPred 2)
(ng #t)
(use "TotalPosOne")
;; ?_10:all p^(
;;       TotalPos p^ -> 
;;       TotalPos(PosPred(SZero p^)) -> TotalPos(PosPred(SZero(SZero p^))))
(assume "q^0" "Tq0" "TPSZq0")
(ng #t)
(use "TotalPosSOne")
(use "TPSZq0")
;; ?_11:all p^(
;;       TotalPos p^ -> 
;;       TotalPos(PosPred(SZero p^)) -> TotalPos(PosPred(SZero(SOne p^))))
(assume "q^1" "Tq1" "TPSZq1")
(ng #t)
(use "TotalPosSOne")
(use "TotalPosSZero")
(use "Tq1")
;; all p^(TotalPos p^ -> TotalPos(PosPred p^) -> TotalPos(PosPred(SOne p^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(use "TotalPosSZero")
(use "Tq")
;; Proof finished.
;; (cp)
(save-totality)

;; PosPredEqP
(set-goal "all p^,q^(EqPPos p^ q^ -> EqPPos(PosPred p^)(PosPred q^))")
(assume "p^" "q^" "EqPpq")
(simp "<-" (pf "p^ eqd q^"))
(use "EqPPosRefl")
(use "PosPredTotal")
(use "EqPPosToTotalLeft" (pt "q^"))
(use "EqPpq")
;; 4
(use "EqPPosToEqD")
(use "EqPpq")
;; Proof finished.
;; (cp)
(save "PosPredEqP")

;; Rules for PosHalf

(add-computation-rules
 "PosHalf One" "One"
 "PosHalf(SZero p)" "p"
 "PosHalf(SOne p)" "p")

;; PosHalfTotal
(set-totality-goal "PosHalf")
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosHalf 1)
(ng #t)
(use "TotalPosOne")
;; ?_4:all p^(
;;      TotalPos p^ ->
;;      TotalPos(PosHalf p^) -> TotalPos(PosHalf(SZero p^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; ?_5:all p^(
;;      TotalPos p^ ->
;;      TotalPos(PosHalf p^) -> TotalPos(PosHalf(SOne p^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; Proof finished.
;; (cp)
(save-totality)

;; Rules for PosToNat

(add-computation-rules
 "PosToNat One" "Succ Zero"
 "PosToNat(SZero p)" "NatDouble(PosToNat p)"
 "PosToNat(SOne p)" "Succ(PosToNat(SZero p))")

;; PosToNatTotal
(set-totality-goal "PosToNat")
(assume "p^" "Tp")
(elim "Tp") ;3-5
(use "TotalNatSucc")
(use "TotalNatZero")
;; 4
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "NatDoubleTotal")
(use "IH")
;; 5
(assume "p^1" "Tp1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatDoubleTotal")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

(replace-item-in-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst "PosToNat"))
	 (make-term-in-var-form var)))))

(add-program-constant "NatToPos" (py "nat=>pos"))
(add-computation-rules
 "NatToPos Zero" "1"
 "NatToPos(Succ Zero)" "1"
 "NatToPos(Succ(Succ n))"
 "[if (NatEven n)
      (SZero(NatToPos(Succ(NatHalf n))))
      (SOne(NatToPos(Succ(NatHalf n))))]")

;; Test
;; (pp (nt (pt "NatToPos 1")))  
;; (pp (nt (pt "NatToPos 2")))  
;; (pp (nt (pt "NatToPos 3")))  
;; (pp (nt (pt "NatToPos 4")))
;; (pp (nt (pt "NatToPos 5")))
;; (pp (nt (pt "NatToPos 6")))
;; (pp (nt (pt "NatToPos 7")))
;; (pp (nt (pt "NatToPos 8")))
;; (pp (nt (pt "NatToPos 9")))

;; We prove that NatToPos is total.

;; 2025-05-17

;; (pp "NatHalfLt")
;; all n(Zero<n -> NatHalf n<n)

;; (pp "CVIndPvar")
;; (F -> all n^ (Pvar nat)n^) -> 
;; all n(all m(m<n -> (Pvar nat)m) -> (Pvar nat)n) -> all n (Pvar nat)n

;; NatToPosStep
(set-goal "all n(Zero<n -> all m(m<=Succ n -> TotalPos(NatToPos m)) -> 
 TotalPos(NatToPos(Succ(Succ n))))")
(assume "n" "0<n" "Prog")
(ng #t)
(cases (pt "NatEven n"))
;; 4,5
(assume "En")
(ng #t)
(use "TotalPosSZero")
(use "Prog")
(ng #t)
(use "NatHalfLe")
;; 5
(assume "On")
(ng #t)
(use "TotalPosSOne")
(use "Prog")
(ng #t)
(use "NatHalfLe")
;; Proof finished.
;; (cp)
(save "NatToPosStep")

(set-totality-goal "NatToPos")
(fold-alltotal)
(use "CVIndPvar")
;; 3,4
(assume "Absurd")
(assume "n")
(use "EfTotalPos")
(use "Absurd")
;; 4
(cases)
;; 8,9
(assume "Useless")
(use "TotalVar")
;; 9
(cases)
;; 11,12
(assume "Useless")
(use "TotalVar")
;; 12
(cases)
;; 14,15
(assume "Useless")
(use "TotalVar")
;; 15
(assume "n" "Prog")
(use "NatToPosStep")
(use "Truth")
(assume "m" "mBd")
(use "Prog")
(use "NatLeToLtSucc")
(use "mBd")
;; Proof finished.
;; (cp)
(save-totality)

;; NatToPosTotalNatNc
(set-goal "all n(TotalNatNc n -> TotalPosNc(NatToPos n))")
(assume "n" "Tn")
(use "CVIndPvarNc")
;; 3,4
(assume "Absurd" "n0")
(use "EfTotalPos")
(use "Absurd")
;; 4
(cases)
;; 8,9
(assume "Useless")
(use "TotalVar")
;; 9
(cases)
;; 10,11
(assume "Useless")
(use "TotalVar")
;; 11
(cases)
;; 13,14
(assume "Useless")
(use "TotalVar")
;; 14
(assume "n0" "Prog")
(use "NatToPosStep")
(use "Truth")
(assume "n1" "n1Bd")
(use "Prog")
(use "NatLeToLtSucc")
(use "n1Bd")
;; Proof finished.
;; (cp)
(save "NatToPosTotalNatNc")

;; We now aim at proving that NatToPos and PosToNat are inverse to each other.

;; (display-pconst "NatToPos" "PosToNat")

;; NatToPos
;;   comprules
;; 0	NatToPos Zero	1
;; 1	NatToPos(Succ Zero)	1
;; 2	NatToPos(Succ(Succ n))
;; 	[if (NatEven n)
;;  (SZero(NatToPos(Succ(NatHalf n))))
;;  (SOne(NatToPos(Succ(NatHalf n))))]
;; PosToNat
;;   comprules
;; 0	PosToNat 1	Succ Zero
;; 1	PosToNat(SZero p)	NatDouble(PosToNat p)
;; 2	PosToNat(SOne p)	Succ(PosToNat(SZero p))

;; NatToPosDouble
(set-goal "all n(Zero<n ->  NatToPos(NatDouble n)=SZero(NatToPos n))")
(cases)
;; 2,3
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "Useless")
(ng #t)
(simp "NatHalfDouble")
(simp "NatEvenDouble")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatToPosDouble")

;; NatToPosSuccDouble
(set-goal "all n(Zero<n ->  NatToPos(Succ(NatDouble n))=SOne(NatToPos n))")
(cases)
;; 2,3
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "Useless")
(ng #t)
(simp "NatHalfSuccDouble")
(simp (pf "NatEven(Succ(NatDouble n)) -> F"))
(use "Truth")
(use "NatEvenToOddSucc")
(use "NatEvenDouble")
;; Proof finished.
;; (cp)
(save "NatToPosSuccDouble")

;; NatLtZeroPos
(set-goal "all p Zero<p")
(ind)
(use "Truth")
(ng #t)
(assume "p" "0<p")
(use "NatLt0Double")
(use "0<p")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroPos")
(save "NatLt0Pos")

;; NatToPosToNatId
(set-goal "all p NatToPos(PosToNat p)=p")
(ind)
;; 2-4
(use "Truth")
;; 3
(ng #t)
(assume "p" "IH")
(simp "NatToPosDouble")
(use "IH")
(use "NatLtZeroPos")
;; 4
(ng #t)
(assume "p" "IH")
(simp "NatToPosSuccDouble")
(use "IH")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "NatToPosToNatId")

;; PosToNatToPosIdSucc
(set-goal "all n PosToNat(NatToPos(Succ n))=Succ n")
(use "CVInd")
(ng #t)
(cases)
;; 4,5
(assume "Useless")
(use "Truth")
;; 5
(assume "n" "Prog")
(ng #t)
(cases (pt "NatEven n"))
;; 9,10
(assume "En")
(ng #t)
(simp "Prog")
;; ?^13:NatDouble(Succ(NatHalf n))=Succ(Succ n)
(use "NatDoubleSuccHalfEven")
(use "En")
(use "NatLeToLtSucc")
(use "NatHalfLe")
;; 10
(assume "On")
(ng #t)
(simp "Prog")
(ng #t)
(use "NatDoubleHalfOdd")
(use "On")
(use "NatLeToLtSucc")
(use "NatHalfLe")
;; Proof finished.
;; (cp)
(save "PosToNatToPosIdSucc")

;; PosToNatToPosId
(set-goal "all n(Zero<n -> PosToNat(NatToPos n)=n)")
(cases)
;; 2,3
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "n" "Useless")
(use "PosToNatToPosIdSucc")
;; Proof finished.
;; (cp)
(save "PosToNatToPosId")

;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; NatPos
(set-goal "all n exl p p=NatToPos n")
(assume "n")
(intro 0 (pt "NatToPos n"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPos")

(animate "NatPos")

;; NatPosExFree
(set-goal "all n cNatPos n=NatToPos n")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatPosExFree")

(deanimate "NatPos")

(set-totality-goal "cNatPos")
(fold-alltotal)
(assume "n")
(use "PosTotalVar")
;; Proof finished.
;; (cp)
(save "cNatPosTotal")

;; Rules for PosPlus

(add-computation-rules
 "p+One" "PosS p"
 "One+SZero p" "SOne p"
 "SZero p+SZero q" "SZero(p+q)"
 "SOne p+SZero q" "SOne(p+q)"
 "One+SOne p" "SZero(PosS p)"
 "SZero p+SOne q" "SOne(p+q)"
 "SOne p+SOne q" "SZero(PosS(p+q))")

;; PosPlusTotal
(set-totality-goal "PosPlus")
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:all p^(TotalPos p^ -> TotalPos(1+p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq1")
;; ?_4:all p^(
;;      TotalPos p^ -> 
;;      all p^0(TotalPos p^0 -> TotalPos(p^ +p^0)) -> 
;;      all p^0(TotalPos p^0 -> TotalPos(SZero p^ +p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")
;; ?_5:all p^(
;;      TotalPos p^ -> 
;;      all p^0(TotalPos p^0 -> TotalPos(p^ +p^0)) -> 
;;      all p^0(TotalPos p^0 -> TotalPos(SOne p^ +p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "IHq")
(use "Tq2")
;; Proof finished.
;; (cp)
(save-totality)

;; PosPlusEqP
(set-goal "all p^1,q^1(EqPPos p^1 q^1 -> all p^2,q^2(EqPPos p^2 q^2 ->
 EqPPos(p^1+p^2)(q^1+q^2)))")
(assume "p^1" "q^1" "EqPp1q1" "p^2" "q^2" "EqPp2q2")
(simp "<-" (pf "p^1 eqd q^1"))
(simp "<-" (pf "p^2 eqd q^2"))
(use "EqPPosRefl")
(use "PosPlusTotal")
(use "EqPPosToTotalLeft" (pt "q^1"))
(use "EqPp1q1")
(use "EqPPosToTotalLeft" (pt "q^2"))
(use "EqPp2q2")
;; 6
(use "EqPPosToEqD")
(use "EqPp2q2")
;; 4
(use "EqPPosToEqD")
(use "EqPp1q1")
;; Proof finished.
;; (cp)
(save "PosPlusEqP")

;; SZeroPosPlus
(set-goal "all p SZero p=p+p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(simp "<-" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "SZeroPosPlus")

;; We derive some rewrite rules.  To ensure termination, we (1) decrease
;; the sum of the lengths of summands, where the rhs counts more than
;; the lhs.

(set-goal "all p PosPred(PosS p)=p")
(ind) ;2-4
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH")
(ng #t)
(use "Truth")
;; 4
(cases) ;8-10
(ng #t)
(strip)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "p" "Hyp")
(use "Hyp")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosPred(PosS p)" "p")

(set-goal "all p PosPred(SZero(PosS p))=SOne p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosPred(SZero(PosS p))" "SOne p")

(set-goal "all p PosS(PosPred(SZero p))=SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS(PosPred(SZero p))" "SZero p")

(set-goal "all p One+p=PosS p")
(cases)
(auto)
;; Proof finished
;; (cp)
(add-rewrite-rule "One+p" "PosS p")

(set-goal "all p,q PosS p+q=PosS(p+q)")
(ind)
  (ind)
  (auto)
(assume "pos" "IHzero")
(ind)
  (auto)
(assume "pos" "IHone")
(ind)
(auto)
;; Proof finished
;; (cp)
(add-rewrite-rule "PosS p+q" "PosS(p+q)")

(set-goal "all p,q p+PosS q=PosS(p+q)")
(ind)
  (cases)
(auto)
(assume "p" "IH1")
(cases)
  (auto)
(assume "p" "IH2")
(cases)
(auto)
;; Proof finished
;; (cp)
(add-rewrite-rule "p+PosS q" "PosS(p+q)")

;; PosEqSym
(set-goal "all p,q(p=q -> q=p)")
(ind)
(cases)
(auto)
(assume "p" 1)
(cases)
(auto)
(assume "p" 1)
(cases)
(auto)
;; Proof finished.
;; (cp)
(save "PosEqSym")

;; PosEqTrans
(set-goal "all p,q,r(p=q -> q=r -> p=r)")
(assume "p" "q" "r" "=Hyp")
(simp "<-" "=Hyp")
(assume "p=r")
(use "p=r")
;; Proof finished.
;; (cp)
(save "PosEqTrans")

;; PosToNatInj
(set-goal "all p,q(PosToNat p=PosToNat q -> p=q)")
(assume "p" "q" "EqHyp")
(assert "NatToPos(PosToNat p)=NatToPos(PosToNat q)")
 (simp "EqHyp")
 (use "Truth")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "p=q")
(use "p=q")
;; Proof finished.
;; (cp)
(save "PosToNatInj")

;; NatLtSuccZeroEven
(set-goal "all n(Zero<n -> NatEven n -> Succ Zero<n)")
(cases)
;; 2,3
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(cases)
;; 5,6
(assume "Useless" "Absurd")
(use "Absurd")
;; 6
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtSuccZeroEven")

;; NatLtSuccZeroOdd
(set-goal "all n((NatEven n -> F) -> (n=Succ Zero -> F) -> Succ Zero<n)")
(cases)
;; 2,3
(assume "Absurd" "Useless")
(use "Absurd")
(use "Truth")
;; 3
(cases)
;; 6,7
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
;; 7
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtSuccZeroOdd")

;; NatToPosEqSZeroNatToPosHalf
(set-goal "all n(Succ Zero<n -> NatEven n ->
 NatToPos n=SZero(NatToPos(NatHalf n)))")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n")
(ng #t)
(assume "Useless" "En")
(simp "En")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatToPosEqSZeroNatToPosHalf")

(pp "NatToPos2CompRule")
;; all n^ 
;;  NatToPos(Succ(Succ n^))eqd
;;  [if (NatEven n^)
;;    (SZero(NatToPos(Succ(NatHalf n^))))
;;    (SOne(NatToPos(Succ(NatHalf n^))))]

;; NatToPosEqSOneNatToPosHalf
(set-goal "all n(Succ Zero<n -> (NatEven n -> F) -> 
                 NatToPos n=SOne(NatToPos(NatHalf n)))")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 3
(cases)
;; 6,7
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 7
(ng #t)
(assume "n" "Useless" "On")
(simp "On")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatToPosEqSOneNatToPosHalf")

(pp "NatToPos2CompRule")

;; all n^ 
;;  NatToPos(Succ(Succ n^))eqd
;;  [if (NatEven n^)
;;    (SZero(NatToPos(Succ(NatHalf n^))))
;;    (SOne(NatToPos(Succ(NatHalf n^))))]

(display-pconst "PosS")
;; 0	PosS 1	2
;; 1	PosS(SZero p)	SOne p
;; 2	PosS(SOne p)	SZero(PosS p)

;; SuccPosS
(set-goal "all n(Zero<n -> NatToPos(Succ n)=PosS(NatToPos n))")
(assert "all n(Zero<n -> Succ n=PosToNat(PosS(NatToPos n)))")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog" "0<n")
(cases (pt "NatEven n"))
;;10,11
(assume "En")
(simp "NatToPosEqSZeroNatToPosHalf")
(simp "PosS1CompRule")
(simp "PosToNat2CompRule")
(simp "PosToNat1CompRule")
(simp "PosToNatToPosId")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En")
(use "NatLtZeroHalfEven")
(use "0<n")
(use "En")
(use "En")
(use "NatLtSuccZeroEven")
(use "0<n")
(use "En")
;; 11
(assume "On")
(cases (pt "n=Succ Zero"))
;; 28,29
(assume "n=1")
(simp "n=1")
;; simp normalizes the goal, which we do not want.  Why?  Ok if order
;; in simp-with-intern is changed: consider normalized items last.
(ng #t)
(use "Truth")
;; 29
(assume "n=/=1")
(simp "NatToPosEqSOneNatToPosHalf")
(simp "PosS2CompRule")
(simp "PosToNat1CompRule")
(simp "<-" "Prog")
(simp "NatDouble1CompRule")
(ng #t)
(simp "NatDoubleHalfOdd")
(use "Truth")
(use "On")
(use "NatLtZeroHalfFinally")
(use "0<n")
(use "n=/=1")
(use "NatHalfLt")
(use "0<n")
(use "On")
;; ?^35:Succ Zero<n
(use "NatLtSuccZeroOdd")
(use "On")
(use "n=/=1")
;; Assertion proved
(assume "SuccPosSAux" "n" "0<n")
(simp "SuccPosSAux")
(simp "NatToPosToNatId")
(use "Truth")
(use "0<n")
;; Proof finished.
;; (cp)
(save "SuccPosS")

;; PosSSucc
(set-goal "all p PosToNat(PosS p)=Succ(PosToNat p)")
(assume "p")
(assert "PosToNat(PosS p)=PosToNat(PosS(NatToPos(PosToNat p)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "SuccPosS")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosSSucc")

;; We prove that PosToNat is an isomorphism w.r.t. +

;; PosToNatPlus
(set-goal "all p,q PosToNat(p+q)=PosToNat p+PosToNat q")
(ind) 
;; 2-4
(assume "q")
(ng #t)
(use "PosSSucc")
;; 3
(assume "p" "IH")
(cases) ;8-10
(ng #t)
(use "Truth")
;; 9
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 10
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 4
(assume "p" "IH")
(cases) ;21-23
(ng #t)
(simp "PosSSucc")
(ng #t)
(use "Truth")
;; 22
(assume "q")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; 23
(assume "q")
(ng #t)
(simp "PosSSucc")
(ng #t)
(simp "NatPlusDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosToNatPlus")

;; NatToPosPlus
(set-goal "all n,m(Zero<n -> Zero<m -> NatToPos(n+m)=NatToPos n+NatToPos m)")
(assume "n" "m" "0<n" "0<m")
(assert "n+m=PosToNat(NatToPos n)+PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatPlus")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatToPosPlus")

;; PosPlusComm
(set-goal "all p,q p+q=q+p")
(assume "p" "q")
(assert "p+q=NatToPos(PosToNat(p+q))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "q+p=NatToPos(PosToNat(q+p))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(p+q)=PosToNat p+PosToNat q")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatPlusComm")
(assert "PosToNat(q+p)=PosToNat q+PosToNat p")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosPlusComm")

;; NatPlusAssoc
(set-goal "all p,q,r p+(q+r)=p+q+r")
(assume "p" "q" "r")
(assert "p+(q+r)=NatToPos(PosToNat(p+(q+r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(p+(q+r))=PosToNat(p)+PosToNat(q+r)")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(q+r)=PosToNat q+PosToNat r")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat p+(NatPlus(PosToNat q)(PosToNat r))=
         NatPlus(PosToNat p+PosToNat q)(PosToNat r)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(use "NatToPosToNatId")
;; Proof finished.
;; (cp)
(save "PosPlusAssoc")
(add-rewrite-rule "p+(q+r)" "p+q+r")

;; To prove PosPlusCancelL we again transfer the problem to nat via
;; PosToNatInj and PosToNatPlus.

;; PosPlusCancelL
(set-goal "all p,q,r(p+q=p+r -> q=r)")
(assume "p" "q" "r" "EqHyp")
(use "PosToNatInj")
(use "NatPlusCancelL" (pt "PosToNat p"))
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(simp "EqHyp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosPlusCancelL")

;; PosPlusCancelR
(set-goal "all p,q,r(p+q=r+q -> p=r)")
(assume "p" "q" "r" "EqHyp")
(use "PosToNatInj")
(use "NatPlusCancelR" (pt "PosToNat q"))
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(simp "EqHyp")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosPlusCancelR")

;; We postpone the treatment (as rewrite rules) of PosLePlusCancelL
;; PosLePlusCancelR PosLtPlusCancelL PosLtPlusCancelR
;; PosLeTimesCancelL PosLeTimesCancelR PosLtTimesCancelL
;; PosLtTimesCancelR until after PosLe and PosLt.

;; The following (former) rules are not used any more, because they
;; increase the number of +'s.

;; (add-rewrite-rule "p+SZero q" "p+q+q")
;; (add-rewrite-rule "p+SOne q" "p+q+q+1")
;; (add-rewrite-rule "SZero p+q" "p+p+q") ;no term. for 2+m
;; (add-rewrite-rule "SOne p+q" "p+p+1+q"

;; (display-pconst "PosPlus")

;; The rules for PosMinus will give correct results for p--q (only) if
;; q<p.  To be able to formulate appropriate assumptions we postpone
;; the treatment of PosMinus until after PosLe and PosLt.

;; Rules for PosTimes:

(add-computation-rules
 "p*One" "p"
 "p*SZero q" "SZero(p*q)"
 "p*SOne q" "SZero(p*q)+p")

;; PosTimesTotal
(set-totality-goal "PosTimes")
(assume "p^" "Tp" "q^" "Tq")
(elim "Tq")

(ng #t)
(use "Tp")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "PosPlusTotal")
(use "TotalPosSZero")
(use "IHq1")
(use "Tp")
;; Proof finished.
;; (cp)
(save-totality)

;; PosTimesEqP
(set-goal "all p^1,q^1(EqPPos p^1 q^1 -> all p^2,q^2(EqPPos p^2 q^2 ->
 EqPPos(p^1*p^2)(q^1*q^2)))")
(assume "p^1" "q^1" "EqPp1q1" "p^2" "q^2" "EqPp2q2")
(simp "<-" (pf "p^1 eqd q^1"))
(simp "<-" (pf "p^2 eqd q^2"))
(use "EqPPosRefl")
(use "PosTimesTotal")
(use "EqPPosToTotalLeft" (pt "q^1"))
(use "EqPp1q1")
(use "EqPPosToTotalLeft" (pt "q^2"))
(use "EqPp2q2")
;; 6
(use "EqPPosToEqD")
(use "EqPp2q2")
;; 4
(use "EqPPosToEqD")
(use "EqPp1q1")
;; Proof finished.
;; (cp)
(save "PosTimesEqP")

(set-goal "all p One*p=p")
(ind)
(auto)
;; Proof finished.
;; (cp)
(add-rewrite-rule "One*p" "p")

(set-goal "all p,q SZero p*q=SZero(p*q)")
(assume "p")
(ind)
(auto)
(assume "q" "IHone")
(ng)
(simp "IHone")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "SZero p*q" "SZero(p*q)")

;; We prove that NatToPos is an isomorphism w.r.t. *

;; PosToNatTimes
(set-goal "all p,q PosToNat(p*q)=PosToNat p*PosToNat q")
(assume "p")
(ind) ;3-5
(ng #t)
(use "Truth")
;; 4
(assume "q" "IH")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; 5
(assume "q" "IH")
(ng #t)
(simp "PosToNatPlus")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosToNatTimes")

;; NatToPosTimes
(set-goal "all n,m(Zero<n -> Zero<m -> NatToPos(n*m)=NatToPos n*NatToPos m)")
(assume "n" "m" "0<n" "0<m")
(assert "n*m=PosToNat(NatToPos n)*PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatTimes")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatToPosTimes")

;; PosTimesPlusDistr
(set-goal "all p,q,r p*(q+r)=p*q+p*r")
(assume "p" "q" "r")
(assert "p*(q+r)=NatToPos(PosToNat(p*(q+r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "p*q+p*r=NatToPos(PosToNat(p*q+p*r))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(simp "PosToNatTimes")
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(simp "NatTimesPlusDistr")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesPlusDistr")
(add-rewrite-rule "p*(q+r)" "p*q+p*r")

;; PosTimesComm
(set-goal "all p,q p*q=q*p")
(assume "p" "q")
(assert "p*q=NatToPos(PosToNat(p*q))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "q*p=NatToPos(PosToNat(q*p))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(p*q)=PosToNat p*PosToNat q")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatTimesComm")
(assert "PosToNat(q*p)=PosToNat q*PosToNat p")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesComm")

;; PosTimesPlusDistrLeft
(set-goal "all p,q,r (p+q)*r=(p*r)+(q*r)")
(assume "p" "q" "r")
(simp-with "PosTimesComm" (pt "p+q") (pt "r"))
(ng)
(simp-with "PosTimesComm" (pt "p") (pt "r"))
(simp-with "PosTimesComm" (pt "q") (pt "r"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesPlusDistrLeft")
(add-rewrite-rule "(p+q)*r" "p*r+q*r")

;; PosTimesAssoc
(set-goal "all p,q,r p*(q*r)=p*q*r")
(assume "p" "q" "r")
(assert "p*(q*r)=NatToPos(PosToNat(p*(q*r)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(p*(q*r))=PosToNat(p)*PosToNat(q*r)")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(q*r)=PosToNat q*PosToNat r")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat p*(NatTimes(PosToNat q)(PosToNat r))=
         NatTimes(PosToNat p*PosToNat q)(PosToNat r)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(use "NatToPosToNatId")
;; Proof finished.
;; (cp)
(save "PosTimesAssoc")
(add-rewrite-rule "p*(q*r)" "p*q*r")

;; PosTimesSOne
(set-goal "all p,q SOne p*q=SZero(p*q)+q")
(assume "p")
(ind)
(ng #t)
(use "Truth")
;; 4
(assume "q" "IH")
(ng #t)
(use "IH")
;; 5
(assume "q" "IH")
(ng #t)
(simp "IH")
(assert "SZero(p*q)+q+p=SZero(p*q)+(q+p)")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "SZero(p*q)+p+q=SZero(p*q)+(p+q)")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "p+q=q+p")
 (use "PosPlusComm")
(assume "p+q=q+p")
(simp "p+q=q+p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesSOne")
(add-rewrite-rule "SOne p*q" "SZero(p*q)+q")

;; Rules for PosExp : pos=>nat=>pos

(add-computation-rules
 "p**Zero" "One"
 "p**Succ m" "p**m*p")

;; PosExpTotal
(set-totality-goal "PosExp")
(assume "p^" "Tp" "n^" "Tn")
(elim "Tn")

(ng #t)
(use "TotalPosOne")

(assume "n^1" "Tn1" "IHn1")
(ng #t)
(use "PosTimesTotal")
(use "IHn1")
(use "Tp")
;; Proof finished.
;; (cp)
(save-totality)

;; PosExpOne
(set-goal "all n 1**n=1")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosExpOne")
(add-rewrite-rules "1**n" "1")

;; Rules for PosLt, PosLe

(add-computation-rules
 "p<One" "False"
 "One<SZero p" "True"
 "One<SOne p" "True"
 "SZero p<SZero q" "p<q"
 "SZero p<SOne q" "p<=q"
 "SOne p<SZero q" "p<q"
 "SOne p<SOne q" "p<q")

(add-computation-rules
 "One<=p" "True"
 "SZero p<=One" "False"
 "SOne p<=One" "False"
 "SZero p<=SZero q" "p<=q"
 "SZero p<=SOne q" "p<=q"
 "SOne p<=SZero q" "p<q"
 "SOne p<=SOne q" "p<=q")

;; PosLtPosLeTotalLemma
(set-goal "all p^(TotalPos p^ -> all q^(TotalPos q^ ->
 TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)))")
(assume "p^" "Tp")
(elim "Tp")

(assume "q^" "Tq")
(split)
(elim "Tq")
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(ng #t)
(use "TotalBooleTrue")
;; ?_4:all p^(
;;      TotalPos p^ -> 
;;      all q^(TotalPos q^ -> TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)) -> 
;;      all q^(
;;      TotalPos q^ -> TotalBoole(SZero p^ <q^) andd TotalBoole(SZero p^ <=q^)))
(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
;; ?_5:all p^(
;;      TotalPos p^ -> 
;;      all q^(TotalPos q^ -> TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)) -> 
;;      all q^(
;;       TotalPos q^ -> TotalBoole(SOne p^ <q^) andd TotalBoole(SOne p^ <=q^)))
(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cp)
(save "PosLtPosLeTotalLemma")

;; PosLtTotal
(set-totality-goal "PosLt")
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")
;; Proof finished.
;; (cp)
(save-totality)

;; PosLeTotal
(set-totality-goal "PosLe")
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
;; Proof finished.
;; (cp)
(save "PosLeTotal")

;; PosLtToLe
(set-goal "all p,q(p<q -> p<=q)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "p" "IH")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "q")
(ng #t)
(use "IH")
(assume "q")
(ng #t)
(assume "p<=p")
(use "p<=p")
;; 4
(assume "p" "IH")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "q")
(ng #t)
(assume "p<p")
(use "p<p")
(assume "q")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLtToLe")

;; PosLTrans
(set-goal "all p,q,r((p<q -> q<=r -> p<r)
                     andnc (p<=q -> q<r -> p<r)
                     andnc (p<=q -> q<=r -> p<=r))")
(ind) ;2-4
(cases) ;5-7
(assume "r")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Useless" "1<r")
(use "1<r")
(strip)
(use "Truth")
;; 6
(assume "q")
(ng #t)
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(split)
(ng #t)
(strip)
(use "Truth")
(split)
(ng #t)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 7
(assume "q")
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "r")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases) ;79-81
(assume "q")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 80
(assume "q")
(cases) ;97-99
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 98
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; 99
(assume "r")
(ng #t)
(split)
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
(split)
(use "IH1")
(use "IH1")
;; 83
(assume "q")
(cases) ;123-25
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 124
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'right 'left "p1<=p2" "p2<p3")
;; 125
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'right 'left "p1<=p2" "p2<p3")
(use "IH1")
;; 4
(assume "p" "IH1")
(cases) ;151-153
(assume "q")
(ng #t)
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(split)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
;; 152
(assume "q")
(cases) ;167-169
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 168
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(use "IH1")
;; 169
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "p2<=p3")
;; 153
(assume "q")
(cases) ;196-98
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 197
(assume "r")
(ng #t)
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "q") (pt "r") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(split)
(use "IH1")
(use "IH1")
;; 198
(assume "r")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; Proof finished.
;; (cp)
(save "PosLTrans")

;; Using this and PosLtToLe we can easily derive PosLeLtTrans
;; PosLtLeTrans PosLeTrans PosLtTrans.

;; PosLtLeTrans
(set-goal "all p,q,r(p<q -> q<=r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cp)
(save "PosLtLeTrans")

;; PosLeLtTrans
(set-goal "all p,q,r(p<=q -> q<r -> p<r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cp)
(save "PosLeLtTrans")

;; PosLeTrans
(set-goal "all p,q,r(p<=q -> q<=r -> p<=r)")
(assume "p" "q" "r")
(use "PosLTrans")
;; Proof finished.
;; (cp)
(save "PosLeTrans")

;; PosLtTrans
(set-goal "all p,q,r(p<q -> q<r -> p<r)")
(assume "p" "q" "r" "p1<p2")
(use "PosLeLtTrans")
(use "PosLtToLe")
(use "p1<p2")
;; Proof finished.
;; (cp)
(save "PosLtTrans")

;; We add some useful rewrite rules.

;; PosLeToEq
(set-goal "all p (p<=1)=(p=1)")
(cases)
(use "Truth")
(assume "p")
(use "Truth")
(assume "p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLeToEq")
(add-rewrite-rule "p<=1" "p=1")

(set-goal "all p (p<p)=False")
(ind)
(use "Truth")
(assume "p" "IH")
(use "IH")
(assume "p" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<p" "False")

(set-goal "all p p<=p")
(ind)
(use "Truth")
(assume "p" "IH")
(use "IH")
(assume "p" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=p" "True")

(set-goal "all p p<PosS p")
(ind)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<PosS p" "True")

(set-goal "all p p<=PosS p")
(cases)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=PosS p" "True")

(set-goal "all p (PosS p<=p)=False")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p<=p" "False")

(set-goal "all p (PosS p<p)=False")
(cases)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p<p" "False")

(set-goal "all p,q p<=p+q")
(ind)
(cases)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "IH1")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "PosLeLtTrans" (pt "p+q"))
(use "IH1")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=p+q" "True")

(set-goal "all p,q p<p+q")
(ind)
(cases)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "Truth")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "PosLtTrans" (pt "p+q"))
(use "IH1")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<p+q" "True")

(set-goal "all p,q p<=q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=q+p" "True")

(set-goal "all p,q p<q+p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<q+p" "True")

(set-goal "all p (PosS p<=1)=False")
(cases)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p<=1" "False")

(set-goal "all p,q (p+q<=p)=False")
(assert "all p,q(p+q<=p -> F)")
 (ind) ;4-6
 (ng)
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "p" "Absurd")
 (use "Absurd")
 (assume "p" "Absurd")
 (use "Absurd")
;; 5
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "p+q<p")
 (use "IH1" (pt "q"))
 (use "PosLtToLe")
 (use "p+q<p")
;; 6
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "S(p+q)<=p")
 (use "IH1" (pt "q"))
 (use "PosLeTrans" (pt "PosS(p+q)"))
 (use "Truth")
 (use "S(p+q)<=p")
;; Assertion proved.
(assume "Assertion" "p" "q")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<=p" "False")

(set-goal "all p,q (p+q<=q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<=q" "False")

(set-goal "all p,q (p+q<p)=False")
(assert "all p,q(p+q<p -> F)")
 (ind) ;4-6
 (ng #t)
 (assume "p" "Absurd")
 (use "Absurd")
;; 5
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "p+q<p")
 (use "IH1" (pt "q"))
 (use "p+q<p")
;; 6
 (assume "p" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "q" "IH2")
 (ng #t)
 (use "IH1")
 (assume "q" "IH2")
 (ng #t)
 (assume "S(p+q)<=p")
 (use "IH1" (pt "q"))
 (use "PosLtLeTrans" (pt "PosS(p+q)"))
 (use "Truth")
 (use "S(p+q)<=p")
;; Assertion proved.
(assume "Assertion" "p" "q")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<p" "False")

(set-goal "all p,q (p+q<q)=False")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<q" "False")

(set-goal "all p One<PosS p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "One<PosS p" "True")

;; PosLtPosS
(set-goal "all p,q (p<PosS q)=(p<=q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished
;; (cp)
(save "PosLtPosS")

;; PosLePosS
(set-goal "all p,q (PosS p<=q)=(p<q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "IH1")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cp)
(save "PosLePosS")

(set-goal "all p,q (PosS p<PosS q)=(p<q)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLtPosS")
;; 4
(assume "p" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLePosS")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p<PosS q" "p<q")

(set-goal "all p,q (PosS p<=PosS q)=(p<=q)")
(ind)
(ng)
(cases)
(use "Truth")
(assume "q")
(use "Truth")
(assume "q")
(use "Truth")
;; 3
(assume "p" "IH1")
(cases)
(ng)
(use "Truth")
(assume "q")
(use "Truth")
(assume "q")
(use "PosLtPosS")
;; 4
(assume "p" "IH1")
(cases)
(ng)
(cases (pt "p"))
(strip)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "q")
(ng #t)
(use "PosLePosS")
(assume "q")
(ng #t)
(use "IH1")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p<=PosS q" "p<=q")

;; PosSPosPredId
(set-goal "all p(One<p -> PosS(PosPred p)=p)")
(cases)
;; 2-4
(assume "Absurd")
(use "Absurd")
;; 3
(assume "p" "Useless")
(ng)
(use "Truth")
;; 4
(assume "p" "Useless")
(ng)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosSPosPredId")

;; PosLtMonPred
(set-goal "all p,q(One<p -> p<q -> PosPred p<PosPred q)")
(assume "p" "q" "1<p" "p<q")
(assert "One<q")
 (use "PosLtTrans" (pt "p"))
 (use "1<p")
 (use "p<q")
(assume "1<q")
(simp "<-" "PosLt8RewRule")
(simp "PosSPosPredId")
(simp "PosSPosPredId")
(use "p<q")
(use "1<q")
(use "1<p")
;; Proof finished.
;; (cp)
(save "PosLtMonPred")

;; PosNotLeToLt and PosNotLtToLe are proved using the isomorphic
;; embedding PosToNat of pos into nat.

;; We prove that NatToPos is an isomorphism w.r.t. <= and <.  Main
;; idea: Translate the computation rules for PosLe, PosLt into
;; equational lemmas for NatLe, NatLt with NatDouble nat for SZero pos
;; and Succ(NatDouble nat) for SOne pos.

;; PosToNatLeLt
(set-goal "all p,q((PosToNat p<=PosToNat q)=(p<=q) andnc
                   (PosToNat p<PosToNat q)=(p<q))")
(ind) ;2-4
(cases) ;5-7
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 6
(assume "p")
(ng #t)
(split)
(assert "Succ Zero<=NatDouble(PosToNat p)")
 (use "NatLtToLe")
 (use "NatLtOneDouble")
 (use "NatLtZeroPos")
(assume "Succ Zero<=NatDouble(PosToNat p)")
(simp "Succ Zero<=NatDouble(PosToNat p)")
(use "Truth")
(assert "Succ Zero<NatDouble(PosToNat p)")
 (use "NatLtOneDouble")
 (use "NatLtZeroPos")
(assume "Succ Zero<NatDouble(PosToNat p)")
(simp "Succ Zero<NatDouble(PosToNat p)")
(use "Truth")
;; 7
(assume "p")
(ng #t)
(split)
(use "Truth")
(assert "Zero<NatDouble(PosToNat p)")
 (use "NatLtOneSuccDouble")
 (use "NatLtZeroPos")
(assume "Zero<NatDouble(PosToNat p)")
(simp "Zero<NatDouble(PosToNat p)")
(use "Truth")
;; 3
(assume "p" "IH1")
(cases) ;36-38
(ng #t)
(split)
(assert "NatDouble(PosToNat p)<=Succ Zero -> F")
 (use "NatLeDoubleOne")
 (use "NatLtZeroPos")
(assume "NatDouble(PosToNat p)<=Succ Zero -> F")
(simp "NatDouble(PosToNat p)<=Succ Zero -> F")
(use "Truth")
(assert "NatDouble(PosToNat p)<Succ Zero -> F")
 (use "NatLtDoubleOne")
 (use "NatLtZeroPos")
(assume "NatDouble(PosToNat p)<Succ Zero -> F")
(simp "NatDouble(PosToNat p)<Succ Zero -> F")
(use "Truth")
;; 37
(assume "q")
(ng #t)
(split)
(simp "NatDoubleLe")
(use "IH1")
(simp "NatDoubleLt")
(use "IH1")
;; 38
(assume "q")
(ng #t)
(split)
(simp "NatLeDoubleSuccDouble")
(use "IH1")
(simp "NatLtDoubleSuccDouble")
(use "IH1")
;; 4
(assume "p" "IH1")
(cases) ;65-67
(ng #t)
(split)
(assert "NatDouble(PosToNat p)=Zero -> F")
 (assume "NatDouble(PosToNat p)=Zero")
 (assert "Zero<PosToNat p")
  (use "NatLtZeroPos")
 (assume "0<p")
 (inst-with-to "NatLt0Double" (pt "PosToNat p") "0<p" "NatLt0DoubleInst")
 (simphyp-with-to "NatLt0DoubleInst" "NatDouble(PosToNat p)=Zero" "Absurd")
 (use "Absurd")
(assume "NatDouble(PosToNat p)=Zero -> F")
(simp "NatDouble(PosToNat p)=Zero -> F")
(use "Truth")
(use "Truth")
;; 66
(assume "q")
(ng #t)
(split)
(simp "NatLeSuccDoubleDouble")
(use "IH1")
(simp "NatLtSuccDoubleDouble")
(use "IH1")
;; 67
(assume "q")
(ng #t)
(split)
(simp "NatLeSuccDoubleSuccDouble")
(use "IH1")
(simp "NatLtSuccDoubleSuccDouble")
(use "IH1")
;; Proof finished.
;; (cp)
(save "PosToNatLeLt")

;; Easy consequences

;; PosToNatLe
(set-goal "all p,q (PosToNat p<=PosToNat q)=(p<=q)")
(assume "p" "q")
(use "PosToNatLeLt")
;; Proof finished.
(save "PosToNatLe")

;; NatToPosLe
(set-goal "all n,m(Zero<n -> Zero<m -> (NatToPos n<=NatToPos m)=(n<=m))")
(assume "n" "m" "0<n" "0<m")
(simp "<-" "PosToNatLe")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<m")
(use "0<n")
;; Proof finished.
;; (cp)
(save "NatToPosLe")

;; PosToNatLt
(set-goal "all p,q (PosToNat p<PosToNat q)=(p<q)")
(assume "p" "q")
(use "PosToNatLeLt")
;; Proof finished.
;; (cp)
(save "PosToNatLt")

;; NatToPosLt
(set-goal "all n,m(Zero<n -> Zero<m -> (NatToPos n<NatToPos m)=(n<m))")
(assume "n" "m" "0<n" "0<m")
(simp "<-" "PosToNatLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<m")
(use "0<n")
;; Proof finished.
;; (cp)
(save "NatToPosLt")

;; PosNotLeToLt
(set-goal "all p,q((p<=q -> F) -> q<p)")
(assume "p" "q")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat q)=q")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat q)=q")
(simp "<-" "NatToPos(PosToNat q)=q")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLeToLt")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosNotLeToLt")

;; PosNotLtToLe
(set-goal "all p,q((p<q -> F) -> q<=p)")
(assume "p" "q")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat q)=q")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat q)=q")
(simp "<-" "NatToPos(PosToNat q)=q")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLtToLe")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosNotLtToLe")

;; PosLeToNotLt
(set-goal "all p,q(p<=q -> q<p -> F)")
(assume "p" "q")
(simp "<-" "PosToNatLt")
(simp "<-" "PosToNatLe")
(use "NatLeToNotLt")
;; (cp)
(save "PosLeToNotLt")

;; PosLeAntiSym
(set-goal "all p,q(p<=q -> q<=p -> p=q)")
(assume "p" "q")
(simp "<-" "PosToNatLe")
(simp "<-" "PosToNatLe")
(assume "NatLeHyp1" "NatLeHyp2")
(assert "PosToNat p=PosToNat q")
(use "NatLeAntiSym")
(use "NatLeHyp1")
(use "NatLeHyp2")
(use "PosToNatInj")
;; Proof finished.
;; (cp)
(save "PosLeAntiSym")

;; PosLeMonPlus
(set-goal "all p,q,r,r0(p<=q -> r<=r0 -> p+r<=q+r0)")
(assume "p" "q" "r" "r0" "p<=q" "r<=r0")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(assert "r=NatToPos(PosToNat r)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r=NatToPos(PosToNat r)")
(simp "r=NatToPos(PosToNat r)")
(drop "r=NatToPos(PosToNat r)")
(assert "r0=NatToPos(PosToNat r0)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r0=NatToPos(PosToNat r0)")
(simp "r0=NatToPos(PosToNat r0)")
(drop "r0=NatToPos(PosToNat r0)")
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosPlus")
(simp "NatToPosLe")
(use "NatLeMonPlus")
(simp "PosToNatLe")
(use "p<=q")
(simp "PosToNatLe")
(use "r<=r0")
;; ?_35:Zero<NatPlus(PosToNat q)(PosToNat r0)
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosLeMonPlus")

;; PosLeMonTimes
(set-goal
 "all p,q,r,r0(p<=q -> r<=r0 -> p*r<=q*r0)")
(assume "p" "q" "r" "r0" "p<=q" "r<=r0")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(assert "r=NatToPos(PosToNat r)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r=NatToPos(PosToNat r)")
(simp "r=NatToPos(PosToNat r)")
(drop "r=NatToPos(PosToNat r)")
(assert "r0=NatToPos(PosToNat r0)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "r0=NatToPos(PosToNat r0)")
(simp "r0=NatToPos(PosToNat r0)")
(drop "r0=NatToPos(PosToNat r0)")
(simp "<-" "NatToPosTimes")
(simp "<-" "NatToPosTimes")
(simp "NatToPosLe")
(use "NatLeMonTimes")
(simp "PosToNatLe")
(use "p<=q")
(simp "PosToNatLe")
(use "r<=r0")
;; ?_35:Zero<NatTimes(PosToNat q)(PosToNat r0)
(simp "<-" "PosToNatTimes")
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosLeMonTimes")

;; PosLtMonTimes
(set-goal "all q1,q2,p1,p2(q1<q2 -> p1<p2 -> q1*p1<q2*p2)")
(assume "q1" "q2" "p1" "p2")
(simp "<-" "PosToNatLt")
(simp "<-" "PosToNatLt")
(simp "<-" "PosToNatLt")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(use "NatLtMonTimes")
;; (cp)
(save "PosLtMonTimes")

;; Since many properties involving PosMinus depend on <-hypotheses
;; we provide PosLtLeMonTimes and PosLeLtMonTimes

;; PosLtLeMonTimes
(set-goal "all p,q,r,r0(
 p<q -> r<=r0 -> p*r<q*r0)")
(assume "p" "q" "r" "r0")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sp<=q" "r<=r0")
(assert "(p+1)*r<=q*r0")
 (use "PosLeMonTimes")
 (use "Sp<=q")
 (use "r<=r0")
(assume "(p+1)r<=qr")
(use "PosLtLeTrans" (pt "(p+1)*r"))
(simp "PosTimesPlusDistrLeft")
(ng)
(use "Truth")
(use "(p+1)r<=qr")
;; Proof finished.
;; (cp)
(save "PosLtLeMonTimes")

;; PosLeLtMonTimes
(set-goal "all p,q,r,r0(
 p<=q -> r<r0 -> p*r<q*r0)")
(assume "p" "q" "r" "r0" "p<=q")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sr<=r0")
(assert "p*(r+1)<=q*r0")
 (use "PosLeMonTimes")
 (use "p<=q")
 (use "Sr<=r0")
(assume "p*(r+1)<=qr0")
(use "PosLtLeTrans" (pt "p*(r+1)"))
(simp "PosTimesPlusDistr")
(ng)
(use "Truth")
(use "p*(r+1)<=qr0")
;; Proof finished.
;; (cp)
(save "PosLeLtMonTimes")

;; PosLePlusCancelL
(set-goal "all p,q,r(p+q<=p+r)=(q<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "<-" (pf "NatToPos(PosToNat(p+q))=p+q"))
(simp "<-" (pf "NatToPos(PosToNat(p+r))=p+r"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "NatToPosLe")
(ng) ;uses NatPlusCancelL
(simp "<-" "NatToPosLe")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatToPosToNatId")
(use "NatToPosToNatId")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<=p+r" "q<=r")

;; PosLePlusCancelR
(set-goal "all p,q,r(p+q<=r+q)=(p<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosPlusComm")
(simp (pf "r+q=q+r"))
(ng)
(use "Truth")
(use "PosPlusComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<=r+q" "p<=r")

;; PosLtPlusCancelL
(set-goal "all p,q,r(p+q<p+r)=(q<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "<-" (pf "NatToPos(PosToNat(p+q))=p+q"))
(simp "<-" (pf "NatToPos(PosToNat(p+r))=p+r"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "NatToPosLt")
(ng) ;uses NatPlusCancelL
(simp "<-" "NatToPosLt")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(simp "<-" "PosToNatPlus")
(use "NatLtZeroPos")
(use "NatToPosToNatId")
(use "NatToPosToNatId")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<p+r" "q<r")

;; PosLtPlusCancelR
(set-goal "all p,q,r(p+q<r+q)=(p<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosPlusComm")
(simp (pf "r+q=q+r"))
(ng)
(use "Truth")
(use "PosPlusComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q<r+q" "p<r")

;; PosTimesCancelL
(set-goal "all p,q,r(p*q=p*r -> q=r)")
(assume "p" "q" "r" "pq=pr")
(use "PosLeAntiSym")
;; 3,4
(use "PosNotLtToLe")
(assume "r<q")
(assert "p*r<p*q")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "r<q")
(simp "pq=pr")
(assume "Absurd")
(use "Absurd")
;; 4 
(use "PosNotLtToLe")
(assume "q<r")
(assert "p*q<p*r")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "q<r")
(simp "pq=pr")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PosTimesCancelL")

;; PosTimesCancelR
(set-goal "all p,q,r(p*r=q*r -> p=q)")
(assume "p" "q" "r" "pr=qr")
(use "PosTimesCancelL" (pt "r"))
(simp "PosTimesComm")
(simp "pr=qr")
(use "PosTimesComm")
;; Proof finished.
;; (cp)
(save "PosTimesCancelR")

(set-goal "all p,q,r (p*r<=q*r)=(p<=q)") ;as rewrite rule
(assume "p" "q" "r")
(use "BooleAeqToEq")
;; 3,4
(assume "pr<=qr")
(use "PosNotLtToLe")
(assume "q<p")
(assert "q*r<p*r")
 (use "PosLtLeMonTimes")
 (use "q<p")
 (use "Truth")
(assume "qr<pr")
(assert "p*r<p*r")
 (use "PosLeLtTrans" (pt "q*r"))
 (use "pr<=qr")
 (use "qr<pr")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "p<=q")
(use "PosLeMonTimes")
(use "p<=q")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p*r<=q*r" "p<=q")

;; PosLeTimesCancelR
(set-goal "all p1,p2,q(p1*q<=p2*q -> p1<=p2)")
(strip)
(simp "<-" "PosToNatLe")
(use "NatLeTimesCancelR" (pt "PosToNat q"))
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(simp "PosToNatLe")
(use 1)
;; (cp)
(save "PosLeTimesCancelR")

(set-goal  "all p,q,r(p*q<=p*r)=(q<=r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosTimesComm")
(simp (pf "p*r=r*p"))
(use "Truth")
(use "PosTimesComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p*q<=p*r" "q<=r")

;; PosLeTimesCancelL
(set-goal "all p1,p2,q(q*p1<=q*p2 -> p1<=p2)")
(strip)
(simp "<-" "PosToNatLe")
(use "NatLeTimesCancelL" (pt "PosToNat q"))
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(simp "PosToNatLe")
(use 1)
;; (cp)
(save "PosLeTimesCancelL")

(set-goal  "all p,q,r(p*q<p*r)=(q<r)") ;as rewrite rule
(assume "p" "q" "r")
(use "BooleAeqToEq")
;; 3,4
(assume "pq<pr")
(use "PosNotLeToLt")
(assume "r<=q")
(assert "p*r<=p*q")
 (use "PosLeMonTimes")
 (use "Truth")
 (use "r<=q")
(assume "pr<=pq")
(assert "p*q<p*q")
 (use "PosLtLeTrans" (pt "p*r"))
 (use "pq<pr")
 (use "pr<=pq")
(assume "Absurd")
(use "Absurd")
;; 4
(use "PosLeLtMonTimes")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p*q<p*r" "q<r")

;; PosLtTimesCancelL
(set-goal "all p1,p2,q(p1*q<p2*q -> p1<p2)")
(strip)
(simp "<-" "PosToNatLt")
(use "NatLtTimesCancelR" (pt "PosToNat q"))
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(simp "PosToNatLt")
(use 1)
;; (cp)
(save "PosLtTimesCancelL")

(set-goal  "all p,q,r(p*q<r*q)=(p<r)") ;as rewrite rule
(assume "p" "q" "r")
(simp "PosTimesComm")
(simp (pf "r*q=q*r"))
(use "Truth")
(use "PosTimesComm")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p*q<r*q" "p<r")

;; PosLtTimesCancelR
(set-goal "all p1,p2,q(p1*q<p2*q -> p1<p2)")
(strip)
(simp "<-" "PosToNatLt")
(use "NatLtTimesCancelR" (pt "PosToNat q"))
(use "NatLtZeroPos")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(simp "PosToNatLt")
(use 1)
;; (cp)
(save "PosLtTimesCancelR")

(set-goal "all p p<SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(use "IH")
(assume "p" "IH")
(ng)
(use "PosLtTrans" (pt "SZero p"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<SZero p" "True")

;; PosLeLtCases
(set-goal "all p,q((p<=q -> Pvar) -> (q<p -> Pvar) -> Pvar)")
(assume "p" "q" "LeHyp" "LtHyp")
(use "NatLeLtCases" (pt "PosToNat p") (pt "PosToNat q") "?" "?")
;; 3,4
(assume "NatLeHyp")
(use "LeHyp")
(simp "<-" "PosToNatLe")
(use "NatLeHyp")
;; 4
(assume "NatLtHyp")
(use "LtHyp")
(simp "<-" "PosToNatLt")
(use "NatLtHyp")
;; Proof finished.
;; (cp)
(save "PosLeLtCases")

;; PosLeCases
(set-goal "all p,q(p<=q -> (p<q -> Pvar) -> (p=q -> Pvar) -> Pvar)")
(assume "p" "q" "p<=q")
(cases (pt "p<q"))
;; Case p<q
(assume "p<p" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case p<q -> F
(assume "p<q -> F" "THyp" "FHyp")
(use "FHyp")
(use "PosLeAntiSym")
(use "p<=q")
(use "PosNotLtToLe")
(use "p<q -> F")
;; Proof finished.
(cp)
(save "PosLeCases")

;; ;; PosLeCases
;; (set-goal "all p,q(p<=q -> (p<q -> Pvar) -> (p=q -> Pvar) -> Pvar)")
;; (assume "p" "q" "p<=q" "LtHyp" "EqHyp")
;; (use "NatLeCases" (pt "PosToNat p") (pt "PosToNat q") "?" "?" "?")
;; ;; 3-5
;; (simp "PosToNatLe")
;; (use "p<=q")
;; ;; 4
;; (simp "PosToNatLt")
;; (use "LtHyp")
;; ;; 5
;; (assume "EqPosToNatHyp") ;Warning: nc-intro with cvar(s) boole20681 boole20682
;; (use "EqHyp")
;; (simp "<-" "NatToPosToNatId")
;; (simp "EqPosToNatHyp")
;; (use "NatToPosToNatId")
;; ;; Proof finished.
;; ;; (cp)
;; (save "PosLeCases")

;; PosLeMonPred
(set-goal "all p,q(p<=q -> PosPred p<=PosPred q)")
(assume "p" "q")
(use "PosLeCases" (pt "1") (pt "p"))
(use "Truth")
;; 3-5
(assume "1<p")
(use "PosLeCases" (pt "1") (pt "q"))
;; 7-9
(use "Truth")
(assume "1<q" "p<=q")
(assert "PosS(PosPred p)<=PosS(PosPred q)")
 (simp "PosSPosPredId")
 (simp "PosSPosPredId")
 (use "p<=q")
 (use "1<q")
 (use "1<p")
(ng)
(assume "Hyp")
(use "Hyp")
;; 9
(assume "1=q")
(simp "<-" "1=q")
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
;; 5
(assume "1=p" "Useless")
(simp "<-" "1=p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLeMonPred")

;; Rules for PosMinus:  They give correct results for p--q (only) if q<p.

(add-computation-rules
 "One--p" "One"
 "SZero p--One" "PosPred(SZero p)"
 "SZero p--SZero q" "SZero(p--q)"
 "SZero p--SOne q" "PosPred(SZero(p--q))"
 "SOne p--One" "SZero p"
 "SOne p--SZero q" "[if (p=q) One (SOne(p--q))]"
 "SOne p--SOne q" "SZero(p--q)")

;; (display-pconst "PosMinus")

;; (pp (nt (pt "7--4")))
;; (pp (nt (pt "6--4")))
;; (pp (nt (pt "66--44")))

;; PosMinusTotal
(set-totality-goal "PosMinus")
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:all p^(TotalPos p^ -> TotalPos(1--p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")
;; ?_4:all p^(
;;      TotalPos p^ -> 
;;      all p^0(TotalPos p^0 -> TotalPos(p^ --p^0)) -> 
;;      all p^0(TotalPos p^0 -> TotalPos(SZero p^ --p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")
;; ?_5:all p^(
;;      TotalPos p^ -> 
;;      all p^0(TotalPos p^0 -> TotalPos(p^ --p^0)) -> 
;;      all p^0(TotalPos p^0 -> TotalPos(SOne p^ --p^0)))
(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tq")
(use "Tq2")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")
;; Proof finished.
;; (cp)
(save-totality)

(set-goal "all p PosS p--1=p")
(cases)
(use "Truth")
(assume "p")
(ng)
(use "Truth")
(assume "p")
;; PosS(SOne p)--1=SOne p
(ng)
;; ?_8:PosPred(SZero(PosS p))=SOne p
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosS p--1" "p")

;; We consider the rules for NatMinus.  Do they hold for PosMinus?

;; PosMinusOneEqPosPred
(set-goal "all p p--1=PosPred p")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosMinusOneEqPosPred")

;; The remaining rewrite rules for NatMinus are

;; (set-goal "all n,m Pred(Succ n--m)=n--m")
;; (set-goal "all nat nat--nat=0")
;; (set-goal "all nat Succ nat--nat=1")
;; (set-goal "all nat 0--nat=0")
;; (set-goal "all n,m n--m<=n")
;; (set-goal "all n,m n+m--m=n")
;; (set-goal "all n,m m+n--m=n")

;; The second computation rule p--PosS q=PosPred(p--q) is
;; wrong for p=2 and q=1.

;; (pp (nt (pt "2--PosS 1"))) ;2
;; (pp (nt (pt "PosPred(2--1)"))) ;1

;; We need a premise PosS q<p.  Since the proof is easiest with
;; an ordinary successor induction, we postpone the proof until we
;; have seen that NatToPos and PosToNat are isomorphisms w.r.t. -

;; We prove that PosToNat is an isomorphism w.r.t. -

;; Need that PosToNat is an isomorphism w.r.t. NatDouble and Pred.

;; SuccPosPred
(set-goal "all p(1<p -> PosToNat p=Succ(PosToNat(PosPred p)))")
(ind)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
;; 6-8
(ng)
(strip)
(use "Truth")
;; 7
(assume "p" "IH" "Useless")
(ng)
(simp "IH")
(ng)
(use "Truth")
(use "Truth")
; 8
(assume "p" "IH" "Useless")
(ng)
(use "Truth")
;; 4
(ng)
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "SuccPosPred")

;; PredPosPred
(set-goal "all p(1<p -> Pred(PosToNat p)=PosToNat(PosPred p))")
(assume "p" "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cp)
(save "PredPosPred")

(set-goal "all p PosPred p<=p")
(assume "p")
(use "PosLeCases" (pt "1") (pt "p"))
(use "Truth")
(assume "1<p")
(simp "<-" "PosToNatLe")
(simp "<-" "PredPosPred")
(ng)
(use "Truth")
(use "1<p")
(assume "1=p")
(simp "<-" "1=p")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "PosPred p<=p" "True")

;; NatDoubleSZero
(set-goal "NatDouble(PosToNat p)=PosToNat(SZero p)")
(ind)
(ng)
(use "Truth")
(assume "p" "IH")
(ng)
(use "Truth")
(assume "p" "IH")
(ng)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatDoubleSZero")

;; Now we can prove that PosToNat is an isomorphism w.r.t. -

;; PosToNatMinus
(set-goal "all p,q(q<p -> PosToNat(p--q)=PosToNat p--PosToNat q)")
(ind)
;; 2-4
(assume "q" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "IH1")
(ind)
;; 8-10
(ng)
;; ?^11:T -> PosToNat(PosPred(SZero p))=Pred(NatDouble(PosToNat p))
(simp "NatDoubleSZero")
(simp "PredPosPred")
(assume "Useless")
(use "Truth")
(ng)
(use "Truth")
;; 9
(assume "q" "IH2" "q<p")
(ng)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "q<p")
;; 10
(ng)
(assume "q" "IH2")
(assume "q<p")
(simp "<-" "NatDoubleMinus")
(simp "<-" "PredPosPred")
(simp "<-" "NatDoubleSZero")
(simp "IH1")
(use "Truth")
(use "q<p")
(ng)
(use "Truth")
;; 4
(assume "p" "IH1")
(ind)
;; 33-35
(ng)
(strip)
(use "Truth")
;; 34
(assume "q" "IH2")
(ng)
(assume "q<=p")
(use "PosLeCases" (pt "q") (pt "p"))
(use "q<=p")
(assume "q<p")
(assert "p=q -> q<q")
 (assume "p=q")
 (simphyp-with-to "q<p" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(simp "p=q -> F")
(ng #t)
(simp "<-" "SuccNatMinus")
(simp "<-" "NatDoubleMinus")
(ng)
(simp "IH1")
(ng)
(use "Truth")
(use "q<p")
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
;; 43
(assume "q=p")
(simp "q=p")
(ng)
(use "Truth")
;; 35
(assume "q" "IH2" "q<p")
(ng #t)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cp)
(save "PosToNatMinus")

;; Code discarded 2021-02-15
;; ;; PosToNatMinus
;; (set-goal "all p,q(q<p -> PosToNat(p--q)=PosToNat p--PosToNat q)")
;; (ind)
;; ;; 2-4
;; (assume "q" "Absurd")
;; (use "EfAtom")
;; (use "Absurd")
;; ;; 3
;; (assume "p" "IH1")
;; (ind)
;; ;; 8-10
;; (ng)
;; ;; ?^11:T -> PosToNat(PosPred(SZero p))=Pred(NatDouble(PosToNat p))
;; (simp "NatDoubleSZero")
;; (simp "PredPosPred")
;; (assume "Useless")
;; (use "Truth")
;; (ng)
;; (use "Truth")
;; ;; 9
;; (assume "q" "IH2" "q<p")
;; (ng)
;; (simp "IH1")
;; (simp "NatDoubleMinus")
;; (use "Truth")
;; (use "q<p")
;; ;; 10
;; (ng)
;; (assume "q" "IH2")
;; (assume "q<p")
;; (simp "<-" "NatDoubleMinus")
;; (simp "<-" "PredPosPred")
;; (simp "<-" "NatDoubleSZero")
;; (simp "IH1")
;; (use "Truth")
;; (use "q<p")
;; (ng)
;; (use "Truth")
;; ;; 4
;; (assume "p" "IH1")
;; (ind)
;; ;; 33-35
;; (ng)
;; (strip)
;; (use "Truth")
;; ;; 34
;; (assume "q" "IH2")
;; (ng)
;; (assume "q<=p")
;; (use "PosLeCases" (pt "q") (pt "p"))
;; (use "q<=p")
;; (assume "q<p")
;; (assert "p=q -> q<q")
;;  (assume "p=q")
;;  (simphyp-with-to "q<p" "p=q" "Absurd")
;;  (use "Absurd")
;; (assume "p=q -> F")
;; (simp "p=q -> F")
;; (ng #t)
;; (simp "<-" "SuccNatMinus")
;; (simp "<-" "NatDoubleMinus")
;; (ng)
;; (simp "IH1")
;; (ng)
;; (use "Truth")
;; (use "q<p")
;; (simp "NatDoubleLt")
;; (simp "PosToNatLt")
;; (use "q<p")
;; ;; 43
;; (assume "q=p")
;; (simp "q=p")
;; (ng)
;; (use "Truth")
;; ;; 35
;; (assume "q" "IH2" "q<p")
;; (ng #t)
;; (simp "IH1")
;; (simp "NatDoubleMinus")
;; (use "Truth")
;; (use "q<p")
;; ;; Proof finished.
;; ;; (cp)
;; (save "PosToNatMinus")

;; NatToPosMinus
(set-goal "all n,m(Zero<m -> m<n -> NatToPos(n--m)=NatToPos n--NatToPos m)")
(assume "n" "m" "0<m" "m<n")
(assert "Zero<n")
 (use "NatLtTrans" (pt "m"))
 (use "0<m")
 (use "m<n")
(assume "0<n") 
(assert "n--m=PosToNat(NatToPos n)--PosToNat(NatToPos m)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<m")
 (use "0<n")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatMinus")
(simp "NatToPosToNatId")
(use "Truth")
(simp "NatToPosLt")
(use "m<n")
(use "0<n")
(use "0<m")
;; Proof finished.
;; (cp)
(save "NatToPosMinus")

;; Now we can continue proving the nat rewrite rules for pos

(set-goal "all p,q p+q--q=p")
(assume "p" "q")
(assert "p=NatToPos(PosToNat p)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "p=NatToPos(PosToNat p)")
(simp "p=NatToPos(PosToNat p)")
(drop "p=NatToPos(PosToNat p)")
(assert "q=NatToPos(PosToNat q)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "q=NatToPos(PosToNat q)")
(simp "q=NatToPos(PosToNat q)")
(drop "q=NatToPos(PosToNat q)")
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosMinus")
(ng #t)
(use "Truth")
(simp "<-" "PosToNatPlus")
(simp "PosToNatLt")
(ng #t)
(use "Truth")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p+q--q" "p")

(set-goal "all p,q q+p--q=p")
(assume "p" "q")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "q+p--q" "p")

;; PosLtMonMinusLeft
(set-goal "all p,q,r(q<r -> p<q -> q--p<r--p)")
(assume "p" "q" "r" "q<r" "p<q")
(inst-with-to "NatToPosToNatId" (pt "q--p") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "r--p") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "NatToPosLt")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(use "NatLtMonMinusLeft")
(simp "PosToNatLt")
(use "q<r")
(use "NatLtToLe")
(simp "PosToNatLt")
(use "p<q")
(use "PosLtTrans" (pt "q"))
(use "p<q")
(use "q<r")
(use "p<q")
(use "NatLtZeroPos")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "PosLtMonMinusLeft")

;; From NatPlusMinus we obtain PosPlusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosPlusMinus
(set-goal "all p,q,r(r<q -> p+(q--r)=p+q--r)")
(assume "p" "q" "r" "r<q")
(assert
 "NatToPos(PosToNat(p+(q--r)))=NatToPos(PosToNat(p+q--r))")
 (simp "PosToNatPlus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatPlusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "r<q")
 (use "PosLtTrans" (pt "q"))
 (use "r<q")
 (use "Truth")
 (use "r<q")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
;; (cp)
(save "PosPlusMinus")

;; Code discarded 2021-02-15
;; ;; PosPlusMinus
;; (set-goal "all p,q,r(r<q -> p+(q--r)=p+q--r)")
;; (assume "p" "q" "r" "r<q")
;; (assert
;;  "NatToPos(PosToNat(p+(q--r)))=NatToPos(PosToNat(p+q--r))")
;;  (simp "PosToNatPlus")
;;  (simp "PosToNatMinus")
;;  (simp "PosToNatMinus")
;;  (simp "PosToNatPlus")
;;  (simp "NatPlusMinus")
;;  (use "Truth")
;;  (use "NatLtToLe")
;;  (simp "PosToNatLt")
;;  (use "r<q")
;;  (use "PosLtTrans" (pt "q"))
;;  (use "r<q")
;;  (use "Truth")
;;  (use "r<q")
;;  (simp "NatToPosToNatId")
;;  (simp "NatToPosToNatId")
;; (assume "Assertion")
;; (use "Assertion")
;; ;; Proof finished.
;; ;; (cp)
;; (save "PosPlusMinus")

;; PosMinusPlus
(set-goal "all p,q,r(r<p -> p--r+q=p+q--r)")
(assume "p" "q" "r" "r<p")
(inst-with-to "PosPlusMinus" (pt "q") (pt "p") (pt "r") "r<p"
	      "PosPlusMinusInst")
(simp "PosPlusComm")
(simp "PosPlusMinusInst")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosMinusPlus")

;; PosMinusPlusEq
(set-goal "all p,q(q<p -> p--q+q=p)")
(assume "p" "q" "q<p")
(simp "PosMinusPlus")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cp)
(save "PosMinusPlusEq")

;; From NatMinusMinus we obtain PosMinusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosMinusMinus
(set-goal "all p,q,r(r<q -> q<p+r -> p--(q--r)=p+r--q)")
(assume "p" "q" "r" "r<q" "q<p+r")
(assert "q--r<p")
 (assert "p=p+r--r")
  (use "Truth")
 (assume "p=p+r-r")
 (simp "p=p+r-r")
 (drop "p=p+r-r")
 (use "PosLtMonMinusLeft")
 (use "q<p+r")
 (use "r<q")
(assume "q-r<p")
(assert "NatToPos(PosToNat(p--(q--r)))=NatToPos(PosToNat(p+r--q))")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatMinusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "<-" "PosToNatPlus")
 (simp "PosToNatLt")
 (use "q<p+r")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "r<q")
 (use "q<p+r")
 (use "r<q")
 (use "q-r<p")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cp)
(save "PosMinusMinus")

;; Similarly to NatMinus5RewRule we have
;; q+r<p -> p--q--r=p--(q+r)
;; The assumption q+r<p is necessary since PosMinus does not
;; behave well for equal arguments.

;; Idea of the proof: Apply PosToNat o NatToPos outside.  Move
;; PosToNat inside (this needs q+r<p), use NatMinus5RewRule.  Notice
;; that the display by pp is not helpful for this level of detail.
;; Use ppn instead.

;; PosMinusMinusLeft
(set-goal "all p,q,r(q+r<p -> p--q--r=p--(q+r))")
(assume "p" "q" "r" "q+r<p")
(assert "q<p")
 (use "PosLtTrans" (pt "q+r"))
 (use "Truth")
 (use "q+r<p")
(assume "q<p")
(inst-with-to "NatToPosToNatId" (pt "p--q--r") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p--(q+r)") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatPlus")
(simp "<-" "NatMinus5RewRule")
(use "Truth")
(use "q+r<p")
(use "q<p")
;; ?_17:r<p--q
(assert "r=q+r--q")
 (use "Truth")
(assume "r=q+r--q")
(simp "r=q+r--q")
(drop "r=q+r--q")
(use "PosLtMonMinusLeft")
(use "q+r<p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosMinusMinusLeft")

;; PosTimesMinusDistr
(set-goal "all p,q,r(r<q ->  p*(q--r)=p*q--p*r)")
(assume "p" "q" "r" "r<q")
(inst-with-to "NatToPosToNatId" (pt "p*(q--r)") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p*q--p*r") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLeLtMonTimes")
(use "Truth")
(use "r<q")
(use "r<q")
;; Proof finished.
;; (cp)
(save "PosTimesMinusDistr")

;; PosTimesMinusDistrLeft
(set-goal "all p,q,r(q<p ->  (p--q)*r=p*r--q*r)")
(assume "p" "q" "r" "q<p")
(inst-with-to "NatToPosToNatId" (pt "(p--q)*r") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "p*r--q*r") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLtLeMonTimes")
(use "q<p")
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cp)
(save "PosTimesMinusDistrLeft")

;; Rules for PosMax

(add-computation-rules
 "One max p" "p"
 "SZero p max One" "SZero p"
 "SZero p max SZero q" "SZero(p max q)"
 "SZero p max SOne q" "[if (p<=q) (SOne q) (SZero p)]"
 "SOne p max One" "SOne p"
 "SOne p max SZero q" "[if (q<=p) (SOne p) (SZero q)]"
 "SOne p max SOne q" "SOne(p max q)")

;; PosMaxTotal
(set-totality-goal "PosMax")
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "Tq")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSOne")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSOne")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cp)
(save-totality)

(set-goal "all p p max One=p")
(cases)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p max One" "p")

(set-goal "all p p max p=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p max p" "p")

(set-goal "all p p max Succ Zero=p")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cp)
(save "NatMaxPosOne")

(set-goal "all p Succ Zero max p=p")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cp)
(save "NatMaxOnePos")

;; PosMaxComm
(set-goal "all p,q p max q = q max p")
(ind)
;; 2-4
(strip)
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(use "Truth")
;; 8
(use "IH")
;; 9
(ng)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(use "Truth")
;; 14
(ng)
(strip)
(use "Truth")
;; 15
(use "IH")
;; Proof finished.
;; (cp)
(save "PosMaxComm")

;; PosMaxEq1
(set-goal "all p,q(q<=p -> p max q=p)")
(ind)
(ng)
(assume "q" "q=1")
(use "q=1")
;; 3
(assume "p" "IH")
(cases)
;; 8-10
(strip)
(use "Truth")
;; 9
(ng)
(use "IH")
;; 10
(ng)
(assume "q" "q<p")
(assert "p<=q -> F")
 (assume "p<=q")
 (assert "p<p")
  (use "PosLeLtTrans" (pt "q"))
  (use "p<=q")
  (use "q<p")
 (assume "p<p")
 (use "p<p")
(assume "p<=q -> F")
(simp "p<=q -> F")
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 26-28
(ng)
(strip)
(use "Truth")
;; 27
(ng)
(assume "q" "q<=p")
(simp "q<=p")
(use "Truth")
;; 28
(use "IH")
;; Proof finished.
;; (cp)
(save "PosMaxEq1")

;; PosMaxEq2
(set-goal "all p,q(p<=q -> p max q=q)")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxEq1")
;; Proof finished.
;; (cp)
(save "PosMaxEq2")

;; We prove that PosToNat is an isomorphism w.r.t. max

;; PosToNatMax
(set-goal "all p,q PosToNat(p max q)=PosToNat p max PosToNat q")
(ind)
;; 2-4
(assume "q")
(ng)
(simp "NatMaxOnePos")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9-11
(ng)
(simp "NatDoubleSZero")
(simp "NatMaxPosOne")
(use "Truth")
;; 10
(assume "q")
(ng)
(simp "IH")
(simp "NatMaxDouble")
(use "Truth")
;; 11
(assume "q")
(ng)
(cases (pt "p<=q"))
(assume "p<=q")
(ng)
(simp "NatMaxEq2")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat q)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "p<=q")
(use "Truth")
;; 22
(assume "p<=q -> F")
(ng)
(simp "NatMaxEq1")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "q<p")
 (use "PosNotLeToLt")
 (use "p<=q -> F")
(assume "q<p")
(simp "PosToNatLt")
(use "q<p")
;; 4
(assume "p" "IH")
(cases)
;; 42-44
(ng)
(use "Truth")
;; 43
(assume "q")
(ng)
(cases (pt "q<=p"))
(assume "q<=p")
(ng)
(simp "NatMaxEq1")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat p)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
(use "Truth")
;; 49
(assume "q<=p -> F")
(ng)
(simp "NatMaxEq2")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "p<q")
 (use "PosNotLeToLt")
 (use "q<=p -> F")
(assume "p<q")
(simp "PosToNatLt")
(use "p<q")
;; 44
(ng)
(assume "q")
(simp "NatMaxDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosToNatMax")

;; PosMaxUB1
(set-goal "all p,q p<=p max q")
(assume "p" "q")
(assert "NatToPos(PosToNat p)<=NatToPos(PosToNat(p max q))")
 (simp "NatToPosLe")
 (simp "PosToNatMax")
 (use "NatMaxUB1")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=p max q")
(use "p<=p max q")
;; Proof finished.
;; (cp)
(save "PosMaxUB1")

;; PosMaxUB2
(set-goal "all p,q q<=p max q")
(assume "p" "q")
(simp "PosMaxComm")
(use "PosMaxUB1")
;; Proof finished.
;; (cp)
(save "PosMaxUB2")

;; PosMaxLUB
(set-goal "all p,q,r(p<=r -> q<=r -> p max q<=r)")
(assume "p" "q" "r")
(assert "NatToPos(PosToNat p)<=NatToPos(PosToNat r) ->
         NatToPos(PosToNat q)<=NatToPos(PosToNat r) ->
         NatToPos(PosToNat(p max q))<=NatToPos(PosToNat r)")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "PosToNatMax")
 (use "NatMaxLUB")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p<=r -> q<=r -> p max q<=r")
(use "p<=r -> q<=r -> p max q<=r")
;; Proof finished.
;; (cp)
(save "PosMaxLUB")

;; PosTimesMaxDistr
(set-goal "all p,q,r p*(q max r)=p*q max(p*r)")
(ind)
;; 2-4
(assume "q" "r")
(use "Truth")
;; 3
(assume "p" "IH" "q" "r")
(ng)
(use "IH")
;; 4
(assume "p" "IH" "q" "r")
(use "PosLeLtCases" (pt "q") (pt "r"))
;; 9,10
(assume "q<=r")
(simp (pf "q max r=r"))
(simp (pf "SOne p*q max(SOne p*r)=SOne p*r"))
(use "Truth")
(use "PosMaxEq2")
(use "PosLeMonTimes")
(use "Truth")
(use "q<=r")
(use "PosMaxEq2")
(use "q<=r")
;; 10
(assume "r<q")
(inst-with-to "PosLtToLe" (pt "r") (pt "q") "r<q" "r<=q")
(simp (pf "q max r=q"))
(simp (pf "SOne p*q max(SOne p*r)=SOne p*q"))
(use "Truth")
(use "PosMaxEq1")
(use "PosLeMonTimes")
(use "Truth")
(use "r<=q")
(use "PosMaxEq1")
(use "r<=q")
;; Proof finished.
;; (cp)
(save "PosTimesMaxDistr")

;; Rules for PosMin

(add-computation-rules
 "One min p" "One"
 "SZero p min One" "One"
 "SZero p min SZero q" "SZero(p min q)"
 "SZero p min SOne q" "[if (p<=q) (SZero p) (SOne q)]"
 "SOne p min One" "One"
 "SOne p min SZero q" "[if (q<=p) (SZero q) (SOne p)]"
 "SOne p min SOne q" "SOne(p min q)")

;; PosMinTotal
(set-totality-goal "PosMin")
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "TotalPosOne")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")
(use "TotalPosSOne")
(use "Tq1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
;; (cp)
(save-totality)

(set-goal "all p p min One=One")
(cases)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
(assume "p")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p min One" "One")

(set-goal "all p p min p=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p min p" "p")

;; NatMinOnePos
(set-goal "all p Succ Zero min p=One")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cp)
(save "NatMinOnePos")

;; NatMinPosOne
(set-goal "all p p min Succ Zero=One")
(assume "p")
(use "PosLeLtCases" (pt "p") (pt "1"))
(ng)
(assume "p=1")
(simp "p=1")
(use "Truth")
(assume "1<p")
(simp "SuccPosPred")
(use "Truth")
(use "1<p")
;; Proof finished.
;; (cp)
(save "NatMinPosOne")

;; PosMinComm
(set-goal "all p,q p min q = q min p")
(ind)
;; 2-4
(strip)
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(use "Truth")
;; 8
(use "IH")
;; 9
(ng)
(strip)
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(use "Truth")
;; 14
(ng)
(strip)
(use "Truth")
;; 15
(use "IH")
;; Proof finished.
;; (cp)
(save "PosMinComm")

;; PosMinEq1
(set-goal "all p,q(q<=p -> p min q=q)")
(ind)
(ng)
(assume "q" "q=1")
(simp "q=1")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9--11
(strip)
(use "Truth")
;; 10
(ng)
(use "IH")
;; 11
(ng)
(assume "q" "q<p")
(assert "p<=q -> F")
 (assume "p<=q")
 (assert "p<p")
  (use "PosLeLtTrans" (pt "q"))
  (use "p<=q")
  (use "q<p")
 (assume "p<p")
 (use "p<p")
(assume "p<=q -> F")
(simp "p<=q -> F")
(use "Truth")
;; 4
(assume "p" "IH")
(cases)
;; 27-29
(ng)
(strip)
(use "Truth")
;; 28
(ng)
(assume "q" "q<=p")
(simp "q<=p")
(use "Truth")
;; 29
(use "IH")
;; Proof finished.
;; (cp)
(save "PosMinEq1")

;; PosMinEq2
(set-goal "all p,q(p<=q -> p min q=p)")
(assume "p" "q")
(simp "PosMinComm")
(use "PosMinEq1")
;; Proof finished.
;; (cp)
(save "PosMinEq2")

;; We prove that PosToNat is an isomorphism w.r.t. min

;; PosToNatMin
(set-goal "all p,q PosToNat(p min q)=PosToNat p min PosToNat q")
(ind)
;; 2-4
(assume "q")
(ng)
(simp "NatMinOnePos")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 9-11
(ng)
(simp "NatDoubleSZero")
(simp "NatMinPosOne")
(use "Truth")
;; 10
(assume "q")
(ng)
(simp "IH")
(simp "NatMinDouble")
(use "Truth")
;; 11
(assume "q")
(ng)
(cases (pt "p<=q"))
(assume "p<=q")
(ng)
(simp "NatMinEq1")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat q)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "p<=q")
(use "Truth")
;; 22
(assume "p<=q -> F")
(ng)
(simp "NatMinEq2")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "q<p")
 (use "PosNotLeToLt")
 (use "p<=q -> F")
(assume "q<p")
(simp "PosToNatLt")
(use "q<p")
;; 4
(assume "p" "IH")
(cases)
;; 42-44
(ng)
(use "Truth")
;; 43
(assume "q")
(ng)
(cases (pt "q<=p"))
(assume "q<=p")
(ng)
(simp "NatMinEq2")
(use "Truth")
(use "NatLeTrans" (pt "NatDouble(PosToNat p)"))
(simp "NatDoubleLe")
(simp "PosToNatLe")
(use "q<=p")
(use "Truth")
;; 49
(assume "q<=p -> F")
(ng)
(simp "NatMinEq1")
(use "Truth")
(simp "NatLeSuccDoubleDouble")
(assert "p<q")
 (use "PosNotLeToLt")
 (use "q<=p -> F")
(assume "p<q")
(simp "PosToNatLt")
(use "p<q")
;; 44
(ng)
(assume "q")
(simp "NatMinDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosToNatMin")

;; PosMinLB1
(set-goal "all p,q p min q<=p")
(assume "p" "q")
(assert "NatToPos(PosToNat(p min q))<=NatToPos(PosToNat p)")
 (simp "NatToPosLe")
 (simp "PosToNatMin")
 (use "NatMinLB1")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "p min q<=p")
(use "p min q<=p")
;; Proof finished.
;; (cp)
(save "PosMinLB1")

;; PosMinLB2
(set-goal "all p,q p min q<=q")
(assume "p" "q")
(simp "PosMinComm")
(use "PosMinLB1")
;; Proof finished.
;; (cp)
(save "PosMinLB2")

;; PosMinGLB
(set-goal "all p,q,r(r<=p -> r<=q -> r<=p min q)")
(assume "p" "q" "r")
(assert "NatToPos(PosToNat r)<=NatToPos(PosToNat p) ->
         NatToPos(PosToNat r)<=NatToPos(PosToNat q) ->
         NatToPos(PosToNat r)<=NatToPos(PosToNat(p min q))")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "NatToPosLe")
 (simp "PosToNatMin")
 (use "NatMinGLB")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
 (use "NatLtZeroPos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "r<=p -> r<=q -> r<=p min q")
(use "r<=p -> r<=q -> r<=p min q")
;; Proof finished.
;; (cp)
(save "PosMinGLB")

;; Rules for NatExp : nat=>nat=>nat

(add-computation-rules
 "n**Zero" "Succ Zero"
 "n**Succ m" "n**m*n")

;; NatExpTotal
(set-totality-goal "NatExp")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatZero")

(assume "m^1" "Tm1" "IHm1")
(ng #t)
(use "NatTimesTotal")
(use "IHm1")
(use "Tn")
;; Proof finished.
;; (cp)
(save-totality)

;; NatLeOneTwoExp
(set-goal "all n Succ Zero<=(Succ(Succ Zero))**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLeTrans" (pt "Succ(Succ Zero)**n+Succ Zero"))
(use "Truth")
(use "NatLeMonPlus")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cp)
(save "NatLeOneTwoExp")

;; NatLeMonTwoExp
(set-goal "all n,m(n<=m -> 2**n<=2**m)")
(ind)
;; 2,3
(ng)
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<=m")
(ng)
(use "IH")
(use "n<=m")
;; Proof finished.
;; (cp)
(save "NatLeMonTwoExp")

(set-goal "all pos,nat (PosToNat pos**nat)=PosToNat(pos**nat)")
(assume "pos")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(simp "PosToNatTimes")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rules
 "(PosToNat pos)**nat" "PosToNat(pos**nat)")

;; Rules for PosLog

(add-computation-rules
 "PosLog 1" "Zero"
 "PosLog(SZero p)" "Succ(PosLog p)"
 "PosLog(SOne p)" "Succ(PosLog p)")

(set-totality-goal "PosLog")
(use "AllTotalElim")
(ind)
(use "TotalNatZero")
(assume "p" "IH")
(ng)
(use "TotalNatSucc")
(use "IH")
(assume "p" "IH")
(ng)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "PosLog 8")))
;; Succ(Succ(Succ Zero))

;; PosLogEqP
(set-goal "all p^,q^(EqPPos p^ q^ -> EqPNat(PosLog p^)(PosLog q^))")
(assume "p^" "q^" "EqPpq")
(elim "EqPpq")
;; 3-5
(ng #t)
(use "EqPNatZero")
;; 4
(assume "p^1" "q^1" "EqPp1q1" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; 5
(assume "p^1" "q^1" "EqPp1q1" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLogEqP")

;; PosLogZero
(set-goal "all p (PosLog p=Zero)=(p=1)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLogZero")

;; PosLogZeroLt
(set-goal "all p (Zero<PosLog p)=(1<p)")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLogZeroLt")

;; PosLtZeroLog
(set-goal "all p(1<p -> Zero<PosLog p)")
(cases)
;; 2-4
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "Useless")
(use "Truth")
;; 4
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLtZeroLog")

;; PosLeExpTwoLog
(set-goal "all p 2**PosLog p<=p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng #t)
(use "IH")
(assume "p" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLeExpTwoLog")

;; PosLtExpTwoSuccLog
(set-goal "all p p<2**Succ(PosLog p)")
(ind)
(use "Truth")
(assume "p")
(ng #t)
(assume "IH")
(use "IH")
(assume "p")
(ng #t)
(assume "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLtExpTwoSuccLog")

;; PosLeMonLog
(set-goal "all p,q(p<=q -> PosLog p<=PosLog q)")
(ind)
;; 2-4
(assume "q" "Useless")
(use "Truth")
;; 3
(assume "p" "IH")
(cases)
;; 7-9
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 8
(use "IH")
;; 9
(use "IH")
;; 4
(assume "p" "IH")
(cases)
;; 13-15
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 14
(assume "q" "p<q")
(ng)
(inst-with-to "PosLtToLe" (pt "p") (pt "q") "p<q" "p<=q")
(use "IH")
(use "p<=q")
;; 15
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLeMonLog")

;; PosExpNatPlus
(set-goal "all p,n,m p**(n+m)=p**n*p**m")
(assume "p" "n")
(ind)
(ng #t)
(use "Truth")
;; Step
(assume "n0" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosExpNatPlus")

;; PosExpTwoNatPlus
(set-goal "2**n*2**m=2**(n+m)")
(assume "n")
(ind)
(ng)
(use "Truth")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosExpTwoNatPlus")

;; PosExpPlus
(set-goal "all p,q,r p**(q+r)=p**q*p**r")
(assume "p" "q" "r")
(simp "PosToNatPlus")
(use "PosExpNatPlus")
;; Proof finished.
;; (cp)
(save "PosExpPlus")

;; PosExpTwoPosPlus
(set-goal "all p,q 2**p*2**q=2**(p+q)")
(assume "p" "q")
(simp "PosToNatPlus")
(use "PosExpTwoNatPlus")
;; Proof finished.
;; (cp)
(save "PosExpTwoPosPlus")

;; PosExpTimes
(set-goal "all p,q,r p**(q*r)=p**q**r")
(assume "p" "q")
(ind)
;; 3-5
(use "Truth")
;; 4
(assume "r" "IH")
(ng #t)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "NatDoublePlusEq")
(simp "PosExpNatPlus")
(simp "PosExpNatPlus")
(simp "IH")
(use "Truth")
;; 5
(assume "r" "IH")
(ng #t)
(simp "PosToNatPlus")
(ng #t)
(simp "PosExpNatPlus")
(simp "<-" "NatDoublePlusEq")
(simp "<-" "NatDoublePlusEq")
(simp "PosExpNatPlus")
(simp "PosExpNatPlus")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosExpTimes")

(set-goal "all p,q p--q<=p")
(assert "all p,q(p<=q -> p--q<=p)")
(ind)
;; 4-6
(strip)
(use "Truth")
;; 5
(assume "p" "IH")
(cases)
;; 9-11
(strip)
(use "Truth")
;; 10
(use "IH")
;; 11
(assume "q" "p<=q")
(ng)
(use "PosLeTrans" (pt "SZero(p--q)"))
(use "Truth")
(use "IH")
(use "p<=q")
;; 6
(assume "p" "IH")
(cases)
;; 19-21
(strip)
(use "Truth")
;; 20
(assume "q" "p<q")
(ng)
(cases (pt "p=q"))
(strip)
(use "Truth")
(assume "p=q -> F")
(use "IH")
(use "PosLtToLe")
(use "p<q")
;; 21
(use "IH")
;; Assertion proved
(assume "Assertion" "p" "q")
(use "PosLeLtCases" (pt "p") (pt "q"))
(use "Assertion")
(drop "Assertion")
;; ?_34:q<p -> p--q<=p
(assume "q<p")
(simp "<-" "PosToNatLe")
(simp "PosToNatMinus")
(ng)
(use "Truth")
(use "q<p")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p--q<=p" "True")

(set-goal "all p p<=SZero p")
(ind)
(use "Truth")
(assume "p" "IH")
(ng)
(use "IH")
(assume "p" "IH")
(ng)
(use "PosLeLtTrans" (pt "SZero p"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=SZero p" "True")

;; Added 2023-10-09

;; PosExpSZero
(set-goal "all p p**SZero q=p**q*p**q")
(assume "p" "q")
(ng #t)
(simp "<-" "NatDoublePlusEq")
(use "PosExpNatPlus")
;; Proof finished.
;; (cp)
(save "PosExpSZero")

;; PosTimesCompat
(set-goal "all p,q,r,r0(p=q -> r=r0 -> p*r=q*r0)")
(assume "p" "q" "r" "r0" "p=q" "r=r0")
(simp "p=q")
(simp "r=r0")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesCompat")

;; PosExpNatTimes
(set-goal "all p,q,n p**n*q**n=(p*q)**n")
(assume "p" "q")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(simp "<-" "IH")
(use "PosTimesCompat")
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(use "PosTimesCompat")
(use "Truth")
(use "PosTimesComm")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosExpNatTimes")

;; Parentheses for * and **: if both appear, then ** binds stronger.
;; Else association to the left.

;; (ppn (pt "p*q**r"))
;; (p PosTimes (q PosExp (PosToNat r)))
;; (ppn (pt "p*(q**r)"))
;; (p PosTimes (q PosExp (PosToNat r)))
;; (ppn (pt "(p*q)**r"))
;; ((p PosTimes q) PosExp (PosToNat r))

;; (ppn (pt "p**q*r"))
;; ((p PosExp (PosToNat q)) PosTimes r)
;; (ppn (pt "(p**q)*r"))
;; ((p PosExp (PosToNat q)) PosTimes r)
;; (ppn (pt "p**(q*r)"))
;; (p PosExp (PosToNat (q PosTimes r)))

;; (ppn (pt "p**q**r"))
;; ((p PosExp (PosToNat q)) PosExp (PosToNat r))
;; (ppn (pt "(p**q)**r"))
;; ((p PosExp (PosToNat q)) PosExp (PosToNat r))
;; (ppn (pt "p**(q**r)"))
;; (p PosExp (PosToNat (q PosExp (PosToNat r))))

;; Added 2023-04-16

;; NatLtZeroPosToNat
(set-goal "all p Zero<PosToNat p")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "p" "IH")
(use "NatLtLeTrans" (pt "PosToNat p"))
(use "IH")
(simp "PosToNatLe")
(use "Truth")
;; 4
(assume "p" "IH")
(use "NatLtLeTrans" (pt "PosToNat p"))
(use "IH")
(simp "PosToNatLe")
(use "PosLeTrans" (pt "SZero p"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroPosToNat")

;; PosToNatNotZero
(set-goal "all p(PosToNat p=Zero -> F)")
(assume "p" "p=0")
(assert "PosToNat p<=Zero")
(use "p=0")
;; Assertion proved.
(assume "p<=0")
(assert "PosToNat p<PosToNat p")
(use "NatLeLtTrans" (pt "Zero"))
(use "p<=0")
(use "NatLtZeroPos")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PosToNatNotZero")

;; PosLeMonPosExp
(set-goal "all p,n,m(n<=m -> p**n<=p**m)")
(assume "p")
(ind)
;; 3,4
(strip)
(use "Truth")
;; 4
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
(save "PosLeMonPosExp")

(set-goal "all p,q p<=p**q")
(assume "p")
(ind)
;; 3,4
(use "Truth")
;; 4
(assume "q" "IH")
(ng #t)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosToNatPlus")
(simp "PosExpPlus")
(use "PosLeTrans" (pt "p**q*1"))
(use "IH")
(use "PosLeMonTimes")
(use "Truth")
(use "Truth")
;; 5
(assume "q" "IH")
(ng #t)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosToNatPlus")
(use "PosLeTrans" (pt "1*p"))
(use "Truth")
(use "PosLeMonTimes")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<=p**q" "True")

;; (set-goal "all p 2<=2**p")
;; (ind)
;; (use "Truth")
;; (assume "p" "IH")
;; (ng)
;; (simp "<-" "NatDoublePlusEq")
;; (simp "<-" "PosExpTwoNatPlus")
;; (use "PosLeTrans" (pt "2*2"))
;; (use "Truth")
;; (use "PosLeMonTimes")
;; (use "IH")
;; (use "IH")
;; ;; 4
;; (assume "p" "IH")
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cp)
;; (add-rewrite-rule "2<=2**p" "True")

(set-goal "all p p<2**p")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "p" "IH")
(ng)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosExpTwoNatPlus")
(simp (pf "SZero p=2*p"))
(use "PosLeLtTrans" (pt "2**p*p"))
(use "PosLeMonTimes")
(use "Truth")
(use "Truth")
(use "PosLeLtMonTimes")
(use "Truth")
(use "IH")
(use "Truth")
;; 4
(assume "p" "IH")
(ng)
(simp "<-" "NatDoublePlusEq")
(simp "<-" "PosExpTwoNatPlus")
;; ?^20:p<2**p*2**p
(use "PosLeLtTrans" (pt "p*1"))
(use "Truth")
(use "PosLtLeMonTimes")
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "p<2**p" "True")

(set-goal "all p 1<2**p")
(assume "p")
(use "PosLeLtTrans" (pt "p"))
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(add-rewrite-rule "1<2**p" "True")

;; TwoExpNatLe
(set-goal "all n,m (2**n<=2**m)=(n<=m)")
(ind)
;; 2,3
(cases)
;; 4,5
(use "Truth")
;; 5
(ng)
(assume "n")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 9.10
(ng)
(use "Truth")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "TwoExpNatLe")

;; TwoExpNatLt
(set-goal "all n,m (2**n<2**m)=(n<m)")
(ind)
;; 2,3
(cases)
;; 4,5
(use "Truth")
;; 5
(ng)
(assume "n")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 9,10
(ng)
(use "Truth")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "TwoExpNatLt")

;; TwoExpPosLe
(set-goal "all p,q (2**p<=2**q)=(p<=q)")
(assume "p" "q")
(inst-with-to "TwoExpNatLe" (pt "PosToNat p") (pt "PosToNat q") "Inst")
(simp "Inst")
(use "PosToNatLe")
;; Proof finished.
;; (cp)
(save "TwoExpPosLe")

;; NatToPosNatPlusSucc
(set-goal "all p,n NatToPos(p+Succ n)=PosS(NatToPos(p+n))")
(assume "p" "n")
(simp "NatPlus1CompRule")
(simp "SuccPosS")
(use "Truth")
(use "NatLeLtTrans" (pt "Zero+n"))
(use "Truth")
(simp "NatLt3RewRule")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "NatToPosNatPlusSucc")

;; NatLePlusTimes
(set-goal "all n,m(2<=n -> 2<=m -> n+m<=n*m)")
(assert "all n,m (n+2)+(m+2)<=(n+2)*(m+2)")
(assume "n" "m")
(simp "NatTimesPlusDistr")
(simp "NatTimesPlusDistrLeft")
(simp "NatTimesPlusDistrLeft")
(ng)
(simp "<-" "NatPlus2RewRule")
(simp "<-" "NatPlus2RewRule")
(use "NatLeTrans" (pt "m+(n+n)"))
(simp "NatPlusComm")
(ng)
(use "Truth")
(ng)
(use "Truth")
;; Assertion proved.
(assume "NatLePlusTimesAux")
(assert "all n(2<=n -> n=Pred(Pred n)+2)")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; Assertion proved.
(assume "Assertion" "n" "m" "2<=n" "2<=m")
(simp (pf "n=Pred(Pred n)+2"))
(simp (pf "m=Pred(Pred m)+2"))
(use "NatLePlusTimesAux")
(use "Assertion")
(use "2<=m")
(use "Assertion")
(use "2<=n")
;; Proof finished.
;; (cp)
(save "NatLePlusTimes")

;; PosLePlusTimes
(set-goal "all p,q(2<=p -> 2<=q -> p+q<=p*q)")
(assume "p" "q" "2<=p" "2<=q")
(simp "<-" "PosToNatLe")
(simp "PosToNatPlus")
(simp "PosToNatTimes")
(use "NatLePlusTimes")
(simp "PosToNatLe")
(use "2<=p")
(simp "PosToNatLe")
(use "2<=q")
;; Proof finished.
;; (cp)
(save "PosLePlusTimes")

;; PosLeMonPosExpPos
(set-goal "all r,p,q(p<=q -> r**p<=r**q)")
(assume "r" "p" "q" "p<=q")
(assert "NatLe p q")
(simp "PosToNatLe")
(use "p<=q")
(use "PosLeMonPosExp")
;; Proof finished.
;; (cp)
(save "PosLeMonPosExpPos")

;; Parallel to PosLeMonTimes we prove PosLeMonExp:

;; PosLeMonExpBase
(set-goal "all p,q(p<=q -> all n p**n<=q**n)")
(assume "p" "q" "p<=q")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "PosLeMonTimes")
(use "IH")
(use "p<=q")
;; Proof finished.
;; (cp)
(save "PosLeMonExpBase")

;; PosLeMonExp
(set-goal "all p,q,r,r0(p<=q -> r<=r0 -> p**r<=q**r0)")
(assume "p" "q" "r" "r0" "p<=q" "r<=r0")
(use "PosLeTrans" (pt "q**r"))
;; 3,4
;; ?^3:p**r<=q**r
(use "PosLeMonExpBase")
(use "p<=q")
;; ?^4:q**r<=q**r0
(use "PosLeMonPosExpPos")
(use "r<=r0")
;; Proof finished.
;; (cp)
(save "PosLeMonExp")

;; PosLeTimesTwoExp
(set-goal "all p 2*p<=2**p")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "p" "IH")
;; ?^5:2*SZero p<=2**SZero p
(simp "PosTimes1CompRule")
(simp "SZeroPosPlus")
(simp (pf "SZero p=p+p"))
(simp "<-" "PosExpTwoPosPlus")
(use "PosLeTrans" (pt "2**p+2**p"))
(use "PosLeMonPlus")
(use "IH")
(use "IH")
(use "PosLePlusTimes")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "SZeroPosPlus")
;; 4
(assume "p" "IH")
(simp "PosTimes2CompRule")
(simp "PosToNat2CompRule")
(simp "PosExp1CompRule")
(assert "all q q*2=q+q")
(assume "q")
(ng #t)
(use "SZeroPosPlus")
;; Assertion proved.
(assume "Assertion")
(simp "Assertion")
(use "PosLeMonPlus")
;; ?^33:SZero(2*p)<=2**SZero p
(simp (pf "SZero(2*p)=2*p+2*p"))
;; 35,36
(simp (pf "SZero p=p+p"))
(simp "<-" "PosExpTwoPosPlus")
(use "PosLeTrans" (pt "2**p+2**p"))
(use "PosLeMonPlus")
(use "IH")
(use "IH")
(use "PosLePlusTimes")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
(use "SZeroPosPlus")
;; 36
(use "SZeroPosPlus")
(use "PosLeTrans" (pt "2**1"))
(use "Truth")
(use "PosLeMonPosExpPos")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLeTimesTwoExp")

(set-goal "all p (2**p<=1)=False")
(assume "p")
(use "AtomFalse")
(assume "LeH")
(assert "2*p<=1")
(use "PosLeTrans" (pt "2**p"))
(use "PosLeTimesTwoExp")
(use "LeH")
;; Assertion proved.
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(add-rewrite-rule "2**p<=1" "False")

;; PosTwoExpEqOneFalse
(set-goal "all p (2**p=1)=False")
(assume "p")
(use "AtomFalse")
(assume "2**p=1")
(assert "2**p<=1")
(simp "2**p=1")
(use "Truth")
(simp "PosLe18RewRule")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "PosTwoExpEqOneFalse")

;; SZeroPosTimes
(set-goal "all p SZero p=2*p")
(ind)
(use "Truth")
(assume "p" "IH")
(use "Truth")
(assume "p" "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "SZeroPosTimes")

;; PosMinusOnePred
(set-goal "all p(1<p -> p--1=PosPred p)")
(cases)
;; 2-4
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; 3
(assume "p" "Useless")
(use "Truth")
;; 4
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosMinusOnePred")

;; PosLtMonPosExpTwo
(set-goal "all n,m(n<m -> 2**n<2**m)")
(ind)
;; 3,4
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; 4
(assume "n" "IH")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLtMonPosExpTwo")

;; PosLtMonPosExpTwoPos
(set-goal "all p,q(p<q -> 2**p<2**q)")
(assume "p" "q" "p<q")
(assert "NatLt p q")
(simp "PosToNatLt")
(use "p<q")
(use "PosLtMonPosExpTwo")
;; Proof finished.
;; (cp)
(save "PosLtMonPosExpTwoPos")

;; Added 2024-01-05

;; PosLeTimesExpAux
(set-goal "all q(all p(2<=p -> p*q<=p**q) ->
 all p(2<=p -> p*SZero q<=p**SZero q))")
(assume "q" "qH" "p" "2<=p")
;; ?^2:p*SZero q<=p**SZero q

(assert "SZero(p*q)<=p**NatDouble(PosToNat q)")
(simp "SZeroPosPlus")
(simp "<-" "NatDoublePlusEq")
(simp "PosExpNatPlus")
(use "PosLeTrans" (pt "p**q+p**q"))
(use "PosLeMonPlus")
(use "qH")
(use "2<=p")
(use "qH")
(use "2<=p")
(use "PosLePlusTimes")
(use "PosLeTrans" (pt "p"))
(use "2<=p")
;; ?^17:p<=p**q
;; Add this as a rewrite rule, replacing 2<=2**p -> True.  Done here.
(use "Truth")
(use "PosLeTrans" (pt "p"))
(use "2<=p")
(use "Truth")
;; Assertion proved.
(assume "Assertion1")

(cases (pt "p"))
;; 21-23
(assume "p=1")
(simphyp-with-to "2<=p" "p=1" "Absurd")
(ng "Absurd")
(efproof)
;; 22
(assume "r" "p=SZero r")
(simp "<-" "p=SZero r")
(ng #t)
(use "Assertion1")
;; 23
(assume "r" "p=SOne r")
(simp "<-" "p=SOne r")
;; ?^32:p*SZero q<=p**SZero q
;; This is done as before.
(ng #t)
(use "Assertion1")
;; Proof finished.
;; (cp)
(save "PosLeTimesExpAux")

;; We use PosLeTimesExpAux to simplify PosLeTimesExp

;;  PosLeTimesExp
(set-goal "all q,p(2<=p -> p*q<=p**q)")
(ind)
;; 2,3
(assume "p" "Useless")
(use "Truth")
;; 3
(assume "q" "IH" "p" "2<=p")
;; ?^6:p*SZero q<=p**SZero q
(use "PosLeTimesExpAux")
(use "IH")
(use "2<=p")
;; 4
(assume "q" "IH" "p" "2<=p")
;; ?^9: p*SOne q<=p**SOne q
(simp (pf "p*SOne q=p*SZero q+p"))
(use "PosLeTrans" (pt "p**SZero q+p"))
;; ?^12:p*SZero p+p<=p**SZero q+p
(use "PosLeMonPlus")
(use "PosLeTimesExpAux")
(use "IH")
(use "2<=p")
(use "Truth")
;; ?^13:p**SZero q+p<=p**SOne q
(simp (pf "SOne q=SZero q+1"))
(get 19)
(use "Truth")
;; ?^18:p**SZero q+p<=p**(SZero q+1)
(simp "PosExpPlus")
(use "PosLePlusTimes")
;; ?^21:2<=p**NatDouble(PosToNat q)
(use "PosLeTrans" (pt "p**Succ Zero"))
(use "2<=p")
(use "PosLeMonPosExp")
(use "NatLtToSuccLe")
(use "NatLeLtTrans" (pt "PosToNat q"))
(use "Truth")
(use "NatLtDouble")
;; ?^29:Zero<q
;; This should rewrite to True
(use "NatLtZeroPos")
(use "2<=p")
;; ?^11:p*SOne q=p*SZero q+p
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLeTimesExp")

;; Added 2021-08-22

;; PosLeMonNatToPos
(set-goal "all n,m(n<=m -> NatToPos n<=NatToPos m)")
(cases)
;; 2,3
(assume "m" "Useless")
(use "Truth")
;; 3
(assume "n")
(cases)
;; 6,7
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
;; ?^7:all n0(Succ n<=Succ n0 -> NatToPos(Succ n)<=NatToPos(Succ n0))
(assume "m" "n<=m")
(simp "NatToPosLe")
(use "n<=m")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLeMonNatToPos")

;; PosLeMoncNatPos
(set-goal "all n,m(n<=m -> cNatPos n<=cNatPos m)")
(assume "n" "m" "n<=m")
(simp "NatPosExFree")
(simp "NatPosExFree")
(use "PosLeMonNatToPos")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "PosLeMoncNatPos")

;; NatEvenTwoExp
(set-goal "all n(Zero<n -> NatEven(PosToNat(2**n)))")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Useless")
(ng #t)
(use "NatEvenDouble")
;; Proof finished.
;; (cp)
(save "NatEvenTwoExp")

;; NatLePosExpNatF
(set-goal "all n 2**n<=NatF(Succ n)")
(ind)
(use "Truth")
(assume "n" "IH")
(simp "PosExp1CompRule" (pt "2"))
(simp "NatF1CompRule")
(simp "PosToNatTimes")
(use "NatLeMonTimes")
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLePosExpNatF")

;; Added 2021-10-15

;; NatLePosExpTwo
(set-goal "all n Succ Zero<=2**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
;; ?^5:Succ Zero<=NatDouble(PosToNat(2**n))
(use "NatLeTrans" (pt "PosToNat(2**n)"))
(use "IH")
(use "NatLeDouble")
;; Proof finished.
;; (cp)
(save "NatLePosExpTwo")

;; ZeroLtTwoExp
(set-goal "all n Zero<2**n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLt0Double")
(use "IH")
;; Proof finished.
;; (cp)
(save "ZeroLtTwoExp")

(add-program-constant "PosEven" (py "pos=>boole"))
(add-computation-rules
 "PosEven 1" "False"
 "PosEven(SZero p)" "True"
 "PosEven(SOne p)" "False")

(set-totality-goal "PosEven")
(fold-alltotal)
(cases)
;; 3-5
(use "TotalVar")
;; 4
(assume "p")
(use "TotalVar")
;; 5
(assume "p")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

(add-program-constant "PosOdd" (py "pos=>boole"))
(add-computation-rules
 "PosOdd 1" "True"
 "PosOdd(SZero p)" "False"
 "PosOdd(SOne p)" "True")

(set-totality-goal "PosOdd")
(fold-alltotal)
(cases)
;; 3-5
(use "BooleTotalVar")
;; 4
(assume "p")
(use "BooleTotalVar")
;; 5
(assume "p")
(use "BooleTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; In 2**n*p with p odd both n and p are uniquely determined.  They can
;; obtained by PosToExp and PosToOdd.

;; PosToExp returns the exponent of two in the prime factor
;; decomposition of a positive number.

(add-program-constant "PosToExp" (py "pos=>nat"))
(add-computation-rules
 "PosToExp 1" "Zero"
 "PosToExp(SZero p)" "Succ(PosToExp p)"
 "PosToExp(SOne p)" "Zero")

(set-totality-goal "PosToExp")
(fold-alltotal)
(ind)
;; 3-5
(use "NatTotalVar")
;; 4
(assume "p" "IH")
(use "TotalNatSucc")
(use "IH")
;; 5
(assume "p" "Useless")
(use "NatTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; PosToOdd returns the odd part of a positive number,
(add-program-constant "PosToOdd" (py "pos=>pos"))
(add-computation-rules
 "PosToOdd 1" "1"
 "PosToOdd(SZero p)" "PosToOdd p"
 "PosToOdd(SOne p)" "SOne p")

(set-totality-goal "PosToOdd")
(fold-alltotal)
(ind)
;; 3-5
(use "PosTotalVar")
;; 4
(assume "p" "IH")
(use "IH")
;; 5
(assume "p" "Useless")
(use "PosTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; PosTimesExpOddId
(set-goal "all p 2**PosToExp p*PosToOdd p=p")
(ind)
;; 2-4
(use "Truth")
(assume "p" "IH")
(use "IH")
;; 4
(ng)
(assume "p" "Useless")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesExpOddId")

;; PosToExpEq
(set-goal "all n PosToExp(2**n)=n")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "PosToExpEq")

;; PosToOddEq
(set-goal "all n PosToOdd(2**n)=1")
(ind)
;; 2,3
(use "Truth")
;; 3
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "PosToOddEq")

;; PosToExpTimesSOneEq
(set-goal "all p,n PosToExp(2**n*SOne p)=n")
(cases)
;; 2-4
(ind)
;; 5,6
(ng)
(use "Truth")
;; 6
(assume "n" "IH")
(ng)
(use "IH")
;; 3
(assume "p")
(ind)
;; 11,12
(ng)
(use "Truth")
;; 12
(assume "n" "IH")
(ng)
(use "IH")
;; 4
(assume "p")
(ind)
;; 17,18
(ng)
(use "Truth")
;; 19
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosToExpTimesSOneEq")

;; PosToExpTimesEq
(set-goal "all n,p(PosOdd p -> PosToExp(2**n*p)=n)")
(assume "n")
(cases)
;; 3-5
(assume "Useless")
(use "PosToExpEq")
;; 4
(assume "p" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 5
(assume "p" "Useless")
(use "PosToExpTimesSOneEq")
;; Proof finished.
;; (cp)
(save "PosToExpTimesEq")

;; PosToOddTimesSOneEq
(set-goal "all p,n PosToOdd(2**n*SOne p)=SOne p")
(cases)
;; 2-4
(ind)
;; 5,6
(use "Truth")
;; 6
(assume "n" "IH")
(use "IH")
;; 3
(assume "p")
(ind)
;; 9,10
(use "Truth")
;; 10
(assume "n" "IH")
(ng)
(use "IH")
;; 4
(assume "p")
(ind)
;; 14,15
(use "Truth")
;; 15
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosToOddTimesOneEq")

;; PosToOddTimesEq
(set-goal "all p,n(PosOdd p -> PosToOdd(2**n*p)=p)")
(ind)
;; 2-4
(assume "n" "Useless")
(ng)
(use "PosToOddEq")
;; 3
(assume "p" "IH" "n" "Absurd")
(use "EfAtom")
(use "Absurd")
;; 4
(assume "p" "IH" "n" "Useless")
(use "PosToOddTimesOneEq")
;; Proof finished.
;; (cp)
(save "PosToOddTimesEq")

;; Already defined, with reversed equality.
;; ;; NatToPosDouble
;; (set-goal "all n(Zero<n -> SZero(NatToPos n)=NatToPos(NatDouble n))")
;; (assume "n" "0<n")
;; (simp "<-" "NatDoublePlusEq")
;; (simp "NatToPosPlus")
;; (use "SZeroPosPlus")
;; (use "0<n")
;; (use "0<n")
;; ;; Proof finished.
;; ;; (cp)
;; (save "NatToPosDouble")

;; PosLogTwoExp
(set-goal "all n PosLog(2**n)=n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cp)
(save "PosLogTwoExp")
;; (add-rewrite-rule "PosLog(2**n)" "n")

;; PosLogTimes
(set-goal "all n,p PosLog(p*2**n)=PosLog p+n")
(ind)
;; 2,3
(assume "p")
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 6-8
(ng #t)
(use "PosLogTwoExp")
;; 7
(assume "p")
(ng #t)
(use "IH")
;; 8
(assume "p")
(ng #t)
(simp (pf "SZero(p*2**n)+2**n=SOne p*2**n"))
(simp "IH")
(ng #t)
(use "Truth")
;; ?^15:SZero(p*2**n)+2**n=SOne p*2**n
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosLogTimes")

;; PosLogTimes cannot be generalized to arbitrary arguments.  Counterexample:
;; (pp (nt (pt "PosLog 6"))) ;2
;; (pp (nt (pt "PosLog 7"))) ;2
;; (pp (nt (pt "PosLog 42"))) ;5

;; PosLeTwoExpToEqTwoExpTimes
(set-goal "all n,m(2**n<=2**m -> 2**m=2**n*2**(m--n))")
(assume "n" "m" "LeH")
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(simp "NatMinusPlusEq")
(use "Truth")
(simp "<-" "TwoExpNatLe")
(use "LeH")
;; Proof finished.
;; (cp)
(save "PosLeTwoExpToEqTwoExpTimes")

;; PosLogMax
(set-goal "all p,q PosLog(p max q)=PosLog p max PosLog q")
(assume "p" "q")
(use "NatLeAntiSym")
;; 3,4
(cases (pt "p<=q"))
;; 5,6
(assume "p<=q")
(simp "PosMaxEq2")
(use "NatMaxUB2")
(use "p<=q")
;; 6
(assume "Notp<=q")
(simp "PosMaxEq1")
(use "NatMaxUB1")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
;; 4
(cases (pt "p<=q"))
;; 15,16
(assume "p<=q")
(simp "PosMaxEq2")
(use "NatMaxLUB")
(use "PosLeMonLog")
(use "p<=q")
(use "Truth")
(use "p<=q")
;; 16
(assume "Notp<=q")
(simp "PosMaxEq1")
(use "NatMaxLUB")
(use "Truth")
(use "PosLeMonLog")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
(use "PosLtToLe")
(use "PosNotLeToLt")
(use "Notp<=q")
;; Proof finished.
;; (cp)
(save "PosLogMax")

;; NatToPosMax
(set-goal "all n,m NatToPos(n max m)=NatToPos n max NatToPos m")
(assume "n" "m")
(use "PosLeAntiSym")
;; 3,4
(cases (pt "n<=m"))
;; 5,6
(assume "n<=m")
(simp "NatMaxEq2")
(use "PosMaxUB2")
(use "n<=m")
;; 6
(assume "Notn<=m")
(simp "NatMaxEq1")
(use "PosMaxUB1")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
;; 4
(cases (pt "n<=m"))
;; 15,16
(assume "n<=m")
(simp "NatMaxEq2")
(use "PosMaxLUB")
(use "PosLeMonNatToPos")
(use "n<=m")
(use "Truth")
(use "n<=m")
;; 16
(assume "Notn<=m")
(simp "NatMaxEq1")
(use "PosMaxLUB")
(use "Truth")
(use "PosLeMonNatToPos")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "Notn<=m")
;; Proof finished.
;; (cp)
(save "NatToPosMax")

;; PosLeBoundSharp
(set-goal "all p(1<p -> exl n(2**Pred n<p andnc p<=2**n))")
(assume "p" "1<p")
(cases (pt "2**PosLog p<p"))
;; 3,4
(assume "LtHyp")
(intro 0 (pt "Succ(PosLog p)"))
(split)
;; 7,8
(use "LtHyp")
;; 8
(use "PosLtToLe")
(use "PosLtExpTwoSuccLog")
;; 4
(assume "NotLtHyp")
(assert "p<=2**PosLog p")
(use "PosNotLtToLe")
(use "NotLtHyp")
;; Assertion proved
(assume "LeHyp")
(drop "NotLtHyp")
(use "PosLeCases" (pt "p") (pt "2**PosLog p"))
;; 16,17
(use "LeHyp")
(drop "LeHyp")
(assume "LtHyp")
(assert "p<p")
(use "PosLtLeTrans" (pt "2**PosLog p"))
(use "LtHyp")
(use "PosLeExpTwoLog")
(assume "Absurd")
(intro 0 (pt "Zero"))
(split)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
;; 18
(assume "EqHyp")
(intro 0 (pt "PosLog p"))
(split)
;; 33,34
(assert "2**Pred(PosLog p)<2**PosLog p")
;; 35,36
(use "PosLtMonPosExpTwo")
(use "NatLtLeTrans" (pt "Succ(Pred(PosLog p))"))
(use "Truth")
(simp "NatSuccPred")
(use "Truth")
(simp "PosLogZeroLt")
(use "1<p")
;; 35
(assume "LtHyp")
(use "PosLtLeTrans" (pt "2**PosLog p"))
(use "LtHyp")
(use "PosLeExpTwoLog")
(use "LeHyp")
;; Proof finished.
;; (cp)
(save "PosLeBoundSharp")

;; (define eterm (proof-to-extracted-term))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [p]
;;  [if (2**PosLog p<p)
;;    (Succ(PosLog p))
;;    ((cPosLeCases nat)p(2**PosLog p)Zero(PosLog p))]

;; (animate "PosLeCases")

;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [p]
;;  [if (2**PosLog p<p)
;;    (Succ(PosLog p))
;;    [if (NatLt(PosToNat p)(PosToNat(2**PosLog p))) Zero (PosLog p)]]

;; (deanimate "PosLeCases")

;; Added 2023-04-16

(add-program-constant "PosF" (py "nat=>pos"))
(add-computation-rules
 "PosF Zero" "One"
 "PosF(Succ n)" "PosF n*NatToPos(Succ n)")

(set-totality-goal "PosF")
(fold-alltotal)
(ind)
(use "TotalVar")
(assume "n" "Tn")
(ng #t)
(use "PosTimesTotal")
(use "Tn")
(use "TotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; PosFToNatF
(set-goal "all n PosToNat(PosF n)=NatF n")
(ind)
(use "Truth")
(assume "n" "IH")
(simp "PosF1CompRule")
(simp "PosToNatTimes")
(simp "PosToNatToPosId")
(simp "IH")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosFToNatF")

;; NatFToPosF
(set-goal "all n NatToPos(NatF n)=PosF n")
(assume "n")
(use "PosEqTrans" (pt "NatToPos(PosToNat(PosF n))"))
(simp "PosFToNatF")
(use "Truth")
(use "NatToPosToNatId")
;; Proof finished.
;; (cp)
(save "NatFToPosF")

;; NatLeOneNatF
(set-goal "all n Succ Zero<=NatF n")
(ind)
(use "Truth")
(assume "n" "IH")
(simp "<-" "PosFToNatF")
(use "NatLtToSuccLe")
(use "NatLtZeroPos")
;; Proof finished.
;; (cp)
(save "NatLeOneNatF")

;; PosTimesChoosePosF
(set-goal "all n,m(m<=n -> NatToPos(Choose n m)*PosF(n--m)*PosF m=PosF n)")
(assume "n" "m" "m<=n")
(simp "<-" "NatFToPosF")
(simp "<-" "NatToPosTimes")
(simp "<-" "NatFToPosF")
(simp "<-" "NatToPosTimes")
(simp "NatTimesChooseNatF")
(use "NatFToPosF")
(use "m<=n")
(use "NatLtZeroNatF")
(use "NatSuccLeToLt")
(simp (pf "Succ Zero=Succ Zero*Succ Zero"))
(use "NatLeMonTimes")
(use "NatLeToLeOneChoose")
(use "m<=n")
(use "NatLeOneNatF")
(use "Truth")
(use "NatLtZeroNatF")
(use "NatLeToLtZeroChoose")
(use "m<=n")
;; Proof finished.
;; (cp)
(save "PosTimesChoosePosF")

;; Added 2024-01-05

;; NatLeMonExpR
(set-goal "all l(Zero<l -> all n,m(n<=m -> l**n<=l**m))")
(assume "l" "0<l" "n")
(ind)
(assume "n=0")
(simp "n=0")
(use "Truth")
;; 4
(assume "m" "IH" "n<=m+1")
(ng #t)
(use "NatLeCases" (pt "n") (pt "Succ m"))
(use "n<=m+1")
(assume "n<m+1")
(use "NatLeTrans" (pt "l**m*(Succ Zero)"))
(use "IH")
(use "NatLtSuccToLe")
(use "n<m+1")
;; ?^14:l**m*Succ Zero<=l**m*l
(use "NatLeMonTimes")
(use "Truth")
(use "NatLtToSuccLe")
(use "0<l")
;; ?^11:n=Succ m -> l**n<=l**m*l
(assume "n=m+1")
(simp "n=m+1")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLeMonExpR")

;; NatLtZeroExp
(set-goal "all m(Zero<m -> all n Zero<m**n)")
(cases)
;; 2,3
(assume "Absurd")
(ng "Absurd")
(efproof)
;; 3
(assume "m" "Useless")
(ind)
;; 7,8
(use "Truth")
;; 4
(assume "n" "IH")
(ng #t)
(use "NatLtLeTrans" (pt "Succ m**n"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "NatLtZeroExp")

;; We prove that NatToPos is an isomorphism w.r.t. **

;; PosToNatExp
(set-goal "all p,n PosToNat(p**n)=PosToNat p**n")
(assume "p")
(ind)
;; 3,4
(use "Truth")
;; 4
(assume "n" "IH")
(ng #t)
(simp "IH")
(simp "PosToNatTimes")
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosToNatExp")

;; NatToPosExp
(set-goal "all m(Zero<m -> all n NatToPos(m**n)=NatToPos m**n)")
(assume "m" "0<m")
(ind)
;; 3,4
(use "Truth")
;; 4
(assume "n" "IH")
(simp "NatExp1CompRule")
(simp "PosExp1CompRule")
(simp "<-" "IH")
(simp "NatToPosTimes")
(use "Truth")
(use "0<m")
(use "NatLtZeroExp")
(use "0<m")
;; Proof finished.
;; (cp)
(save "NatToPosExp")

;; Added 2025-02-15

;; PosLtPosToLtTimes
(set-goal "all p,q(1<p -> q<q*p)")
(assume "p" "q")
(simp "<-" "PosToNatLt")
(simp "<-" "PosToNatLt")
(simp "PosToNatTimes")
(assume 1)
(use "NatLtPosToLtTimes")
(use 1)
(use "NatLtZeroPos")
;; (cp)
(save "PosLtPosToLtTimes")

;; PosLeTimesPos
(set-goal "all p,q0,q1(q0<=q1 -> q0<=q1*p)")
(ind)
(strip)
(use 1)
(assume "p" 1 "q0" "q1" 2)
(ng)
(simp "SZeroPosPlus")
(use "PosLeTrans" (pt "q0+1"))
(use "Truth")
(use "PosLeMonPlus")
(use 1)
(use 2)
(use "Truth")
(assume "p" 1 "q0" "q1" 2)
(ng)
(use "PosLeTrans" (pt "q1"))
(use 2)
(use "Truth")
;; (cp)
(save "PosLeTimesPos")

;; PosLeNotEqToLt
(set-goal "all p, q(p<=q -> (p=q -> F) -> p<q)")
(strip)
(simp "<-" "PosToNatLt")
(use "NatLeNotEqToLt")
(simp "PosToNatLe")
(use 1)
(assume 3)
(use 2)
(use "PosToNatInj")
(use 3)
;; (cp)
(save "PosLeNotEqToLt")

;; PosExpTwoSucc
(set-goal "all n 2**n+2**n=2**Succ n")
(strip)
(use "PosEqSym")
(use "SZeroPosPlus")
;; (cp)
(save "PosExpTwoSucc")

;; PosThirdBinom
(set-goal "all q,p(q<p -> p*p--q*q=(p+q)*(p--q))")
(assume "q" "p" 1)
(use "PosToNatInj")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatPlus")
(use "NatThirdBinom")
(use 1)
(use "PosLtMonTimes")
(use 1)
(use 1)
;; (cp)
(save "PosThirdBinom")

;; PosSquare
;; =========

(add-program-constant "PosSquare" (py "pos=>pos"))
(add-computation-rules
 "PosSquare p" "p*p")

(set-totality-goal "PosSquare")
(fold-alltotal)
(assume "p")
(use "TotalVar")
;; (cp)
(save-totality)

;; PosLtMonSquare
(set-goal "all p,q(p<q->PosSquare p<PosSquare q)")
(strip)
(use "PosLtMonTimes")
(use 1)
(use 1)
;; (cp)
(save "PosLtMonSquare")

;; PosLeMonSquare
(set-goal "all p,q(p<=q->PosSquare p <=PosSquare q)")
(strip)
(use "PosLeMonTimes")
(use 1)
(use 1)
;; (cp)
(save "PosLeMonSquare")

;; PosLtMonSquareInv
(set-goal "all p,q(PosSquare q<PosSquare p -> q<p)")
(ng)
(strip)
(use "PosNotLeToLt")
(assume "2")
(assert "p*p<p*p")
(use "PosLeLtTrans" (pt "q*q"))
(use "PosLeMonSquare")
(use 2)
(use 1)
(search)
;; (cp)
(save "PosLtMonSquareInv")

;; PosLeMonSquareInv"
(set-goal "all p,q(PosSquare q<=PosSquare p -> q<=p)")
(ng)
(strip)
(use "PosNotLtToLe")
(assume "2")
(use "PosLeToNotLt" (pt "q*q") (pt "p*p"))
(use 1)
(use "PosLtMonSquare")
(use 2)
;; (cp)
(save "PosLeMonSquareInv")

;; ExBPos
;; ======

(add-var-name "wf" (py "pos=>boole"))

;; (remove-program-constant "ExBPos")
(add-program-constant "ExBPos" (py "pos=>(pos=>boole)=>boole"))
(add-computation-rules
 "ExBPos 1 wf" "wf 1"
 "ExBPos(SZero p)wf" "[if (ExBPos p wf) True (ExBPos p([q]wf(p+q)))]"
 "ExBPos(SOne p)wf" "[if (wf(SOne p)) True (ExBPos(SZero p)wf)]")

;; (pp (nt (pt "ExBPos 7([p](6<p))"))) ;True
;; (pp (nt (pt "ExBPos 6([p](6<p))"))) ;False

(set-totality-goal "ExBPos")
(fold-alltotal)
(ind)
(fold-alltotal)
(assume "wf")
(use "TotalVar")
(assume "p" 1)
(fold-alltotal)
(assume "wf")
(ng)
(use "BooleIfTotal")
(use 1)
(fold-alltotal)
(assume "p1")
(use "TotalVar")
(use "TotalVar")
(use 1)
(fold-alltotal)
(assume "p0")
(use "TotalVar")
(assume "p" 1)
(fold-alltotal)
(ng)
(assume "wf")
(use "BooleIfTotal")
(use "TotalVar")
(use "TotalVar")
(use "BooleIfTotal")
(use 1)
(fold-alltotal)
(assume "p0")
(use "TotalVar")
(use "TotalVar")
(use 1)
(fold-alltotal)
(assume "p0")
(use "TotalVar")
;; (cp)
(save-totality)

;; (display-pconst "ExBPos")
;; 0	ExBPos 1 wf	wf 1
;; 1	ExBPos(SZero p)wf	[if (ExBPos p wf) True (ExBPos p([q]wf(p+q)))]
;; 2	ExBPos(SOne p)wf	[if (wf(SOne p)) True (ExBPos(SZero p)wf)]

;; ExBPosIntro
(set-goal "all q,wf,p(p<=q -> wf p -> ExBPos q wf)")
(ind)
(assume "wf" "p" 1)
(simp 1)
(search)
(ng)
(assume "q" 1 "wf" "p" 2 3)
(cases (pt "p<=q"))
(assume 4)
(inst-with 1 (pt "wf") (pt "p") 4 3)
(simp 5)
(use "Truth")
(assume "4")
(inst-with "PosNotLeToLt" (pt "p") (pt "q") 4)
(inst-with 1 (pt "[p0]wf(q+p0)") (pt "p--q") "?" "?")
(simp 6)
(use "Truth")
(use "PosLeCases" (pt "p") (pt "SZero q"))
(use 2)
(assume 6)
(use "PosLtToLe")
(use "PosLtLeTrans" (pt "SZero q--q"))
(use "PosLtMonMinusLeft")
(use 6)
(use 5)
(simp "SZeroPosPlus")
(use "Truth")
(assume 6)
(simp 6)
(simp "SZeroPosPlus")
(use "Truth")
(ng)
(simp (pf "q+(p--q)=p"))
(use 3)
(simp "PosPlusComm")
(use "PosMinusPlusEq")
(use 5)
(assume "q" 1 "wf" "p" 2 3)
(simp "ExBPos2CompRule")
(cases (pt "wf(SOne q)"))
(assume 4)
(use "Truth")
(assume 4)
(simp "IfFalse")
(ng)
(cases (pt "p<=q"))
(assume 5)
(inst-with 1 (pt "wf") (pt "p") 5 3)
(simp 6)
(use "Truth")
(assume 5)
(inst-with "PosNotLeToLt" (pt "p") (pt "q") 5)
(inst-with 1 (pt "[p0]wf(q+p0)") (pt "p--q") "?" "?")
(simp 7)
(use "Truth")
(use "PosLeCases" (pt "p") (pt "SZero q"))
(use "PosLeCases" (pt "p") (pt "SOne q"))
(use 2)
(assume 7)
(simp "<-" "PosLtPosS")
(use 7)
(assume 7)
(use "EfAtom")
(use 4)
(simp "<-" 7)
(use 3)
(assume 7)
(use "PosLtToLe")
(use "PosLtLeTrans" (pt "SZero q--q"))
(use "PosLtMonMinusLeft")
(use 7)
(use 6)
(simp "SZeroPosPlus")
(use "Truth")
(assume 7)
(simp 7)
(simp "SZeroPosPlus")
(use "Truth")
(ng)
(simp (pf "q+(p--q)= p"))
(use 3)
(simp "PosPlusComm")
(use "PosMinusPlusEq")
(use 6)
;; (cp)
(save "ExBPosIntro")

;; ExBPosElim
(set-goal "all p,wf(ExBPos p wf -> all q(q<=p -> wf q -> Pvar) -> Pvar)")
(ind)
(strip)
(ng)
(use 2 (pt "1"))
(use "Truth")
(use 1)
(assume "p" 1 "wf" 2 3)
(ng 2)
(cases (pt "ExBPos p wf"))
(assume 4)
(use 1 (pt "wf"))
(use 4)
(assume "q" 5 6)
(use 3 (pt "q"))
(use "PosLeTrans" (pt "p"))
(use 5)
(use "Truth")
(use 6)
(assume 4)
(simphyp 2 4)
;; (simphyp 5 "OrConst2CompRule")
(use 1 (pt "[p0]wf(p+p0)"))
(cases (pt "ExBPos p wf"))
(assume 6)
(use "EfAtom")
(use 4)
(use 6)
(assume 6)
(simphyp 2 6)
(use 7)
(assume "q" 7 8)
(bpe-ng 7)
(use 3 (pt "p+q"))
(simp "SZeroPosPlus")
(use "PosLeMonPlus")
(use "Truth")
(use 6)
(use 7)
(assume "p" 1 "wf")
(ng #t)
(cases (pt "wf(SOne p)"))
(assume 2 3 4)
(use 4 (pt "SOne p"))
(use "Truth")
(use 2)
(assume 2)
(simp "IfFalse")
(assume 3)
(cases (pt "ExBPos p wf"))
(assume 4 5)
(use 1 (pt "wf"))
(use 4)
(assume "q" 6 7)
(use 5 (pt "q"))
(use "PosLeTrans" (pt "p"))
(use 6)
(use "PosLeTrans" (pt "SZero p"))
(use "Truth")
(use "Truth")
(use 7)
(assume 4 5) 
(simphyp 3 4)
;; (simphyp 6 "OrConst2CompRule")
(use 1 (pt "[p0]wf(p+p0)"))
(cases (pt "ExBPos p wf"))
(assume 7)
(use "EfAtom")
(use 4)
(use 7)
(assume 7)
(simphyp 3 7)
(use 8)
(assume "q" 7 8)
(bpe-ng 8)
(use 5 (pt "p+q"))
(use "PosLeTrans" (pt "SZero p"))
(simp "SZeroPosPlus")
(use "PosLeMonPlus")
(use "Truth")
(use 7)
(use "Truth")
(use 8)
;; (cp)
(save "ExBPosElim")

;; ExBPosToExNc
(set-goal "all wf,p(ExBPos p wf -> exnc q(q<=p andnc wf q))")
(assume "wf" "p" 1)
(use "ExBPosElim" (pt "p") (pt "wf"))
(use 1)
(assume "q" 2 3)
(intro 0 (pt "q"))
(split)
(use 2)
(use 3)
;; (cp)
(save "ExBPosToExNc")

;; PosProd
;; =======

(add-var-name "ps" "qs" (py "nat=>pos"))

(add-program-constant "PosProd" (py "nat=>nat=>(nat=>pos)=>pos"))

(add-computation-rules
 "PosProd n Zero ps" "1"
 "PosProd n(Succ m)ps" "PosProd n m ps*ps(n+m)")

(set-totality-goal "PosProd")
(assert "all ps,n,m TotalPos(PosProd n m ps)")
(assume "ps" "n")
(ind)
(ng #t)
(use "TotalVar")
(assume "m" 1)
(ng #t)
(use "PosTimesTotal")
(use 1)
(use "TotalVar")
(assume 1)
(fold-alltotal)
(assume "n")
(fold-alltotal)
(assume "m")
(fold-alltotal)
(assume "ps")
(use 1)
;; (cp)
(save-totality)

;;PosProdCompat
(set-goal "all ps,qs,n,m(
     all l(n<=l -> l<n+m -> ps l=qs l) -> PosProd n m ps=PosProd n m qs)")
(assume "ps" "qs" "n")
(ind)
(search)
(assume "m" 1 2)
(simp "PosProd1CompRule")
(simp "PosProd1CompRule")
(simp 1)
(simp 2)
(auto)
(strip)
(use 2)
(use 3)
(use "NatLtTrans" (pt "n+m"))
(use 4)
(use "Truth")
;; (cp)
(save "PosProdCompat")

;; PosTimesEqualOneToOne
(set-goal "all p,q(p*q=1 -> p=1)")
(assume "p" "q" 1)
(use "PosLeAntiSym")
(use "PosNotLtToLe")
(assume 2)
(inst-with "PosLtLeMonTimes" (pt "1") (pt "p") (pt "1") (pt "q") 2 "Truth")
(simphyp 3 1)
(use 4)
(use "Truth")
;; (cp)
(save "PosTimesEqualOneToOne")

;; PosTimesProd
(set-goal "all ps,qs,m,n
 PosProd n m ps*PosProd n m qs=PosProd n m([l]ps l*qs l)")
(assume "ps" "qs")
(ind)
(assume "n")
(use "Truth")
(assume "m" "IH" "n")
(ng #t)
(simp "<-" "IH")
(use "PosLeAntiSym")
;; 9,10
(use "PosLeMonTimes")
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(use "PosLeMonTimes")
(use "Truth")
(simp "PosTimesComm")
(use "Truth")
(use "Truth")
;; 10
(use "PosLeMonTimes")
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(use "PosLeMonTimes")
(use "Truth")
(simp "PosTimesComm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cp)
(save "PosTimesProd")

;; PosProdSplit (generalizes PosTimesProdBound)
(set-goal "all ps,n,m,l PosProd n m ps*PosProd(n+m)l ps=PosProd n(m+l)ps")
(assume "ps" "m" "n")
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
(save "PosProdSplit")

;; PosProdSplitZero (was PosTimesProdBound)
(set-goal "all ps,m,l PosProd Zero m ps*PosProd m l ps=PosProd Zero(m+l)ps")
(strip)
(simp "<-" "PosProdSplit")
(use "Truth")
;; (cp)
(save "PosProdSplitZero")

;; PosProdShift
(set-goal "all n,ps,m PosProd Zero m ps=PosProd n m([l]ps(l--n))")
(assume "n" "ps")
(ind)
(search)
(assume "m" 1)
(ng)
(simp 1)
(use "Truth")
;; (cp)
(save "PosProdShift")

;; PosProdOne
(set-goal "all n,m PosProd n m([n]1)=1")
(assume "n")
(ind)
(use "Truth")
(assume "m" 1)
(ng)
(use 1)
;; (cp)
(save "PosProdOne")

;; PosEvenOrOdd
(set-goal "all p(PosEven p oru PosEven(PosS p))")
(cases)
(intro 1)
(use "Truth")
(assume "p")
(intro 0)
(use "Truth")
(assume "p")
(intro 1)
(use "Truth")
;; (cp)
(save "PosEvenOrOdd")

;; Maximum of a monotone boolean predicate
;; =======================================

;; (remove-program-constant "PosMonMaxAux")
(add-program-constant "PosMonMaxAux" (py "(pos=>boole)=>nat=>pos=>pos"))
;; The following algorithm is based on interval nesting.
(add-computation-rules
 "PosMonMaxAux wf Zero q" "q"
 "PosMonMaxAux wf(Succ n)1"
 "[if (wf(2**n)) (PosMonMaxAux wf n(2**n)) (PosMonMaxAux wf n 1)]"
 "PosMonMaxAux wf(Succ n)(SZero q)"
 "[if (wf(SZero q+2**n))
      (PosMonMaxAux wf n(SZero q+2**n)) (PosMonMaxAux wf n(SZero q))]"
 "PosMonMaxAux wf(Succ n)(SOne q)"
 "[if (wf(SOne q+2**n))
      (PosMonMaxAux wf n(SOne q+2**n)) (PosMonMaxAux wf n(SOne q))]")

(set-totality-goal "PosMonMaxAux")
(fold-alltotal)
(assume "wf")
(fold-alltotal)
(ind)
(fold-alltotal)
(assume "q")
(use "TotalVar")
(assume "n" 1)
(fold-alltotal)
(cases)
(ng #t)
(use "BooleIfTotal")
(use "TotalVar")
(use 1)
(use "TotalVar")
(use 1)
(use "TotalVar")
(assume "p0")
(use "BooleIfTotal")
(use "TotalVar")
(use 1)
(use "TotalVar")
(use 1)
(use "TotalVar")
(assume "q")
(use "BooleIfTotal")
(use "TotalVar")
(use 1)
(use "TotalVar")
(use 1)
(use "TotalVar")
;; (cp)
(save-totality)

;; PosMonMaxAuxProp
(set-goal "all wf,n,p(wf p -> wf(PosMonMaxAux wf n p))")
(assume "wf")
(ind)
(search)
(assume "n" 1)
(cases)
(assume 2)
(ng #t)
(cases (pt "wf(2**n)"))
(assume 3)
(use 1)
(use 3)
(assume 3)
(use 1)
(use 2)
(assume "q" 2)
(ng #t)
(cases (pt "wf(SZero q+2**n)"))
(assume 3)
(simp "IfTrue")
(use 1)
(use 3)
(assume 3)
(simp "IfFalse")
(use 1)
(use 2)
(assume "q" 2)
(ng #t)
(cases (pt "wf(SOne q+2**n)"))
(assume 3)
(simp "IfTrue")
(use 1)
(use 3)
(assume 3)
(simp "IfFalse")
(use 1)
(use 2)
;; (cp)
(save "PosMonMaxAuxProp")

;; PosMonMaxAuxNegProp
(set-goal "all wf( all p,q(p<=q -> wf q -> wf p) -> all q,n,p(
     negb(wf(2**n)) andnc p=1 oru negb(wf(p+2**n)) andnc 1<p -> 
     negb(wf(PosMonMaxAux wf n p+q))))")
(assume "wf" 1 "q")
(ind)
;; Case 0
(assume "p")
(elim)
(elim)
(assume 4 5)
(simp 5)
(ng)
(cases (pt "wf(PosS q)"))
(assume 6)
(inst-with 1 (pt "1") (pt "PosS q") "Truth" "?")
(simphyp 4 7)
(use 8)
(use 6)
(search)
(elim)
(assume 4 5)
(ng)
(cases (pt "wf(p+q)"))
(assume 6)
(inst-with 1 (pt "p+1") (pt "p+q") "?" 6)
(simphyp 4 7)
(use 8)
(use "PosLeMonPlus")
(use "Truth")
(use "Truth")
(search)
;;Case Succ n
(assume "n" 2)
(cases)
;;Case p = 1
(elim)
(assume 4)
(ng)
(cases (pt "wf(2**n)"))
(assume 5)
(ng)
(cases (pt "n"))
(assume 6)
(simphyp 4 6)
(ng)
(cases (pt "wf(PosS q)"))
(assume 8)
(inst-with 1 (pt "2") (pt "PosS q") "?" 8)
(simphyp 7 9)
(use 10)
(simp (pf "2=PosS 1"))
(simp "PosLe9RewRule")
(use "Truth")
;; (use "PosLeMonPosS")
(use "Truth")
(search)
(assume "n0" 5)
(simp "<-" 6)
(use 2)
(intro 1)
(simp "PosExpTwoSucc")
(split)
(use 4)
(simp 6)
(use "Truth")
(assume 5)
(ng)
(use 2)
(intro 0)
(simp 5)
(split)
(use "Truth")
(use "Truth")
(assume 4)
(use "EfAtom")
(use 4)
(assume "p")
(elim)
(assume 4)
(use "EfAtom")
(use 4)
(assume 4)
(ng)
(cases (pt "wf(SZero p+2**n)"))
(assume 5)
(ng)
(use 2)
(intro 1)
(split)
(simp "<-" "PosPlusAssoc")
(simp "PosExpTwoSucc")
(use 4)
(use "PosLtTrans"(pt "SZero p"))
(use "Truth")
(use "Truth")
(assume 5)
(ng)
(use 2)
(intro 1)
(split)
(simp 5)
(use "Truth")
(use "Truth")
(assume "p")
(elim)
(assume 4)
(use "EfAtom")
(use 4)
(assume 4)
(ng)
(cases (pt "wf(SOne p+2**n)"))
(assume 5)
(ng)
(use 2)
(intro 1)
(simp "<-" "PosPlusAssoc")
(simp "<-" "SZeroPosPlus")
(split)
(use 4)
(use "PosLtTrans" (pt "SOne p"))
(use "Truth")
(use "Truth")
(assume 5)
(ng)
(use 2)
(intro 1)
(simp 5)
(split)
(use "Truth")
(use "Truth")
;; (cp)
(save "PosMonMaxAuxNegProp")

(add-program-constant "PosMonMax" (py "(pos=>boole)=>nat=>pos"))
(add-computation-rules
 "PosMonMax wf n" "PosMonMaxAux wf n 1")

(set-totality-goal "PosMonMax")
(strip)
(ng)
(use "PosMonMaxAuxTotal")
(use 1)
(use 2)
(use "TotalVar")
;; (cp)
(save-totality)

;; PosMonMaxProp
(set-goal "all wf,n(wf 1 -> wf(PosMonMax wf n))")
(strip)
(use "PosMonMaxAuxProp")
(use 1)
;; (cp)
(save "PosMonMaxProp")

;; PosMonMaxNegPropPlus
(set-goal "all wf,n(
     negb(wf(2**n)) -> 
     all p,q(p<=q -> wf q -> wf p) -> all q negb(wf(PosMonMax wf n+q)))")
(strip)
(simp "PosMonMax0CompRule")
(use "PosMonMaxAuxNegProp")
(auto)
(intro 0)
(split)
(auto)
;; (cp)
(save "PosMonMaxNegPropPlus")

;; PosMonMaxNegProp
(set-goal "all wf,n(
     negb(wf(2**n)) -> 
     all p,q(p<=q -> wf q -> wf p) -> all q(PosMonMax wf n<q -> negb(wf q)))")
(strip)
(inst-with "PosMonMaxNegPropPlus"
 (pt "wf") (pt "n") 1 2 (pt "q--PosMonMax wf n"))
(simphyp 4 "PosPlusComm")
(simphyp 5 "PosMinusPlusEq")
(use 6)
(use 3)
;; (cp)
(save "PosMonMaxNegProp")

;; PosMonMaxChar
(set-goal "all n,wf(
     wf 1 -> 
     negb(wf(2**n)) ->
     all p,q(p<=q -> wf q -> wf p) -> 
     all p(wf p -> all q(p<q -> negb(wf q)) -> p=PosMonMax wf n))")
(strip)
(use "PosLeAntiSym")
(use "PosNotLtToLe")
(assume 6)
(ng)
(inst-with "PosMonMaxNegProp" (pt "wf") (pt "n") 2 3 (pt "p") 6)
(simphyp 7 4)
(use 8)
(use "PosNotLtToLe")
(assume 7)
(inst-with "PosMonMaxProp" (pt "wf") (pt "n") 1)
(inst-with 5 (pt "PosMonMax wf n") 6)
(simphyp 8 7)
(use 9)
;; (cp)
(save "PosMonMaxChar")

;; PosSqrt
;; =======

(add-program-constant "PosSqrt" (py "pos=>pos"))
(add-computation-rules
 "PosSqrt p" "PosMonMax([q]q*q<=p)(NatHalf(PosLog p)+1)")

(set-totality-goal "PosSqrt")
(fold-alltotal)
(assume "p")
(use "TotalVar")
;; (cp)
(save-totality)

;; PosSquareBoundPosLog
(set-goal "all p negb(([q]q*q<=p)(2**(NatHalf(PosLog p)+1)))")
(assume "p")
(ng)
(simp "PosExpTwoNatPlus")
(simp "NatDoublePlusEq")
(inst-with "NatEvenOrOdd" (pt "PosLog p"))
(elim 1)
(assume 2)
(simp "NatDoubleHalfEven")
(assert "p<SZero(SZero(2**PosLog p))")
(use "PosLtLeTrans" (pt "2**Succ(PosLog p)"))
(use "PosLtExpTwoSuccLog")
(use "Truth")
(assume 3)
(cases (pt "SZero(SZero(2**PosLog p))<=p"))
(assume 1)
(assert "p<p")
(use "PosLtLeTrans" (pt "SZero(SZero(2**PosLog p))"))
(use 3)
(use 4)
(auto)
(assume 1)
(assert "p< SZero(SZero(2**NatDouble(NatHalf(PosLog p))))")
(use "PosLtLeTrans" (pt "2**Succ(PosLog p)"))
(use "PosLtExpTwoSuccLog")
(use "PosLeTrans" (pt "2**(Succ(Succ(NatDouble(NatHalf(PosLog p)))))"))
(simp "NatDoubleHalfOdd")
(use "Truth")
(assume 3)
(use "NatEvenToOddSucc" (pt "PosLog p"))
(use 3)
(use 2)
(use "Truth")
(assume 3)
(cases (pt "SZero(SZero(2**NatDouble(NatHalf(PosLog p))))<=p"))
(assume 4)
(assert "p<p")
(use "PosLtLeTrans" (pt "SZero(SZero(2**NatDouble(NatHalf(PosLog p))))"))
(use 3)
(use 4)
(auto)
;; (cp)
(save "PosSquareBoundPosLog")

;; PosSquareBoundMon
(set-goal "all p0,q(p0<=q -> ([q0]q0*q0<=p)q -> ([q0]q0*q0<=p)p0)")
(ng)
(strip)
(use "PosLeTrans" (pt "q*q"))
(use "PosLeMonSquare")
(use 1)
(use 2)
;; (cp)
(save "PosSquareBoundMon")

;; PosSquareSqrtUpBound
(set-goal "all p PosSquare(PosSqrt p)<=p")
(assume "p")
(simp "PosSqrt0CompRule")
(simp "PosSquare0CompRule")
(use-with "PosMonMaxProp" (pt "[q]q*q<=p") (pt "NatHalf(PosLog p)+1") "?")
(use "Truth")
;; (cp)
(save "PosSquareSqrtUpBound")

;; PosSquareSqrtLowBound
(set-goal "all p,q(PosSqrt p<q -> p<PosSquare q)")
(strip)
(use "PosNotLeToLt")
(assume 2)
(inst-with "PosMonMaxNegProp"
 (pt "[q]q*q<=p") (pt "NatHalf (PosLog p)+1") "?" "?" (pt "q") 1)
(ng 2 3)
(simphyp 3 2)
(use 4)
(bpe-ng)
(use "PosSquareBoundPosLog")
(use "PosSquareBoundMon")
;; (cp)
(save "PosSquareSqrtLowBound")

;; PosSqrtTimesLowBound
(set-goal "all p,q0,q1(PosSqrt p<q0 -> PosSqrt p<q1 -> p<q0*q1)")
(assume "p" "q0" "q1" 1 2)
(cases (pt "q0<=q1"))
(assume 1)
(use "PosLtLeTrans" (pt "q0*q0"))
(use "PosSquareSqrtLowBound")
(use 1)
(use "PosLeMonTimes")
(use "Truth")
(use 3)
(assume 3)
(use "PosLtLeTrans" (pt "q1*q1"))
(use "PosSquareSqrtLowBound")
(use 2)
(use "PosLeMonTimes")
(use "PosNotLtToLe")
(assume 4)
(use 3)
(use "PosLtToLe")
(use 4)
(use "Truth")
;; (cp)
(save "PosSqrtTimesLowBound")

;; PosSqrtChar
(set-goal "all p,q(q*q<=p ->all q0(q<q0 -> p<q0*q0) -> q=PosSqrt p)")
(strip)
(simp "PosSqrt0CompRule")
(use "PosMonMaxChar")
(use "Truth")
(use "PosSquareBoundPosLog")
(use "PosSquareBoundMon")
(use 1)
(ng)
(assume "q0" 1)
(cases (pt "q0*q0<=p"))
(assume 4)
(assert "p<p")
(use "PosLtLeTrans" (pt "q0*q0"))
(use 2)
(use 3)
(use 4)
(auto)
;; (cp)
(save "PosSqrtChar")

;; PosSqrtSquareId
(set-goal "all p PosSqrt(PosSquare p) = p")
(assume "p")
(use "PosEqSym")
(use "PosSqrtChar")
(use "Truth")
(assume "q" 1)
(use "PosLtMonTimes")
(use 1)
(use 1)
;; (cp)
(save "PosSqrtSquareId")

;; PosLeMonSqrt
(set-goal "all p,q(p<=q -> PosSqrt p<=PosSqrt q)")
(strip)
(use "PosNotLtToLe")
(assume 2)
(assert "p<p")
(use "PosLeLtTrans" (pt "q"))
(use 1)
(use "PosLtLeTrans" (pt "PosSquare(PosSqrt p)"))
(use "PosSquareSqrtLowBound")
(use 2)
(use "PosSquareSqrtUpBound")
(search)
;; (cp)
(save "PosLeMonSqrt")

;; PosEqSqrtToOne
(set-goal "all p(p<=PosSqrt p -> p=1)")
(assume "p" 1)
(simp "<-" "PosLe0RewRule")
(inst-with "PosLeMonSquare" (pt "p") (pt "PosSqrt p") 1)
(simphyp 2 "PosSquare0CompRule")
(simphyp 3 "PosSquare0CompRule")
(use "PosNotLtToLe")
(assume 4)
(assert "p*p<p*p") 
(use "PosLeLtTrans" (pt "PosSquare(PosSqrt p)"))
(use 3)
(use "PosLeLtTrans" (pt "p"))
(use "PosSquareSqrtUpBound")
(use "PosLtPosToLtTimes")
(use 5)
(search)
;; (cp)
(save "PosEqSqrtToOne")

;; PosLtSqrt
(set-goal "all p(1<p -> PosSqrt p<p)")
(assume "p" 1)
(use "PosNotLeToLt")
(assume 2)
(assert "PosSqrt p*PosSqrt p<=PosSqrt p*1")
(use "PosLeTrans" (pt "p"))
(use "PosSquareSqrtUpBound")
(use 2)
(assume 3)
(assert "PosSqrt p<=1")
(use "PosLeTimesCancelL" (pt "PosSqrt p"))
(use 3)
(assume 4)
(assert "1<1")
(use "PosLtLeTrans" (pt "p"))
(use 1)
(use "PosLeTrans" (pt "PosSqrt p"))
(use 2)
(use 4)
(search)
;; (cp)
(save "PosLtSqrt")

;; PosSqr
(set-goal "all p exl q q=PosSqrt p")
(assume "p")
(intro 0 (pt "PosSqrt p"))
(use "Truth")
;; (cp)
(save "PosSqr")

(animate "PosSqr")

;; PosSqrExFree
(set-goal "all p cPosSqr p = PosSqrt p")
(assume "p")
(use "Truth")
;; (cp)
(save "PosSqrExFree")

(deanimate "PosSqr")
