;; 2025-10-11.  list.scm.

#|
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)
|#

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading list.scm ...") (newline)

(add-algs "list" 'prefix-typeop
	  '("list" "Nil")
	  '("alpha=>list=>list" "Cons"))

(add-var-name "x" (py "alpha"))
(add-var-name "xl" (py "list alpha"))
(add-var-name "xs" (py "nat=>alpha"))

;; Infix notation allowed (and type parameters omitted) for binary
;; constructors, as follows.  This would also work for prefix notation.
;; Example: :: for Cons.  x::y::z:
;; Here : is postfix for z

;; The line below is commented out.
;; (add-infix-display-string "Cons" "::" 'pair-op) ;right associative
;; Instead add-token and add-display are specially done for ::

(add-token
 "::" 'pair-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((const (constr-name-to-constr "Cons"))
	    (uninst-type (const-to-uninst-type const))
	    (patterns (arrow-form-to-arg-types uninst-type 2)) ;al, list al
	    (instances (map term-to-type (list x y))) ;e.g.  nat, list int
	    (type1 (car instances)) ;nat
	    (type2 (car (alg-form-to-types (cadr instances)))) ;int
	    (tsubst (cond ((type-le? type1 type2)
			   (make-subst (car patterns) type2))
			  ((type-le? type2 type1)
			   (make-subst (car patterns) type1))
			  (else (myerror "comparable types expected"
					 type1 type2)))))
       (const-substitute const tsubst #f)))
    x y)))

(add-display
 (py "list alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if
	  (and (term-in-const-form? op)
	       (string=? "Cons"
			 (const-to-name (term-in-const-form-to-const op)))
	       (= 2 (length args)))
	  (list 'pair-op  "::"
		(term-to-token-tree (car args))
		(term-to-token-tree (cadr args)))
	  #f))
       #f)))

;; The postfix-op ":" with "x:" for "x::(Nil rho)" needs a special
;; treatment with explicit uses of add-token and add-display.

(add-token
 ":" 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Cons"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f)))
    x
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Nil"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f))))))

(add-display
 (py "list alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "Cons" (const-to-name
				    (term-in-const-form-to-const op)))
		  (= 2 (length args))
		  (term-in-const-form? (cadr args))
		  (string=? "Nil" (const-to-name
				   (term-in-const-form-to-const (cadr args)))))
	     (list 'postfix-op ":" (term-to-token-tree (car args)))
	     #f))
       #f)))

;; We collect definitions and properties of TotalList and EqPList,
;; including the Nc, Co and MR variants.  In the present file we only
;; give the definitions.  The (somewhat lengthy) properties are in a
;; separate extension file listext.scm.

;; 1.  Totality
;; 1-1.  Total and CoTotal

;; 1-1-1.  Total
;; 1-1-1-1.  Definitions
;; 1-1-1-1-1.  Definitions of predicates with cterms
;; 1-1-1-1-2.  Definitions of predicates without cterms
;; 1-1-1-2.  Properties
;; 1-1-1-2-1.  Ex falso
;; 1-1-1-2-2.  Monotonicity
;; 1-1-1-2-3.  Connections

;; 1-1-2.  CoTotal
;; 1-1-2-1.  Definitions
;; 1-1-2-2.  Properties
;; 1-1-2-2-1.  Monotonicity
;; 1-1-2-2-2.  Total implies CoTotal
;; 1-1-2-2-3.  Ex falso

;; 1-2.  TotalMR and CoTotalMR

;; 1-2-1.  TotalMR
;; 1-2-1-1.  Definitions
;; 1-2-1-2.  Properties
;; 1-2-1-2-1.  Ex falso
;; 1-2-1-2-2.  Monotonicity
;; 1-2-1-2-3.  Connections

;; 1-2-2.  CoTotalMR
;; 1-2-2-1.  Definitions
;; 1-2-2-2.  Properties
;; 1-2-2-2-1.  Ex falso
;; 1-2-2-2-2.  Monotonicity
;; 1-2-2-2-3.  Total implies CoTotal

;; 2.  Pointwise equality (similar)
;; 2-1.  EqP and CoEqP

;; 2-1-1.  EqP
;; 2-1-1-1.  Definitions
;; 2-1-1-1-1.  Definitions of predicates with cterms
;; 2-1-1-1-2.  Definitions of predicates without cterms
;; 2-1-1-2.  Properties
;; 2-1-1-2-1.  Ex falso
;; 2-1-1-2-2.  Monotonicity
;; 2-1-1-2-3.  EqP implies EqD
;; 2-1-1-2-4.  Symmetry
;; 2-1-1-2-5.  Connections
;; 2-1-1-2-6.  Relations between Total and EqP

;; 2-1-2.  CoEqP
;; 2-1-2-1.  Definitions
;; 2-1-2-2.  Properties
;; 2-1-2-2-1.  Monotonicity
;; 2-1-2-2-2.  Symmetry
;; 2-1-2-2-3.  EqPList implies CoEqPList, Ex falso
;; 2-1-2-2-4.  Relations between CoTotal and CoEqP

;; 2-2.  EqPMR and CoEqPMR

;; 2-2-1.  EqPMR
;; 2-2-1-1.  Definitions
;; 2-2-1-2.  Properties
;; 2-2-1-2-1.  Ex falso
;; 2-2-1-2-2.  Monotonicity
;; 2-2-1-2-3.  Connections

;; 2-2-2.  CoEqPMR
;; 2-2-2-1.  Definitions
;; 2-2-2-2.  Properties
;; 2-2-2-2-1.  Ex falso
;; 2-2-2-2-2.  Monotonicity
;; 2-2-2-2-3.  Total implies CoTotal

;; 3.  ListNat, ListBoole

;; 1.  Totality
;; ============

;; 1-1.  Total and CoTotal
;; =======================

;; 1-1-1.  Total
;; =============

;; 1-1-1-1.  Definitions
;; =====================

;; 1-1-1-1-1.  Definitions of predicates with cterms
;; =================================================

;; RTotalList (R: c.r.)      \typeL{\alpha}
;; NTotalList (N: n.c.)      \typeN
;; RTotalListNc              --

(add-ids
 (list (list "RTotalList" (make-arity (py "list alpha")) "list"))
 '("RTotalList (Nil alpha)" "RTotalListNil")
 '("all x^((Pvar alpha)x^ -> all xl^(RTotalList xl^ ->
    RTotalList(x^ ::xl^)))"
   "RTotalListCons"))

(pp "RTotalListNil")
;; (RTotalList (cterm (x^) (Pvar alpha)x^))(Nil alpha)

(pp "RTotalListCons")

;; all x^(
;;  (Pvar alpha)x^ -> 
;;  all xl^(
;;   (RTotalList (cterm (x^0) (Pvar alpha)x^0))xl^ -> 
;;   (RTotalList (cterm (x^0) (Pvar alpha)x^0))(x^ ::xl^)))

(add-ids
 (list (list "NTotalList" (make-arity (py "list alpha")) "nat"))
 '("NTotalList (Nil alpha)" "NTotalListNil")
 '("all x^((Pvar alpha)^ x^ -> all xl^(NTotalList xl^ ->
    NTotalList (x^ ::xl^)))"
   "NTotalListCons"))

(pp "NTotalListNil")
;; (NTotalList (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)

(pp "NTotalListCons")

;; all x^(
;;  (Pvar alpha)^ x^ -> 
;;  all xl^(
;;   (NTotalList (cterm (x^0) (Pvar alpha)^ x^0))xl^ -> 
;;   (NTotalList (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xl^)))

(add-ids
 (list (list "RTotalListNc" (make-arity (py "list alpha"))))
 '("RTotalListNc (Nil alpha)" "RTotalListNcNil")
 '("all x^((Pvar alpha)^ x^ -> all xl^(RTotalListNc xl^ ->
    RTotalListNc(x^ ::xl^)))"
  "RTotalListNcCons"))
 
(pp "RTotalListNcNil")
;; (RTotalListNc (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)

(pp "RTotalListNcCons")

;; all x^(
;;  (Pvar alpha)^ x^ -> 
;;  all xl^(
;;   (RTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))xl^ -> 
;;   (RTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xl^)))

;; 1-1-1-1-2.  Definitions of predicates without cterms
;; ====================================================

;; TotalList                 \typeL{\alpha} (Y^c  -> Total predconst)
;; ANTotalList (A: absolute) \typeN         (Y^nc -> TotalNc predconst)
;; STotalList                \typeN         (Y^nc -> {x|T})
;; TotalListNc               --             (Y^nc -> TotalNc predconst)
;; STotalListNc              --             (Y^nc -> {x|T})

(add-totality "list")

(pp "TotalListNil")
;; TotalList(Nil alpha)

(pp "TotalListCons")
;; all x^(Total x^ -> all xl^(TotalList xl^ -> TotalList(x^ ::xl^)))

(add-ids
 (list (list "ANTotalList" (make-arity (py "list alpha")) "nat"))
 '("ANTotalList(Nil alpha)" "ANTotalListNil")
 '("all x^(TotalNc x^ -> all xl^(ANTotalList xl^ ->
    ANTotalList(x^ ::xl^)))"
   "ANTotalListCons"))

(pp "ANTotalListNil")
;; ANTotalList(Nil alpha)

(pp "ANTotalListCons")
;; all x^(TotalNc x^ -> all xl^(ANTotalList xl^ -> ANTotalList(x^ ::xl^)))

(add-ids (list (list "STotalList" (make-arity (py "list alpha")) "nat"))
	 '("STotalList(Nil alpha)" "STotalListNil")
	 '("all x^,xl^(
             STotalList xl^ -> STotalList(x^ ::xl^))" "STotalListCons"))

(pp "STotalListNil")
;; STotalList(Nil alpha)

(pp "STotalListCons")
;; all x^,xl^(STotalList xl^ -> STotalList(x^ ::xl^))

;; We could use (RTotalList (cterm (x^) T))xl^ for STotalList xl^.
;; However, STotalList is just convenient.

(add-totalnc "list")

(pp "TotalListNcNil")
;; TotalListNc(Nil alpha)

(pp "TotalListNcCons")
;; all x^(TotalNc x^ -> all xl^(TotalListNc xl^ -> TotalListNc(x^ ::xl^)))

(add-ids (list (list "STotalListNc" (make-arity (py "list alpha"))))
	 '("STotalListNc(Nil alpha)" "STotalListNcNil")
	 '("all x^,xl^(STotalListNc xl^ -> STotalListNc(x^ ::xl^))"
	   "STotalListNcCons"))

(pp "STotalListNcNil")
;; STotalListNc(Nil alpha)

(pp "STotalListNcCons")
;; all x^,xl^(STotalListNc xl^ -> STotalListNc(x^ ::xl^))

;; 1-1-2-1.  Definitions
;; =====================

;; For the 8 variants of TotalList defined in 1-1-1-1 we define their duals

(add-co "RTotalList")
(add-co "NTotalList")
(add-co "RTotalListNc")
(add-co "TotalList")
(add-co "ANTotalList")
(add-co "STotalList")
(add-co "TotalListNc")
(add-co "STotalListNc")

(for-each pp (list
"CoRTotalListClause"
"CoNTotalListClause"
"CoRTotalListNcClause"
"CoTotalListClause"
"CoANTotalListClause"
"CoSTotalListClause"
"CoTotalListNcClause"
"CoSTotalListNcClause"))

;; all xl^(
;;  (CoRTotalList (cterm (x^) (Pvar alpha)x^))xl^ -> 
;;  xl^ eqd(Nil alpha) orr 
;;  exr x^(
;;   (Pvar alpha)x^ andd 
;;   exr xl^0(
;;    (CoRTotalList (cterm (x^0) (Pvar alpha)x^0))xl^0 andl
;;    xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xl^ -> 
;;  xl^ eqd(Nil alpha) orr 
;;  exr x^(
;;   (Pvar alpha)^ x^ andr 
;;   exr xl^0(
;;    (CoNTotalList (cterm (x^0) (Pvar alpha)^ x^0))xl^0 andl
;;    xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  (CoRTotalListNc (cterm (x^) (Pvar alpha)^ x^))xl^ -> 
;;  xl^ eqd(Nil alpha) ornc 
;;  exnc x^(
;;   (Pvar alpha)^ x^ andnc 
;;   exnc xl^0(
;;    (CoRTotalListNc (cterm (x^0) (Pvar alpha)^ x^0))xl^0 andnc 
;;    xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  CoTotalList xl^ -> 
;;  xl^ eqd(Nil alpha) orr 
;;  exr x^(Total x^ andd exr xl^0(CoTotalList xl^0 andl xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  CoANTotalList xl^ -> 
;;  xl^ eqd(Nil alpha) orr 
;;  exr x^(
;;   TotalNc x^ andr exr xl^0(CoANTotalList xl^0 andl xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  CoSTotalList xl^ -> 
;;  xl^ eqd(Nil alpha) orr 
;;  exr x^,xl^0(CoSTotalList xl^0 andl xl^ eqd(x^ ::xl^0)))

;; all xl^(
;;  CoTotalListNc xl^ -> 
;;  xl^ eqd(Nil alpha) ornc 
;;  exnc x^(
;;   TotalNc x^ andnc exnc xl^0(CoTotalListNc xl^0 andnc xl^ eqd(x^ ::xl^0))))

;; all xl^(
;;  CoSTotalListNc xl^ -> 
;;  xl^ eqd(Nil alpha) ornc 
;;  exnc x^,xl^0(CoSTotalListNc xl^0 andnc xl^ eqd(x^ ::xl^0)))

;; 1-2-1-1.  Definitions
;; =====================

;; RTotalListMR
;; NTotalListMR
;; TotalListMR
;; ANTotalListMR
;; STotalListMR

(add-mr-ids "RTotalList")

(pp "RTotalListNilMR")
;; (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^ x^ gamma^))(Nil alpha)
;; (Nil gamma)

(pp "RTotalListConsMR")

;; all x^,gam^(
;;  (Pvar alpha gamma)^ x^ gam^ -> 
;;  all xl^,(list gamma)^(
;;   (RTotalListMR (cterm (x^0,gam^0) (Pvar alpha gamma)^ x^0 gam^0))xl^
;;   (list gamma)^ -> 
;;   (RTotalListMR (cterm (x^0,gam^0) (Pvar alpha gamma)^ x^0 gam^0))(x^ ::xl^)
;;   (gam^ ::(list gamma)^)))

(add-mr-ids "NTotalList")

(pp "NTotalListNilMR")
;; (NTotalListMR (cterm (x^) (Pvar alpha)^ x^))(Nil alpha)0

(pp "NTotalListConsMR")

;; all x^(
;;  (Pvar alpha)^ x^ -> 
;;  all xl^,n^(
;;   (NTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))xl^ n^ -> 
;;   (NTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))(x^ ::xl^)(Succ n^)))

(add-mr-ids "TotalList")

(pp "TotalListNilMR")
;; TotalListMR(Nil alpha)(Nil alpha)

(pp "TotalListConsMR")

;; all x^,x^0(
;;  TotalMR x^ x^0 -> 
;;  all xl^,xl^0(TotalListMR xl^ xl^0 -> TotalListMR(x^ ::xl^)(x^0::xl^0)))

(add-mr-ids "ANTotalList")

(pp "ANTotalListNilMR")
;; ANTotalListMR(Nil alpha)0

(pp "ANTotalListConsMR")
;; all x^(
;;  TotalNc x^ -> 
;;  all xl^,n^(ANTotalListMR xl^ n^ -> ANTotalListMR(x^ ::xl^)(Succ n^)))

(add-mr-ids "STotalList")

(pp "STotalListNilMR")
;; STotalListMR(Nil alpha)0

(pp "STotalListConsMR")
;; all x^,xl^,n^(STotalListMR xl^ n^ -> STotalListMR(x^ ::xl^)(Succ n^))

;; 1-2-2-1.  Definitions
;; =====================

;; CoRTotalListMR
;; CoNTotalListMR
;; CoTotalListMR
;; CoANTotalListMR
;; CoSTotalListMR

(add-co "RTotalListMR")

(pp "CoRTotalListMRClause")

;; all xl^,(list gamma)^(
;;  (CoRTotalListMR (cterm (x^,gamma^0) (Pvar alpha gamma)^ x^ gamma^0))xl^
;;  (list gamma)^ -> 
;;  xl^ eqd(Nil alpha) andnc (list gamma)^ eqd(Nil gamma) ornc 
;;  exnc x^,gamma^0(
;;   (Pvar alpha gamma)^ x^ gamma^0 andnc 
;;   exnc xl^0,(list gamma)^1(
;;    (CoRTotalListMR (cterm (x^0,gamma^2) (Pvar alpha gamma)^ x^0 gamma^2))xl^0
;;    (list gamma)^1 andnc 
;;    xl^ eqd(x^ ::xl^0) andnc (list gamma)^ eqd(gamma^0::(list gamma)^1))))

(add-co "NTotalListMR")

(pp "CoNTotalListMRClause")

;; all xl^,n^(
;;  (CoNTotalListMR (cterm (x^) (Pvar alpha)^ x^))xl^ n^ -> 
;;  xl^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^(
;;   (Pvar alpha)^ x^ andnc 
;;   exnc xl^0,n^0(
;;    (CoNTotalListMR (cterm (x^0) (Pvar alpha)^ x^0))xl^0 n^0 andnc 
;;    xl^ eqd(x^ ::xl^0) andnc n^ eqd Succ n^0)))

(add-co "TotalListMR")

(pp "CoTotalListMRClause")

;; all xl^,xl^0(
;;  CoTotalListMR xl^ xl^0 -> 
;;  xl^ eqd(Nil alpha) andnc xl^0 eqd(Nil alpha) ornc 
;;  exnc x^,x^0(
;;   TotalMR x^ x^0 andnc 
;;   exnc xl^1,xl^2(
;;    CoTotalListMR xl^1 xl^2 andnc 
;;    xl^ eqd(x^ ::xl^1) andnc xl^0 eqd(x^0::xl^2))))

(add-co "ANTotalListMR")

(pp "CoANTotalListMRClause")

;; all xl^,n^(
;;  CoANTotalListMR xl^ n^ -> 
;;  xl^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^(
;;   TotalNc x^ andnc 
;;   exnc xl^0,n^0(
;;    CoANTotalListMR xl^0 n^0 andnc xl^ eqd(x^ ::xl^0) andnc n^ eqd Succ n^0)))

(add-co "STotalListMR")

(pp "CoSTotalListMRClause")

;; all xl^,n^(
;;  CoSTotalListMR xl^ n^ -> 
;;  xl^ eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,xl^0,n^0(
;;   CoSTotalListMR xl^0 n^0 andnc xl^ eqd(x^ ::xl^0) andnc n^ eqd Succ n^0))

;; 2-1-1-1.  Definitions
;; =====================

;; 2-1-1-1-1.  Definitions of predicates with cterms
;; =================================================

;; REqPList (R: c.r.)      \typeL{\alpha}
;; NEqPList (N: n.c.)      \typeN
;; REqPListNc              --

(add-ids
 (list
  (list "REqPList" (make-arity (py "list alpha") (py "list alpha")) "list"))
 '("REqPList(Nil alpha)(Nil alpha)" "REqPListNil")
 '("all x^1,x^2((Pvar alpha alpha)x^1 x^2 ->
    all xl^1,xl^2(REqPList xl^1 xl^2 -> REqPList(x^1 ::xl^1)(x^2 ::xl^2)))"
   "REqPListCons"))

(pp "REqPListNil")
;; (REqPList (cterm (x^,x^0) (Pvar alpha alpha)x^ x^0))(Nil alpha)(Nil alpha)

(pp "REqPListCons")

;; all x^,x^0(
;;  (Pvar alpha alpha)x^ x^0 -> 
;;  all xl^,xl^0(
;;   (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xl^ xl^0 -> 
;;   (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))
;;    (x^ ::xl^)(x^0::xl^0)))

(add-ids
 (list
  (list "NEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("NEqPList(Nil alpha)(Nil alpha)" "NEqPListNil")
 '("all x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
    all xl^1,xl^2(NEqPList xl^1 xl^2 -> NEqPList(x^1 ::xl^1)(x^2 ::xl^2)))"
   "NEqPListCons"))

(pp "NEqPListNil")
;; (NEqPList (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)(Nil alpha)

(pp "NEqPListCons")

;; all x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  all xl^,xl^0(
;;   (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xl^ xl^0 -> 
;;   (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xl^)
;;   (x^0::xl^0)))

(add-ids
 (list
  (list "REqPListNc" (make-arity (py "list alpha") (py "list alpha"))))
 '("REqPListNc(Nil alpha)(Nil alpha)" "REqPListNcNil")
 '("all x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
    all xl^1,xl^2(REqPListNc xl^1 xl^2 ->
                    REqPListNc(x^1 ::xl^1)(x^2 ::xl^2)))"
   "REqPListNcCons"))

(pp "REqPListNcNil")

;; (REqPListNc (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)
;; (Nil alpha)

(pp "REqPListNcCons")

;; all x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  all xl^,xl^0(
;;   (REqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xl^ xl^0 -> 
;;   (REqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xl^)
;;   (x^0::xl^0)))

;; 2-1-1-1-2.  Definitions of predicates without cterms
;; ====================================================

;; EqPList                 \typeL{\alpha} (Y^c  -> EqP predconst)
;; ANEqPList (A: absolute) \typeN         (Y^nc -> EqPNc predconst)
;; SEqPList                \typeN         (Y^nc -> {x,y|T})
;; EqPListNc               --             (Y^nc -> EqPNc predconst)
;; SEqPListNc              --             (Y^nc -> {x,y|T})

(add-eqp "list")

(pp "EqPListNil")
;; EqPList(Nil alpha)(Nil alpha)

(pp "EqPListCons")

;; all x^,x^0(
;;  EqP x^ x^0 -> 
;;  all xl^,xl^0(EqPList xl^ xl^0 -> EqPList(x^ ::xl^)(x^0::xl^0)))

(add-ids
 (list
  (list "ANEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("ANEqPList(Nil alpha)(Nil alpha)" "ANEqPListNil")
 '("all x^1,x^2(EqPNc x^1 x^2 -> all xl^1,xl^2(ANEqPList xl^1 xl^2 ->
    ANEqPList(x^1 ::xl^1)(x^2 ::xl^2)))"
   "ANEqPListCons"))

(pp "ANEqPListNil")
;; ANEqPList(Nil alpha)(Nil alpha)

(pp "ANEqPListCons")

;; all x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  all xl^,xl^0(ANEqPList xl^ xl^0 -> ANEqPList(x^ ::xl^)(x^0::xl^0)))

(add-ids
 (list
  (list "SEqPList" (make-arity (py "list alpha") (py "list alpha")) "nat"))
 '("SEqPList(Nil alpha)(Nil alpha)" "SEqPListNil")
 '("all x^1,x^2,xl^1,xl^2(
     SEqPList xl^1 xl^2 -> SEqPList(x^1 ::xl^1)(x^2 ::xl^2))" "SEqPListCons"))

(pp "SEqPListNil")
;; SEqPList(Nil alpha)(Nil alpha)

(pp "SEqPListCons")
;; all x^,x^0,xl^,xl^0(SEqPList xl^ xl^0 -> SEqPList(x^ ::xl^)(x^0::xl^0))

;; We could use (REqPList (cterm (x^1,x^2) T))xl^1 xl^2 for
;;  SEqPList xl^.1 xl^2 

(add-eqpnc "list")

(pp "EqPListNcNil")
;; EqPListNc(Nil alpha)(Nil alpha)

(pp "EqPListNcCons")

;; all x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  all xl^,xl^0(EqPListNc xl^ xl^0 -> EqPListNc(x^ ::xl^)(x^0::xl^0)))


(add-ids
 (list
  (list "SEqPListNc" (make-arity (py "list alpha") (py "list alpha"))))
 '("SEqPListNc(Nil alpha)(Nil alpha)" "SEqPListNcNil")
 '("all x^1,x^2,xl^1,xl^2(
    SEqPListNc xl^1 xl^2 -> SEqPListNc(x^1 ::xl^1)(x^2 ::xl^2))"
   "SEqPListNcCons"))

(pp "SEqPListNcNil")
;; SEqPListNc(Nil alpha)(Nil alpha)

(pp "SEqPListNcCons")

;; all x^,x^0,xl^,xl^0(
;;  SEqPListNc xl^ xl^0 -> SEqPListNc(x^ ::xl^)(x^0::xl^0))

;; 2-1-2-1.  Definitions
;; =====================

;; For the 8 variants of EqPList defined in 2-1-1-1 we define their duals

(add-co "REqPList")
(add-co "NEqPList")
(add-co "REqPListNc")
(add-co "EqPList")
(add-co "ANEqPList")
(add-co "SEqPList")
(add-co "EqPListNc")
(add-co "SEqPListNc")

(for-each pp (list
"CoREqPListClause"
"CoNEqPListClause"
"CoREqPListNcClause"
"CoEqPListClause"
"CoANEqPListClause"
"CoSEqPListClause"
"CoEqPListNcClause"
"CoSEqPListNcClause"))

;; 2-2-1-1.  Definitions
;; =====================

;; For simplicity we only consider MR-variants of idpcs without cterms

(add-mr-ids "REqPList")

(pp "REqPListNilMR")

;; (REqPListMR (cterm (x^,x^0,alpha700^) 
;;               (Pvar alpha alpha alpha700)^403 x^ x^0 alpha700^))
;; (Nil alpha)
;; (Nil alpha)
;; (Nil alpha700)

(pp "REqPListConsMR")

;; all x^,x^0,alpha700^(
;;  (Pvar alpha alpha alpha700)^403 x^ x^0 alpha700^ -> 
;;  all xl^,xl^0,(list alpha700)^0(
;;   (REqPListMR (cterm (x^1,x^2,alpha700^1) 
;;                 (Pvar alpha alpha alpha700)^403 x^1 x^2 alpha700^1))
;;   xl^ 
;;   xl^0
;;   (list alpha700)^0 -> 
;;   (REqPListMR (cterm (x^1,x^2,alpha700^1) 
;;                 (Pvar alpha alpha alpha700)^403 x^1 x^2 alpha700^1))
;;   (x^ ::xl^)
;;   (x^0::xl^0)
;;   (alpha700^ ::(list alpha700)^0)))

(add-mr-ids "NEqPList")

(pp "NEqPListNilMR")

;; (NEqPListMR (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))(Nil alpha)
;; (Nil alpha)
;; 0

(pp "NEqPListConsMR")

;; all x^,x^0(
;;  (Pvar alpha alpha)^ x^ x^0 -> 
;;  all xl^,xl^0,n^(
;;   (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xl^ xl^0 n^ -> 
;;   (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))(x^ ::xl^)
;;   (x^0::xl^0)
;;   (Succ n^)))

(add-mr-ids "EqPList")

(pp "EqPListNilMR")
;; EqPListMR(Nil alpha)(Nil alpha)(Nil alpha)

(pp "EqPListConsMR")

;; all x^,x^0,x^1(
;;  EqPMR x^ x^0 x^1 -> 
;;  all xl^,xl^0,xl^1(
;;   EqPListMR xl^ xl^0 xl^1 -> EqPListMR(x^ ::xl^)(x^0::xl^0)(x^1::xl^1)))

(add-mr-ids "ANEqPList")

(pp "ANEqPListNilMR")
;; ANEqPListMR(Nil alpha)(Nil alpha)0

(pp "ANEqPListConsMR")

;; all x^,x^0(
;;  EqPNc x^ x^0 -> 
;;  all xl^,xl^0,n^(
;;   ANEqPListMR xl^ xl^0 n^ -> ANEqPListMR(x^ ::xl^)(x^0::xl^0)(Succ n^)))

(add-mr-ids "SEqPList")

(pp "SEqPListNilMR")
;; SEqPListMR(Nil alpha)(Nil alpha)0

(pp "SEqPListConsMR")

;; all x^,x^0,xl^,xl^0,n^(
;;  SEqPListMR xl^ xl^0 n^ -> SEqPListMR(x^ ::xl^)(x^0::xl^0)(Succ n^))

;; 2-2-2-1.  Definitions
;; =====================

;; CoREqPListMR
;; CoNEqPListMR
;; CoEqPListMR
;; CoANEqPListMR
;; CoSEqPListMR

(add-co "REqPListMR")

(pp "CoREqPListMRClause")

;; all xl^,xl^0,(list alpha768)^(
;;  (CoREqPListMR (cterm (x^,x^0,alpha768^0) 
;;                  (Pvar alpha alpha alpha768)^404 x^ x^0 alpha768^0))
;;  xl^ 
;;  xl^0
;;  (list alpha768)^ -> 
;;  xl^ eqd(Nil alpha) andnc 
;;  xl^0 eqd(Nil alpha) andnc (list alpha768)^ eqd(Nil alpha768) ornc 
;;  exnc x^,x^0,alpha768^0(
;;   (Pvar alpha alpha alpha768)^404 x^ x^0 alpha768^0 andnc 
;;   exnc xl^1,xl^2,(list alpha768)^1(
;;    (CoREqPListMR (cterm (x^1,x^2,alpha768^2) 
;;                    (Pvar alpha alpha alpha768)^404 x^1 x^2 alpha768^2))
;;    xl^1 
;;    xl^2
;;    (list alpha768)^1 andnc 
;;    xl^ eqd(x^ ::xl^1) andnc 
;;    xl^0 eqd(x^0::xl^2) andnc 
;;    (list alpha768)^ eqd(alpha768^0::(list alpha768)^1))))

(add-co "NEqPListMR")

(pp "CoNEqPListMRClause")

;; all xl^,xl^0,n^(
;;  (CoNEqPListMR (cterm (x^,x^0) (Pvar alpha alpha)^ x^ x^0))xl^ xl^0 n^ -> 
;;  xl^ eqd(Nil alpha) andnc xl^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0(
;;   (Pvar alpha alpha)^ x^ x^0 andnc 
;;   exnc xl^1,xl^2,n^0(
;;    (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xl^1 xl^2 n^0
;;  andnc 
;;    xl^ eqd(x^ ::xl^1) andnc xl^0 eqd(x^0::xl^2) andnc n^ eqd Succ n^0)))

(add-co "EqPListMR")

(pp "CoEqPListMRClause")

;; all xl^,xl^0,xl^1(
;;  CoEqPListMR xl^ xl^0 xl^1 -> 
;;  xl^ eqd(Nil alpha) andnc xl^0 eqd(Nil alpha) andnc xl^1 eqd(Nil alpha) ornc 
;;  exnc x^,x^0,x^1(
;;   EqPMR x^ x^0 x^1 andnc 
;;   exnc xl^2,xl^3,xl^4(
;;    CoEqPListMR xl^2 xl^3 xl^4 andnc 
;;    xl^ eqd(x^ ::xl^2) andnc xl^0 eqd(x^0::xl^3) andnc xl^1 eqd(x^1::xl^4))))

(add-co "ANEqPListMR")

(pp "CoANEqPListMRClause")

;; all xl^,xl^0,n^(
;;  CoANEqPListMR xl^ xl^0 n^ -> 
;;  xl^ eqd(Nil alpha) andnc xl^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0(
;;   EqPNc x^ x^0 andnc 
;;   exnc xl^1,xl^2,n^0(
;;    CoANEqPListMR xl^1 xl^2 n^0 andnc 
;;    xl^ eqd(x^ ::xl^1) andnc xl^0 eqd(x^0::xl^2) andnc n^ eqd Succ n^0)))

(add-co "SEqPListMR")

(pp "CoSEqPListMRClause")

;; all xl^,xl^0,n^(
;;  CoSEqPListMR xl^ xl^0 n^ -> 
;;  xl^ eqd(Nil alpha) andnc xl^0 eqd(Nil alpha) andnc n^ eqd 0 ornc 
;;  exnc x^,x^0,xl^1,xl^2,n^0(
;;   CoSEqPListMR xl^1 xl^2 n^0 andnc 
;;   xl^ eqd(x^ ::xl^1) andnc xl^0 eqd(x^0::xl^2) andnc n^ eqd Succ n^0))

;; 3.  ListNat, ListBoole
;; ======================

(add-var-name "nl" (py "list nat"))

;; ListNatEqToEqD
(set-goal "all nl1,nl2(nl1=nl2 -> nl1 eqd nl2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n1" "nl1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n1" "nl1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n2" "nl2" "n1::nl1=n2::nl2")
(ng)
(inst-with-to "n1::nl1=n2::nl2" 'right "nl1=nl2")
(inst-with-to "n1::nl1=n2::nl2" 'left "n1=n2")
(drop "n1::nl1=n2::nl2")
(assert "nl1 eqd nl2")
 (use "IH")
 (use "nl1=nl2")
(assume "nl1 eqd nl2")
(assert "n1 eqd n2")
 (use "NatEqToEqD")
 (use "n1=n2")
(assume "n1 eqd n2")
(elim "nl1 eqd nl2")
(assume "nl^3")
(elim "n1 eqd n2")
(assume "n^3")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListNatEqToEqD")

;; ListNatEqTotal
(set-goal "all nl^1(TotalList nl^1 -> all nl^2(TotalList nl^2 ->
 TotalBoole(nl^1 =nl^2)))")
(assume "nl^1" "Tnl1")
(elim "Tnl1")
(assume "nl^2" "Tnl2")
(elim "Tnl2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "n^3" "Tn3" "nl^3" "Tnl3" "IHnl3" "nl^4" "Tnl4")
(elim "Tnl4")
(use "TotalBooleFalse")
(assume "n^5" "Tn5" "nl^5" "Tnl5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "NatEqTotal")
(use "Tn3")
(use "Tn5")
(use "IHnl3")
(use "Tnl5")
;; Proof finished.
;; (cp)
(save "ListNatEqTotal")

(add-var-name "p" (py "boole"))
(add-var-name "pl" (py "list boole"))

;; ListBooleEqToEqD
(set-goal "all pl1,pl2(pl1=pl2 -> pl1 eqd pl2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "p1" "pl1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "p1" "pl1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "p2" "pl2" "p1::pl1=p2::pl2")
(ng)
(inst-with-to "p1::pl1=p2::pl2" 'right "pl1=pl2")
(inst-with-to "p1::pl1=p2::pl2" 'left "p1=p2")
(drop "p1::pl1=p2::pl2")
(assert "pl1 eqd pl2")
 (use "IH")
 (use "pl1=pl2")
(assume "pl1 eqd pl2")
(assert "p1 eqd p2")
 (use "BooleEqToEqD")
 (use "p1=p2")
(assume "p1 eqd p2")
(elim "pl1 eqd pl2")
(assume "pl^3")
(elim "p1 eqd p2")
(assume "p^3")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListBooleEqToEqD")

;; ListBooleEqTotal
(set-goal "all pl^1(TotalList pl^1 -> all pl^2(TotalList pl^2 ->
 TotalBoole(pl^1 =pl^2)))")
(assume "pl^1" "Tpl1")
(elim "Tpl1")
(assume "pl^2" "Tpl2")
(elim "Tpl2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "boole^3" "Tp3" "pl^3" "Tpl3" "IHpl3" "pl^4" "Tpl4")
(elim "Tpl4")
(use "TotalBooleFalse")
(assume "boole^5" "Tp5" "pl^5" "Tpl5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "BooleEqTotal")
(use "Tp3")
(use "Tp5")
(use "IHpl3")
(use "Tpl5")
;; Proof finished.
;; (cp)
(save "ListBooleEqTotal")

;; This concludes the collection of properties of TotalList and
;; EqPList.  For faster loading: only keep the definitions and move
;; the rest into a lib file called listeqp.scm.

;; ListTotalVar
(set-goal "all xl TotalList xl")
(use "AllTotalIntro")
(assume "xl^" "Txl")
(use "Txl")
;; Proof finished.
;; (cp)
(save "ListTotalVar")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xl]xl

;; ListSTotalVar
(set-goal "all xl STotalList xl")
(use "AllTotalIntro")
(assume "xl^" "Txl")
(elim "Txl")
(use "STotalListNil")
(assume "x^" "Tx" "xl^0" "Txl0" "STxl0")
(use "STotalListCons")
(use "STxl0")
;; Proof finished.
;; (cp)
(save "ListSTotalVar")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xl](Rec list alpha=>nat)xl 0([x,xl0]Succ)

;; ListTotalToSTotal
(set-goal "all xl^(TotalList xl^ -> STotalList xl^)")
(assume "xl^" "Txl")
(elim "Txl")
;; 3,4
(use "STotalListNil")
;; 4
(assume "x^" "Tx" "xl^1" "Txl1" "STxl1")
(use "STotalListCons")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ListTotalToSTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [xl](Rec list alpha=>nat)xl 0([x,xl0]Succ)

(add-program-constant
 "ListAppend" (py "list alpha=>list alpha=>list alpha") t-deg-zero 'const 1)

(add-infix-display-string "ListAppend" ":+:" 'mul-op)

(add-computation-rules
 "(ListAppend alpha)(Nil alpha)" "[xl]xl"
 "(ListAppend alpha)(x::xl1)" "[xl2](x::xl1:+:xl2)")

(set-totality-goal "ListAppend")
(assume "xl^1" "Txl1" "xl^2" "Txl2")
(elim "Txl1")
(ng #t)
(use "Txl2")
(assume "x^" "Tx" "xl^3" "Txl3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListAppendTotalReal
;; (set-goal (real-and-formula-to-mr-formula
;; 	   (pt "(ListAppend alpha)")
;; 	   (proof-to-formula (theorem-name-to-proof "ListAppendTotal"))))
;; (assume "xl^1" "xl^10" "TMRxl10xl1" "xl^2" "xl^20" "TMRxl20xl2")
;; (elim "TMRxl10xl1")
;; (use "TMRxl20xl2")
;; (assume "x^" "x^0" "TMRx0x" "xl^" "xl^0" "TMRxl0xl" "IH")
;; (ng #t)
;; (use "TotalListConsMR")
;; (use "TMRx0x")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListAppendTotalReal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))

;; all xl^(
;;  STotalList xl^ -> all xl^0(STotalList xl^0 -> STotalList(xl^ :+:xl^0)))

;; ListAppendSTotal
(set-goal
 (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))
(assume "xl^1" "STxl1" "xl^2" "STxl2")
(elim "STxl1")
(ng #t)
(use "STxl2")
(assume "x^" "xl^3" "STxl3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListAppendSTotal")

;; (pp (rename-variables (proof-to-extracted-term "ListAppendSTotal")))
;; [n,n0](Rec nat=>nat)n n0([n1,n2]Succ n2)

;; ListAppendNil
(set-goal "all xl xl:+:(Nil alpha)eqd xl")
(ind)
(use "InitEqD")
(assume "x" "xl" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListAppendNil")

;; ListAppendNilPartial
(set-goal "all xl^(STotalList xl^ -> xl^ :+:(Nil alpha)eqd xl^)")
(assume "xl^" "STxl")
(elim "STxl")
(use "InitEqD")
(assume "x^" "xl^1" "STxl1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListAppendNilPartial")

;; This is not added as a rewrite rule, because ListAppend is defined
;; by recursion over the first argument and expects rules of arity 1.

;; We also provide a variant ListAppd of ListAppend (with display ++),
;; which allows rewrite rules with two arguments.

(add-program-constant
 "ListAppd" (py "list alpha=>list alpha=>list alpha") t-deg-zero)

(add-infix-display-string "ListAppd" "++" 'mul-op)

(add-computation-rules
 "(Nil alpha)++xl2" "xl2"
 "(x1::xl1)++xl2" "x1::xl1++xl2")

(set-totality-goal "ListAppd")
(assume "xl^1" "Txl1" "xl^2" "Txl2")
(elim "Txl1")
(ng #t)
(use "Txl2")
(assume "x^" "Tx" "xl^3" "Txl3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppd alpha)"))))

;; all xl^(
;;  STotalList xl^ -> all xl^0(STotalList xl^0 -> STotalList(xl^ ++xl^0)))

;; ListAppdSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListAppd alpha)"))))
(assume "xl^1" "STxl1" "xl^2" "STxl2")
(elim "STxl1")
(ng #t)
(use "STxl2")
(assume "x^" "xl^3" "STxl3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListAppdSTotal")

;; x: ++xl converts into x::xl.  However, xl1++x2: ++xl2 does not rewrite,
;; because ++ associates to the left.  But we can add the corresponding
;; rule:

(set-goal "all xl1 all x^2,xl^2 xl1++x^2: ++xl^2 eqd xl1++(x^2::xl^2)")
(ind)
(assume "x^2" "xl^2")
(use "InitEqD")
(assume "x" "xl1" "IHxl1" "x^2" "xl^2")
(ng)
(simp "IHxl1")
(use "InitEqD")
;; Proof finished.
;; (cp)

(add-rewrite-rule "xl1++x^2: ++xl^2" "xl1++(x^2::xl^2)")

;; In the other direction this rule would lead to non-termination, if
;; we also had associativity as a rewrite rule.  x2: is x2::(Nil par),
;; and this again is a redex for associativity.

(set-goal "all xl xl++(Nil alpha)eqd xl")
(ind)
(use "InitEqD")
(assume "x" "xl" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(add-rewrite-rule "xl++(Nil alpha)" "xl")

;; ListAppdNilPartial
(set-goal "all xl^(STotalList xl^ -> xl^ ++(Nil alpha)eqd xl^)")
(assume "xl^" "STxl")
(elim "STxl")
(use "InitEqD")
(assume "x^" "xl^1" "STxl1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListAppdNilPartial")

;; ListAppdAssoc
(set-goal "all xl1,xl2,xl3 xl1++(xl2++xl3)eqd xl1++xl2++xl3")
(ind)
(assume "xl2" "xl3")
(use "InitEqD")
(assume "x1" "xl1" "IH")
(ng)
(assume "xl2" "xl3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListAppdAssoc")

;; ListAppdAssocPartial
(set-goal "all xl^1(STotalList xl^1 ->
  all xl^2,xl^3 xl^1++(xl^2++xl^3)eqd xl^1++xl^2++xl^3)")
(assume "xl^1" "STxl1")
(elim "STxl1")
(assume "xl^2" "xl^3")
(use "InitEqD")
(assume "x^" "xl^" "STxl" "IH")
(ng #t)
(assume "xl^2" "xl^3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListAppdAssocPartial")

;; We could add associativity as a rewrite rule by executing
;; (add-rewrite-rule "xl1++(xl2++xl3)" "xl1++xl2++xl3")

;; However, this will block other rewriting rules in long appends.
;; Example: consider (pt "s++(L::t++R:)") and (pt "s++(L::t)++R:").
;; Both are normal, since rewriting (pt "(L::t)++R:") into (pt
;; "L::t++R:") is blocked by the leading s++ and the fact that ++
;; associates to the left.

(add-program-constant "ListLength" (py "list alpha=>nat") t-deg-zero)
;; (add-prefix-display-string "ListLength" "Lh")
(add-token
 "Lh" 'prefix-op
 (lambda (x)
   (make-term-in-app-form
    (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "ListLength"))
	    (uninst-type (const-to-uninst-type const))
	    (pattern (arrow-form-to-arg-type uninst-type))
	    (instance (term-to-type x))
	    (tsubst (type-match pattern instance)))
       (if tsubst
	   (const-substitute const tsubst #f)
	   (myerror "types do not match" pattern instance))))
    x)))

(add-display (py "nat") (make-display-creator1 "ListLength" "Lh" 'prefix-op))

;; (add-display
;;  (py "nat")
;;  (lambda (x)
;;    (if (term-in-app-form? x)
;;        (let ((op (term-in-app-form-to-final-op x)))
;; 	 (if
;; 	  (and (term-in-const-form? op)
;; 	       (string=? "ListLength"
;; 			 (const-to-name (term-in-const-form-to-const op))))
;; 	  (list 'prefix-op "Lh"
;; 		(term-to-token-tree (term-in-app-form-to-arg x)))
;; 	  #f))
;;        #f)))

;; (make-display-creator1 "ListLength" "Lh" 'prefix-op)

(add-computation-rules
 "Lh(Nil alpha)" "Zero"
 "Lh(x::xl)" "Succ Lh xl")

(set-totality-goal "ListLength")
(assume "xl^" "Txl")
(elim "Txl")
(ng #t)
(use "TotalNatZero")
(assume "x^" "Tx" "xl^1" "Txl1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; ListLengthSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListLength alpha)"))))
(assume "xl^" "STxl")
(elim "STxl")
(ng #t)
(use "TotalNatZero")
(assume "x^" "xl^1" "STxl1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLengthSTotal")

(pp (rename-variables (proof-to-extracted-term "ListLengthSTotal")))
;; [n](Rec nat=>nat)n 0([n0,n1]Succ n1)

;; ListLhZeroToEqNil
(set-goal "all xl(Lh xl=0 -> xl eqd(Nil alpha))")
(cases)
(assume "Useless")
(use "InitEqD")
(assume "x" "xl" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "ListLhZeroToEqNil")

;; ListLhZeroToEqNilPartial
(set-goal "all xl^(STotalList xl^ -> Lh xl^ =0 -> xl^ eqd(Nil alpha))")
(assume "xl^" "STxl")
(elim "STxl")
(assume "Useless")
(use "InitEqD")
(assume "x^" "xl^1" "STxl1" "IH" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "ListLhZeroToEqNilPartial")

;; ListLhAppend
(set-goal "all xl1,xl2 Lh(xl1:+:xl2)=Lh xl1+Lh xl2")
(ind)
(assume "xl2")
(use "Truth")
(assume "x" "xl1" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLhAppend")

(add-rewrite-rule "Lh(xl1:+:xl2)" "Lh xl1+Lh xl2")

;; ListLhAppd
(set-goal "all xl1,xl2 Lh(xl1++xl2)=Lh xl1+Lh xl2")
(ind)
(assume "xl2")
(use "Truth")
(assume "x" "xl1" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLhAppd")

(add-rewrite-rule "Lh(xl1++xl2)" "Lh xl1+Lh xl2")

;; Now for projection ListProj.  We use the rule (n thof (Nil alpha)) ->
;; (Inhab alpha)

(add-program-constant "ListProj" (py "nat=>list alpha=>alpha") t-deg-zero)

(add-infix-display-string "ListProj" "thof" 'pair-op) ;right associative

(add-token
 "__" 'mul-op ;hence left associative
 (lambda (xl y)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "ListProj"))
	    (tvars (const-to-tvars const))
	    (listtype (term-to-type xl))
	    (type (car (alg-form-to-types listtype)))
	    (subst (make-substitution tvars (list type))))
       (const-substitute const subst #f)))
    y xl)))

;; Not used (reason: occurrences of "thof" examples/tait)
;; (add-display
;;  (py "alpha")
;;  (lambda (x)
;;    (if (term-in-app-form? x)
;;        (let ((op (term-in-app-form-to-final-op x))
;; 	     (args (term-in-app-form-to-args x)))
;; 	 (if (and (term-in-const-form? op)
;; 		  (string=? "ListProj"
;; 			    (const-to-name (term-in-const-form-to-const op)))
;; 		  (= 2 (length args)))
;; 	     (list 'mul-op "__"
;; 		   (term-to-token-tree (car args))
;; 		   (term-to-token-tree (cadr args)))
;; 	     #f))
;;        #f)))

(add-computation-rules
 "nat thof(Nil alpha)" "(Inhab alpha)"
 "Zero thof x::xl1" "x"
 "Succ nat1 thof x::xl1" "nat1 thof xl1")

;; (pp (nt (pt "0 thof 3::2::1::0:")))
;; 3
;; (pp (nt (pt "1 thof 3::2::1::0:")))
;; 2
;; (pp (nt (pt "3 thof 3::2::1::0:")))
;; 0
;; (pp (nt (pt "4 thof 3::2::1::0:")))
;; (Inhab nat)
;; (pp (nt (pt "(3::2::1::0:)__1")))
;; 2
;; (pp (nt (pt "(3::2::1::0:)__4")))
;; (Inhab nat)

;; (set-totality-goal "ListProj")
;; (assume "n^" "Tn")
;; (elim "Tn")
;; (assume "xl^" "Txl")
;; (elim "Txl")
;; (ng #t)
;; (use "InhabTotal") ;does not exist
;; (assume "x^" "Tx" "xl^1" "Txl1" "IH")
;; (ng #t)
;; (use "Tx")
;; (assume "n^1" "Tn1" "IHn1" "xl^1" "Txl1")
;; (elim "Txl1")
;; (ng #t)
;; (use "InhabTotal") ;does not exist
;; (assume "x^" "Tx" "xl^2" "Txl2" "IHxl2")
;; (ng #t)
;; (use "IHn1")
;; (use "Txl2")
;; ;; Proof finished.
;; ;; (cp)
;; (save-totality)

;; Since InhabTotal was used, totality of (ListProj tau) requires that
;; tau is a closed type with a total inhabitant (e.g. streams of booleans
;; are not allowed).  This remark also applies to ListBar ListHead ListLast

;; ListProjExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListProj alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> all n^,n^0(
;;      EqPNatNc n^ n^0 -> 
;;      all xl^,xl^0(
;;       (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xl^ xl^0 -> 
;;       EqPNc(n^ thof xl^)(n^0 thof xl^0)))

(assume "InhabExtNc")
(assert "all xl^,xl^0(
     (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xl^ xl^0 -> 
     all n^,n^0(EqPNatNc n^ n^0 -> EqPNc(n^ thof xl^)(n^0 thof xl^0)))")
(assume "xl^1" "xl^2" "xl1=xl2")
(elim "xl1=xl2")
;; 6,7
(assume "n^1" "n^2" "n1=n2")
(ng #t)
(use "InhabExtNc")
;; 7
(assume "x^1" "x^2" "x1=x2" "xl^3" "xl^4" "xl3=xl4" "IH" "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 11,12
(ng #t)
(use "x1=x2")
;; 12
(assume "n^3" "n^4" "n3=n4" "IHn")
(ng #t)
(use "IH")
(use "n3=n4")
;; Assertion proved.
(assume "Assertion" "n^1" "n^2" "n1=n2" "xl^1" "xl^2" "xl1=xl2")
(use "Assertion")
(use "xl1=xl2")
(use "n1=n2")
;; Proof finished.
;; (cp)
(save "ListProjExtNc")	

;; The following only works for totally inhabitant types like nat

;; ListNatProjAppdLeft
(set-goal "all nl1,n,nl2(n<Lh nl1 -> (n thof(nl1++nl2))eqd(n thof nl1))")
(ind)
(assume "n" "nl2" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n1" "nl1" "IHnl1")
(ng)
(cases)
(ng)
(strip)
(use "InitEqD")
(ng)
(use "IHnl1")
;; Proof finished.
;; (cp)
(save "ListNatProjAppdLeft")

;; ListProjAppdLeft
;; (set-goal "all xl1,n,xl2(n<Lh xl1 -> (n thof(xl1++xl2))eqd(n thof xl1))")
;; (ind)
;; (assume "n" "xl2" "Absurd")
;; (use "EfEqD")
;; (use "Absurd")
;; (assume "x1" "xl1" "IHxl1")
;; (ng)
;; (cases)
;; x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
;; the type
;; alpha
;; of the syntactically total term
;; x1
;; should be totally inhabited

;; ListNatProjAppdRight
(set-goal "all nl1,nl2,n(n<Lh nl2 -> (Lh nl1+n thof(nl1++nl2))eqd(n thof nl2))")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "n1" "nl1" "IHnl1")
(ng)
(use "IHnl1")
;; Proof finished.
;; (cp)
(save "ListNatProjAppdRight")

;; Usage of InhabTotal in the proof of totality of (ListProj tau) can be
;; avoided if tau is a closed type with a total inhabitant.  Example:

(add-program-constant "ListNatProj" (py "nat=>list nat=>nat") t-deg-zero)

(add-computation-rules
 "ListNatProj n(Nil nat)" "Zero"
 "ListNatProj Zero (n::nl)" "n"
 "ListNatProj(Succ n)(n0::nl)" "ListNatProj n nl")

(set-totality-goal "ListNatProj")
(assert "all nl^(TotalList nl^ -> all n^(TotalNat n^ -> 
         TotalNat(ListNatProj n^ nl^)))")
(assume "nl^" "Tnl")
(elim "Tnl")
;; 5,6
(ng)
(assume "n^" "Tn")
(intro 0)
;; 6
(assume "n^" "Tn" "nl^1" "Tnl1" "IH" "n^1" "Tn1")
(elim "Tn1")
;; 10,11
(ng)
(use "Tn")
;; 11
(assume "n^2" "Tn2" "Useless")
(ng)
(use "IH")
(use "Tn2")
;; Assertion proved.
(search)
;; Proof finished.
;; (cp)
(save-totality)

(add-program-constant
 "ListFBar" (py "(nat=>alpha)=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListFBar" "fbar" 'pair-op) ;right associative

(add-computation-rules
 "xs fbar 0" "(Nil alpha)"
 "xs fbar Succ n" "xs Zero::([n1]xs(Succ n1))fbar n")

;; (pp (nt (pt "Succ fbar 4")))
;; 1::2::3::4:
;; (pp (nt (pt "([n]n+3)fbar 4")))
;; 3::4::5::6:

;; ListFBarTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(ListFBar alpha)"))))

;; all xs^(
;;      all n^(TotalNat n^ -> Total(xs^ n^)) -> 
;;      all n^(TotalNat n^ -> TotalList(xs^ fbar n^)))

(assert "all n^(
     TotalNat n^ -> 
     all xs^(
      all n^0(TotalNat n^0 -> Total(xs^ n^0)) -> TotalList(xs^ fbar n^)))")
(assume "n^" "Tn")
(elim "Tn")
;; 5,6
(assume "xs^" "Txs")
(ng #t)
(use "TotalListNil")
;; 6
(assume "n^1" "Tn1" "IH" "xs^" "Txs")
(ng #t)
(use "TotalListCons")
(use "Txs")
(use "TotalNatZero")
(use "IH")
(ng #t)
(assume "n^2" "Tn2")
(use "Txs")
(use "TotalNatSucc")
(use "Tn2")
;; Assertion proved.
(assume "Assertion" "xs^" "Txs" "n^" "Tn")
(use "Assertion")
(use "Tn")
(use "Txs")
;; Proof finished.
;; (cp)
(save-totality)

;; ok, ListFBarTotal has been added as a new theorem.
;; ok, computation rule xs fbar 0 -> (Nil alpha) added
;; ok, computation rule xs fbar Succ n -> xs 0::([n1]xs(Succ n1))fbar n added

;; (term-to-t-deg (pt "(ListFBar alpha)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs,n]
;;  (Rec nat=>(nat=>alpha)=>list alpha)n([xs0](Nil alpha))
;;  ([n0,((nat=>alpha)=>list alpha),xs0]
;;    xs0 0::((nat=>alpha)=>list alpha)([n1]xs0(Succ n1)))
;;  xs

;; Moreover we have extensionality of ListFBar:

;; ListFBarExtNc
(set-goal
 (rename-variables (term-to-pure-extnc-formula (pt "(ListFBar alpha)"))))

;; all xs^,xs^0(
;;      all n^,n^0(EqPNatNc n^ n^0 -> EqPNc(xs^ n^)(xs^0 n^0)) -> 
;;      all n^,n^0(
;;       EqPNatNc n^ n^0 -> 
;;       (REqPListNc (cterm (alpha^,alpha^0) EqPNc alpha^ alpha^0))(xs^ fbar n^)
;;       (xs^0 fbar n^0)))

(assert "all n^,n^0(
     EqPNatNc n^ n^0 -> 
     all xs^,xs^0(
      all n^1,n^2(EqPNatNc n^1 n^2 -> EqPNc(xs^ n^1)(xs^0 n^2)) -> 
      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(xs^ fbar n^)
      (xs^0 fbar n^0)))")
(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 5,6
(assume "xs^1" "xs^2" "EqPHyp")
(ng #t)
(intro 0)
;; 6
(assume "n^3" "n^4" "n3=n4" "IH" "xs^1" "xs^2" "EqPHyp")
(ng #t)
(use-with
 "REqPListNcCons"
 (py "alpha") (make-cterm (pv "x^1")  (pv "x^2") (pf "EqPNc x^1 x^2"))
 (pt "xs^1 0") (pt "xs^2 0") "?"
 (pt "([n]xs^1(Succ n))fbar n^3") (pt "([n]xs^2(Succ n))fbar n^4") "?")
(use "EqPHyp")
(intro 0)
(use "IH")
(ng #t)
(assume "n^5" "n^6" "n5=n6")
(use "EqPHyp")
(intro 1)
(use "n5=n6")
;; Assertion proved.
(assume "Assertion" "xs^1" "xs^2" "EqPHyp" "n^1" "n^2" "n1=n2")
(use "Assertion")
(use "n1=n2")
(use "EqPHyp")
;; Proof finished.
;; (cp)
(save "ListFBarExtNc")

(set-goal "all n,xs^ Lh(xs^ fbar n)=n")
(ind)
(assume "xs^")
(ng #t)
(use "Truth")
(assume "n" "IHn" "xs^")
(ng #t)
(use "IHn")
;; Proof finished.
;; (cp)

(add-rewrite-rule "Lh(xs^ fbar n)" "n")

(add-program-constant "ListBar" (py "list alpha=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListBar" "bar" 'add-op) ;left associative

(add-computation-rules
 "xl bar Zero" "(Nil alpha)"
 "(Nil alpha)bar(Succ n)" "(Inhab alpha)::(Nil alpha) bar n"
 "(x::xl)bar Succ n" "x::xl bar n")

;; (pp (nt (pt "(0::1::2::3::4:)bar 2")))
;; 0::1:
;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

;; (add-computation-rule "(Inhab nat)" "0")

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::0::0:

;; Usage of InhabTotal in the proof of totality of ListBar can be
;; avoided if the list elements are of a closed type with a total
;; inhabitant.  Example:

;; (pp (pf "nl bar 0"))

(add-program-constant "ListNatBar" (py "list nat=>nat=>list nat") t-deg-zero)

(add-computation-rules
 "ListNatBar nl Zero" "(Nil nat)"
 "ListNatBar(Nil nat)(Succ n0)" "Zero::ListNatBar(Nil nat)n0"
 "ListNatBar(n::nl)(Succ n0)" "n::(ListNatBar nl n0)")

(set-totality-goal "ListNatBar")
(assert "all n^(TotalNat n^ -> all nl^(TotalList nl^ -> 
         TotalList(ListNatBar nl^ n^)))")
(fold-alltotal)
(ind)
(strip)
(ng #t)
(intro 0)
;; 6
(assume "n" "IH")
(fold-alltotal)
(cases)
;; 11,12
(ng #t)
(intro 1)
(intro 0)
(use "IH")
(intro 0)
;; 12
(assume "n0" "nl")
(ng #t)
(intro 1)
(use "TotalVar")
(use "IH")
(use "TotalVar")
;; Assertion proved.
(auto)
;; Proof finished.
;; (cp)
(save-totality)

;; ListBarExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListBar alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> 
;;     all xl^,xl^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xl^ xl^0 -> 
;;      all n^,n^0(
;;       EqPNatNc n^ n^0 -> 
;;       (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(xl^ bar n^)(xl^0 bar n^0)))

(assume "InhabExtNc" "xl^1" "xl^2" "xl1=xl2")
(elim "xl1=xl2")
;; 3,4
(assume "n^1" "n^2" "n1=n2")
(elim "n1=n2")
(ng #t)
(intro 0)
;; 7
(assume "n^3" "n^4" "n3=n4" "IH")
(ng #t)
(intro 1)
(use "InhabExtNc")
(use "IH")
;; 4
(assume "x^1" "x^2" "x1=x2" "xl^3" "xl^4" "xl3=xl4" "IH" "n^1" "n^2" "n1=n2")
(elim "n1=n2")
;; 14,15
(ng #t)
(intro 0)
;; 15
(assume "n^3" "n^4" "n3=n4" "IHn")
(ng #t)
(intro 1)
(use "x1=x2")
(use "IH")
(use "n3=n4")
;; Proof finished.
;; (cp)
(save "ListBarExtNc")

(add-program-constant "ListLengthNat" (py "list nat=>nat"))

(add-computation-rules
 "ListLengthNat(Nil nat)" "Zero"
 "ListLengthNat(n::nl)" "Succ(ListLengthNat nl)")

(set-totality-goal "ListLengthNat")
(fold-alltotal)
(ind)
;; 3,4
(intro 0)
;; 4
(assume "n" "nl" "IH")
(intro 1)
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; ListLengthNatZeroToEqNil
(set-goal "all nl(ListLengthNat nl=0 -> nl eqd(Nil nat))")
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n" "nl" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "ListLengthNatZeroToEqNil")

;; ListLengthNatZeroToEqNilPartial
(set-goal "all nl^(STotalList nl^ -> ListLengthNat nl^ =0 -> nl^ eqd(Nil nat))")
(assume "nl^" "STnl")
(elim "STnl")
(assume "Useless")
(use "InitEqD")
(assume "n^" "nl^1" "STnl1" "IH" "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cp)
(save "ListLengthNatZeroToEqNilPartial")

;; ListLengthNatAppend
(set-goal
 "all nl1,nl2 ListLengthNat(nl1:+:nl2)=ListLengthNat nl1+ListLengthNat nl2")
(ind)
(assume "nl2")
(use "Truth")
(assume "n" "nl1" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLengthNatAppend")

(add-rewrite-rule "ListLengthNat(nl1:+:nl2)"
		  "ListLengthNat nl1+ListLengthNat nl2")

;; ListLengthNatAppd
(set-goal
 "all nl1,nl2 ListLengthNat(nl1++nl2)=ListLengthNat nl1+ListLengthNat nl2")
(ind)
(assume "nl2")
(use "Truth")
(assume "n" "nl1" "IH")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLengthNatAppd")

(set-goal "all n all ns^ ListLengthNat(ns^ fbar n)=n")
(ind)
(assume "ns^")
(ng #t)
(use "Truth")
(assume "n" "IHn")
(assume "ns^")
(ng #t)
(use "IHn")
;; Proof finished.
;; (cp)

(add-rewrite-rule "ListLengthNat(ns^ fbar n)" "n")

(set-goal "all nl,n ListLengthNat(ListNatBar nl n)=n")
(ind)
(ind)
(ng #t)
(use "Truth")
(assume "n" "IHn")
(ng #t)
(use "IHn")
(assume "n" "nl" "IHnl")
(cases)
(ng #t)
(use "Truth")
(assume "n0")
(ng #t)
(use "IHnl")
;; Proof finished.
;; (cp)
(add-rewrite-rule "ListLengthNat(ListNatBar nl n)" "n")

;; A list of length n+1 can be seen as the result of appending to its
;; initial segment of length n its final element.

;; ListNatBarAppdLast
(set-goal "all n,nl(ListLengthNat nl=Succ n -> (nl bar n)++(n thof nl):eqd nl)")
(ind)
;; Base
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "nl" "ListLengthNat nl=0")
(ng #t)
(assert "nl eqd(Nil nat)")
 (use "ListLengthNatZeroToEqNil")
 (use "ListLengthNat nl=0")
(assume "nl=Nil")
(simp "nl=Nil")
(use "InitEqD")
;; Step
(assume "n" "IHn")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n0" "nl" "ListLengthNat nl=Succ n0")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "ListLengthNat nl=Succ n0")
;; Proof finished.
;; (cp)
(save "ListNatBarAppdLast")

;; ListFBarAppdLast
(set-goal "all n all xs^ (xs^ fbar Succ n)eqd(xs^ fbar n)++(xs^ n):")
(ind)
(assume "xs^")
(ng #t)
(use "InitEqD")
;; Step
(assume "n" "IHn" "xs^")
(assert "(xs^ fbar Succ(Succ n))eqd(xs^ 0::([n]xs^ (Succ n))fbar Succ n)")
 (ng #t)
 (use "InitEqD")
(assume "Equality")
(simp "Equality")
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListFBarAppdLast")

;; Now the relation between ListBar and ListFBar

;; ListBarFBar
(set-goal "all n,xl xl bar n eqd(([m]m thof xl)fbar n)")
(ind)
(assume "xl")
(ng #t)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
(assume "x" "xl")
(ng #t)
(simp "IHn")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListBarFBar")

;; ListBarFBarPlus
(set-goal "all n all m,xs^((xs^ fbar(n+m))bar n eqd(xs^ fbar n))")
(ind)
(assume "m" "xs^")
(ng)
(use "InitEqD")
(assume "n" "IH"  "m" "xs^")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListBarFBarPlus")

;; ListProjFBar
(set-goal "all l,n all xs^(n<l -> (n thof xs^ fbar l)eqd xs^ n)")
(ind)
;; 2,3
(assume "n" "xs^" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(strip)
(use "InitEqD")
(assume "m" "xs^" "m<n")
(ng #t)
(use "IH")
(use "m<n")
;; Proof finished.
;; (cp)
(save "ListProjFBar")

;; (add-var-name "ns" (py "nat=>nat"))

;; ListNatProjFBar
(set-goal "all l,n all ns^(n<l -> (ListNatProj n(ns^ fbar l))eqd ns^ n)")
(ind)
;; 2,3
(assume "n" "ns^" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(strip)
(use "InitEqD")
(assume "m" "ns^" "m<n")
(ng #t)
(use "IH")
(use "m<n")
;; Proof finished.
;; (cp)
(save "ListNatProjFBar")

(add-var-name "psi" (py "alpha1=>list alpha1=>alpha2"))
(add-var-name "y" (py "alpha1"))
(add-var-name "yl" (py "list alpha1"))
(add-var-name "z" (py "alpha2"))
(add-var-name "zl" (py "list alpha2"))

;; ListIfTotal
(set-goal "all yl^(TotalList yl^ ->
 all z^,psi^(Total z^ ->
 all y^,yl^(Total y^ -> TotalList yl^ -> Total(psi^ y^ yl^)) ->
 Total[if yl^ z^ psi^]))")
(assume "yl^" "Tyl" "z^" "psi^" "Tz" "Tpsi")
(elim "Tyl")
(use "Tz")
(assume "y^1" "Ty1" "yl^1" "Tyl1" "Useless")
(ng #t)
(use "Tpsi")
(use "Ty1")
(use "Tyl1")
;; Proof finished.
;; (cp)
(save "ListIfTotal")

;; ListIfSTotal
(set-goal "all yl^(STotalList yl^ ->
 all z^,psi^(Total z^ ->
 all y^,yl^(STotalList yl^ -> Total(psi^ y^ yl^)) ->
 Total[if yl^ z^ psi^]))")
(assume "yl^" "STyl" "z^" "psi^" "Tz" "STpsi")
(elim "STyl")
(use "Tz")
(assume "y^1" "yl^1" "STyl1" "Useless")
(ng #t)
(use "STpsi")
(use "STyl1")
;; Proof finished.
;; (cp)
(save "ListIfSTotal")

(add-program-constant
 "ListMap" (py "(alpha1=>alpha2)=>list alpha1=>list alpha2") t-deg-zero)

(add-infix-display-string "ListMap" "map" 'pair-op) ;right associative

(add-var-name "phi" (py "alpha1=>alpha2"))

(add-computation-rules
 "phi map(Nil alpha1)" "(Nil alpha2)"
 "phi map y::yl" "phi y::phi map yl")

;; (pp (nt (pt "Pred map 2::3::4:")))
;; 1::2::3:

;; ListMapTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(ListMap alpha1 alpha2)"))))

;; all phi^(
;;      all y^(Total y^ -> Total(phi^ y^)) -> 
;;      all yl^(TotalList yl^ -> TotalList(phi^ map yl^)))

(assume "phi^" "Tphi" "yl^" "Tyl^")
(elim "Tyl^")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "y^" "Ty" "yl^1" "Tyl1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tphi")
(use "Ty")
(use "IH")
;; Proof finished.
;; (cp)
;; (save "ListMapTotal")
(save-totality)

;; ok, ListMapTotal has been added as a new theorem.
;; ok, computation rule phi map(Nil alpha1) -> (Nil alpha2) added
;; ok, computation rule phi map y::yl -> phi y::phi map yl added

;; (term-to-t-deg (pt "(ListMap alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [phi,yl]
;;  (Rec list alpha1=>list alpha2)yl(Nil alpha2)([y,yl0](Cons alpha2)(phi y))

;; Moreover we have extensionality of ListMap:

;; ListMapExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(ListMap alpha1 alpha2)")
					 (pt "(ListMap alpha1 alpha2)"))))

;; all phi^,phi^0(
;;      all y^,y^0(EqP y^ y^0 -> EqP(phi^ y^)(phi^0 y^0)) -> 
;;      all yl^,yl^0(
;;       (REqPList (cterm (y^,y^0) EqP y^ y^0))yl^ yl^0 -> 
;;       (REqPList (cterm (z^,z^0) EqP z^ z^0))(phi^ map yl^)(phi^0 map yl^0)))

(assume "phi^1" "phi^2" "EqPphi1phi2" "yl^1" "yl^2" "EqPyl1yl2")
(elim "EqPyl1yl2")
;; 3,4
(ng #t)
(use "REqPListNil")
;; 4
(assume "y^1" "y^2" "EqPy1y2" "yl^3" "yl^4" "EqPyl3yl4" "IH")
(ng #t)
(use-with
 "REqPListCons"
 (py "alpha2") (make-cterm (pv "z^1")  (pv "z^2") (pf "EqP z^1 z^2"))
 (pt "phi^1 y^1") (pt "phi^2 y^2") "?"
 (pt "phi^1 map yl^3") (pt "phi^2 map yl^4") "?")
(use "EqPphi1phi2")
(use "EqPy1y2")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListMapExt")

;; ListMapSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)"))))
(assume "phi^" "Tphi" "yl^" "STyl")
(elim "STyl")
(ng #t)
(use "STotalListNil")
(assume "y^1" "yl^1" "STyl1" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
;; (cp)
(save "ListMapSTotal")

;; ListLengthNatMap
(set-goal "all ns,nl ListLengthNat(ns map nl)=ListLengthNat nl")
(assume "ns")
(ind)
(ng #t)
(use "Truth")
(assume "n" "nl" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLengthNatMap")

;; ;; ListLhMap
;; (set-goal "all phi,yl Lh(phi map yl)=Lh yl")
;; (assume "phi")
;; (ind)
;; (use "Truth")
;; (assume "y" "yl" "IH")
;; (use "IH")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListLhMap")

;; ListLhMapPartial
(set-goal "all phi^,yl^(STotalList yl^ -> Lh(phi^ map yl^)=Lh yl^)")
(assume "phi^" "yl^" "STyl")
(elim "STyl")
(ng #t)
(use "Truth")
(assume "y^" "yl^1" "STyl1" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLhMapPartial")

;; ;; ListMapAppend
;; (set-goal "all phi,yl2,yl1 (phi map yl1:+:yl2)eqd(phi map yl1):+:(phi map yl2)")
;; (assume "phi" "yl2")
;; (ind)
;; (ng)
;; (use "InitEqD")
;; (assume "y" "yl" "IH")
;; (ng)
;; (simp "IH")
;; (use "InitEqD")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListMapAppend")

;; ListMapAppendPartial
(set-goal "all phi^,yl^2,yl^1(
       STotalList yl^1 ->
       (phi^ map yl^1:+:yl^2)eqd(phi^ map yl^1):+:(phi^ map yl^2))")
(assume "phi^" "yl^2" "yl^1" "STyl1")
(elim "STyl1")
(ng #t)
(use "InitEqD")
(assume "y^" "yl^" "STyl" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListMapAppendPartial")

;; ;; ListMapAppd
;; (set-goal "all phi,yl2,yl1 (phi map yl1++yl2)eqd(phi map yl1)++(phi map yl2)")
;; (assume "phi" "yl2")
;; (ind)
;; (ng)
;; (use "InitEqD")
;; (assume "y" "yl" "IH")
;; (ng)
;; (simp "IH")
;; (use "InitEqD")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListMapAppd")

;; ListMapAppdPartial
(set-goal "all phi^,yl^2,yl^1(
       STotalList yl^1 ->
       (phi^ map yl^1++yl^2)eqd(phi^ map yl^1)++(phi^ map yl^2))")
(assume "phi^" "yl^2" "yl^1" "STyl1")
(elim "STyl1")
(ng #t)
(use "InitEqD")
(assume "y^" "yl^" "STyl" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListMapAppdPartial")

;; ;; ListProjMap
;; (set-goal "all phi^ all yl,n(n<Lh yl ->
;;  (n thof phi^ map yl)eqd phi^(n thof yl))")
;; (assume "phi^")
;; (ind)
;; (assume "n" "Absurd")
;; (use "EfEqD")
;; (use "Absurd")
;; (assume "y" "yl" "IH")
;; (cases) ;alpha1 should be totally inhabited
;; (assume "Useless")
;; (ng #t)
;; (use "InitEqD")
;; (assume "n" "n<Lh yl")
;; (ng #t)
;; (use "IH")
;; (use "n<Lh yl")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListProjMap")

;; ListProjMapPartial
(set-goal "all phi^,yl^(STotalList yl^ -> all n(n<Lh yl^ ->
 (n thof phi^ map yl^)eqd phi^(n thof yl^)))")
(assume "phi^" "yl^" "STyl")
(elim "STyl")
(assume "n" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "y^" "yl^0" "IH")
(ng #t)
(assume "AllH")
(cases)
(ng #t)
(assume "Useless")
(use "InitEqD")
(ng #t)
(use "AllH")
;; Proof finished.
;; (cp)
(save "ListProjMapPartial")

(add-var-name "ys" (py "nat=>alpha1"))

;; ListMapFbar
(set-goal "all phi^ all n all ys^(
       phi^ map ys^ fbar n)eqd(([n]phi^(ys^ n))fbar n)")
(assume "phi^")
(ind)
(assume "ys^")
(ng #t)
(use "InitEqD")
(assume "n" "IHn" "ys^")
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListMapFbar")

(add-rewrite-rule
 "phi^ map ys^ fbar n" "([n]phi^(ys^ n))fbar n")

(add-program-constant
 "Consn" (py "alpha=>nat=>list alpha=>list alpha") t-deg-zero)

(add-computation-rules
 "(Consn alpha)x 0 xl" "xl"
 "(Consn alpha)x(Succ n)(Nil alpha)" "x::(Consn alpha)x n(Nil alpha)"
 "(Consn alpha)x(Succ n)(x1::xl)" "x1::(Consn alpha)x n(xl)")

;; (pp (nt (pt "(Consn nat)n 7(0::1::2:)")))
;; => 0::1::2::n::n::n::n:

(set-totality-goal "Consn")
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xl^" "Txl")
(elim "Txl")
(ng #t)
(use "TotalListNil")
(assume "x^1" "Tx1" "xl^1" "Txl1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx1")
(use "Txl1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xl^" "Txl")
(elim "Txl")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IHn1")
(use "TotalListNil")
(assume "x^1" "Tx1" "xl^1" "Txl1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx1")
(use "IHn1")
(use "Txl1")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))

;; all x^(
;;  Total x^ ->
;;  all n^(
;;   TotalNat n^ ->
;;   all xl^(STotalList xl^ -> STotalList((Consn alpha)x^ n^ xl^))))

;; ConsnSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xl^" "Txl")
(elim "Txl")
(ng #t)
(use "STotalListNil")
(assume "x^1" "xl^1" "Txl1" "Useless")
(ng #t)
(use "STotalListCons")
(use "Txl1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xl^" "STxl")
(elim "STxl")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STotalListNil")
(assume "x^1" "xl^1" "STxl1" "Useless")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ConsnSTotal")

;; ListLhConsn
(set-goal "all x^1,xl^(
        STotalList xl^ ->
        all n(
         Lh xl^ <=n ->
         Lh(xl^ :+:(Consn alpha)x^1(n--Lh xl^)(Nil alpha))eqd n))")
(assume "x^1" "xl^" "STxl")
(elim "STxl")
(ind)
;; 5,6
(assume "Useless")
(ng #t)
(use  "InitEqD")
;; 6
(assume "n" "IHn" "Useless")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Truth")
;; 4
(assume "x^2" "xl^1" "STxl1" "IHl")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "Lh xl^1 <=n")
(ng #t)
(assert "all n1,n^2(TotalNat n^2 -> Pred(Succ n1--n^2)eqd n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)eqd n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "InitEqD")
(assume "H")
(simp "H")
(simp "IHl")
(use "InitEqD")
(use "Lh xl^1 <=n")
(use "ListLengthSTotal")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ListLhConsn")

;; ListLhConsnAppd
(set-goal "all x^1,xl^(
        STotalList xl^ ->
        all n(
         Lh xl^ <=n ->
         Lh(xl^ ++(Consn alpha)x^1(n--Lh xl^)(Nil alpha))eqd n))")
(assume "x^1" "xl^" "STxl")
(elim "STxl")
(ind)
(assume "Useless")
(ng #t)
(use "InitEqD")
(assume "n" "IHn" "Useless")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Truth")
(assume "x^2" "xl^2" "STxl2" "IHl")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "Lh xl^ <=n")
(ng #t)
(assert "all n1 all n^2(TotalNat n^2 -> Pred(Succ n1--n^2)eqd n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)eqd n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "InitEqD")
(assume "H")
(simp "H")
(simp "IHl")
(use "InitEqD")
(use "Lh xl^ <=n")
(use "ListLengthSTotal")
(use "STxl2")
;; Proof finished.
;; (cp)
(save "ListLhConsnAppd")

;; We add a bounded universal quantifier.  AllBList n P means that for
;; all lists of length n of booleans the property P holds.

(add-program-constant
 "AllBList" (py "nat=>(list boole=>boole)=>boole") t-deg-zero)

(add-var-name "pl" (py "list boole"))
(add-var-name "pltop" (py "list boole=>boole"))

(add-computation-rules
 "AllBList 0 pltop" "pltop(Nil boole)"
 "AllBList(Succ n)pltop" "(AllBList n([pl]pltop(True::pl)))andb
                          (AllBList n([pl]pltop(False::pl)))")

;; AllBListTotal
(set-goal (rename-variables (term-to-totality-formula (pt "AllBList"))))

;; all n^(
;;      TotalNat n^ -> 
;;      all pltop^(
;;       all pl^(TotalList pl^ -> TotalBoole(pltop^ pl^)) -> 
;;       TotalBoole(AllBList n^ pltop^)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(assume "pltop^" "Tpltop")
(ng #t)
(use "Tpltop")
(use "TotalListNil")
;; 4
(assume "n^1" "Tn1" "IH" "pltop^" "Tpltop")
(ng #t)
(use "AndConstTotal")
;; 10,11
(use "IH")
(ng #t)
(assume "pl^" "Tpl")
(use "Tpltop")
(use "TotalListCons")
(use "TotalBooleTrue")
(use "Tpl")
;; 11
(use "IH")
(ng #t)
(assume "pl^" "Tpl")
(use "Tpltop")
(use "TotalListCons")
(use "TotalBooleFalse")
(use "Tpl")
;; Proof finished.
;; (cp)
;; (save "AllBListTotal")
(save-totality)

;; ok, AllBListTotal has been added as a new theorem.
;; ok, computation rule AllBList 0 pltop -> pltop(Nil boole) added
;; ok, computation rule AllBList(Succ n)pltop ->
;;        AllBList n([pl]pltop(True::pl))andb
;;        AllBList n([pl]pltop(False::pl)) added

;; (term-to-t-deg (pt "AllBList"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(list boole=>boole)=>boole)n([pltop]pltop(Nil boole))
;;  ([n0,((list boole=>boole)=>boole),pltop]
;;    ((list boole=>boole)=>boole)([pl]pltop(True::pl))andb
;;    ((list boole=>boole)=>boole)([pl]pltop(False::pl)))

;; Moreover we have extensionality of AllBList:

;; AllBListExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "AllBList") (pt "AllBList"))))

;; all n^(
;;      TotalNat n^ -> 
;;      all pltop^,pltop^0(
;;       all pl^(TotalList pl^ -> EqPBoole(pltop^ pl^)(pltop^0 pl^)) -> 
;;       EqPBoole(AllBList n^ pltop^)(AllBList n^ pltop^0)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(assume  "pltop^1" "pltop^2" "Hyp")
(use "Hyp")
(use "TotalListNil")
;; 4
(assume "n^1" "Tn1" "IH" "pltop^1" "pltop^2" "EqPHyp")
(ng #t)
(use "AndConstEqP")
;; 9,10
(use "IH")
(ng #t)
(assume "pl^" "Tpl")
(use "EqPHyp")
(use "TotalListCons")
(use "TotalBooleTrue")
(use "Tpl")
;; 10
(use "IH")
(ng #t)
(assume "pl^" "Tpl")
(use "EqPHyp")
(use "TotalListCons")
(use "TotalBooleFalse")
(use "Tpl")
;; Proof finished.
;; (cp)
(save "AllBListExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(list boole=>boole)=>boole)n([pltop]pltop(Nil boole))
;;  ([n0,((list boole=>boole)=>boole),pltop]
;;    cAndConstEqP(((list boole=>boole)=>boole)([pl]pltop(True::pl)))
;;    (((list boole=>boole)=>boole)([pl]pltop(False::pl))))

;; AllBListIntro
(set-goal
 "all n,pltop(all pl^(Lh pl^ =n -> pltop pl^) -> AllBList n pltop)")
(ind)
;; Base
(assume "pltop" "Hyp")
(ng #t)
(use "Hyp")
(ng #t)
(use "Truth")
;; Step
(assume "n" "IH" "pltop" "Hyp")
(ng #t)
(split)
(use "IH")
(assume "pl^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
(use "IH")
(assume "pl^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
;; Proof finished.
;; (cp)
(save "AllBListIntro")

;; AllBListElim
(set-goal "all n,pltop(AllBList n pltop -> all pl(Lh pl=n -> pltop pl))")
(ind)
;; Base
(assume "pltop" "H1")
(cases)
(assume "Useless")
(use "H1")
(assume "boole" "pl" "Absurd")
(use "EfAtom")
(use "Absurd")
;; Step
(assume "n" "IH" "pltop" "H1")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(cases)
(assume "pl" "Lhn")
(use-with "IH" (pt "[pl1]pltop(True::pl1)") "?" (pt "pl") "?")
(ng "H1")
(use "H1")
(use "Lhn")
(assume "pl" "Lhn")
(use-with "IH" (pt "[pl1]pltop(False::pl1)") "?" (pt "pl") "?")
(ng "H1")
(use "H1")
(use "Lhn")
;; Proof finished.
;; (cp)
(save "AllBListElim")

(add-program-constant "ListRev" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListRev" "Rev")
(add-computation-rules
 "Rev(Nil alpha)" "(Nil alpha)"
 "Rev(x::xl)" "Rev xl++x:")

(set-totality-goal "ListRev")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "x" "xl" "IH")
(ng #t)
(use "ListAppdTotal")
(use "IH")
(use "ListTotalVar")
;; Proof finished.
;; (cp)
(save-totality)

;; ListRevSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(ListRev alpha)"))))
(assume "xl^" "STxl")
(elim "STxl")
(use "STotalListNil")
(assume "x^1" "xl^1" "STxl1" "IH")
(ng #t)
(use "ListAppdSTotal")
(use "IH")
(use "STotalListCons")
(use "STotalListNil")
;; Proof finished.
;; (cp)
(save "ListRevSTotal")

;; ListLengthRev
(set-goal "all xl Lh Rev xl eqd Lh xl")
(ind)
(use "InitEqD")
(assume "x" "xl" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListLengthRev")

;; ListRevAppd
(set-goal "all xl1,xl2 Rev(xl1++xl2)eqd Rev xl2++Rev xl1")
(ind)
(ng #t)
(strip)
(use "InitEqD")
(assume "x" "xl" "IH")
(ng #t)
(assume "xl2")
(simp "IH")
(simp "ListAppdAssoc")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRevAppd")

;; ListRevAppdPartial
(set-goal "all xl^1(STotalList xl^1 -> all xl^2(STotalList xl^2 ->
                   Rev(xl^1 ++xl^2)eqd Rev xl^2 ++Rev xl^1))")
(assume "xl^1" "STxl1")
(elim "STxl1")
(ng #t)
(assume "xl^2" "STxl2")
(simp "ListAppdNilPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxl2")
(assume "x^" "xl^" "STxl" "IH")
(ng #t)
(assume "xl^2" "STxl2")
(simp "IH")
(simp "ListAppdAssocPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxl2")
(use "STxl2")
;; Proof finished.
;; (cp)
(save "ListRevAppdPartial")

;; ListRevInvol
(set-goal "all xl Rev(Rev xl)eqd xl")
(ind)
(use "InitEqD")
(assume "x" "xl" "IH")
(ng #t)
(simp "ListRevAppd")
(simp "IH")
(ng #t)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRevInvol")

;; ListRevInvolPartial
(set-goal "all xl^(STotalList xl^ -> Rev(Rev xl^)eqd xl^)")
(assume "xl^" "STxl")
(elim "STxl")
(ng #t)
(use "InitEqD")
(assume "x^1" "xl^1" "STxl1" "IH")
(ng #t)
(simp "ListRevAppdPartial")
(simp "IH")
(ng #t)
(use "InitEqD")
(use "STotalListCons")
(use "STotalListNil")
(use "ListRevSTotal")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ListRevInvolPartial")

;; ListNatProjRev
(set-goal "all nl,n(n<Lh nl -> (n thof Rev nl)eqd(Pred(Lh nl--n)thof nl))")
(assert "all nl,n(n<Lh nl -> (n thof nl)eqd(Pred(Lh nl--n)thof Rev nl))")
 (ind)
 (ng)
 (assume "n" "Absurd")
 (use "InitEqD")
 (assume "n" "nl" "IH")
 (ng #t)
(cases)
 (ng #t)
 (assume "Useless")
 (assert "Lh nl eqd Lh Rev nl+0")
  (simp "ListLengthRev")
  (use "InitEqD")
 (assume "EqHyp")
 (simp "EqHyp")
 (simp "ListNatProjAppdRight")
 (use "InitEqD")
 (use "Truth")
;; Case Succ n
 (ng #t)
 (assume "n0" "n0<Lh nl")
 (simp "ListNatProjAppdLeft")
 (use "IH")
 (use "n0<Lh nl")
;; ?_24:Pred(Lh nl--n0)<Lh Rev nl
 (simp "ListLengthRev")
 (cases (pt "Lh nl"))
 (assume "Lh nl=0")
 (simphyp-with-to "n0<Lh nl" "Lh nl=0" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "n1" "Lh nl=Sn1")
 (ng #t)
 (use "NatLeLtTrans" (pt "n1"))
 (use "Truth")
 (use "Truth")
(assume "ListNatProjRevAux" "nl" "n" "n<Lh nl")
(inst-with-to "ListNatProjRevAux" (pt "Rev nl") (pt "n") "Aux")
(assert "Rev Rev nl eqd nl")
 (use "ListRevInvol")
(assume "Assertion")
(simphyp-with-to "Aux" "Assertion" "SimpAux")
(assert "Lh Rev nl eqd Lh nl")
 (use "ListLengthRev")
(assume "Lh Rev nl eqd Lh nl")
(simphyp-with-to "SimpAux" "Lh Rev nl eqd Lh nl" "SimpSimpAux")
(use "SimpSimpAux")
(use "n<Lh nl")
;; Proof finished.
;; (cp)
(save "ListNatProjRev")

;; ListRevFBarSucc
(set-goal "all n,xs Rev(xs fbar Succ n)eqd(xs n::Rev(xs fbar n))")
(assume "n" "xs")
(simp "ListFBarAppdLast")
(simp "ListRevAppd")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRevFBarSucc")

;; Similar to Pred in nat.scm we define Head and Tail.  They are
;; easier to handle than the general (Destr list alpha).

(add-program-constant "ListHead" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListHead" "Head")
(add-computation-rules
 "Head(Nil alpha)" "(Inhab alpha)"
 "Head(x::xl)" "x")

;; (set-totality-goal "ListHead")
;; (assume "xl^" "Txl")
;; (elim "Txl")
;; (ng #t)
;; (use "InhabTotal") ;does not exist
;; (assume "x^" "Tx" "xl^1" "Txl1" "IH")
;; (ng #t)
;; (use "Tx")
;; ;; Proof finished.
;; ;; (cp)
;; (save-totality)

;; ListHeadExtNc
(set-goal
 (make-imp
  (pf "EqPNc(Inhab alpha)(Inhab alpha)")
  (rename-variables (term-to-pure-extnc-formula (pt "(ListHead alpha)")))))

;; EqPNc(Inhab alpha)(Inhab alpha) -> 
;;     all xl^,xl^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xl^ xl^0 -> 
;;      EqPNc(Head xl^)(Head xl^0))

(assume "InhabExtNc" "xl^1" "xl^2" "xl1=xl2")
(elim "xl1=xl2")
;; 3,4
(ng #t)
(use "InhabExtNc")
;; 4
(assume "x^1" "x^2" "x1=x2" "xl^3" "xl^4" "xl3=xl4" "Useless")
(ng #t)
(use "x1=x2")
;; Proof finished.
;; (cp)
(save "ListHeadExtNc")

(add-program-constant "ListTail" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListTail" "Tail")
(add-computation-rules
 "Tail(Nil alpha)" "(Nil alpha)"
 "Tail(x::xl)" "xl")

(set-totality-goal "ListTail")
(assume "xl^" "Txl")
(elim "Txl")
(ng #t)
(intro 0)
(assume "x^" "Tx" "xl^1" "Txl1" "IH")
(ng #t)
(use "Txl1")
;; Proof finished.
;; (cp)
(save-totality)

;; ListTailExtNc
(set-goal
 (rename-variables
  (term-to-pure-extnc-formula (pt "(ListTail alpha)"))))

;; all xl^,xl^0(
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))xl^ xl^0 -> 
;;      (REqPListNc (cterm (x^,x^0) EqPNc x^ x^0))(Tail xl^)(Tail xl^0))

(assume "xl^1" "xl^2" "xl1=xl2")
(elim "xl1=xl2")
;; 3,4
(ng #t)
(intro 0)
;; 4
(assume "x^1" "x^2" "x1=x2" "xl^3" "xl^4" "xl3=xl4" "Useless")
(ng #t)
(use "xl3=xl4")
;; Proof finished.
;; (cp)
(save "ListTailExtNc")

;; ListZeroLtLhToHeadTailId
(set-goal "all xl(0<Lh xl -> (Head xl::Tail xl)eqd xl)")
(cases)
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xl" "Useless")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListZeroLtLhToHeadTailId")

(add-program-constant "ListLast" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListLast" "Last")
(add-computation-rules
 "Last(Nil alpha)" "(Inhab alpha)"
 "Last(x::xl)" "[if (Lh xl=0) x (Last xl)]")

;; (set-totality-goal "ListLast")
;; (assume "xl^" "Txl")
;; (elim "Txl")
;; (ng #t)
;; (use "InhabTotal") ;does not exist
;; (assume "x^" "Tx" "xl^1" "Txl1" "IH")
;; (ng #t)
;; (use "BooleIfTotal")
;; (use "NatEqTotal")
;; (use "ListLengthTotal")
;; (use "Txl1")
;; (use "TotalNatZero")
;; (use "Tx")
;; (use "IH")
;; ;; Proof finished.
;; ;; (cp)
;; (save-totality)

(add-program-constant "ListMain" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListMain" "Main")
(add-computation-rules
 "Main(Nil alpha)" "(Nil alpha)"
 "Main(x::xl)" "[if (Lh xl=0) (Nil alpha) (x::Main xl)]")

(set-totality-goal "ListMain")
(assume "xl^" "Txl")
(elim "Txl")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "x^" "Tx" "xl^1" "Txl1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "ListLengthTotal")
(use "Txl1")
(use "TotalNatZero")
(use "TotalListNil")
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; ListZeroLtLhToMainLastId
(set-goal "all xl(0<Lh xl -> Main xl++(Last xl):eqd xl)")
(assert "all n,xl(Lh xl<=n -> 0<Lh xl -> Main xl++(Last xl):eqd xl)")
(ind)
(assume "xl")
(ng)
(assume "Lh xl=0")
(simp "Lh xl=0")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "n" "IHn")
(cases)
(ng)
(assume "Useless" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xl" "LhBound" "Useless")
(ng)
(cases (pt "Lh xl=0"))
(assume "Lh xl=0")
(assert "xl eqd(Nil alpha)")
 (use "ListLhZeroToEqNilPartial")
 (use "ListSTotalVar")
 (use "Lh xl=0")
(assume "xl eqd(Nil alpha)")
(simp "xl eqd(Nil alpha)")
(ng)
(use "InitEqD")
(assume "0=Lh xl -> F")
(ng)
(simp "IHn")
(use "InitEqD")
(cases (pt "Lh xl"))
(assume "Lh xl=0")
(use "0=Lh xl -> F")
(use "Lh xl=0")
(strip)
(use "Truth")
(use "LhBound")
;; Now the assertion is proved.
(assume "Assertion" "xl")
(use "Assertion" (pt "Lh xl"))
(use "Truth")
;; Proof finished.
;; (cp)
(save "ListZeroLtLhToMainLastId")

(add-var-name "xll" (py "list list alpha"))

(add-program-constant "ListHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListHeads" "Heads")
(add-computation-rules
 "Heads(Nil list alpha)" "(Nil alpha)"
 "Heads(xl::xll)" "Head xl::Heads xll")

;; 2020-07-13.  Commented out, since we do not have ListHeadTotal.
;; (set-totality-goal "ListHeads")
;; (assume "xll^" "Txll")
;; (elim "Txll")
;; (use "TotalListNil")
;; (assume "xl^" "Txl" "xll^1" "Txll1" "IH")
;; (ng #t)
;; (use "TotalListCons")
;; (use "ListHeadTotal")
;; (use "Txl")
;; (use "IH")
;; ;; Proof finished.
;; ;; (cp)
;; (save-totality)

;; We also define ListPHeads (p for proper), which ignores heads of
;; empty lists.

(add-program-constant
 "ListPHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListPHeads" "PHeads")
(add-computation-rules
 "PHeads(Nil list alpha)" "(Nil alpha)"
 "PHeads((Nil alpha)::xll)" "PHeads xll"
 "PHeads((x::xl)::xll)" "x::PHeads xll")

(set-totality-goal "ListPHeads")
(assume "xll^" "Txll")
(elim "Txll")
(use "TotalListNil")
(assume "xl^" "Txl")
(elim "Txl")
(assume "xll^1" "Txll1" "IH")
(ng #t)
(use "IH")
(assume "x^" "Tx" "xl^1" "Txl1" "Useless" "xll^1" "Txll1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

(add-program-constant "ListInit" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListInit" "init" 'mul-op)
(add-computation-rules
 "0 init xl" "(Nil alpha)"
 "Succ n init(Nil alpha)" "(Nil alpha)"
 "Succ n init(x::xl)" "x::n init xl")

;; Above there is a similar ListBar.  Difference: in case the number n
;; is larger than the length, ListInit returns the original list
;; whereas ListBar appends Inhab's.

;; (pp (nt (pt "7 init(0::1::2::3::4:)")))
;; 0::1::2::3::4:

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

(set-totality-goal "ListInit")
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalListNil")
(assume "n" "IHn" "xl^" "Txl")
(elim "Txl")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xl^1" "Txl1" "Useless")
(ng)
(use "TotalListCons")
(use "Tx")
(use "IHn")
(use "Txl1")
;; Proof finished.
;; (cp)
(save "ListInitTotal")

(add-program-constant "ListRest" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListRest" "rest" 'mul-op)
(add-computation-rules
 "0 rest xl" "xl"
 "Succ n rest(Nil alpha)" "(Nil alpha)"
 "Succ n rest(x::xl)" "n rest xl")

(set-totality-goal "ListRest")
(use "AllTotalElim")
(ind)
(ng)
(assume "xl^" "Txl")
(use "Txl")
(assume "n" "IHn" "xl^" "Txl")
(elim "Txl")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xl^1" "Txl1" "Useless")
(ng)
(use "IHn")
(use "Txl1")
;; Proof finished.
;; (cp)
(save-totality)

;; (pp (nt (pt "1 init(5::6::7::8::9:)")))
;; 5:
;; (pp (nt (pt "1 rest(5::6::7::8::9:)")))
;; 6::7::8::9:

;; (pp (nt (pt "7 init(5::6::7::8::9:)")))
;; (pp (nt (pt "7 rest(5::6::7::8::9:)")))
;; (pp (nt (pt "0 init(5::6::7::8::9:)")))
;; (pp (nt (pt "0 rest(5::6::7::8::9:)")))

;; ListAppdInitRest
(set-goal "all n,xl xl eqd n init xl++(n rest xl)")
(ind)
(ng)
(assume "xl")
(use "InitEqD")
(assume "n" "IHn")
(ind)
(ng)
(use "InitEqD")
(assume "x" "xl" "IHxl")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
;; Proof finished
;; (cp)
(save "ListAppdInitRest")

;; ListAppdInitRestPartial
(set-goal
 "all n all xl^(STotalList xl^ -> xl^ eqd n init xl^ ++(n rest xl^))")
(ind)
(ng)
(assume "xl^" "STxl")
(elim "STxl")
(use "InitEqD")
(strip)
(use "InitEqD")
(assume "n" "IHn" "xl^" "STxl")
(elim "STxl")
(ng)
(use "InitEqD")
(assume "x^1" "xl^1" "STxl1" "IH")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ListAppdInitRestPartial")

;; ListLhAppdSinglePartial
(set-goal "all xl^,x^(STotalList xl^ -> Lh(xl^ ++x^ :)eqd Succ Lh xl^)")
(assume "xl^" "x^" "STxl")
(elim "STxl")
(ng)
(use "InitEqD")
(assume "x^1" "xl^1" "STxl1" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListLhAppdSinglePartial")

;; ListLhRevPartial
(set-goal "all xl^(STotalList xl^ -> Lh(Rev xl^)eqd Lh xl^)")
(assume "xl^" "STxl")
(elim "STxl")
(use "InitEqD")
(assume "x^1" "xl^1" "STxl1" "IH")
(ng)
(simp "ListLhAppdSinglePartial")
(simp "IH")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxl1")
;; Proof finished.
;; (cp)
(save "ListLhRevPartial")

;; ListLhAppdPartial
(set-goal "all xl^1(STotalList xl^1 -> all xl^2(STotalList xl^2 ->
 Lh(xl^1++xl^2) eqd Lh xl^1+Lh xl^2))")
(assume "xl^1" "STxl1")
(elim "STxl1")
(assume "xl^2" "STxl2")
(elim "STxl2")
(use "InitEqD")
(assume "x^" "xl^3" "STxl3" "IH")
(ng)
(simp "<-" "IH")
(use "InitEqD")
;; 4
(assume "x^1" "xl^11" "STxl11" "IH1" "xl^2" "STxl2")
(elim "STxl2")
(ng)
(simp "IH1")
(ng)
(use "InitEqD")
(use "STotalListNil")
(assume "x^2" "xl^3" "STxl3" "IH2")
(ng)
(simp "IH1")
(ng)
(simp "<-" "IH2")
(simp "IH1")
(use "InitEqD")
(use "STxl3")
(use "STotalListCons")
(use "STxl3")
;; Proof finished.
;; (cp)
(save "ListLhAppdPartial")

;; ListInitLh
(set-goal "all xl Lh xl init xl eqd xl")
(ind)
(use "InitEqD")
(assume "x" "xl" "IHxl")
(ng)
(simp "IHxl")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListInitLh")
(add-rewrite-rule "Lh xl init xl" "xl")

;; ListInitLhPartial
(set-goal "all xl^(STotalList xl^ -> Lh xl^ init xl^ eqd xl^)")
(assume "xl^" "STxl")
(elim "STxl")
(ng)
(use "InitEqD")
(assume "x^" "xl^1" "STxl1")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListInitLhPartial")

;; ListRestLh
(set-goal "all xl Lh xl rest xl eqd(Nil alpha)")
(ind)
(use "InitEqD")
(assume "x" "xl" "IHxl")
(ng)
(simp "IHxl")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRestLh")
(add-rewrite-rule "Lh xl rest xl" "(Nil alpha)")

;; ListLhInitPartial
(set-goal "all xl^(STotalList xl^ -> all n(n<=Lh xl^ -> Lh(n init xl^)eqd n))")
(assume "xl^" "STxl")
(elim "STxl")
(ng #t)
(assume "n" "n=0")
(simp "n=0")
(ng #t)
(use "InitEqD")
;; 4
(assume "x^" "xl^1" "STxl1")
(ng #t)
(assume "AllHyp")
(cases)
(ng #t)
(assume "Useless")
(use "InitEqD")
;; 13
(ng #t)
(assume "n" "LeH")
(simp "AllHyp")
(use "InitEqD")
(use "LeH")
;; Proof finished.
;; (cp)
(save "ListLhInitPartial")

;; ;; ListLhInit
;; (set-goal "all xl,n(n<=Lh xl -> Lh(n init xl)=n)")
;; (ind)
;; (ng)
;; (assume "n" "n=0")
;; (simp "n=0")
;; (use "Truth")
;; (assume "x" "xl" "IHxl")
;; (ng)
;; (cases)
;; (ng)
;; (assume "Useless")
;; (use "Useless")
;; (use "IHxl")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListLhInit")

;; ListLhRestPartial
(set-goal "all xl^(STotalList xl^ ->
 all n(n<=Lh xl^ -> Lh(n rest xl^)+n eqd Lh xl^))")
(assume "xl^" "STxl")
(elim "STxl")
(ng #t)
(cases)
(ng #t)
(assume "Useless")
(use "InitEqD")
;; 7
(assume "n" "Absurd")
(use "EfEqD")
(use "Absurd")
;; 4
(assume "x^" "xl^1" "STxl1")
(ng #t)
(assume "AllHyp")
(cases)
(ng #t)
(assume "Useless")
(use "InitEqD")
;; 16
(ng #t)
(assume "n" "LeH")
(simp "AllHyp")
(use "InitEqD")
(use "LeH")
;; Proof finished.
;; (cp)
(save "ListLhRestPartial")

;; ;; ListLhRest
;; (set-goal "all xl,n(n<=Lh xl -> Lh(n rest xl)=Lh xl--n)")
;; (ind)
;; (ng)
;; (assume "n" "n=0")
;; (simp "n=0")
;; (use "Truth")
;; (assume "x" "xl" "IHxl")
;; (ng)
;; (cases)
;; (ng)
;; (assume "Useless")
;; (use "Useless")
;; (use "IHxl")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListLhRest")

;; ListInitAppd
(set-goal "all xl1,xl2 Lh xl1 init(xl1++xl2) eqd xl1")
(ind)
(ng)
(assume "xl")
(use "InitEqD")
(assume "x" "xl" "IH" "xl2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListInitAppd")

;; ListInitAppdPartial
(set-goal "all xl^1,xl^2(
 STotalList xl^1 -> Lh xl^1 init(xl^1++xl^2) eqd xl^1)")
(assume "xl^1" "xl^2" "Txl1")
(elim "Txl1")
(ng)
(use "InitEqD")
(assume "x^" "xl^" "Txl" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListInitAppdPartial")

;; ListInitAppdGen
(set-goal "all n,xl1,xl2(n<=Lh xl1 -> n init(xl1++xl2)eqd n init xl1)")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(assume "xl1")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x" "xl1" "xl2")
(ng)
(assume "n<=Lh xl1")
(simp "IHn")
(use "InitEqD")
(use "n<=Lh xl1")
;; Proof finished.
;; (cp)
(save "ListInitAppdGen")

;; ListInitPlusAppdPartial
(set-goal "all n all xl^1(STotalList xl^1 ->
 all xl^2((n+Lh xl^1)init(xl^1 ++xl^2)eqd xl^1++(n init xl^2)))")
(assume "n" "xl^1" "STxl1")
(elim "STxl1")
(ng)
(strip)
(use "InitEqD")
;; 4
(assume "x^" "xl^2" "STxl2" "IH" "xl^")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListInitPlusAppdPartial")

;; ListInitPlusAppd
(set-goal
 "all n all xl1,xl^2 (n+Lh xl1)init(xl1 ++xl^2)eqd xl1++(n init xl^2)")
(assume "n" "xl1" "xl^2")
(use "ListInitPlusAppdPartial")
(use "ListSTotalVar")
;; Proof finished.
;; (cp)
(save "ListInitPlusAppd")

;; ListRestAppd
(set-goal "all xl1,xl2 Lh xl1 rest(xl1++xl2) eqd xl2")
(ind)
(ng)
(assume "xl")
(use "InitEqD")
(assume "x" "xl" "IH" "xl2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRestAppd")

;; ListRestAppdPartial
(set-goal "all xl^1,xl^2(
 STotalList xl^1 -> Lh xl^1 rest(xl^1++xl^2) eqd xl^2)")
(assume "xl^1" "xl^2" "Txl1")
(elim "Txl1")
(ng)
(use "InitEqD")
(assume "x^" "xl^" "Txl" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListRestAppdPartial")

;; ListRestAppdGen
(set-goal
 "all n^ all xl1 all xl^2 (n^ +Lh xl1)rest(xl1++xl^2) eqd n^ rest xl^2")
(assume "n^")
(ind)
(ng)
(assume "xl^2")
(use "InitEqD")
(assume "x" "xl1" "IHxl1" "xl^2")
(ng)
(use "IHxl1")
;; Proof finished.
;; (cp)
(save "ListRestAppdGen")

;; ;; ListLhInitRestEq
;; (set-goal "all xl(NatEven Lh xl ->
;;  Lh(NatHalf Lh xl init xl)=
;;  Lh(NatHalf Lh xl rest xl))")
;; (assume "xl" "Exl")
;; (simp "ListLhInitPartial")
;; (simp "ListLhRestPartial") ;no simplification possible
;; (use "NatPlusCancelR" (pt "NatHalf Lh xl"))
;; (simp "NatMinusPlusEq")
;; (simp "NatDoublePlusEq")
;; (use "NatDoubleHalfEven")
;; (use "Exl")
;; (use "NatHalfLe")
;; (use "NatHalfLe")
;; (use "NatHalfLe")
;; ;; Proof finished.
;; ;; (cp)
;; (save "ListLhInitRestEq")

;; ;; ListProjRest
;; (set-goal "all xl,n,m(n thof m rest xl)eqd(n+m thof xl)")
;; (ind)
;; (ind)
;; (cases)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (use "InitEqD")
;; (assume "n" "IHn")
;; (cases)
;; (ng #t)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (use "InitEqD")
;; ;; 3
;; (assume "x")
;; (ind) ;the type of x should be totally inhabited.
;; (ng #t)
;; (assume "AllH")
;; (ind)
;; (cases)
;; (ng #t)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (use "AllH")
;; (assume "n" "IHn")
;; (cases)
;; (ng #t)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (use "AllH")
;; ;; 18
;; (assume "x0" "xl0" "IH" "AllH")
;; (ind)
;; (cases)
;; (ng #t)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (simp "AllH")
;; (use "InitEqD")
;; ;; 36
;; (assume "n" "IHn")
;; (cases)
;; (ng #t)
;; (use "InitEqD")
;; (assume "m")
;; (ng #t)
;; (simp "AllH")
;; (ng #t)
;; (use "InitEqD")
;; ;; Proof finiwshed.
;; ;; (cp)
;; (save "ListProjRest")

;; Now ListFilter

(add-var-name "xtop" (py "alpha=>boole"))

(add-program-constant
 "ListFilter" (py "(alpha=>boole)=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListFilter" "filter" 'pair-op) ;right associative
(add-computation-rules
 "xtop filter(Nil alpha)" "(Nil alpha)"
 "xtop filter x::xl" "[if (xtop x) (x::xtop filter xl) (xtop filter xl)]")

;; ListFilterTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(ListFilter alpha)"))))

;; all xtop^(
;;      all x^(Total x^ -> TotalBoole(xtop^ x^)) -> 
;;      all xl^(TotalList xl^ -> TotalList(xtop^ filter xl^)))

(assume "xtop^" "Txtop" "xl^" "Txl")
(elim "Txl")
;; 3,4
(ng #t)
(use "TotalListNil")
;; 4
(assume "x^1" "Tx1" "xl^1" "Txl1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "Txtop")
(use "Tx1")
(use "TotalListCons")
(use "Tx1")
(use "IH")
(use "IH")
;; Proof finished.
;; (cp)
;; (save "ListFilterTotal")
(save-totality)

;; ok, ListFilterTotal has been added as a new theorem.
;; ok, computation rule xtop filter(Nil alpha) -> (Nil alpha) added
;; ok, computation rule xtop filter x::xl ->
;; [if (xtop x) (x::xtop filter xl) (xtop filter xl)] added

;; (term-to-t-deg (pt "(ListFilter alpha)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xtop,xl]
;;  (Rec list alpha=>list alpha)xl(Nil alpha)
;;  ([x,xl0,xl1][if (xtop x) (x::xl1) xl1])

;; Moreover we have extensionality of ListFilter:

;; Need (in ets.scm)

;; BooleIfREqPList
(set-goal
 "all p^1,p^2(
     EqPBoole p^1 p^2 -> 
     all xl^11,xl^21(
      (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xl^11 xl^21 -> 
      all xl^12,xl^22(
       (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xl^12 xl^22 -> 
       (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))
       [if p^1 xl^11 xl^12]
       [if p^2 xl^21 xl^22])))")
(assume "p^1" "p^2" "EqPp1p2")
(elim "EqPp1p2")
;; 3,4
(ng #t)
(search)
;; 4
(ng #t)
(search)
;; Proof finished.
;; (cp)
(save "BooleIfREqPList")

;; ListFilterExt
(set-goal (rename-variables
	   (terms-to-eqp-formula
	    (pt "(ListFilter alpha)") (pt "(ListFilter alpha)"))))

;; all xtop^,xtop^0(
;;      all x^,x^0(EqP x^ x^0 -> EqPBoole(xtop^ x^)(xtop^0 x^0)) -> 
;;      all xl^,xl^0(
;;       (REqPList (cterm (x^,x^0) EqP x^ x^0))xl^ xl^0 -> 
;;       (REqPList (cterm (x^,x^0) EqP x^ x^0))(xtop^ filter xl^)
;;       (xtop^0 filter xl^0)))

(assume "xtop^1" "xtop^2" "EqPBooleHyp" "xl^1" "xl^2" "REqPHyp")
(elim "REqPHyp")
;; 3,4
(ng #t)
(use "REqPListNil")
;; 4
(assume "x^1" "x^2" "EqPHyp" "xl^3" "xl^4" "H1" "H2")
(ng #t)
(use-with
 "BooleIfREqPList"
 (py "alpha")
 (make-cterm (pv "x^1") (pv "x^2") (pf "EqP x^1 x^2"))
 (pt "xtop^1 x^1")  (pt "xtop^2 x^2") "?"
 (pt "(x^1::xtop^1 filter xl^3)") (pt "(x^2::xtop^2 filter xl^4)") "?"
 (pt "xtop^1 filter xl^3") (pt "xtop^2 filter xl^4") "?")
(use "EqPBooleHyp")
(use "EqPHyp")
(use-with
 "REqPListCons"
 (py "alpha")
 (make-cterm (pv "x^1") (pv "x^2") (pf "EqP x^1 x^2"))
 (pt "x^1") (pt "x^2") "EqPHyp" 
 (pt "xtop^1 filter xl^3") (pt "xtop^2 filter xl^4") "?")
(use "H2")
(use "H2")
;; Proof finished.
;; (cp)
(save "ListFilterExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xtop,xl]
;;  (Rec list alpha=>list alpha)xl(Nil alpha)
;;  ([x,xl0,xl1](cBooleIfREqPList alpha)(xtop x)(x::xl1)xl1)

(add-var-name "fst" (py "alpha1=>alpha2=>alpha1"))
(add-var-name "snd" (py "alpha1=>alpha2=>alpha2"))

;; (Foldl bin-op init-val list).  If list is empty, return init-val.
;; If not, apply ListFoldl with (i) initial value: the result of
;; applying bin-op to init-val and the head of list and (ii) the tail
;; of the list.

(add-program-constant
 "Foldl" (py "(alpha1=>alpha2=>alpha1)=>alpha1=>list alpha2=>alpha1")
 t-deg-zero)
(add-computation-rules
 "(Foldl alpha1 alpha2)fst y(Nil alpha2)" "y"
 "(Foldl alpha1 alpha2)fst y(z::zl)" "(Foldl alpha1 alpha2)fst(fst y z)zl")

;; FoldLTotal
(set-totality-goal "Foldl")

;; all fst^(
;;      all y^(Total y^ -> all z^(Total z^ -> Total(fst^ y^ z^))) -> 
;;      all y^(
;;       Total y^ -> 
;;       all zl^(TotalList zl^ -> Total((Foldl alpha1 alpha2)fst^ y^ zl^))))

(assume "fst^" "Tfst")
(assert "all zl^(TotalList zl^ ->
 all y^(Total y^ -> Total((Foldl alpha1 alpha2)fst^ y^ zl^)))")
(assume "zl^" "Tzl")
(elim "Tzl")
;; 6,7
(assume "y^" "Ty")
(ng #t)
(use "Ty")
;; 7
(assume "z^1" "Tz1" "zl^1" "Tzl1" "IH" "y^" "Ty")
(ng #t)
(use "IH")
(use "Tfst")
(use "Ty")
(use "Tz1")
;; Assertion proved.
(assume "Assertion" "y^" "Ty" "zl^" "Tzl")
(use "Assertion")
(use "Tzl")
(use "Ty")
;; Proof finished.
;; (cp)
(save-totality)

;; (term-to-t-deg (pt "(Foldl alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fst,y,zl]
;;  (Rec list alpha2=>alpha1=>alpha1)zl([y0]y0)
;;  ([z,zl0,(alpha1=>alpha1),y0](alpha1=>alpha1)(fst y0 z))
;;  y

;; Moreover we have extensionality of FoldlExt:

;; FoldlExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(Foldl alpha1 alpha2)")
					 (pt "(Foldl alpha1 alpha2)"))))

;; all fst^,fst^0(
;;      all y^,y^0(
;;       EqP y^ y^0 -> 
;;       all z^,z^0(EqP z^ z^0 -> EqP(fst^ y^ z^)(fst^0 y^0 z^0))) -> 
;;      all y^,y^0(
;;       EqP y^ y^0 -> 
;;       all zl^,zl^0(
;;        (REqPList (cterm (z^,z^0) EqP z^ z^0))zl^ zl^0 -> 
;;        EqP((Foldl alpha1 alpha2)fst^ y^ zl^)
;;        ((Foldl alpha1 alpha2)fst^0 y^0 zl^0))))

(assume "fst^1" "fst^2" "EqPfst1fst2")
(assert "all zl^,zl^0(
     (REqPList (cterm (z^,z^0) EqP z^ z^0))zl^ zl^0 -> 
     all y^,y^0(
      EqP y^ y^0 -> 
      EqP((Foldl alpha1 alpha2)fst^1 y^ zl^)
      ((Foldl alpha1 alpha2)fst^2 y^0 zl^0)))")
(assume "zl^1" "zl^2" "EqPzl1zl2")
(elim "EqPzl1zl2")
;; 6,7
(assume "y^1" "y^2" "EqPy1y2")
(ng #t)
(use "EqPy1y2")
;; 7
(assume "z^1" "z^2" "EqPz1z2" "zl^3" "zl^4" "EqPzl3zl4" "IH"
	"y^1" "y^2" "EqPy1y2")
(ng #t)
(use "IH")
(use "EqPfst1fst2")
(use "EqPy1y2")
(use "EqPz1z2")
;; Assertion proved.
(assume "Assertion" "y^1" "y^2" "EqPy1y2" "zl^1" "zl^2" "EqPzl1zl2")
(use "Assertion")
(use "EqPzl1zl2")
(use "EqPy1y2")
;; Proof finished.
;; (cp)
(save "FoldlExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fst,y,zl]
;;  (Rec list alpha2=>alpha1=>alpha1)zl([y0]y0)
;;  ([z,zl0,(alpha1=>alpha1),y0](alpha1=>alpha1)(fst y0 z))

;; (Foldr bin-op init-val list).  If list is empty, return init-val.
;; If not, apply bin-op to the head of list and the result of applying
;; Foldr to bin-op, init-val and the tail of the list.

(add-program-constant
 "Foldr" (py "(alpha1=>alpha2=>alpha2)=>alpha2=>list alpha1=>alpha2")
 t-deg-zero)
(add-computation-rules
 "(Foldr alpha1 alpha2)snd z(Nil alpha1)" "z"
 "(Foldr alpha1 alpha2)snd z(y::yl)" "snd y((Foldr alpha1 alpha2)snd z yl)") 

;; FoldRTotal
(set-totality-goal "Foldr")

;; all snd^(
;;      all y^(Total y^ -> all z^(Total z^ -> Total(snd^ y^ z^))) -> 
;;      all z^(
;;       Total z^ -> 
;;       all yl^(TotalList yl^ -> Total((Foldr alpha1 alpha2)snd^ z^ yl^))))

(assume "snd^" "Tsnd")
(assert "all yl^(
     TotalList yl^ -> 
     all z^(Total z^ -> Total((Foldr alpha1 alpha2)snd^ z^ yl^)))")
(assume "yl^" "Tyl")
(elim "Tyl")
;; 6,7
(assume "z^" "Tz")
(ng #t)
(use "Tz")
;; 7
(assume "y^1" "Ty1" "yl^1" "Tyl1" "IH" "z^" "Tz")
(ng #t)
(use "Tsnd")
(use "Ty1")
(use "IH")
(use "Tz")
;; Assertion proved.
(assume "Assertion" "z^" "Tz" "yl^" "Tyl")
(use "Assertion")
(use "Tyl")
(use "Tz")
;; Proof finished.
;; (cp)
(save-totality)

;; ok, FoldrTotal has been added as a new theorem.
;; ok, computation rule (Foldr alpha1 alpha2)snd z(Nil alpha1) -> z added
;; ok, computation rule (Foldr alpha1 alpha2)snd z(y::yl) ->
;;  snd y((Foldr alpha1 alpha2)snd z yl) added

;; (term-to-t-deg (pt "(Foldr alpha1 alpha2)"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [snd,z,yl]
;;  (Rec list alpha1=>alpha2=>alpha2)yl([z0]z0)
;;  ([y,yl0,(alpha2=>alpha2),z0]snd y((alpha2=>alpha2)z0))
;;  z

;; Moreover we have extensionality of FoldrExt:

;; FoldrExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "(Foldr alpha1 alpha2)")
					 (pt "(Foldr alpha1 alpha2)"))))

;; all snd^,snd^0(
;;      all y^,y^0(
;;       EqP y^ y^0 -> 
;;       all z^,z^0(EqP z^ z^0 -> EqP(snd^ y^ z^)(snd^0 y^0 z^0))) -> 
;;      all z^,z^0(
;;       EqP z^ z^0 -> 
;;       all yl^,yl^0(
;;        (REqPList (cterm (y^,y^0) EqP y^ y^0))yl^ yl^0 -> 
;;        EqP((Foldr alpha1 alpha2)snd^ z^ yl^)
;;        ((Foldr alpha1 alpha2)snd^0 z^0 yl^0))))

(assume "snd^1" "snd^2" "EqPsnd1snd2")
(assert "all yl^,yl^0(
     (REqPList (cterm (y^,y^0) EqP y^ y^0))yl^ yl^0 -> 
     all z^,z^0(
      EqP z^ z^0 -> 
      EqP((Foldr alpha1 alpha2)snd^1 z^ yl^)
      ((Foldr alpha1 alpha2)snd^2 z^0 yl^0)))")
(assume "yl^1" "yl^2" "EqPyl1yl2")
(elim "EqPyl1yl2")
;; 6,7
(assume "z^1" "z^2" "EqPz1z2")
(ng #t)
(use "EqPz1z2")
;; 7
(assume "y^1" "y^2" "EqPy1y2" "yl^3" "yl^4" "EqPyl3yl4" "IH"
	"z^1" "z^2" "EqPz1z2")
(ng #t)
(use "EqPsnd1snd2")
(use "EqPy1y2")
(use "IH")
(use "EqPz1z2")
;; Assertion proved.
(assume "Assertion" "z^1" "z^2" "EqPz1z2" "yl^1" "yl^2" "EqPyl1yl2")
(use "Assertion")
(use "EqPyl1yl2")
(use "EqPz1z2")
;; Proof finished.
;; (cp)
(save "FoldrExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [snd,z,yl]
;;  (Rec list alpha1=>alpha2=>alpha2)yl([z0]z0)
;;  ([y,yl0,(alpha2=>alpha2),z0]snd y((alpha2=>alpha2)z0))

;; ListFrom m n returns the list of increasing natural numbers
;; starting from m of length n.

(add-program-constant "ListFrom" (py "nat=>nat=>list nat") t-deg-zero)
(add-computation-rules
 "ListFrom m 0" "(Nil nat)"
 "ListFrom m(Succ n)" "m::ListFrom(Succ m)n")

;; (pp (nt (pt "ListFrom 2 5")))
;; 2::3::4::5::6:

(set-totality-goal "ListFrom")
(assert "all n,m TotalList(ListFrom m n)")
 (ind)
 (assume "m")
 (use "TotalListNil")
 (assume "n" "IH" "m")
 (ng)
 (use "TotalListCons")
 (use "NatTotalVar")
 (use "IH")
(assume "Assertion")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(assume "m")
(use "Assertion")
;; Proof finished.
;; (cp)
(save-totality)

;; Some important concepts for list depend on a decidable equality for
;; the list elements and hence are defined for finitary algebras only.

(add-program-constant "ListNatIn" (py "nat=>list nat=>boole") t-deg-zero)
(add-infix-display-string "ListNatIn" "in" 'pair-op)
(add-computation-rules
 "n in(Nil nat)" "False"
 "n in(m::nl)" "[if (n=m) True (n in nl)]")

(set-totality-goal "ListNatIn")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "m" "nl" "IHn")
(ng)
(cases (pt "n=m"))
(strip)
(use "TotalBooleTrue")
(strip)
(use "IHn")
;; Proof finished.
;; (cp)
(save-totality)

(add-var-name "nll" (py "list list nat"))

;; ListListNatEqToEqD
(set-goal "all nll1,nll2(nll1=nll2 -> nll1 eqd nll2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "nl1" "nll1" "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "nl1" "nll1" "IH")
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(ng #t)
(assume "nl2" "nll2" "Conj")
(inst-with-to "Conj" 'left "nl1=nl2")
(inst-with-to "Conj" 'right "nll1=nll2")
(drop "Conj")
(assert "nl1 eqd nl2")
 (use "ListNatEqToEqD")
 (use "nl1=nl2")
(assume "nl1 eqd nl2")
(assert "nll1 eqd nll2")
 (use "IH")
 (use "nll1=nll2")
(assume "nll1 eqd nll2")
(elim "nll1 eqd nll2")
(assume "(list list nat)^1")
(elim "nl1 eqd nl2")
(assume "nl^")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListListNatEqToEqD")

(define (list-to-first lst)
  (and (pair? lst)
       (or (car lst) (list-to-first (cdr lst)))))

;; (list-to-first '(#f #f 1 #f 2 3)) ;1
;; (list-to-first '(#f #f)) ;#f

;; Computation rule for (Inhab list alpha) with CoRec, which can be
;; undelayed.  Extensionality w.r.t. colist alpha is a special case of
;; ListCoRecExtNc.

(add-computation-rules
 "(Inhab list alpha)"
 "(CoRec unit=>list alpha)Dummy
  ([unit]Inr((Inhab alpha)pair(InR unit (list alpha))unit))")

;; (pp (rename-variables (nt (undelay-delayed-corec (nt (pt "(Inhab list alpha)")) 3))))

;; (Inhab alpha)::
;; (Inhab alpha)::
;; (Inhab alpha)::
;; (CoRec unit=>list alpha)Dummy
;; ([unit]Inr((Inhab alpha)pair(InR unit (list alpha))unit))

;; Added 2021-06-14

;; To approximate Riemann integrable functions we use equidistant
;; partitions whose length is a power of two.  For rational arguments
;; we can view them as step functions.  To deal with lists of objects
;; of an arbitrary type alpha we need STotalList.

;; A basic operation for step functions is refining them by doubling
;; each argument.

(add-program-constant "ListRef" (py "list alpha=>list alpha"))
(add-prefix-display-string "ListRef" "Ref")

(add-computation-rules
 "Ref(Nil alpha)" "(Nil alpha)"
 "Ref(x::xl)" "x::x::Ref xl")

;; (set-totality-goal "ListRef")
;; (fold-alltotal)
;; (ind)
;; (use "TotalVar")
;; (assume "x" "xl" "IH")
;; (ng)
;; (use "TotalListCons")
;; (use "TotalVar") ;type of x needs to be totally inhabited
;; (use "TotalListCons")
;; (use "TotalVar")
;; (use "IH")
;; ;; Proof finished.
;; ;; (cp)
;; (save-totality)

;; ListRefSTotal
(set-goal "all xl^(STotalList xl^ -> STotalList(Ref xl^))")
(assume "xl^" "STxl")
(elim "STxl")
;; 3,4
(ng #t)
(intro 0)
;; 4
(assume "x^" "xl^0" "STxl0" "IH")
(intro 1)
(intro 1)
(use "IH")
;; Proof finshed.
;; (cp)
(save "ListRefSTotal")

(set-goal "all xl STotalList xl")
(ind)
;; 2,3
(intro 0)
;; 3
(assume "x" "xl" "STxl")
(intro 1)
(use "STxl")
;; Proof finished.
;; (cp)
(save "STotalListVar")

;; ListLhRef
(set-goal "all xl^(STotalList xl^ ->  Lh(Ref xl^)=NatDouble Lh xl^)")
(assume "xl^" "STxl")
(elim "STxl")
;; 3,4
(ng #t)
(use "Truth")
(assume "x^" "xl^0" "STxl0" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLhRef")

(add-program-constant "ListItRef" (py "nat=>list alpha=>list alpha"))
(add-infix-display-string "ListItRef" "rf" 'pair-op) ;right associative

(add-computation-rules
 "Zero rf xl" "xl"
 "Succ n rf xl" "Ref(n rf xl)")

(set-goal "all xl^(STotalList xl^ -> all n STotalList(n rf xl^))")
(assume "xl^" "STxl")
(ind)
;; 3,4
(ng #t)
(use "STxl")
;; 4
(assume "n" "IH")
(ng #t)
(use "ListRefSTotal")
(use "IH")
;; Proof finished.
(cp)

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
(pp neterm)

;; [n0,n1](Rec nat=>nat)n1 n0([n2,n3](Rec nat=>nat)n3 0([n4,n5]Succ(Succ n5)))

(set-goal "all n,xl^(STotalList xl^ -> STotalList(n rf xl^))")
(ind)
;; 2,3
(ng #t)
(search)
;; 3
(assume "n" "IH" "xl^" "STxl")
(ng #t)
(use "ListRefSTotal")
(use "IH")
(use "STxl")
;; Proof finished.
(cp)

(define eterm (proof-to-extracted-term))
(define neterm (nt eterm))
(pp neterm)

;; [n0]
;;  (Rec nat=>nat=>nat)n0([n2]n2)
;;  ([n2,ns3,n4](Rec nat=>nat)(ns3 n4)0([n5,n6]Succ(Succ n6)))

(set-goal "all n(n rf(Nil alpha))eqd(Nil alpha)")
(ind)
;; 2,3
(use "InitEqD")
;; 3
(assume "n" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(add-rewrite-rule "n rf(Nil alpha)" "(Nil alpha)")

;; We defined ItRef by Succ n rf xl=Ref(n rf xl).  An
;; alternative would be Succ n rf xl= n rf(Ref xl).  Generally
;; for iteration the latter follows from the former.

;; ListItRefEq
(set-goal "all xl,n (Succ n rf xl)eqd(n rf Ref xl)")
(assume "xl")
(ind)
(use "InitEqD")
(assume "n" "IH")
(simp "ListItRef1CompRule")
(simp "ListItRef1CompRule")
(simp "ListItRef1CompRule")
(simp "<-" "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListItRefEq")

;; ListItRefPlus
(set-goal "all xl,n,m (n+m rf xl)eqd(m rf n rf xl)")
(assume "xl" "n")
(ind)
(use "InitEqD")
(assume "m" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListItRefPlus")

;; ListItRefComm
(set-goal "all xl,n,m (n rf m rf xl)eqd(m rf n rf xl)")
(assume "xl" "n" "m")
(simp "<-" "ListItRefPlus")
(simp "<-" "ListItRefPlus")
(simp "NatPlusComm")
(use "InitEqD")
;; Proof finished.
;; (cp)
(save "ListItRefComm")

;; ;; ListLtLhRef
;; (set-goal "all xl(Zero<Lh xl -> Lh xl<Lh Ref xl)")
;; (assume "xl" "0<Lx")
;; (simp "ListLhRef")
;; (use "NatLtDouble")
;; (use "0<Lx")
;; (use "STotalListVar")
;; ;; Proof finished.
;; ;; (cp)
;; ;; degrees of totality do not fit for variable
;; ;; n19126
;; ;; and term
;; ;; Lh Ref xl

;; This problem can be overcome by considering lists of objects of a
;; totally inhabited type.  We do this for nat here.  Similarly it can
;; be done for rat.  Then Riemann integrable functions can be defined.

(add-program-constant "ListRefNat" (py "list nat=>list nat"))
(add-prefix-display-string "ListRefNat" "RefNat")

(add-computation-rules
 "RefNat(Nil nat)" "(Nil nat)"
 "RefNat(n::nl)" "n::n::RefNat nl")

(set-totality-goal "ListRefNat")
(fold-alltotal)
(ind)
;; 3,4
(ng #t)
(intro 0)
;; 4
(assume "n" "nl" "IH")
(ng #t)
(intro 1)
(use "TotalVar")
(intro 1)
(use "TotalVar")
(use "IH")
;; Proof finished.
;; (cp)
(save-totality)

;; ListLhRefNat
(set-goal "all nl ListLengthNat RefNat nl=NatDouble(ListLengthNat nl)")
(ind)
(ng #t)
(use "Truth")
(assume "n" "nl" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cp)
(save "ListLhRefNat")

;; ListLtLhRefNat
(set-goal "all nl(Zero<ListLengthNat nl ->
 ListLengthNat nl<ListLengthNat(RefNat nl))")
(assume "nl" "0<Lnl")
(simp "ListLhRefNat")
(use "NatLtDouble")
(use "0<Lnl")
;; Proof finished.
;; (cp)
(save "ListLtLhRefNat")

;; (display-default-varnames)

;; nll: 	list list nat
;; snd: 	alpha1=>alpha2=>alpha2
;; fst: 	alpha1=>alpha2=>alpha1
;; xtop: 	alpha=>boole
;; xll: 	list list alpha
;; pltop: 	list boole=>boole
;; ys: 	nat=>alpha1
;; phi: 	alpha1=>alpha2
;; zl: 	list alpha2
;; z: 	alpha2
;; yl: 	list alpha1
;; y: 	alpha1
;; psi: 	alpha1=>list alpha1=>alpha2
;; pl: 	list boole
;; p: 	boole
;; nl: 	list nat
;; xs: 	nat=>alpha
;; xl: 	list alpha
;; x: 	alpha
;; ngam: 	nat ysum gamma
;; gam: 	gamma
;; ns: 	nat=>nat
;; ws: 	nat=>boole
;; n: 	nat

(remove-var-name "nll" "snd" "fst" "xtop" "xll" "pltop" "ys" "phi"
"zl" "z" "yl" "y" "psi" "pl" "p" "nl" "xs" "xl" "x" "ngam" "gam")

;; (display-default-varnames)

;; ns: 	nat=>nat
;; ws: 	nat=>boole
;; n: 	nat
