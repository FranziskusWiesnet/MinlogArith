module Main where

----- Algebras ------------------

type Pos = Integer

type Nat = Integer

----- Recursion operators -------

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

yprodRec :: ((alpha1, alpha2) -> ((alpha1 -> (alpha2 -> alpha4970)) -> alpha4970))
yprodRec (a , b) f = ((f a) b)

----- Program constants ---------

exBPos :: (Pos -> ((Pos -> Bool) -> Bool))
exBPos 1 wf = (wf 1)
exBPos p wf | even p = (if (exBPos (p `quot` 2) wf) then True else (exBPos (p `quot` 2) (\ q -> (wf ((p `quot` 2) + q)))))
exBPos p wf | odd p = (if (wf (((p - 1) `quot` 2) * 2 + 1)) then True else (exBPos (((p - 1) `quot` 2) * 2) wf))

posLog :: (Pos -> Nat)
posLog 1 = 0
posLog p | even p = ((posLog (p `quot` 2)) + 1)
posLog p | odd p = ((posLog ((p - 1) `quot` 2)) + 1)

natHalf :: (Nat -> Nat)
natHalf 0 = 0
natHalf 1 = 0
natHalf n | n > 1 = ((natHalf (n - 2)) + 1)

posMonMaxAux :: ((Pos -> Bool) -> (Nat -> (Pos -> Pos)))
posMonMaxAux wf 0 q = q
posMonMaxAux wf n 1 | n > 0 = (if (wf (2 ^ (n - 1))) then (posMonMaxAux wf (n - 1) (2 ^ (n - 1))) else (posMonMaxAux wf (n - 1) 1))
posMonMaxAux wf n q | n > 0 && even q = (if (wf (((q `quot` 2) * 2) + (2 ^ (n - 1)))) then (posMonMaxAux wf (n - 1) (((q `quot` 2) * 2) + (2 ^ (n - 1)))) else (posMonMaxAux wf (n - 1) ((q `quot` 2) * 2)))
posMonMaxAux wf n q | n > 0 && odd q = (if (wf ((((q - 1) `quot` 2) * 2 + 1) + (2 ^ (n - 1)))) then (posMonMaxAux wf (n - 1) ((((q - 1) `quot` 2) * 2 + 1) + (2 ^ (n - 1)))) else (posMonMaxAux wf (n - 1) (((q - 1) `quot` 2) * 2 + 1)))

posMonMax :: ((Pos -> Bool) -> (Nat -> Pos))
posMonMax wf n = (posMonMaxAux wf n 1)

natLeast :: (Nat -> ((Nat -> Bool) -> Nat))
natLeast 0 ws = 0
natLeast n ws | n > 0 = (if (ws 0) then 0 else ((natLeast (n - 1) (\ m -> (ws (m + 1)))) + 1))

posSqrt :: (Pos -> Pos)
posSqrt p = (posMonMax (\ q -> ((q * q) <= p)) ((natHalf (posLog p)) + 1))

posLeastFactorAux :: (Pos -> Pos)
posLeastFactorAux 1 = 2
posLeastFactorAux p | even p = (if ((natLeast ((posSqrt ((p `quot` 2) * 2)) + 1) (\ n -> ((1 < n) && (exBPos ((p `quot` 2) * 2) (\ q1 -> ((q1 * n) == ((p `quot` 2) * 2)))))))) <= 1 then 1 else ((natLeast ((posSqrt ((p `quot` 2) * 2)) + 1) (\ n -> ((1 < n) && (exBPos ((p `quot` 2) * 2) (\ q1 -> ((q1 * n) == ((p `quot` 2) * 2)))))))))
posLeastFactorAux p | odd p = (if ((natLeast ((posSqrt (((p - 1) `quot` 2) * 2 + 1)) + 1) (\ n -> ((1 < n) && (exBPos (((p - 1) `quot` 2) * 2 + 1) (\ q1 -> ((q1 * n) == (((p - 1) `quot` 2) * 2 + 1)))))))) <= 1 then 1 else ((natLeast ((posSqrt (((p - 1) `quot` 2) * 2 + 1)) + 1) (\ n -> ((1 < n) && (exBPos (((p - 1) `quot` 2) * 2 + 1) (\ q1 -> ((q1 * n) == (((p - 1) `quot` 2) * 2 + 1)))))))))

posLeastFactor :: (Pos -> Pos)
posLeastFactor p = (if ((posLeastFactorAux p) == ((posSqrt p) + 1)) then p else (posLeastFactorAux p))

cPosDivToProd :: (Pos -> (Pos -> Pos))
cPosDivToProd = ((\ f -> (\ p -> (\ q -> (((f ((p + q) + 1)) p) q)))) (\ l -> (natRec l (\ p -> (\ q -> ((\ p39 -> p39) 1))) (\ l -> (\ g1 -> (\ p3 -> (((((\ p -> (\ h -> (\ g0 -> (\ g -> (\ p1 -> (if (1 == p) then (h p1) else (if (even p) then ((\ p2 -> ((g0 p2) p1))(p `quot` 2)) else ((\ p0 -> ((g p0) p1))(p `quot` 2))))))))) p3) (\ q -> ((\ p4 -> p4) q))) (\ p -> (\ q7 -> (((((\ p5 -> (\ p6 -> (\ h1 -> (\ h0 -> (if (1 == p5) then p6 else (if (even p5) then (h1(p5 `quot` 2)) else (h0(p5 `quot` 2)))))))) q7) ((\ p8 -> p8) 1)) (\ q -> ((g1 p) q))) (\ q -> ((\ p9 -> p9) 1)))))) (\ p -> (\ q12 -> (((((\ p10 -> (\ p11 -> (\ h3 -> (\ h2 -> (if (1 == p10) then p11 else (if (even p10) then (h3(p10 `quot` 2)) else (h2(p10 `quot` 2)))))))) q12) ((\ p13 -> p13) 1)) (\ q -> ((\ p15 -> (((\ p14 -> (\ h4 -> (h4 p14))) p15) (\ p0 -> ((\ p16 -> p16) (p0 * 2))))) ((g1 (p * 2 + 1)) q)))) (\ q -> ((((\ x0 -> ((((\ x -> (\ g2 -> (\ g3 -> (\ p17 -> (\ p18 -> (if x then ((g2 p17) p18) else ((g3 p17) p18))))))) x0) (\ p19 -> (\ p20 -> p19))) (\ p22 -> (\ p21 -> p21)))) (p == q)) ((\ p23 -> p23) ((\ p24 -> p24) ((\ p25 -> p25) 1)))) ((\ p26 -> p26) ((((\ x0 -> ((((\ x1 -> (\ g4 -> (\ g5 -> (\ p27 -> (\ p28 -> (if x1 then ((g4 p27) p28) else ((g5 p27) p28))))))) x0) (\ p29 -> (\ p30 -> p29))) (\ p32 -> (\ p31 -> p31)))) (p < q)) ((\ p33 -> p33) ((\ p35 -> (((\ p34 -> (\ h5 -> (h5 p34))) p35) (\ p0 -> ((\ p36 -> p36) (p0 * 2 + 1))))) ((g1 (p * 2 + 1)) (q - p))))) ((\ p37 -> p37) ((\ p38 -> p38) 1))))))))))))))))

posDiv :: (Pos -> (Pos -> Bool))
posDiv p q = ((posGcd p q) == p)

posProd :: (Nat -> (Nat -> ((Nat -> Pos) -> Pos)))
posProd n 0 ps = 1
posProd n m ps | m > 0 = ((posProd n (m - 1) ps) * (ps (n + (m - 1))))

cPosPrimeDivProdToDiv :: ((Nat -> Pos) -> (Pos -> (Nat -> Nat)))
cPosPrimeDivProdToDiv = (\ ps -> (\ p -> (\ m10 -> (natRec m10 ((\ n11 -> n11) 0) (\ m -> (\ n8 -> ((((\ x0 -> ((((\ x -> (\ f -> (\ f0 -> (\ n -> (\ n0 -> (if x then ((f n) n0) else ((f0 n) n0))))))) x0) (\ n1 -> (\ n2 -> n1))) (\ n4 -> (\ n3 -> n3)))) (posDiv p (posProd 0 m ps))) ((\ n6 -> (((\ n5 -> (\ ns -> (ns n5))) n6) (\ l1 -> ((\ n7 -> n7) l1)))) n8)) ((\ n9 -> n9) m))))))))

posGcd :: (Pos -> (Pos -> Pos))
posGcd 1 p = 1
posGcd p 1 | even p = 1
posGcd p q | even p && even q = ((posGcd (p `quot` 2) (q `quot` 2)) * 2)
posGcd p q | even p && odd q = (posGcd (p `quot` 2) (((q - 1) `quot` 2) * 2 + 1))
posGcd p 1 | odd p = 1
posGcd p q | odd p && even q = (posGcd (((p - 1) `quot` 2) * 2 + 1) (q `quot` 2))
posGcd p q | odd p && odd q = (if (((p - 1) `quot` 2) == ((q - 1) `quot` 2)) then (((p - 1) `quot` 2) * 2 + 1) else (if (((p - 1) `quot` 2) < ((q - 1) `quot` 2)) then (posGcd (((p - 1) `quot` 2) * 2 + 1) (((q - 1) `quot` 2) - ((p - 1) `quot` 2))) else (posGcd (((p - 1) `quot` 2) - ((q - 1) `quot` 2)) (((q - 1) `quot` 2) * 2 + 1))))

transp :: (Nat -> (Nat -> (Nat -> Nat)))
transp n m l = (if (l == n) then m else (if (l == m) then n else l))

cPosPrimeDivProdPrimesToInPrimes :: ((Nat -> Pos) -> (Pos -> (Nat -> Nat)))
cPosPrimeDivProdPrimesToInPrimes = (\ ps -> (\ p -> (\ m -> ((\ n0 -> (((\ n -> (\ ns -> (ns n))) n0) (\ l -> ((\ n1 -> n1) l)))) (cPosPrimeDivProdToDiv ps p m)))))

cPosExPrimeFactorisation :: (Pos -> ((Nat -> Pos), Nat))
cPosExPrimeFactorisation = ((\ f -> (\ p -> ((f (p + 1)) p))) (\ l3 -> (natRec l3 (\ p -> ((\ n -> 1) , ((\ n4 -> n4) 0))) (\ l10 -> (\ h0 -> (\ p -> ((((\ x0 -> ((((\ x -> (\ g -> (\ g0 -> (\ y -> (\ y0 -> (if x then ((g y) y0) else ((g0 y) y0))))))) x0) (\ y1 -> (\ y2 -> y1))) (\ y4 -> (\ y3 -> y3)))) (p == 1)) ((\ y5 -> y5) ((\ n -> 1) , ((\ n -> n) 0)))) ((\ p0 -> (((\ p -> (\ h -> (h p))) p0) (\ q -> ((\ y6 -> (yprodRec y6 (\ qs -> (\ n1 -> (((\ n0 -> (\ a -> (a n0))) n1) (\ n -> ((\ n0 -> (if (n0 < n) then (qs n0) else (posLeastFactor p))) , ((\ n2 -> n2) (n + 1))))))))) (h0 q))))) (cPosDivToProd (posLeastFactor p) p)))))))))

cPosPrimeFactorisationsToPms :: (Nat -> (Nat -> ((Nat -> Pos) -> ((Nat -> Pos) -> ((Nat -> Nat), (Nat -> Nat))))))
cPosPrimeFactorisationsToPms = (\ n4 -> (natRec n4 (\ m7 -> ((((\ n5 -> (\ f0 -> (\ g1 -> (\ ps1 -> (\ ps2 -> (if (n5 == 0) then ((f0 ps1) ps2) else ((((g1 (n5 - 1)) ps1) ps2)))))))) m7) (\ ps -> (\ qs -> ((\ x14 -> x14) ((\ n -> n) , ((\ ns6 -> ns6) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((\ x15 -> x15) ((\ x16 -> x16) ((\ x17 -> x17) ((\ n -> n) , ((\ ns7 -> ns7) (\ n -> n))))))))))) (\ n -> (\ g0 -> (\ m1 -> ((((\ n -> (\ f -> (\ g -> (\ ps -> (\ ps0 -> (if (n == 0) then ((f ps) ps0) else ((((g (n - 1)) ps) ps0)))))))) m1) (\ ps -> (\ qs -> ((\ x -> x) ((\ n -> n) , ((\ ns -> ns) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((((\ y0 -> ((((\ y -> (\ h -> (\ h0 -> (\ x0 -> (\ x1 -> (if y then ((h x0) x1) else ((h0 x0) x1))))))) y0) (\ x2 -> (\ x3 -> x2))) (\ x5 -> (\ x4 -> x4)))) (posDiv (qs m) (posProd 0 n ps))) ((\ n3 -> (((\ n2 -> (\ a -> (a n2))) n3) (\ l -> ((\ x7 -> (((\ x6 -> (\ b -> (b x6))) x7) (\ x8 -> (yprodRec x8 (\ ns -> (\ ns1 -> (((\ ns0 -> (\ c -> (c ns0))) ns1) (\ ms -> ((\ x9 -> x9) ((\ l1 -> (transp l n (ns l1))) , ((\ ns2 -> ns2) (\ l1 -> (ms (transp l n l1)))))))))))))) (((g0 m) (\ l0 -> (ps (transp l n l0)))) qs))))) (cPosPrimeDivProdPrimesToInPrimes ps (qs m) n))) ((\ x11 -> (((\ x10 -> (\ b0 -> (b0 x10))) x11) (\ x13 -> ((\ x12 -> x12) (yprodRec x13 (\ ns -> (\ ns4 -> (((\ ns3 -> (\ c0 -> (c0 ns3))) ns4) (\ ms -> (ns , ((\ ns5 -> ns5) ms))))))))))) (((g0 m) ps) qs))))))))))))

---------------------------------

toPrimes :: (Pos -> ((Nat -> Pos), Nat))
toPrimes = ((\ g -> (\ p -> ((g (p + 1)) p))) (\ l3 -> (natRec l3 (\ p -> ((\ n -> 1) , ((\ n4 -> n4) 0))) (\ l10 -> (\ c0 -> (\ p -> ((((\ x0 -> ((((\ x -> (\ h -> (\ h0 -> (if x then h else h0)))) x0) (\ y -> (\ y0 -> y))) (\ y2 -> (\ y1 -> y1)))) (p == 1)) ((\ y3 -> y3) ((\ n -> 1) , ((\ n -> n) 0)))) ((\ p0 -> (((\ p -> (\ c -> (c p))) p0) (\ q -> ((\ y4 -> (yprodRec y4 (\ qs -> (\ n1 -> (((\ n0 -> (\ d -> (d n0))) n1) (\ n -> ((\ n0 -> (if (n0 < n) then (qs n0) else (posLeastFactor p))) , ((\ n2 -> n2) (n + 1))))))))) (c0 q))))) (cPosDivToProd (posLeastFactor p) p)))))))))

genPms :: (Nat -> (Nat -> ((Nat -> Pos) -> ((Nat -> Pos) -> ((Nat -> Nat), (Nat -> Nat))))))
genPms = (\ n9 -> (natRec n9 (\ m11 -> ((((\ n10 -> (\ e0 -> (\ i1 -> (if (n10 == 0) then e0 else ((i1 (n10 - 1))))))) m11) (\ ps -> (\ qs -> ((\ z12 -> z12) ((\ n -> n) , ((\ ns6 -> ns6) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((\ z13 -> z13) ((\ z14 -> z14) ((\ z15 -> z15) ((\ n -> n) , ((\ ns7 -> ns7) (\ n -> n))))))))))) (\ n -> (\ i0 -> (\ m6 -> ((((\ n5 -> (\ e -> (\ i -> (if (n5 == 0) then e else ((i (n5 - 1))))))) m6) (\ ps -> (\ qs -> ((\ z -> z) ((\ n -> n) , ((\ ns -> ns) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((((\ x0 -> ((((\ x1 -> (\ j -> (\ j0 -> (if x1 then j else j0)))) x0) (\ z0 -> (\ z1 -> z0))) (\ z3 -> (\ z2 -> z2)))) (posDiv (qs m) (posProd 0 n ps))) ((\ n8 -> (((\ n7 -> (\ k -> (k n7))) n8) (\ l -> ((\ z5 -> (((\ z4 -> (\ o -> (o z4))) z5) (\ z6 -> (yprodRec z6 (\ ns -> (\ ns1 -> (((\ ns0 -> (\ s -> (s ns0))) ns1) (\ ms -> ((\ z7 -> z7) ((\ l1 -> (transp l n (ns l1))) , ((\ ns2 -> ns2) (\ l1 -> (ms (transp l n l1)))))))))))))) (((i0 m) (\ l0 -> (ps (transp l n l0)))) qs))))) (cPosPrimeDivProdPrimesToInPrimes ps (qs m) n))) ((\ z9 -> (((\ z8 -> (\ o0 -> (o0 z8))) z9) (\ z11 -> ((\ z10 -> z10) (yprodRec z11 (\ ns -> (\ ns4 -> (((\ ns3 -> (\ s0 -> (s0 ns3))) ns4) (\ ms -> (ns , ((\ ns5 -> ns5) ms))))))))))) (((i0 m) ps) qs))))))))))))

prodSplit :: (Pos -> (Pos -> (Pos -> (Pos -> (Pos, (Pos, (Pos, Pos)))))))
prodSplit = (\ p0 -> (\ p1 -> (\ p2 -> (\ p3 -> (case (cPosExPrimeFactorisation p0) of
      { ((,) ps4 n5) -> (case (cPosExPrimeFactorisation p1) of
      { ((,) ps6 n7) -> (case (cPosExPrimeFactorisation p2) of
      { ((,) ps8 n9) -> (case (cPosExPrimeFactorisation p3) of
      { ((,) ps10 n11) -> (case (cPosPrimeFactorisationsToPms (n5 + n7) (n9 + n11) (\ n12 -> (if (n12 < n5) then (ps4 n12) else (ps6 (n12 - n5)))) (\ n12 -> (if (n12 < n9) then (ps8 n12) else (ps10 (n12 - n9))))) of
      { ((,) ns12 ns13) -> ((posProd 0 n5 (\ n14 -> (if ((ns13 n14) < n9) then (if (n14 < n5) then (ps4 n14) else (ps6 (n14 - n5))) else 1))) , ((posProd 0 n5 (\ n14 -> (if (not ((ns13 n14) < n9)) then (if (n14 < n5) then (ps4 n14) else (ps6 (n14 - n5))) else 1))) , ((posProd n5 n7 (\ n14 -> (if ((ns13 n14) < n9) then (if (n14 < n5) then (ps4 n14) else (ps6 (n14 - n5))) else 1))) , (posProd n5 n7 (\ n14 -> (if (not ((ns13 n14) < n9)) then (if (n14 < n5) then (ps4 n14) else (ps6 (n14 - n5))) else 1)))))) }) }) }) }) })))))

---------------------------------

main :: IO ()
main = putStrLn ""