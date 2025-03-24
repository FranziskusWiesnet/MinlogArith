module Main where

----- Algebras ------------------

type Pos = Integer

type Nat = Integer

----- Recursion operators -------

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

yprodRec :: ((alpha1, alpha2) -> ((alpha1 -> (alpha2 -> alpha5465)) -> alpha5465))
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
cPosDivToProd = (\ p0 -> (\ p1 -> (if (1 == p0) then p1 else (if (even p0) then ((\ p2 -> (if (1 == p1) then 1 else (if (even p1) then ((natRec (p0 + p1) (\ p4 -> (\ p5 -> 1)) (\ n4 -> (\ f -> (\ p6 -> (\ p7 -> (if (1 == p6) then p7 else (if (even p6) then ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((f p8)(p7 `quot` 2)) else ((\ p9 -> 1)(p7 `quot` 2)))))(p6 `quot` 2)) else ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((\ p9 -> (((f (p8 * 2 + 1)) p9) * 2))(p7 `quot` 2)) else ((\ p9 -> (if (p8 == p9) then 1 else (if (p8 < p9) then (((f (p8 * 2 + 1)) (p9 - p8)) * 2 + 1) else 1)))(p7 `quot` 2)))))(p6 `quot` 2)))))))) p2)(p1 `quot` 2)) else ((\ p3 -> 1)(p1 `quot` 2)))))(p0 `quot` 2)) else ((\ p2 -> (if (1 == p1) then 1 else (if (even p1) then ((\ p3 -> ((natRec (p0 + p1) (\ p4 -> (\ p5 -> 1)) (\ n4 -> (\ f -> (\ p6 -> (\ p7 -> (if (1 == p6) then p7 else (if (even p6) then ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((f p8)(p7 `quot` 2)) else ((\ p9 -> 1)(p7 `quot` 2)))))(p6 `quot` 2)) else ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((\ p9 -> (((f (p8 * 2 + 1)) p9) * 2))(p7 `quot` 2)) else ((\ p9 -> (if (p8 == p9) then 1 else (if (p8 < p9) then (((f (p8 * 2 + 1)) (p9 - p8)) * 2 + 1) else 1)))(p7 `quot` 2)))))(p6 `quot` 2)))))))) (p2 * 2 + 1) p3) * 2))(p1 `quot` 2)) else ((\ p3 -> (if (p2 == p3) then 1 else (if (p2 < p3) then ((natRec (p0 + p1) (\ p4 -> (\ p5 -> 1)) (\ n4 -> (\ f -> (\ p6 -> (\ p7 -> (if (1 == p6) then p7 else (if (even p6) then ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((f p8)(p7 `quot` 2)) else ((\ p9 -> 1)(p7 `quot` 2)))))(p6 `quot` 2)) else ((\ p8 -> (if (1 == p7) then 1 else (if (even p7) then ((\ p9 -> (((f (p8 * 2 + 1)) p9) * 2))(p7 `quot` 2)) else ((\ p9 -> (if (p8 == p9) then 1 else (if (p8 < p9) then (((f (p8 * 2 + 1)) (p9 - p8)) * 2 + 1) else 1)))(p7 `quot` 2)))))(p6 `quot` 2)))))))) (p2 * 2 + 1) (p3 - p2)) * 2 + 1) else 1)))(p1 `quot` 2)))))(p0 `quot` 2))))))

posGcd :: (Pos -> (Pos -> Pos))
posGcd 1 p = 1
posGcd p 1 | even p = 1
posGcd p q | even p && even q = ((posGcd (p `quot` 2) (q `quot` 2)) * 2)
posGcd p q | even p && odd q = (posGcd (p `quot` 2) (((q - 1) `quot` 2) * 2 + 1))
posGcd p 1 | odd p = 1
posGcd p q | odd p && even q = (posGcd (((p - 1) `quot` 2) * 2 + 1) (q `quot` 2))
posGcd p q | odd p && odd q = (if (((p - 1) `quot` 2) == ((q - 1) `quot` 2)) then (((p - 1) `quot` 2) * 2 + 1) else (if (((p - 1) `quot` 2) < ((q - 1) `quot` 2)) then (posGcd (((p - 1) `quot` 2) * 2 + 1) (((q - 1) `quot` 2) - ((p - 1) `quot` 2))) else (posGcd (((p - 1) `quot` 2) - ((q - 1) `quot` 2)) (((q - 1) `quot` 2) * 2 + 1))))

posProd :: (Nat -> (Nat -> ((Nat -> Pos) -> Pos)))
posProd n 0 ps = 1
posProd n m ps | m > 0 = ((posProd n (m - 1) ps) * (ps (n + (m - 1))))

cPosPrimeDivProdToDiv :: ((Nat -> Pos) -> (Pos -> (Nat -> Nat)))
cPosPrimeDivProdToDiv = (\ ps0 -> (\ p1 -> (\ n2 -> (natRec n2 0 (\ n3 -> (\ n4 -> (if ((posGcd p1 (posProd 0 n3 ps0)) == p1) then n4 else n3)))))))

posDiv :: (Pos -> (Pos -> Bool))
posDiv p q = ((posGcd p q) == p)

transp :: (Nat -> (Nat -> (Nat -> Nat)))
transp n m l = (if (l == n) then m else (if (l == m) then n else l))

cPosPrimeDivProdPrimesToInPrimes :: ((Nat -> Pos) -> (Pos -> (Nat -> Nat)))
cPosPrimeDivProdPrimesToInPrimes = cPosPrimeDivProdToDiv

posSeqFilter :: ((Nat -> Pos) -> ((Nat -> Bool) -> (Nat -> Pos)))
posSeqFilter ps ws n = (if (ws n) then (ps n) else 1)

posSeqConcat :: (Nat -> (Nat -> ((Nat -> Pos) -> ((Nat -> Pos) -> (Nat -> Pos)))))
posSeqConcat n m ps qs l = (if (l < n) then (ps l) else (qs (l - n)))

cPosPrimeFactorisationsToPms :: (Nat -> (Nat -> ((Nat -> Pos) -> ((Nat -> Pos) -> ((Nat -> Nat), (Nat -> Nat))))))
cPosPrimeFactorisationsToPms = (\ n0 -> (natRec n0 (\ n4 -> (\ ps5 -> (\ ps6 -> ((\ n7 -> n7) , (\ n7 -> n7))))) (\ n4 -> (\ f -> (\ n6 -> (\ ps7 -> (\ ps8 -> (if (n6 == 0) then ((\ n9 -> n9) , (\ n9 -> n9)) else ((if ((posGcd (ps8 (n6 - 1)) (posProd 0 n4 ps7)) == (ps8 (n6 - 1))) then (case (((f (n6 - 1)) (\ n10 -> (ps7 (if (n10 == (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4)) then n4 else (if (n10 == n4) then (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4) else n10))))) ps8) of
      { (,) ns3 ns4 -> ((\ n12 -> (if ((ns3 n12) == (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4)) then n4 else (if ((ns3 n12) == n4) then (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4) else (ns3 n12)))) , (\ n12 -> (ns4 (if (n12 == (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4)) then n4 else (if (n12 == n4) then (cPosPrimeDivProdPrimesToInPrimes ps7 (ps8 (n6 - 1)) n4) else n12))))) }) else (case (((f (n6 - 1)) ps7) ps8) of
      { (,) ns5 ns6 -> (ns5 , ns6) })))))))))))

cPosExPrimeFactorisation :: (Pos -> ((Nat -> Pos), Nat))
cPosExPrimeFactorisation = (\ p0 -> (if (p0 == 1) then ((\ n1 -> 1) , 0) else (case (natRec p0 (\ p1 -> ((\ n2 -> 1) , 0)) (\ n1 -> (\ f -> (\ p3 -> (if (p3 == 1) then ((\ n4 -> 1) , 0) else (case (f (cPosDivToProd (if ((posLeastFactorAux p3) == ((if (((2 ^ (natHalf (posLog p3))) * (2 ^ (natHalf (posLog p3)))) <= p3) then (posMonMaxAux (\ p4 -> ((p4 * p4) <= p3)) (natHalf (posLog p3)) (2 ^ (natHalf (posLog p3)))) else (posMonMaxAux (\ p4 -> ((p4 * p4) <= p3)) (natHalf (posLog p3)) 1)) + 1)) then p3 else (posLeastFactorAux p3)) p3)) of
      { (,) ps n -> ((\ n6 -> (if (n6 < n) then (ps n6) else (if ((posLeastFactorAux p3) == ((if (((2 ^ (natHalf (posLog p3))) * (2 ^ (natHalf (posLog p3)))) <= p3) then (posMonMaxAux (\ p7 -> ((p7 * p7) <= p3)) (natHalf (posLog p3)) (2 ^ (natHalf (posLog p3)))) else (posMonMaxAux (\ p7 -> ((p7 * p7) <= p3)) (natHalf (posLog p3)) 1)) + 1)) then p3 else (posLeastFactorAux p3)))) , (n + 1)) }))))) (cPosDivToProd (if ((posLeastFactorAux p0) == ((if (((2 ^ (natHalf (posLog p0))) * (2 ^ (natHalf (posLog p0)))) <= p0) then (posMonMaxAux (\ p1 -> ((p1 * p1) <= p0)) (natHalf (posLog p0)) (2 ^ (natHalf (posLog p0)))) else (posMonMaxAux (\ p1 -> ((p1 * p1) <= p0)) (natHalf (posLog p0)) 1)) + 1)) then p0 else (posLeastFactorAux p0)) p0)) of
      { (,) ps0 n0 -> ((\ n3 -> (if (n3 < n0) then (ps0 n3) else (if ((posLeastFactorAux p0) == ((if (((2 ^ (natHalf (posLog p0))) * (2 ^ (natHalf (posLog p0)))) <= p0) then (posMonMaxAux (\ p4 -> ((p4 * p4) <= p0)) (natHalf (posLog p0)) (2 ^ (natHalf (posLog p0)))) else (posMonMaxAux (\ p4 -> ((p4 * p4) <= p0)) (natHalf (posLog p0)) 1)) + 1)) then p0 else (posLeastFactorAux p0)))) , (n0 + 1)) })))

---------------------------------

toPrimes :: (Pos -> ((Nat -> Pos), Nat))
toPrimes = ((\ d -> (\ p -> ((d (p + 1)) p))) (\ l11 -> (natRec l11 (\ p -> ((\ n -> 1) , ((\ n12 -> n12) 0))) (\ l10 -> (\ i0 -> (\ p -> ((((\ w0 -> ((((\ w -> (\ e -> (\ e0 -> (if w then e else e0)))) w0) (\ x3 -> (\ x4 -> x3))) (\ x6 -> (\ x5 -> x5)))) (p == 1)) ((\ x7 -> x7) ((\ n -> 1) , ((\ n7 -> n7) 0)))) ((\ p1 -> (((\ p0 -> (\ i -> (i p0))) p1) (\ q -> ((\ x8 -> (yprodRec x8 (\ qs -> (\ n9 -> (((\ n8 -> (\ j -> (j n8))) n9) (\ n -> ((\ n0 -> (if (n0 < n) then (qs n0) else (posLeastFactor p))) , ((\ n10 -> n10) (n + 1))))))))) (i0 q))))) (cPosDivToProd (posLeastFactor p) p)))))))))

genPms :: (Nat -> (Nat -> ((Nat -> Pos) -> ((Nat -> Pos) -> ((Nat -> Nat), (Nat -> Nat))))))
genPms = (\ n17 -> (natRec n17 (\ m19 -> ((((\ n18 -> (\ k0 -> (\ o1 -> (if (n18 == 0) then k0 else ((o1 (n18 - 1))))))) m19) (\ ps -> (\ qs -> ((\ y15 -> y15) ((\ n -> n) , ((\ ns8 -> ns8) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((\ y16 -> y16) ((\ y17 -> y17) ((\ y18 -> y18) ((\ n -> n) , ((\ ns9 -> ns9) (\ n -> n))))))))))) (\ n -> (\ o0 -> (\ m14 -> ((((\ n13 -> (\ k -> (\ o -> (if (n13 == 0) then k else ((o (n13 - 1))))))) m14) (\ ps -> (\ qs -> ((\ y2 -> y2) ((\ n -> n) , ((\ ns1 -> ns1) (\ n -> n))))))) (\ m -> (\ ps -> (\ qs -> ((((\ w0 -> ((((\ w1 -> (\ s -> (\ s0 -> (if w1 then s else s0)))) w0) (\ y3 -> (\ y4 -> y3))) (\ y6 -> (\ y5 -> y5)))) (posDiv (qs m) (posProd 0 n ps))) ((\ n16 -> (((\ n15 -> (\ t -> (t n15))) n16) (\ l -> ((\ y8 -> (((\ y7 -> (\ u -> (u y7))) y8) (\ y9 -> (yprodRec y9 (\ ns -> (\ ns3 -> (((\ ns2 -> (\ v -> (v ns2))) ns3) (\ ms -> ((\ y10 -> y10) ((\ l1 -> (transp l n (ns l1))) , ((\ ns4 -> ns4) (\ l1 -> (ms (transp l n l1)))))))))))))) (((o0 m) (\ l0 -> (ps (transp l n l0)))) qs))))) (cPosPrimeDivProdPrimesToInPrimes ps (qs m) n))) ((\ y12 -> (((\ y11 -> (\ u0 -> (u0 y11))) y12) (\ y14 -> ((\ y13 -> y13) (yprodRec y14 (\ ns -> (\ ns6 -> (((\ ns5 -> (\ v0 -> (v0 ns5))) ns6) (\ ms -> (ns , ((\ ns7 -> ns7) ms))))))))))) (((o0 m) ps) qs))))))))))))

prodSplit :: (Pos -> (Pos -> (Pos -> (Pos -> (Pos, (Pos, (Pos, Pos)))))))
prodSplit = (\ p0 -> (\ p1 -> (\ q0 -> (\ q1 -> ((\ x -> ((\ x0 -> ((\ x1 -> ((\ x2 -> (yprodRec x (\ ps0 -> (\ n0 -> (yprodRec x0 (\ ps1 -> (\ n2 -> (yprodRec x1 (\ qs0 -> (\ n4 -> (yprodRec x2 (\ qs1 -> (\ n6 -> (((\ n -> (\ g -> (g n))) n0) (\ m10 -> (((\ n1 -> (\ g0 -> (g0 n1))) n2) (\ m11 -> (((\ n3 -> (\ g1 -> (g1 n3))) n4) (\ n10 -> (((\ n5 -> (\ g2 -> (g2 n5))) n6) (\ n11 -> ((\ y0 -> (((\ y -> (\ h -> (h y))) y0) (\ y1 -> (yprodRec y1 (\ ns -> (\ ns0 -> (((\ ns -> (\ c -> (c ns))) ns0) (\ ms -> ((\ z -> z) ((posProd 0 m10 (posSeqFilter (posSeqConcat m10 m11 ps0 ps1) (\ l -> ((ms l) < n10)))) , ((posProd 0 m10 (posSeqFilter (posSeqConcat m10 m11 ps0 ps1) (\ l -> (not ((ms l) < n10))))) , ((posProd m10 m11 (posSeqFilter (posSeqConcat m10 m11 ps0 ps1) (\ l -> ((ms l) < n10)))) , ((\ p -> p) (posProd m10 m11 (posSeqFilter (posSeqConcat m10 m11 ps0 ps1) (\ l -> (not ((ms l) < n10)))))))))))))))))) (cPosPrimeFactorisationsToPms (m10 + m11) (n10 + n11) (posSeqConcat m10 m11 ps0 ps1) (posSeqConcat n10 n11 qs0 qs1)))))))))))))))))))))))) (cPosExPrimeFactorisation q1))) (cPosExPrimeFactorisation q0))) (cPosExPrimeFactorisation p1))) (cPosExPrimeFactorisation p0))))))

---------------------------------

main :: IO ()
main = putStrLn ""