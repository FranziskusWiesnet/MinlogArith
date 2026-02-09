module Main where

----- Algebras ------------------

type Pos = Integer

type Nat = Integer

----- Recursion operators -------



----- Program constants ---------

natLeast :: (Nat -> ((Nat -> Bool) -> Nat))
natLeast 0 ws = 0
natLeast n ws | n > 0 = (if (ws 0) then 0 else ((natLeast (n - 1) (\ m -> (ws (m + 1)))) + 1))

fastSqrt :: (Pos -> Pos)
fastSqrt 1 = 1
fastSqrt 2 = 1
fastSqrt 3 = 1
fastSqrt p | even (p `quot` 2) && even p = ((\ q -> (if (((((p `quot` 2) `quot` 2) * 2) * 2) < ((q * 2 + 1) * (q * 2 + 1))) then (q * 2) else (q * 2 + 1))) (fastSqrt ((p `quot` 2) `quot` 2)))
fastSqrt p | even ((p - 1) `quot` 2) && odd p = ((\ q -> (if ((((((p - 1) `quot` 2) `quot` 2) * 2 + 1) * 2) < ((q * 2 + 1) * (q * 2 + 1))) then (q * 2) else (q * 2 + 1))) (fastSqrt (((p - 1) `quot` 2) `quot` 2)))
fastSqrt p | odd (p `quot` 2) && even p = ((\ q -> (if ((((((p `quot` 2) - 1) `quot` 2) * 2) * 2 + 1) < ((q * 2 + 1) * (q * 2 + 1))) then (q * 2) else (q * 2 + 1))) (fastSqrt (((p `quot` 2) - 1) `quot` 2)))
fastSqrt p | odd ((p - 1) `quot` 2) && odd p = ((\ q -> (if (((((((p - 1) `quot` 2) - 1) `quot` 2) * 2 + 1) * 2 + 1) < ((q * 2 + 1) * (q * 2 + 1))) then (q * 2) else (q * 2 + 1))) (fastSqrt ((((p - 1) `quot` 2) - 1) `quot` 2)))

fastSquareNumber :: (Pos -> Bool)
fastSquareNumber p = ((\ q -> ((q * q) == p)) (fastSqrt p))

posSquareNumber :: (Pos -> Bool)
posSquareNumber p = ((\ q -> ((q * q) == p)) (posSqrt p))

cFastSqr :: (Pos -> Pos)
cFastSqr = fastSqrt

natLeastUp :: (Nat -> (Nat -> ((Nat -> Bool) -> Nat)))
natLeastUp n0 n ws = (if (n0 <= n) then ((natLeast (n - n0) (\ m -> (ws (m + n0)))) + n0) else 0)

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

posSqrt :: (Pos -> Pos)
posSqrt p = (posMonMax (\ q -> ((q * q) <= p)) ((natHalf (posLog p)) + 1))

cPosSqr :: (Pos -> Pos)
cPosSqr = posSqrt

---------------------------------

fermat :: (Pos -> (Maybe (Pos, Pos)))
fermat = (\ p0 -> (((((\ p -> (\ x -> (\ f0 -> (\ f -> (if (1 == p) then x else (if (even p) then (f0(p `quot` 2)) else (f(p `quot` 2)))))))) p0) Nothing) (\ p2 -> (((((\ p1 -> (\ x0 -> (\ f2 -> (\ f1 -> (if (1 == p1) then x0 else (if (even p1) then (f2(p1 `quot` 2)) else (f1(p1 `quot` 2)))))))) p2) Nothing) (\ p -> (Just (2 , ((\ p3 -> p3) (p * 2)))))) (\ p -> (Just (2 , ((\ p4 -> p4) (p * 2 + 1)))))))) (\ p -> ((((\ y0 -> ((((\ y -> (\ g -> (\ g0 -> (if y then g else g0)))) y0) (\ x1 -> (\ x2 -> x1))) (\ x4 -> (\ x3 -> x3)))) (fastSquareNumber (p * 2 + 1))) (Just ((fastSqrt (p * 2 + 1)) , ((\ p5 -> p5) (fastSqrt (p * 2 + 1)))))) ((((\ y0 -> ((((\ y1 -> (\ g1 -> (\ g2 -> (if y1 then g1 else g2)))) y0) (\ x5 -> (\ x6 -> x5))) (\ x8 -> (\ x7 -> x7)))) (p <= 2)) (((((\ p6 -> (\ x9 -> (\ f4 -> (\ f3 -> (if (1 == p6) then x9 else (if (even p6) then (f4(p6 `quot` 2)) else (f3(p6 `quot` 2)))))))) p) Nothing) (\ p8 -> (((((\ p7 -> (\ x10 -> (\ f6 -> (\ f5 -> (if (1 == p7) then x10 else (if (even p7) then (f6(p7 `quot` 2)) else (f5(p7 `quot` 2)))))))) p8) Nothing) (\ q -> Nothing)) (\ q -> Nothing)))) (\ q -> Nothing))) ((\ n0 -> (((\ n -> (\ h -> (h n))) n0) (\ l -> ((((\ y0 -> ((((\ y2 -> (\ g3 -> (\ g4 -> (if y2 then g3 else g4)))) y0) (\ x11 -> (\ x12 -> x11))) (\ x14 -> (\ x13 -> x13)))) (l == p)) Nothing) (Just ((\ p10 -> (((\ p9 -> (\ a -> (a p9))) p10) (\ q -> (((if (l) <= 1 then 1 else (l)) + q) , ((\ p11 -> p11) ((if (l) <= 1 then 1 else (l)) - q)))))) ((\ p12 -> p12) (cFastSqr (((if (l) <= 1 then 1 else (l)) * (if (l) <= 1 then 1 else (l))) - (p * 2 + 1)))))))))) ((\ n1 -> n1) (natLeastUp ((cFastSqr (p * 2 + 1)) + 1) p (\ l -> (fastSquareNumber (((if (l) <= 1 then 1 else (l)) * (if (l) <= 1 then 1 else (l))) - (p * 2 + 1))))))))))))

fermatPosSqrt :: (Pos -> (Maybe (Pos, Pos)))
fermatPosSqrt = (\ p0 -> (((((\ p -> (\ x -> (\ f0 -> (\ f -> (if (1 == p) then x else (if (even p) then (f0(p `quot` 2)) else (f(p `quot` 2)))))))) p0) Nothing) (\ p2 -> (((((\ p1 -> (\ x0 -> (\ f2 -> (\ f1 -> (if (1 == p1) then x0 else (if (even p1) then (f2(p1 `quot` 2)) else (f1(p1 `quot` 2)))))))) p2) Nothing) (\ p -> (Just (2 , ((\ p3 -> p3) (p * 2)))))) (\ p -> (Just (2 , ((\ p4 -> p4) (p * 2 + 1)))))))) (\ p -> ((((\ y0 -> ((((\ y -> (\ g -> (\ g0 -> (if y then g else g0)))) y0) (\ x1 -> (\ x2 -> x1))) (\ x4 -> (\ x3 -> x3)))) (posSquareNumber (p * 2 + 1))) (Just ((posSqrt (p * 2 + 1)) , ((\ p5 -> p5) (posSqrt (p * 2 + 1)))))) ((((\ y0 -> ((((\ y1 -> (\ g1 -> (\ g2 -> (if y1 then g1 else g2)))) y0) (\ x5 -> (\ x6 -> x5))) (\ x8 -> (\ x7 -> x7)))) (p <= 2)) (((((\ p6 -> (\ x9 -> (\ f4 -> (\ f3 -> (if (1 == p6) then x9 else (if (even p6) then (f4(p6 `quot` 2)) else (f3(p6 `quot` 2)))))))) p) Nothing) (\ p8 -> (((((\ p7 -> (\ x10 -> (\ f6 -> (\ f5 -> (if (1 == p7) then x10 else (if (even p7) then (f6(p7 `quot` 2)) else (f5(p7 `quot` 2)))))))) p8) Nothing) (\ q -> Nothing)) (\ q -> Nothing)))) (\ q -> Nothing))) ((\ n0 -> (((\ n -> (\ h -> (h n))) n0) (\ l -> ((((\ y0 -> ((((\ y2 -> (\ g3 -> (\ g4 -> (if y2 then g3 else g4)))) y0) (\ x11 -> (\ x12 -> x11))) (\ x14 -> (\ x13 -> x13)))) (l == p)) Nothing) (Just ((\ p10 -> (((\ p9 -> (\ a -> (a p9))) p10) (\ q -> (((if (l) <= 1 then 1 else (l)) + q) , ((\ p11 -> p11) ((if (l) <= 1 then 1 else (l)) - q)))))) ((\ p12 -> p12) (posSqrt (((if (l) <= 1 then 1 else (l)) * (if (l) <= 1 then 1 else (l))) - (p * 2 + 1)))))))))) ((\ n1 -> n1) (natLeastUp ((posSqrt (p * 2 + 1)) + 1) p (\ l -> (posSquareNumber (((if (l) <= 1 then 1 else (l)) * (if (l) <= 1 then 1 else (l))) - (p * 2 + 1))))))))))))

testSqrt :: (Pos -> Pos)
testSqrt = cPosSqr

---------------------------------

main :: IO ()
main = putStrLn ""
