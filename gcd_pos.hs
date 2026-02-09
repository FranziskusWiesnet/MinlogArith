module Main where

----- Algebras ------------------

type Pos = Integer

type Nat = Integer

----- Recursion operators -------

ysumRec :: ((Either alpha1 alpha2) -> ((alpha1 -> alpha3953) -> ((alpha2 -> alpha3953) -> alpha3953)))
ysumRec (Left a) g f = (g a)
ysumRec (Right b) g f = (f b)

yprodRec :: ((alpha1, alpha2) -> ((alpha1 -> (alpha2 -> alpha3955)) -> alpha3955))
yprodRec (a , b) f = ((f a) b)

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

----- Program constants ---------

posLog :: (Pos -> Nat)
posLog 1 = 0
posLog p | even p = ((posLog (p `quot` 2)) + 1)
posLog p | odd p = ((posLog ((p - 1) `quot` 2)) + 1)

posMonMaxAux :: ((Pos -> Bool) -> (Nat -> (Pos -> Pos)))
posMonMaxAux wf 0 q = q
posMonMaxAux wf n 1 | n > 0 = (if (wf (2 ^ (n - 1))) then (posMonMaxAux wf (n - 1) (2 ^ (n - 1))) else (posMonMaxAux wf (n - 1) 1))
posMonMaxAux wf n q | n > 0 && even q = (if (wf (((q `quot` 2) * 2) + (2 ^ (n - 1)))) then (posMonMaxAux wf (n - 1) (((q `quot` 2) * 2) + (2 ^ (n - 1)))) else (posMonMaxAux wf (n - 1) ((q `quot` 2) * 2)))
posMonMaxAux wf n q | n > 0 && odd q = (if (wf ((((q - 1) `quot` 2) * 2 + 1) + (2 ^ (n - 1)))) then (posMonMaxAux wf (n - 1) ((((q - 1) `quot` 2) * 2 + 1) + (2 ^ (n - 1)))) else (posMonMaxAux wf (n - 1) (((q - 1) `quot` 2) * 2 + 1)))

posMonMax :: ((Pos -> Bool) -> (Nat -> Pos))
posMonMax wf n = (posMonMaxAux wf n 1)

euclidGcd :: (Pos -> (Pos -> Pos))
euclidGcd p q = (if (q <= p) then (if (((roundDiv p q) * q) == p) then q else (euclidGcd (p - ((roundDiv p q) * q)) q)) else (if (((roundDiv q p) * p) == q) then p else (euclidGcd (q - ((roundDiv q p) * p)) p)))

roundDiv :: (Pos -> (Pos -> Pos))
roundDiv p q = (posMonMax (\ q0 -> ((q0 * q) <= p)) (((posLog p) - (posLog q)) + 1))

posGcd :: (Pos -> (Pos -> Pos))
posGcd 1 p = 1
posGcd p 1 | even p = 1
posGcd p q | even p && even q = ((posGcd (p `quot` 2) (q `quot` 2)) * 2)
posGcd p q | even p && odd q = (posGcd (p `quot` 2) (((q - 1) `quot` 2) * 2 + 1))
posGcd p 1 | odd p = 1
posGcd p q | odd p && even q = (posGcd (((p - 1) `quot` 2) * 2 + 1) (q `quot` 2))
posGcd p q | odd p && odd q = (if (((p - 1) `quot` 2) == ((q - 1) `quot` 2)) then (((p - 1) `quot` 2) * 2 + 1) else (if (((p - 1) `quot` 2) < ((q - 1) `quot` 2)) then (posGcd (((p - 1) `quot` 2) * 2 + 1) (((q - 1) `quot` 2) - ((p - 1) `quot` 2))) else (posGcd (((p - 1) `quot` 2) - ((q - 1) `quot` 2)) (((q - 1) `quot` 2) * 2 + 1))))

---------------------------------

euclid :: (Pos -> (Pos -> Pos))
euclid = euclidGcd

stein :: (Pos -> (Pos -> Pos))
stein = posGcd

extEuclid :: (Pos -> (Pos -> (Either Pos (Either Pos (Either (Pos, Pos) (Pos, Pos))))))
extEuclid = ((\ h -> (\ p0 -> (\ p1 -> ((((\ x0 -> ((((\ x -> (\ g -> (\ g0 -> (if x then g else g0)))) x0) (\ y -> (\ y0 -> y))) (\ y2 -> (\ y1 -> y1)))) (p0 <= p1)) (((h ((p0 + p1) + 1)) p0) p1)) ((\ y3 -> y3) ((\ y4 -> (ysumRec y4 (\ p6 -> (Right (Left p6))) (\ d -> (ysumRec d (\ p5 -> (Left p5)) (\ w -> (ysumRec w (\ z0 -> (yprodRec z0 (\ q0 -> (\ p3 -> (((\ p2 -> (\ c0 -> (c0 p2))) p3) (\ q1 -> (Right (Right (Right (q1 , ((\ p4 -> p4) q0))))))))))) (\ z -> (yprodRec z (\ q0 -> (\ p0 -> (((\ p -> (\ c -> (c p))) p0) (\ q1 -> (Right (Right (Left (q1 , ((\ p1 -> p1) q0))))))))))))))))) (((h ((p1 + p0) + 1)) p1) p0))))))) (\ l -> (natRec l (\ p0 -> (\ p1 -> (Left ((\ p20 -> p20) 1)))) (\ l -> (\ e -> (\ p0 -> (\ p1 -> ((((\ x0 -> ((((\ x1 -> (\ g1 -> (\ g2 -> (if x1 then g1 else g2)))) x0) (\ y5 -> (\ y6 -> y5))) (\ y8 -> (\ y7 -> y7)))) (((roundDiv p1 p0) * p0) == p1)) (Left ((\ p7 -> p7) (roundDiv p1 p0)))) ((\ y9 -> (ysumRec y9 (\ p18 -> (((\ p17 -> (\ c4 -> (c4 p17))) p18) (\ q -> (Right (Right (Left ((roundDiv p1 p0) , ((\ p19 -> p19) 1)))))))) (\ d0 -> (ysumRec d0 (\ p15 -> (((\ p14 -> (\ c3 -> (c3 p14))) p15) (\ q -> (Left ((\ p16 -> p16) (q + (roundDiv p1 p0))))))) (\ w0 -> (ysumRec w0 (\ z2 -> (yprodRec z2 (\ q0 -> (\ p12 -> (((\ p11 -> (\ c2 -> (c2 p11))) p12) (\ q1 -> (Right (Right (Right ((q1 + (q0 * (roundDiv p1 p0))) , ((\ p13 -> p13) q0))))))))))) (\ z1 -> (yprodRec z1 (\ q0 -> (\ p9 -> (((\ p8 -> (\ c1 -> (c1 p8))) p9) (\ q1 -> (Right (Right (Left ((q1 + (q0 * (roundDiv p1 p0))) , ((\ p10 -> p10) q0))))))))))))))))) ((e (p1 - ((roundDiv p1 p0) * p0))) p0))))))))))

extStein :: (Pos -> (Pos -> (Either Pos (Either Pos (Either (Pos, Pos) (Pos, Pos))))))
extStein = ((\ h0 -> (\ p0 -> (\ p1 -> (((h0 ((p0 + p1) + 1)) p0) p1)))) (\ l0 -> (natRec l0 (\ p0 -> (\ p1 -> (Left ((\ p81 -> p81) 1)))) (\ n -> (\ e2 -> (\ p22 -> (((((\ p21 -> (\ c5 -> (\ e1 -> (\ e0 -> (if (1 == p21) then c5 else (if (even p21) then (e1(p21 `quot` 2)) else (e0(p21 `quot` 2)))))))) p22) (\ p -> (Left ((\ p23 -> p23) p)))) (\ p0 -> (\ p25 -> (((((\ p24 -> (\ y10 -> (\ c7 -> (\ c6 -> (if (1 == p24) then y10 else (if (even p24) then (c7(p24 `quot` 2)) else (c6(p24 `quot` 2)))))))) p25) (Right (Left ((\ p26 -> p26) (p0 * 2))))) (\ p1 -> ((e2 p0) p1))) (\ p1 -> ((\ y11 -> (ysumRec y11 (\ p37 -> (((\ p36 -> (\ c11 -> (c11 p36))) p37) (\ p -> ((\ y12 -> y12) ((\ y13 -> y13) (Right (Right (Left (p1 , ((\ p38 -> p38) p0)))))))))) (\ d1 -> (ysumRec d1 (\ p34 -> (((\ p33 -> (\ c10 -> (c10 p33))) p34) (\ p -> (Right (Left ((\ p35 -> p35) (p * 2))))))) (\ w1 -> (ysumRec w1 (\ z4 -> (yprodRec z4 (\ p2 -> (\ p31 -> (((\ p30 -> (\ c9 -> (c9 p30))) p31) (\ p3 -> (Right (Right (Left (((p1 + 1) * p2) , ((\ p32 -> p32) (p3 + (p2 * p0))))))))))))) (\ z3 -> (yprodRec z3 (\ p2 -> (\ p28 -> (((\ p27 -> (\ c8 -> (c8 p27))) p28) (\ p3 -> (Right (Right (Right (((p1 * p2) + p2) , ((\ p29 -> p29) (p3 + (p2 * p0))))))))))))))))))) ((e2 p0) (p1 * 2 + 1)))))))) (\ p0 -> (\ p40 -> (((((\ p39 -> (\ y14 -> (\ c13 -> (\ c12 -> (if (1 == p39) then y14 else (if (even p39) then (c13(p39 `quot` 2)) else (c12(p39 `quot` 2)))))))) p40) (Right (Left ((\ p41 -> p41) (p0 * 2 + 1))))) (\ p1 -> ((\ y17 -> (ysumRec y17 (\ p52 -> (((\ p51 -> (\ c17 -> (c17 p51))) p52) (\ q -> (Left ((\ p53 -> p53) ((\ p54 -> p54) (q * 2))))))) (\ d2 -> (ysumRec d2 (\ p49 -> (((\ p48 -> (\ c16 -> (c16 p48))) p49) (\ q -> ((\ y15 -> y15) ((\ y16 -> y16) (Right (Right (Right (p1 , ((\ p50 -> p50) p0)))))))))) (\ w2 -> (ysumRec w2 (\ z6 -> (yprodRec z6 (\ p3 -> (\ p46 -> (((\ p45 -> (\ c15 -> (c15 p45))) p46) (\ p4 -> (Right (Right (Left ((p3 + (p4 * p1)) , ((\ p47 -> p47) ((p4 * p0) + p4)))))))))))) (\ z5 -> (yprodRec z5 (\ p2 -> (\ p43 -> (((\ p42 -> (\ c14 -> (c14 p42))) p43) (\ p3 -> (Right (Right (Right ((p2 + (p3 * p1)) , ((\ p44 -> p44) ((p3 * p0) + p3)))))))))))))))))) ((e2 (p0 * 2 + 1)) p1)))) (\ p1 -> ((\ y18 -> y18) ((((\ x0 -> ((((\ x2 -> (\ g3 -> (\ g4 -> (if x2 then g3 else g4)))) x0) (\ y19 -> (\ y20 -> y19))) (\ y22 -> (\ y21 -> y21)))) (p0 == p1)) (Left ((\ p55 -> p55) ((\ p56 -> p56) 1)))) ((((\ x0 -> ((((\ x3 -> (\ g5 -> (\ g6 -> (if x3 then g5 else g6)))) x0) (\ y23 -> (\ y24 -> y23))) (\ y26 -> (\ y25 -> y25)))) (p0 < p1)) ((\ y27 -> y27) ((\ y28 -> y28) ((\ y29 -> (ysumRec y29 (\ p67 -> (((\ p66 -> (\ c21 -> (c21 p66))) p67) (\ q -> (Left ((\ p68 -> p68) (q + 1)))))) (\ d3 -> (ysumRec d3 (\ p64 -> (((\ p63 -> (\ c20 -> (c20 p63))) p64) (\ q -> (Left ((\ p65 -> p65) 1))))) (\ w3 -> (ysumRec w3 (\ z8 -> (yprodRec z8 (\ p2 -> (\ p61 -> (((\ p60 -> (\ c19 -> (c19 p60))) p61) (\ p3 -> (Right (Right (Left ((p2 + p3) , ((\ p62 -> p62) p3))))))))))) (\ z7 -> (yprodRec z7 (\ p2 -> (\ p58 -> (((\ p57 -> (\ c18 -> (c18 p57))) p58) (\ p3 -> (Right (Right (Right ((p2 + p3) , ((\ p59 -> p59) p3))))))))))))))))) ((e2 (p0 * 2 + 1)) ((p1 * 2) - (p0 * 2))))))) ((\ y30 -> y30) ((\ y31 -> y31) ((\ y32 -> (ysumRec y32 (\ p79 -> (((\ p78 -> (\ c25 -> (c25 p78))) p79) (\ q -> (Left ((\ p80 -> p80) 1))))) (\ d4 -> (ysumRec d4 (\ p76 -> (((\ p75 -> (\ c24 -> (c24 p75))) p76) (\ q -> (Right (Left ((\ p77 -> p77) (q + 1))))))) (\ w4 -> (ysumRec w4 (\ z10 -> (yprodRec z10 (\ p2 -> (\ p73 -> (((\ p72 -> (\ c23 -> (c23 p72))) p73) (\ p3 -> (Right (Right (Left (p2 , ((\ p74 -> p74) (p3 + p2)))))))))))) (\ z9 -> (yprodRec z9 (\ p2 -> (\ p70 -> (((\ p69 -> (\ c22 -> (c22 p69))) p70) (\ p3 -> (Right (Right (Right (p2 , ((\ p71 -> p71) (p3 + p2)))))))))))))))))) ((e2 ((p0 * 2) - (p1 * 2))) (p1 * 2 + 1)))))))))))))))))))

---------------------------------

main :: IO ()
main = putStrLn ""