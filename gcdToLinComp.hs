module Main where

----- Algebras ------------------

type Nat = Integer

----- Recursion operators -------

natRec :: Nat -> a -> (Nat -> a -> a) -> a
natRec 0 g h = g
natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

----- Program constants ---------

gcd :: (Nat -> (Nat -> Nat))
gcd 0 n = n
gcd n 0 = n
gcd n m | n > 0 && m > 0 = (if ((n - 1) < (m - 1)) then (Main.gcd ((n - 1) + 1) ((m - 1) - (n - 1))) else (Main.gcd ((n - 1) - (m - 1)) ((m - 1) + 1)))

---------------------------------

gcdToLinComp :: (Nat -> (Nat -> (Nat, (Nat, Bool))))
gcdToLinComp = (\ n0 -> (\ n1 -> (if (n0 < n1) then (if (n0 == 0) then (0 , (1 , True)) else ((if (n1 == 0) then (0 , (1 , False)) else ((if (((n1 - 1) - (n0 - 1)) < ((n0 - 1) + 1)) then (case (natRec n1 (\ n4 -> (\ n5 -> (0 , (0 , True)))) (\ n4 -> (\ b5 -> (\ n6 -> (\ n7 -> (if (n6 == 0) then (0 , (1 , True)) else ((if (n7 == 0) then (0 , (1 , False)) else ((if (((n7 - 1) - (n6 - 1)) < ((n6 - 1) + 1)) then (case ((b5 ((n7 - 1) - (n6 - 1))) ((n6 - 1) + 1)) of
      { (,) n180 nb59 -> (case nb59 of
      { (,) n181 b120 -> (if b120 then (n180 , ((n181 + n180) , False)) else ((n180 + n181) , (n181 , True))) }) }) else (if (((n7 - 1) - (n6 - 1)) == ((n6 - 1) + 1)) then ((n7 - 1) , (((n6 - 1) + 1) , True)) else (case ((b5 ((n6 - 1) + 1)) ((n7 - 1) - (n6 - 1))) of
      { (,) n183 nb60 -> (case nb60 of
      { (,) n184 b122 -> (if b122 then ((n183 + n184) , (n184 , True)) else (n183 , ((n184 + n183) , False))) }) }))))))))))) ((n1 - 1) - (n0 - 1)) ((n0 - 1) + 1)) of
      { (,) n186 nb61 -> (case nb61 of
      { (,) n187 b124 -> (if b124 then (n186 , ((n187 + n186) , False)) else ((n186 + n187) , (n187 , True))) }) }) else (if (((n1 - 1) - (n0 - 1)) == ((n0 - 1) + 1)) then ((n1 - 1) , (((n0 - 1) + 1) , True)) else (case (natRec n1 (\ n4 -> (\ n5 -> (0 , (0 , True)))) (\ n4 -> (\ b5 -> (\ n6 -> (\ n7 -> (if (n6 == 0) then (0 , (1 , True)) else ((if (n7 == 0) then (0 , (1 , False)) else ((if (((n7 - 1) - (n6 - 1)) < ((n6 - 1) + 1)) then (case ((b5 ((n7 - 1) - (n6 - 1))) ((n6 - 1) + 1)) of
      { (,) n207 nb68 -> (case nb68 of
      { (,) n208 b138 -> (if b138 then (n207 , ((n208 + n207) , False)) else ((n207 + n208) , (n208 , True))) }) }) else (if (((n7 - 1) - (n6 - 1)) == ((n6 - 1) + 1)) then ((n7 - 1) , (((n6 - 1) + 1) , True)) else (case ((b5 ((n6 - 1) + 1)) ((n7 - 1) - (n6 - 1))) of
      { (,) n210 nb69 -> (case nb69 of
      { (,) n211 b140 -> (if b140 then ((n210 + n211) , (n211 , True)) else (n210 , ((n211 + n210) , False))) }) }))))))))))) ((n0 - 1) + 1) ((n1 - 1) - (n0 - 1))) of
      { (,) n213 nb70 -> (case nb70 of
      { (,) n214 b142 -> (if b142 then ((n213 + n214) , (n214 , True)) else (n213 , ((n214 + n213) , False))) }) }))))))) else (if (n0 == n1) then (0 , (1 , True)) else (if (n1 == 0) then (0 , (1 , False)) else ((if (n0 == 0) then (0 , (1 , True)) else ((if (((n0 - 1) - (n1 - 1)) < ((n1 - 1) + 1)) then (case (natRec n0 (\ n4 -> (\ n5 -> (0 , (0 , True)))) (\ n4 -> (\ b5 -> (\ n6 -> (\ n7 -> (if (n6 == 0) then (0 , (1 , True)) else ((if (n7 == 0) then (0 , (1 , False)) else ((if (((n7 - 1) - (n6 - 1)) < ((n6 - 1) + 1)) then (case ((b5 ((n7 - 1) - (n6 - 1))) ((n6 - 1) + 1)) of
      { (,) n396 nb131 -> (case nb131 of
      { (,) n397 b264 -> (if b264 then (n396 , ((n397 + n396) , False)) else ((n396 + n397) , (n397 , True))) }) }) else (if (((n7 - 1) - (n6 - 1)) == ((n6 - 1) + 1)) then ((n7 - 1) , (((n6 - 1) + 1) , True)) else (case ((b5 ((n6 - 1) + 1)) ((n7 - 1) - (n6 - 1))) of
      { (,) n399 nb132 -> (case nb132 of
      { (,) n400 b266 -> (if b266 then ((n399 + n400) , (n400 , True)) else (n399 , ((n400 + n399) , False))) }) }))))))))))) ((n0 - 1) - (n1 - 1)) ((n1 - 1) + 1)) of
      { (,) n402 nb133 -> (case nb133 of
      { (,) n403 b268 -> (if b268 then (n402 , ((n403 + n402) , True)) else ((n402 + n403) , (n403 , False))) }) }) else (if (((n0 - 1) - (n1 - 1)) == ((n1 - 1) + 1)) then ((n0 - 1) , (((n1 - 1) + 1) , False)) else (case (natRec n0 (\ n4 -> (\ n5 -> (0 , (0 , True)))) (\ n4 -> (\ b5 -> (\ n6 -> (\ n7 -> (if (n6 == 0) then (0 , (1 , True)) else ((if (n7 == 0) then (0 , (1 , False)) else ((if (((n7 - 1) - (n6 - 1)) < ((n6 - 1) + 1)) then (case ((b5 ((n7 - 1) - (n6 - 1))) ((n6 - 1) + 1)) of
      { (,) n423 nb140 -> (case nb140 of
      { (,) n424 b282 -> (if b282 then (n423 , ((n424 + n423) , False)) else ((n423 + n424) , (n424 , True))) }) }) else (if (((n7 - 1) - (n6 - 1)) == ((n6 - 1) + 1)) then ((n7 - 1) , (((n6 - 1) + 1) , True)) else (case ((b5 ((n6 - 1) + 1)) ((n7 - 1) - (n6 - 1))) of
      { (,) n426 nb141 -> (case nb141 of
      { (,) n427 b284 -> (if b284 then ((n426 + n427) , (n427 , True)) else (n426 , ((n427 + n426) , False))) }) }))))))))))) ((n1 - 1) + 1) ((n0 - 1) - (n1 - 1))) of
      { (,) n429 nb142 -> (case nb142 of
      { (,) n430 b286 -> (if b286 then ((n429 + n430) , (n430 , False)) else (n429 , ((n430 + n429) , True))) }) })))))))))))

gcd45 :: Nat
gcd45 = (Main.gcd 4 5)

---------------------------------

main :: IO ()
main = putStrLn ""