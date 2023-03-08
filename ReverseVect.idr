import Data.Vect

-- myReverse : Vect n elem -> Vect n elem
-- myReverse [] = []
-- myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
--     where
--         reverseProof : Vect (k + 1) elem -> Vect (S k) elem
--         reverseProof {k} result = rewrite plusCommutative 1 k in result


reverseProof_nil : Vect n1 a -> Vect (plus n1 0) a
reverseProof_nil {n1} xs = rewrite plusZeroRightNeutral n1 in xs

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
        reverse' acc [] = reverseProof_nil acc
        reverse' {n} {m = S k} acc (x :: xs)
                        = rewrite sym (plusSuccRightSucc n k) in (reverse' (x::acc) xs)
-- myReverse {n = S k} (x :: xs) = let result = myReverse xs ++ [x] in
--                                     rewrite plusCommutative 1 k in result


-- myPlusCommutes_rhs_3 : (k : Nat) -> (m : Nat) -> S (plus k m) = plus m (S k)
-- myPlusCommutes_rhs_3 k m = rewrite plusSuccRightSucc k m in Refl

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite (myPlusCommutes k m) in (plusSuccRightSucc m k)
-- myPlusCommutes (S k) m = rewrite (myPlusCommutes k m) in plusSuccRightSucc m k
-- myPlusCommutes (S k) m = (\_aX => rewrite plusSuccRightSucc k m in (sym ?hole1)) (myPlusCommutes k m)
-- myPlusCommutes (S k) m = rewrite plusSuccRightSucc k m in rewrite sym (myPlusCommutes k m) in Refl
-- myPlusCommutes (S k) m = myPlusCommutes_rhs_3 k m (myPlusCommutes k m)


append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in xs

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append [] ys = append_nil ys
append (x :: xs) ys = append_xs (x :: append xs ys)
