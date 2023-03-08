import Data.List.Views
import Data.Nat.Views

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | (Snoc xs_rec) with (snocList ys)
    equalSuffix (zs ++ [x]) [] | (Snoc xs_rec) | Empty = []
    equalSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc xs_rec) | (Snoc rec) = if x == y then (equalSuffix zs xs | xs_rec | rec) ++ [x]
                                                                          else []

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n  | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1" 


toBinary2 : Nat -> String
toBinary2 Z = "0"
toBinary2 (S k) = "1" ++ toBinary k

palindrome : List Char -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = if x == y then palindrome ys | rec
                                                          else False
