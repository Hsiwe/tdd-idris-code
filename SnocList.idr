data SnocList : List a -> Type where
    Empty : SnocList []
    Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

snocListHelp : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) = rewrite appendAssociative input [x] xs in 
                                              snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

myReverse : List a -> List a
myReverse xs = myReverseHelper xs (snocList xs)

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc xs_rec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc xs_rec) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xs_rec) | (Snoc rec) = if x == y then isSuffix xs ys | xs_rec | rec
                                                                               else False

-- fib : -> List Integer
-- fib = [0,1] ++ zipWith (+) fib (tail fib)
