data InfList : Type -> Type where
    (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))


-- getPrefix : (count : Nat) -> InfList ty -> List ty
-- getPrefix Z x = []
-- getPrefix (S k) (value :: xs) = value :: ?hole

getPrefix : (count : Nat) -> Stream a -> List a
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith xs [] = []
labelWith (value :: xs) (x :: ys) = (value, x) :: labelWith xs ys

label : List a -> List (Integer, a)
label = labelWith (iterate (+1) 0)

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score 
    = do putStrLn ("Score so far: " ++ show score)
         putStr (show num1 ++ " * " ++ show num2 ++ "? ")
         answer <- getLine
         if cast answer == num1 * num2
            then do putStrLn "Correct!"
                    quiz nums (score + 1)
            else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                    quiz nums score


every_other : Stream Int -> Stream Int
every_other (x :: y :: xs) = y :: every_other xs

Functor InfList where
  map func (value :: xs) = (func value) :: Delay (map func xs)

foo : List Integer
foo = getPrefix 10 (map (*2) ?hole)

