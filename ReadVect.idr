import Data.Vect
readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
    x <- getLine
    xs <- readVectLen k
    pure (x :: xs)

data VectUnknown : Type -> Type where
    MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (len ** Vect len String)
readVect = do
    x <- getLine
    if (x == "")
        then pure (_ ** [])
        else do (_ ** xs) <- readVect
                pure (_ ** (x :: xs))
-- readVect = do
--     x <- getLine
--     if (x == "")
--         then pure (MkVect _ [])
--         else do MkVect _ xs <- readVect
--                 pure (MkVect _ (x :: xs))

printVect : Show a => VectUnknown a -> IO()
printVect (MkVect len xs) = putStrLn (show xs ++ " (length " ++ show len ++ ")")

zipInputs : IO ()
zipInputs = do putStrLn "Enter first vector (blank line to end):"
               (len1 ** vect1) <- readVect
               putStrLn "Enter second vector (blank line to end):"
               (len2 ** vect2) <- readVect
               (case exactLength len1 vect2 of
                     Nothing => putStrLn "Vectors are different lengths"
                     (Just vect2') => printLn (zip vect1 vect2'))
