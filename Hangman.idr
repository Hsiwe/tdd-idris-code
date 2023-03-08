import Data.Vect

removeElem : (value : a) -> (xs : Vect (S n) a) -> auto (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem value {n = Z} (y :: []) (There later) = absurd later
removeElem value {n = (S k)} (y :: ys) (There later) = y :: removeElem value ys later


data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) -> 
                   (missing : Vect letters Char) ->
                   WordState guesses_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won :  (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]

notValidEmpty : ValidInput [] -> Void
notValidEmpty (Letter _) impossible

notValidMany : ValidInput (x :: (y :: xs)) -> Void
notValidMany (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No notValidEmpty
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No notValidMany

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               (case isValidString (toUpper x) of
                     (Yes prf) => pure (_ ** prf)
                     (No contra) => do putStrLn "Invalid guess"
                                       readGuess)

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = case isElem letter missing of
                                                      (Yes prf) => Right (MkWordState word (removeElem letter missing prf))
                                                      (No contra) => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do (_ ** Letter letter) <- readGuess
                                 (case processGuess letter st of
                                       (Left l) => do putStrLn "Wrong!"
                                                      (case guesses of
                                                            Z => pure (Lost l)
                                                            (S k) => game l)
                                       (Right r) => do putStrLn "Right!"
                                                       (case letters of
                                                             Z => pure (Won r)
                                                             (S k) => game r))

main : IO ()
main = do result <- game {guesses=2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
            (Lost (MkWordState word missing)) => putStrLn ("You lose. The word wa " ++ word)
            (Won (MkWordState word missing)) => putStrLn "You win!"
