data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

-- data RunIO : Type -> Type where
--     Quit : a -> RunIO a
--     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

-- (>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
-- (>>=) = Do

-- greet : RunIO ()
-- greet = do putStrLn "Enter your name: "
--            name <- getLine
--            if name == ""
--             then do putStrLn "Bye bye!"
--                     Quit ()
--             else do putStrLn ("Hello " ++ name)
--                     greet

-- run : Fuel -> RunIO a -> IO (Maybe a)
-- run x (Quit value) = pure (Just value)
-- run Dry (Do c f) = pure Nothing
-- run (More x) (Do c f) = do res <- c
--                            run x (f res)

-- main : IO ()
-- main = do run forever greet
--           pure ()

data Command : Type -> Type where
        PutStr : String -> Command ()
        GetLine : Command String

data ConsoleIO : Type -> Type where
        Quit : a -> ConsoleIO a
        Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
        
(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry (Quit y) = pure Nothing
run (More x) (Quit y) = pure (Just y)
run (More x) (Do z f) = do val <- runCommand z
                           run x (f val)
