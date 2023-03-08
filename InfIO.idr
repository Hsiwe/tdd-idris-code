data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

data InfIO : Type where
    Do : IO a
         -> (a -> Inf InfIO)
         -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do
         
loopPrint : String -> InfIO
loopPrint msg = do putStrLn msg
                   loopPrint msg
         
run : Fuel -> InfIO -> IO ()
run Dry (Do action cont) = putStrLn "Out of fuel"
run (More fuel) (Do action cont) = do res <- action
                                      run fuel (cont res)
