data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

testTree : Tree String
testTree = Node (Node (Node Empty "Jis" Empty) "Fred"
                      (Node Empty "Shella" Empty)) "Alice"
                (Node Empty "Rob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node x y z) = flatten x ++ y :: flatten z


data State : (stateType : Type) -> Type -> Type where
    Get : State stateType stateType
    Put : stateType -> State stateType ()

    Pure : ty -> State stateType ty
    Bind : State stateType a -> (a -> State stateType b) -> State stateType b

-- Functor (State stateType) where
--   map func x = Bind x (\val => Pure (func val))
    
-- Applicative (State stateType) where
--   pure = Pure
--   (<*>) f a = Bind f (\f' => 
--               Bind a (\a' => Pure (f' a')))
  
mutual
  Functor (State stateType) where
    map func x = do val <- x
                    pure (func val)

  Applicative (State stateType) where
    pure = Pure
    (<*>) x y = do x' <- x
                   y' <- y
                   pure (x' y')

  Monad (State stateType) where
    (>>=) = Bind

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) 
    = do left_labelled <- treeLabelWith left
         (this :: rest) <- get
         put rest
         right_labelled <- treeLabelWith right
         pure (Node left_labelled (this, val) right_labelled)

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put x) st = ((), x)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                              runState (prog val) nextState


addIfPositive : Integer -> State Integer Bool
addIfPositive val = do when (val > 0) $ 
                           do current <- get
                              put (current + val)
                       pure (val > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- traverse addIfPositive xs
                     pure (length (filter id added))

