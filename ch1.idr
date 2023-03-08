import Data.Vect
-- transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)

-- allLengths : List String -> List Nat
-- allLengths [] = []
-- allLengths (word :: words) = length word :: allLengths words

xor : Bool -> Bool -> Bool
xor False y =  y
xor True y =  not y

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not (isEven k)


allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs


insert : Ord elem => (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x (y :: xs) = case x < y of
                          False => y :: insert x xs
                          True => x :: y :: xs

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in
                    insert x xsSorted


my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = my_reverse xs ++ [x]

my_map : (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect len elem)) -> Vect n (Vect (S len) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys
-- transposeHelper : (x : Vect n elem) ->
--                   (xsTrans : Vect n (Vect k elem)) ->
--                   Vect n (Vect (S k) elem)
-- transposeHelper [] [] = []
-- transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                            zipWith (::) x xsTrans

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = let xsAdded = addMatrix xs ys in 
                                    zipWith (+) x y :: xsAdded
                                    
-- multMatrix : Num numType => Vect n (Vect m numType) -> Vect m (Vect p numType) -> Vect n (Vect p numType)
-- multMatrix [] [] = []
-- -- multMatrix (x :: xs) [] = ?multMatrix_rhs_5 :: multMatrix xs []
-- -- multMatrix [] (x :: ys) = ?multMatrix_rhs_1
-- multMatrix (y :: xs) ys = let ysTrans = transposeMat ys in
--                               ?mult

my_length2 : Vect n elem -> Nat
my_length2 {n} xs = n