data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Foldable Tree where
    foldr func acc Empty = acc
    foldr func acc (Node left y right) = let leftFold = foldr func acc left in
                                             rightFold = foldr func leftFold right in
                                             func e rightFold

totalLen : List String -> Nat
totalLen = foldr ((+) . length) 0
