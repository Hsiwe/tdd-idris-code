-- import Data.List

data Last : List a -> a -> Type where
    LastOne : Last [value] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

notLastInEmpty : Last [] value -> Void
notLastInEmpty LastOne impossible
notLastInEmpty (LastCons _) impossible

-- notLastInMany : (contra : Last xs value -> Void) -> Last (x :: xs) value -> Void
-- notLastInMany contra xs = contra ?notLastInMany_rhs_3
-- notLastInMany contra (LastCons prf) = contra prf

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast _ (LastCons LastOne) impossible
notLast _ (LastCons (LastCons _)) impossible

notLastConstTailNotLast : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notLastConstTailNotLast contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notLastInEmpty
isLast (x :: []) value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No contra) => No (notLast contra)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of
                                     (Yes prf) => Yes (LastCons prf)
                                     (No contra) => No (notLastConstTailNotLast contra)
