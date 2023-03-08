AdderType : (numArgs : Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next : numType) -> AdderType k numType

adder : Num numType => 
    (numArgs : Nat) -> numType -> AdderType numArgs numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)
