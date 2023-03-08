import Data.Vect

data Format = Number Format
            | Str Format
            | Ch Format
            | Doub Format
            | Lit String Format
            | End

PrintfType : Format -> Type 
PrintfType (Number x) = (i : Int) -> PrintfType x
PrintfType (Str x) = (str : String) -> PrintfType x
PrintfType (Ch x) = (ch : Char) -> PrintfType x
PrintfType (Doub x) = (doub : Double) -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number x) acc = \i => printfFmt x (acc ++ show i)
printfFmt (Str x) acc = \str => printfFmt x (acc ++ str)
printfFmt (Lit x y) acc = printfFmt y (acc ++ x)
printfFmt (Doub doub) acc = \doub1 => printfFmt doub (acc ++ show doub1)
printfFmt (Ch ch) acc = \ch1 => printfFmt ch (pack (unpack acc ++ [ch1]))
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Ch (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Doub (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""


Matrix : Nat -> Nat -> Type
Matrix k j = Vect k (Vect j Double)

TupleVect : Nat -> Type -> Type
TupleVect Z x = ()
TupleVect (S k) x = (x, TupleVect k x)

test : TupleVect 4 Nat
test = (0, 0, 0, 0, ())
