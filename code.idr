
%default total

data Digit = I | V | X | L | C | D | M

value : Digit -> Int
value I = 1
value V = 5 
value X = 10
value L = 50
value C = 100
value D = 500
value M = 1000

limit : Digit -> Int
limit I = 5
limit V = 10
limit X = 50
limit L = 100
limit C = 500
limit D = 1000
limit M = 5000

data Numeral : List Digit -> Int -> Type where
 SimpleNumeral : (d : Digit) -> Numeral [d] (value d)
 ComplexNumeral : (d : Digit) -> (n : Numeral ds v) -> True = (limit d) > (value d + v) -> Numeral (d :: ds) (value d + v)

numeralToDigits : Numeral ds v -> List Digit
numeralToDigits (SimpleNumeral d) = [d]
numeralToDigits (ComplexNumeral d n p) = d :: (numeralToDigits n)

numeralToInt : Numeral ds v -> Int
numeralToInt (SimpleNumeral d) = value d
numeralToInt (ComplexNumeral d n p) = value d + (numeralToInt n)

numeralToDigitsAndProof : Numeral ds v -> (ds' : List Digit ** ds = ds')
numeralToDigitsAndProof (SimpleNumeral d) = ([d] ** Refl)
numeralToDigitsAndProof (ComplexNumeral d n p) with (numeralToDigitsAndProof n)
 | (ds ** q) = (d :: ds ** rewrite q in Refl)

numeralToIntAndProof : Numeral ds v -> (v' : Int ** v = v')
numeralToIntAndProof (SimpleNumeral d) = (value d ** Refl)
numeralToIntAndProof (ComplexNumeral d n p) with (numeralToIntAndProof n)
 | (v ** q) = (value d + v ** rewrite q in Refl)

numeralFromDigits : (ds : List Digit) -> Maybe (v : Int ** Numeral ds v)
numeralFromDigits [] = Nothing
numeralFromDigits (d :: []) = Just (value d ** SimpleNumeral d)
numeralFromDigits (d :: ds) with (numeralFromDigits ds)
 | Nothing = Nothing
 | Just (v ** n) with (limit d > value d + v) proof p
    | True = Just (value d + v ** ComplexNumeral d n p)
    | False = Nothing 

numeralFromInt : (v : Int) -> Maybe (ds : List Digit ** Numeral ds v)
numeralFromInt v = numeralFromInt' [M, D, C, L, X, V, I] v where
 plusMinusIdentity : (a, b : Int) -> b = a + (b - a)
 plusMinusIdentity a b = believe_me $ Refl {A=Int} {x=b}
 numeralFromInt' : List Digit -> (w : Int) -> Maybe (es : List Digit ** Numeral es w)
 numeralFromInt' [] w = Nothing
 numeralFromInt' (c :: cs) w with (decEq w (value c))
  | Yes p = rewrite p in Just ([c] ** SimpleNumeral c)
  | No contra with (limit c > value c + (w - value c)) proof q
     | False = Nothing
     | True with (w < value c)
        | True = numeralFromInt' cs w
        | False with (assert_total $ numeralFromInt' (c :: cs) (w - value c))
           | Nothing = Nothing
           | Just (es ** n) = rewrite plusMinusIdentity (value c) w in Just (c :: es ** ComplexNumeral c n q)

digitToChar : Digit -> Char
digitToChar I = 'I'
digitToChar V = 'V'
digitToChar X = 'X'
digitToChar L = 'L'
digitToChar C = 'C'
digitToChar D = 'D'
digitToChar M = 'M'

test : (v : Int) -> Maybe String
test v = do
 (ds ** n) <- numeralFromInt v
 pure $ pack $ map digitToChar $ numeralToDigits n
 
uniqueInt : (n : Numeral ds v) -> (m : Numeral ds w) -> v = w
uniqueInt (SimpleNumeral d) (SimpleNumeral d) = Refl
uniqueInt (ComplexNumeral d n p) (ComplexNumeral d m q) with (uniqueInt n m)
 | r = rewrite r in Refl 

contradiction : (False = x) -> (True = x) -> Void
contradiction Refl Refl impossible

numeralFromDigitsWithProof : (ds : List Digit) -> Either ((v : Int) -> Numeral ds v -> Void) (v : Int ** Numeral ds v)
numeralFromDigitsWithProof [] = Left emptyNumeral where
 emptyNumeral v n impossible
numeralFromDigitsWithProof (d :: []) = Right (value d ** SimpleNumeral d)
numeralFromDigitsWithProof (e :: d :: ds) with (numeralFromDigitsWithProof (d :: ds))
 | Left contra = Left (impossibleNumeral e) where
    impossibleNumeral e (value e + v) (ComplexNumeral e n p) = contra v n
 | Right (v ** n) with (limit e > value e + v) proof p
    | True = Right (value e + v ** ComplexNumeral e n p)
    | False = Left (invalidNumeral e n p) where
       invalidNumeral e n p (value e + v) (ComplexNumeral e m q) = contradiction p (rewrite uniqueInt n m in q)

positiveValue : (d : Digit) -> True = value d > 0
positiveValue I = Refl
positiveValue V = Refl
positiveValue X = Refl
positiveValue L = Refl
positiveValue C = Refl
positiveValue D = Refl
positiveValue M = Refl

positiveLemma : {a, b : Int} -> True = a > 0 -> True = b > 0 -> True = (a + b) > 0
positiveLemma p q = believe_me $ Refl {x=True}

positiveInt : Numeral ds v -> True = v > 0
positiveInt (SimpleNumeral d) = rewrite positiveValue d in Refl
positiveInt (ComplexNumeral d n p) with (positiveInt n)
 | q = rewrite positiveLemma (positiveValue d) q in Refl

boundValue : (d : Digit) -> True = 5000 > value d
boundValue I = Refl
boundValue V = Refl
boundValue X = Refl
boundValue L = Refl
boundValue C = Refl
boundValue D = Refl
boundValue M = Refl

boundLemma : {a, b, c : Int} -> False = a < b -> True = b > c -> True = a > c
boundLemma p q = believe_me $ Refl {x=True}

boundLimit : (d : Digit) -> False = 5000 < (limit d)
boundLimit I = Refl
boundLimit V = Refl
boundLimit X = Refl
boundLimit L = Refl
boundLimit C = Refl
boundLimit D = Refl
boundLimit M = Refl

boundInt : Numeral ds v -> True = 5000 > v
boundInt (SimpleNumeral d) = boundValue d
boundInt (ComplexNumeral d n p) = boundLemma (boundLimit d) p

numeralsCount : Int
numeralsCount = numeralsCount' [I, V, X, L, C, D, M] where
 numeralsCount' digits = foldl (+) 0 $ map count $ map (\d => (_ ** _ ** SimpleNumeral d)) digits where
  count : (ds : List Digit ** v : Int ** Numeral ds v) -> Int
  count (ds ** v ** n) = foldl (+) 1 $ map try digits where
   try d with (limit d > value d + v) proof p
    | False = 0
    | True = assert_total $ count (_ ** _ ** ComplexNumeral d n p)

numeralsExist : Int -> Bool
numeralsExist 0 = True
numeralsExist i with (numeralFromInt i)
 | Nothing = False
 | Just n = assert_total $ numeralsExist (i - 1)

main : IO ()
main = let count = numeralsCount in do
 putStrLn $ "there are " ++ (show count) ++ " numerals"
 if numeralsExist count
  then putStrLn "and all numerals exist with regards to conversion"
  else putStrLn "some numerals are missing with regards to conversion"

uniqueDigits : (n : Numeral ds v) -> (m : Numeral es v) -> ds = es
uniqueDigits {ds} n m = believe_me $ Refl {x=ds}

