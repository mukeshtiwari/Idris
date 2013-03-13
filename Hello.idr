module Main

infixr 10 ::
infixr 5 ++

data Nat = O | S Nat
data Bool = False | True
data List a = Nil | ( :: ) a  ( List a )

plus : Nat -> Nat -> Nat
plus O y = y
plus ( S n ) y = S ( plus n y )

mult : Nat -> Nat -> Nat
mult O y = O
mult ( S n ) y = plus y ( mult n y )


data Vect : Type -> Nat -> Type where
    Null : Vect a O
    Con : a -> Vect a n -> Vect a ( S n )

( ++ ) : { A : Type } -> Vect A n -> Vect A m -> Vect A ( plus n m )
( ++ ) Null ys = ys
( ++ ) ( Con x xs ) ys = Con x (   xs ++  ys )


reverse : List a -> List a
reverse xs = reverseAcc [] xs where
      reverseAcc : List a -> List a -> List a
      reverseAcc acc [] = acc
      reverseAcc acc (  ( :: ) y ys ) =  reverseAcc (  ( :: ) y acc ) ys

foldl : ( a -> b -> a ) -> a -> List b -> a
foldl f z [] = z
foldl f z ( ( :: ) x xs ) = foldl f ( f z x ) xs

foldr : ( a -> b -> b ) -> b -> List a -> b
foldr f z [] = z
foldr f z ( ( :: ) x xs ) = f x ( foldr f z xs )

even : Nat -> Bool
even O = True
even ( S n ) = odd n where
    odd O = False
    odd ( S n ) = even n

{-
main : IO ()
main = putStrLn "Hello dependent type world!"
-}
