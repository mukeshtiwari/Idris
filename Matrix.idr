module Main

private
transposeMat : { a : Type } -> { m : Nat } -> { n : Nat } -> Vect m ( Vect n a ) -> Vect n ( Vect m a )
transposeMat { m } { n = Z   }  _  = []
transposeMat { m } { n = S n }  xs = map head xs :: transposeMat ( map tail xs )

private
dotP : ( Num a ) => { m : Nat } -> Vect m a -> Vect m a ->  a
dotP { m }  xs ys = sum ( zipWith ( * ) xs ys )

private
matMult : ( Num a ) => Vect m ( Vect n a ) -> Vect p ( Vect n a ) -> Vect m ( Vect p a ) 
matMult { m = Z } _  _ = []
matMult { m =  S m } ( x :: xs ) ys = map ( dotP x ) ys :: matMult xs ys

public
matrixMult :  ( Num a ) => Vect m ( Vect n a ) -> Vect n ( Vect p a ) -> Vect m ( Vect p a )
matrixMult xs ys = matMult xs ( transposeMat ys )

plus_nO : ( n : Nat ) -> n + Z = n 
plus_nO Z = refl
plus_nO ( S k ) = let ih = plus_nO k in ?plus_Scase





---------- Proofs ----------

Main.plus_Scase = proof
  compute
  intros 
  rewrite ih
  rewrite ih
  trivial


