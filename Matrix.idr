module Main

transposeMat : { a : Type } -> { m : Nat } -> { n : Nat } -> Vect m ( Vect n a ) -> Vect n ( Vect m a )
transposeMat { m } { n = Z   }  _  = []
transposeMat { m } { n = S n }  xs = map head xs :: transposeMat ( map tail xs )

vectorMult : ( Num a ) => { m : Nat } -> Vect m a -> Vect m a -> Vect m a
vectorMult { m }  xs ys = zipWith ( * ) xs ys

matMult : ( Num a ) => Vect m ( Vect n a ) -> Vect n ( Vect p a ) -> Vect m ( Vect p a ) 

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


