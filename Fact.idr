module Fact



main : IO ()
main = putStrLn "Hello World" 



vApp : { a , b : Type } -> { n : Nat } -> Vect n ( a -> b )  -> Vect n a  -> Vect n b
vApp [] [] = []
vApp ( f :: fs )  ( a :: as ) = f a :: vApp fs as


plus_nO : ( n : Nat ) -> n + Z = n
plus_nO Z = refl
plus_nO ( S k ) = let ih = plus_nO k in ?plus_Scase


data Parity : Nat -> Type where
  even : { n : Nat } -> Parity ( n + n )
  odd : { n : Nat } -> Parity (  S ( n + n ) )

parity : ( n : Nat ) -> Parity n
parity Z = even { n = Z }
parity ( S Z ) = odd { n = Z } 
parity ( S ( S k ) ) with ( parity k ) 
     parity ( S ( S ( j + j ) ) )       | even ?= even { n = S j }
     parity ( S ( S ( S ( j + j ) ) ) ) | odd  ?= odd  { n = S j } 


data Expr =   Val Int
          | Var String
          | Add Expr Expr

data Ty = TyInt 
        | TyBool
        | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyBool = Bool
interpTy ( TyFun s t ) = interpTy s -> interpTy t

using ( n : Nat, G : Vect n Ty )
  data Env : Vect n Ty -> Type where
    Nil : Env Nil
    ( :: ) : interpTy a -> Env G -> Env ( a :: G )

  data HasType :  ( i : Fin n ) -> Vect n Ty -> Ty -> Type where 
      stop : HasType fO ( t :: G ) t 
      pop : HasType k G t -> HasType ( fS k ) ( u :: G ) t

ctxt : Vect ( S ( S Z ) ) Ty
ctxt = [ TyInt , TyBool ]

env : Env ctxt
env = [ 42 , True ]

isBool : HasType ( fS fO ) ctxt TyBool
isBool = pop stop




---------- Proofs ----------

Fact.plus_Scase = proof
  compute
  intros
  rewrite ih
  trivial


Fact.parity_lemma_1 = proof {
  compute;
  intros;
  rewrite sym ( plusSuccRightSucc j j );
  trivial;
}

Fact.parity_lemma_2 = proof {
  compute;
  intros;
  rewrite sym ( plusSuccRightSucc j j );
  trivial;
}


