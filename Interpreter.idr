module Interpreter 

data Ty = TyInt
        | TyBool
        | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt  = Int
interpTy TyBool = Bool
interpTy ( TyFun A T ) =  interpTy A -> interpTy T

using ( G : Vect n Ty )
  data HasType : ( i : Fin n ) -> Vect n Ty -> Ty -> Type where
    stop : HasType fZ ( t :: G ) t
    pop  : HasType k G t -> HasType ( fS k ) ( u :: G ) t


  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : ( x : Int ) -> Expr G TyInt
    Lam : Expr ( a :: G ) t -> Expr G ( TyFun a t )
    App : Expr G ( TyFun a t ) -> Expr G a -> Expr G t
    Op  : ( interpTy a -> interpTy b -> interpTy c ) -> Expr G a -> Expr G b -> Expr G c
    If  : Expr G TyBool -> Lazy ( Expr G a ) -> Lazy ( Expr G a ) ->  Expr G a


  data Env : Vect n Ty -> Type where
    Nil    : Env Nil
    ( :: ) : interpTy a -> Env G -> Env ( a :: G )

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop ( x :: xs )      = x
  lookup ( pop k ) ( x :: xs ) = lookup k xs

  interp : Env G -> Expr G t -> interpTy t
  interp env ( Var i     ) = lookup i env
  interp env ( Val x     ) = x
  interp env ( Lam sc    ) = \x => interp ( x :: env ) sc
  interp env ( App f s   ) = interp env f ( interp env s )
  interp env ( Op op x y ) = op ( interp env x ) ( interp env y )
  interp env ( If x  t e ) = if interp env x then interp env t 
                                             else interp env e

  add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  add = Lam (Lam (Op (+) (Var stop) (Var (pop stop))))

  fact : Expr G (TyFun TyInt TyInt)
  fact = Lam (If (Op (==) (Var stop) (Val 0))
                 (Val 1) (Op (*) (App fact (Op (-) (Var stop) (Val 1)))
                                 (Var stop)))
