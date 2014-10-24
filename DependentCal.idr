module DependentCal

data Expr : Nat -> Type where
  Const : ( n : Nat ) -> Expr n
  Add : Expr m -> Expr n -> Expr ( m + n )
  Sub : Expr m -> Expr n -> Expr ( m - n )
  Mul : Expr m -> Expr n -> Expr ( m * n )
  Div : Expr m -> Expr n -> Expr ( divNat m n )



exone  : Expr 8
exone = Add ( Const 4 ) ( Const 4 )

add :  ( m : Nat ) -> ( n : Nat ) -> Nat
add m n  = m + n

extwo : Nat
extwo = add 3 3 


