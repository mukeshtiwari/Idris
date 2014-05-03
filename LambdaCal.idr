module LambdaCal 
import Data.Bits

infix 5 \\


deleteBy : (a -> a -> Bool) -> a -> List a -> List a
deleteBy _  _ []      = []
deleteBy eq x (y::ys) = if x `eq` y then ys else y :: deleteBy eq x ys

delete : (Eq a) => a -> List a -> List a
delete = deleteBy (==)

(\\) : (Eq a) => List a -> List a -> List a
(\\) =  foldl (flip delete)

unionBy : (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

union : (Eq a) => List a -> List a -> List a
union = unionBy (==)


data Expr : Type where
  Var : String -> Expr
  App : Expr -> Expr -> Expr
  Lam : String -> Expr -> Expr

freeVar : Expr -> List String
freeVar ( Var x ) = [ x ]
freeVar ( App f g ) = union  ( freeVar f )  ( freeVar g )
freeVar ( Lam v e ) = ( freeVar e ) \\ [ v ]


||| The result of substituting N for the free occurence of 
||| x in M. M[x := N ]
subst : Expr -> String -> Expr -> Expr 
subst ( Var v ) x n = if x == v then n else ( Var v )
subst ( App f g ) x n = App ( subst f x n ) ( subst f x n )
subst ( Lam y f ) x n = Lam y ( subst f x n )

I : Expr
I = Lam "x" ( Var "x" )
K : Expr
K = Lam "x" ( Lam "y" ( Var "x" ) )
Ks : Expr
Ks = Lam "x" ( Lam "y" ( Var "y" ) )
Sc : Expr
Sc = Lam "x" ( Lam "y" ( Lam "z" ( App ( Var "x" ) ( App ( Var "z" ) ( App ( Var "y" ) ( Var "z" ) ) ) ) ) )
Y : Expr
Y = App ( Lam "f" ( Lam "x" ( App ( Var "f" ) ( App ( Var "x" ) ( Var "x" ) ) ) ) ) ( ( Lam "x" ( App ( Var "f" ) ( App ( Var "x" ) ( Var "x" ) ) ) ) )
zero : Expr
zero  = Lam "s" $ Lam "z" ( Var "z" )
one : Expr
one   = Lam "s" $ Lam "z" $ App ( Var "s" ) ( Var "z" )
app : Expr -> Expr -> Expr -> Expr
app f x y = App ( App f x ) y 
plus : Expr
plus  = Lam "m" ( Lam "n" ( Lam "s" ( Lam "z" ( app ( Var "m" ) ( Var "s" ) ( app ( Var "n" ) ( Var "s" ) ( Var "z" ) ) ) ) ) )


