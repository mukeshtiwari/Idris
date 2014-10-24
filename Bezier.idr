module Bezier
 
Point : Nat -> Type -> Type
Point = Vect
 
line : ( Num a ) =>   Point d a -> Point d a -> a -> Point d a
line  p q t = zipWith interpolate p q where 
  interpolate a b = (1 - t)*a + t*b
       
-- bezier of just one point is fixed at that point,
-- and bezier of a list of points is just linear interpolation
-- between bezier of the initial part of the list
-- and bezier of the tail of the list:
bezier : ( Num a ) =>  Vect ( S n ) (Point d a) -> a -> Point d a
bezier (p :: Nil) t = p
bezier (p1 :: p2 :: ps) t =
  let points = (p1 :: p2 :: ps) in
      line (bezier (init points) t) (bezier (tail points) t) t
