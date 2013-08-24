module Missionaries 

data Side : Type where 
    C : Nat -> Nat -> Side

data Loc : Type where
    L : Loc
    R : Loc

data State : Type where 
    P :  Side ->  Side ->  Loc  -> State


initialState : State
initialState = P ( C 3 3 )  ( C 0 0 )  L

finalState : State
finalState = P  ( C 0  0  )  ( C 3 3 )  R

instance Eq a => Eq State where
    (==) ( P ( C m1 n1 ) ( C m2 n2 ) _ ) ( P ( C m3 n3 ) ( C m4 n4 ) _ ) = m1 == m3 && n1 == n3 && m2 == m4 &&  n2 == n4 

instance Ord a => Ord State where
    compare ( P ( C m1 n1 ) ( C m2 n2 ) _ ) ( P ( C m3 n3 ) ( C m4 n4 ) _ ) = EQ
                                                                                  

move :  State  -> List State
move (  P ( C  ml cl ) ( C mr cr ) L ) =
          [ P ( C ( ml - 2 ) cl ) ( C ( mr + 2 ) cr ) R
          , P ( C ( ml - 1 ) cl ) ( C ( mr + 1 ) cr ) R
          , P ( C ( ml - 1 ) ( cl - 1 ) ) ( C ( mr + 1 ) ( cr + 1 ) ) R
          , P ( C ml ( cl - 2 ) ) ( C mr ( cr + 2 ) ) R
          , P ( C ml ( cl - 1 ) ) ( C mr ( cr + 1 ) ) R       
          ] 
move (  P ( C ml cl ) ( C mr cr ) R ) =
          [ P ( C ( ml + 2 ) cl ) ( C ( mr - 2 ) cr ) L
          , P ( C ( ml + 1 ) cl ) ( C ( mr - 1 ) cr ) L
          , P ( C ( ml + 1 ) ( cl + 1 ) ) ( C ( mr - 1 ) ( cr - 1 ) ) L
          , P ( C ml ( cl + 2 ) ) ( C mr ( cr - 2 ) ) L
          , P ( C ml ( cl + 1 ) ) ( C mr ( cr - 1 ) ) L       
          ]  


isLegal : State -> Bool
isLegal  ( P ( C ml cl ) ( C mr cr ) y ) = case ( ml == 0 , mr == 0 ) of 
                                              ( True , _ ) => mr >= cr  && cr >= 0 
                                              ( _ , True ) => ml >= cl  && cl >= 0
                                              ( _ , _ ) => ml >= cl && mr >= cr && cl >= 0 && cr >= 0



path : ( Eq State ) => List State -> List State -> List State
path Nil vis = reverse vis
path ( x :: xs ) vis = case ( x == finalState, ( elem x vis ) ) of 
                            ( True, _ )  => reverse ( x :: vis ) 
                            ( _, True )  => path xs vis
                            ( _, _ ) => path ( x :: xs ) ( ( filter  isLegal  ( move x ) ) ++ xs ) 
