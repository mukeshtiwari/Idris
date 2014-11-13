module Crypto.Des

data Bin = Zero | One

xorBin : Bin -> Bin -> Bin
xorBin Zero Zero = Zero
xorBin One One   = Zero
xorBin _ _       = One


initialPerm : Vect 64 Nat 
initialPerm = [57, 49, 41, 33, 25, 17,  9, 1, 59, 51, 43, 35, 27, 19, 11, 3,
                    61, 53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7,
                    56, 48, 40, 32, 24, 16,  8, 0, 58, 50, 42, 34, 26, 18, 10, 2,
                    60, 52, 44, 36, 28, 20, 12, 4, 62, 54, 46, 38, 30, 22, 14, 6]


finalPerm : Vect 64 Nat
finalPerm = [39, 7, 47, 15, 55, 23, 63, 31, 38, 6, 46, 14, 54, 22, 62, 30,
             37, 5, 45, 13, 53, 21, 61, 29, 36, 4, 44, 12, 52, 20, 60, 28,
             35, 3, 43, 11, 51, 19, 59, 27, 34, 2, 42, 10, 50, 18, 58, 26,
             33, 1, 41,  9, 49, 17, 57, 25, 32, 0, 40 , 8, 48, 16, 56, 24]


computePermutation : ( input : Vect 64 Bin )  -> ( perm : Vect 64 Nat ) ->  Vect 64 Bin
computePermutation input perm = 
 let
   MkSigma ( cast { from = Integer } { to = Prelude.Nat.Nat } 64 )  ys = 
     catMaybes .  map ( \i => natToFin i 64 ) $ perm
 in  map ( \i =>  Prelude.Vect.index i input ) ys


firstStep : Vect 64 Bin -> ( Vect 32 Bin , Vect 32 Bin )
firstStep  = splitAt 32

expansionPerm : Vect 48 Nat
expansionPerm = [31,  0,  1,  2,  3,  4,  3,  4,  5,  6,  7,  8,
                 7,  8,  9, 10, 11, 12, 11, 12, 13, 14, 15, 16,
                15, 16, 17, 18, 19, 20, 19, 20, 21, 22, 23, 24,
                23, 24, 25, 26, 27, 28, 27, 28, 29, 30, 31,  0]


expandRightInput : ( input : Vect 32 Bin ) -> ( perm : Vect 48 Nat ) -> Vect 48 Bin
expandRightInput input perm = 
  let
     MkSigma ( cast { from = Integer } { to = Prelude.Nat.Nat } 48 ) ys = 
       catMaybes .  map ( \i => natToFin i 32 ) $ perm
  in map ( \i =>  Prelude.Vect.index i input ) ys



roundXor : ( input : Vect n Bin ) -> ( key : Vect n Bin ) -> Vect n Bin
roundXor input key = zipWith xorBin input key


inputToSB : { n : Nat } -> Vect n Bin -> Sigma Nat ( \p => Vect p ( Vect 6 Bin ))
inputToSB { n = Z } _  = MkSigma 0 Nil
inputToSB { n = ( S ( S ( S ( S ( S ( S n ) ) ) ) ) ) } ( a :: b :: c :: d :: e :: f :: rest ) with ( inputToSB { n } rest )
  | MkSigma 0 rest' = MkSigma 1 ( [ a , b , c , d , e , f ] :: rest' )
  | MkSigma k rest' = MkSigma ( S k ) ( [ a , b , c , d , e , f ] :: rest' )


inputToSBox : Vect 48 Bin -> Sigma Nat ( \p => Vect p ( Vect 6 Bin ) )
inputToSBox = inputToSB

bintoNat : Bin -> Nat
bintoNat Zero = Z
bintoNat One  = S Z


rowCol : Vect 6 Bin -> ( Nat , Nat )
rowCol xs =
  let
     [ a , b , c , d , e , f ] = map bintoNat xs
  in ( 2 * a + f , 8 * b + 4 * c + 2 * d + e )


nattoBin : Nat -> Sigma Nat ( \p => Vect p Bin )
nattoBin Z = MkSigma 1 [ Zero ]
nattoBin ( S Z ) = MkSigma 1 [ One ]
nattoBin n with ( modNat n 2 , nattoBin ( divNat n 2) )
  | ( Z   , MkSigma k rest ) = MkSigma ( k + 1 ) ( rest  ++ [ Zero ])
  | ( S Z , MkSigma k rest ) = MkSigma ( k + 1 ) ( rest  ++ [ One  ])



outfromSBox : Vect 6 Bin -> ( sbox : Vect 4 ( Vect 16 Nat ) ) -> Vect 4 Bin
outfromSBox xs sbox = 
  let 
     ( row , col ) = rowCol xs
     ( Just row' , Just col' ) = ( natToFin row 4 , natToFin col 16 )
     MkSigma ( S ( S ( S ( S Z ) ) ) )  ys 
                       =  nattoBin ( index col' ( index row' sbox ) )
  in ys


sBoxOne : Vect 4 ( Vect 16 Nat )
sBoxOne = [[14,  4, 13,  1,  2, 15, 11,  8,  3, 10,  6, 12,  5,  9,  0,  7],
           [ 0, 15,  7,  4, 14,  2, 13,  1, 10,  6, 12, 11,  9,  5,  3,  8],
           [ 4,  1, 14,  8, 13,  6,  2, 11, 15, 12,  9,  7,  3, 10,  5,  0],
           [15, 12,  8,  2,  4,  9,  1,  7,  5, 11,  3, 14, 10,  0,  6, 13]]

sBoxTwo : Vect 4 ( Vect 16 Nat )
sBoxTwo = [[15,  1,  8, 14,  6, 11,  3,  4,  9,  7,  2, 13, 12,  0,  5, 10],
            [3,  13,  4,  7, 15,  2,  8, 14, 12,  0,  1, 10,  6,  9,  11, 5],
            [0,  14,  7, 11, 10,  4, 13,  1,  5,  8, 12,  6,  9,  3,  2, 15],
            [13,  8, 10,  1,  3, 15,  4,  2, 11,  6,  7, 12,  0,  5,  14, 9]]


sBoxThree : Vect 4 ( Vect 16 Nat )
sBoxThree = [[10,  0,  9, 14 , 6,  3, 15,  5,  1, 13, 12,  7, 11,  4,  2,  8],
            [13,  7,  0,  9,  3,  4,  6, 10,  2,  8,  5, 14, 12, 11, 15,  1],
            [13,  6,  4,  9,  8, 15,  3,  0, 11,  1,  2, 12,  5, 10, 14,  7],
            [1,  10, 13,  0,  6,  9,  8,  7,  4, 15, 14,  3, 11,  5,  2, 12]]


sBoxFour : Vect 4 ( Vect 16 Nat )
sBoxFour = [[7,  13, 14,  3,  0,  6,  9, 10,  1,  2,  8,  5, 11, 12,  4, 15],
            [13,  8, 11,  5,  6, 15,  0,  3,  4,  7,  2, 12,  1, 10, 14,  9],
            [10,  6,  9,  0, 12, 11,  7, 13, 15,  1,  3, 14,  5,  2,  8,  4],
            [3,  15,  0,  6, 10,  1, 13,  8,  9,  4,  5, 11, 12,  7,  2, 14]]


sBoxFive : Vect 4 ( Vect 16 Nat )
sBoxFive = [[2,  12,  4,  1,  7, 10, 11,  6,  8,  5,  3, 15, 13,  0, 14,  9],
            [14, 11,  2, 12,  4,  7, 13,  1,  5,  0, 15, 10,  3,  9,  8,  6],
            [4,   2,  1, 11, 10, 13,  7,  8, 15,  9, 12,  5,  6,  3,  0, 14],
            [11,  8, 12,  7,  1, 14,  2, 13,  6, 15,  0,  9, 10,  4,  5,  3]]


sBoxSix : Vect 4 ( Vect 16 Nat )
sBoxSix = [[12,  1, 10, 15,  9,  2,  6,  8,  0, 13,  3,  4, 14,  7,  5, 11],
           [10, 15,  4,  2,  7, 12,  9,  5,  6,  1, 13, 14,  0, 11,  3,  8],
           [9,  14, 15,  5,  2,  8, 12,  3,  7,  0,  4, 10,  1, 13, 11,  6],
           [4,  3,   2, 12,  9,  5, 15, 10, 11, 14,  1,  7,  6,  0,  8, 13]]

sBoxSeven : Vect 4 ( Vect 16 Nat )
sBoxSeven = [[4,  11,  2, 14, 15,  0,  8, 13,  3, 12,  9,  7,  5, 10,  6,  1],
            [13, 0,  11,  7,  4,  9,  1, 10, 14,  3,  5, 12,  2, 15,  8,  6],
            [1,  4,  11, 13, 12,  3,  7, 14, 10, 15,  6,  8,  0,  5,  9,  2],
            [6,  11, 13,  8,  1,  4, 10,  7,  9,  5,  0, 15, 14,  2,  3, 12]]


sBoxEight : Vect 4 ( Vect 16 Nat )
sBoxEight = [[13,  2,  8,  4,  6, 15, 11,  1, 10,  9,  3, 14,  5,  0, 12,  7],
            [1,  15, 13,  8, 10,  3,  7,  4, 12,  5,  6, 11,  0, 14,  9,  2],
            [7,  11,  4,  1,  9, 12, 14,  2,  0,  6, 10, 13, 15,  3,  5,  8],
            [2,   1, 14,  7,  4, 10,  8, 13, 15, 12,  9,  0,  3,  5,  6, 11]]

computesDBoxPermutation : ( input : Vect 32 Bin )  -> ( dperm : Vect 32 Nat ) 
                                                   ->  Vect 32 Bin
computesDBoxPermutation input dperm =
   let
     MkSigma ( cast { from = Integer } { to = Prelude.Nat.Nat } 32 )  ys =
       catMaybes .  map ( \i => natToFin i 32 ) $ dperm
   in  map ( \i =>  Prelude.Vect.index i input ) ys

sDBox : Vect 32 Nat
sDBox = [15, 6, 19, 20, 28, 11, 27, 16,  0, 14, 22, 25,  4, 17, 30,  9,
          1, 7, 23, 13, 31, 26,  2,  8, 18, 12, 29,  5, 21, 10,  3, 24]


{- Start encryption -}

oneRoundEnc : ( Vect 32 Bin , Vect 32 Bin ) -> ( roundKey : Vect 48 Bin ) 
                                        ->  ( Vect 32 Bin , Vect 32 Bin )
oneRoundEnc ( xs , ys ) roundKey = 
  let 
      MkSigma ( cast { from = Integer } { to = Prelude.Nat.Nat } 8 ) xs'  
            = inputToSBox ( roundXor 
                          ( expandRightInput ys expansionPerm ) roundKey )
      xs''  = roundXor ( computesDBoxPermutation 
                       ( concat ( zipWith outfromSBox xs'  
                                [ sBoxOne , sBoxTwo , sBoxThree, sBoxFour , 
                                  sBoxFive , sBoxSix , sBoxSeven , sBoxEight ] ) ) 
                                  sDBox ) xs
   
  in ( ys , xs'' )
  













