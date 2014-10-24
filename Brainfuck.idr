module Brainfuck


data Ins : Type where 
    MoveF : Ins
    MoveB : Ins
    Increment : Ins
    Decrement : Ins
    Print : Ins
    Read : Ins
    LLoop : Ins
    RLoop : Ins
   

parseBrainfuck : List Char -> List Ins
parseBrainfuck  = map f  where 
        f : Char -> Ins
        f '>' = MoveF
        f '<' = MoveB
        f '+' = Increment
        f '-' = Decrement
        f '.' = Print
        f ',' = Read
        f '[' = LLoop
        f ']' = RLoop

data Tape : Type -> Type  where
  T : List a -> a -> List a -> Tape a



