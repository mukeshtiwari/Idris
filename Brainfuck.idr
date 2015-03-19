module Main


data BrainfuckCommand : Type where
  GoRight : BrainfuckCommand
  GoLeft  : BrainfuckCommand
  Increment : BrainfuckCommand
  Decrement : BrainfuckCommand
  Print : BrainfuckCommand
  Read  : BrainfuckCommand
  Loop  : List BrainfuckCommand -> BrainfuckCommand
 

data Tape : Type where 
  RTape : (xs : Stream Int) -> (r : Int) -> (ys : Stream Int) -> Tape

emptyTape : Tape
emptyTape = RTape (repeat 0) 0 (repeat 0)

moveRight : Tape -> Tape
moveRight (RTape xs x (y :: ys)) = RTape (x :: xs) y ys

moveLeft : Tape -> Tape
moveLeft (RTape (x :: xs) y ys) = RTape xs x (y :: ys)

tapeState : Tape -> List BrainfuckCommand -> IO Tape
tapeState x [] = return x
tapeState (RTape xs x (y :: ys)) (GoRight :: zs) = 
  tapeState (RTape (x :: xs) y ys) zs
tapeState (RTape (x :: xs) y ys) (GoLeft :: zs)  = 
  tapeState (RTape xs x (y :: ys)) zs
tapeState (RTape xs r ys) (Increment :: zs) = 
  tapeState (RTape xs (r + 1) ys) zs
tapeState (RTape xs r ys) (Decrement :: zs) = 
  tapeState (RTape xs (r - 1) ys) zs
tapeState (RTape xs r ys) (Print :: zs) = 
  do
    putChar . chr $ r
    tapeState (RTape xs r ys) zs
tapeState (RTape xs r ys) (Read :: zs) =
  do
    c <- getChar
    tapeState (RTape xs (ord c) ys) zs
tapeState (RTape xs 0 ys) (Loop ins :: zs ) = 
  tapeState (RTape xs 0 ys) zs
tapeState (RTape xs r ys) (Loop ins :: zs) =
  do
    tps <- tapeState (RTape xs r ys) ins
    tapeState  tps (Loop ins :: zs) 


parseSource : List Char -> (List BrainfuckCommand, List Char)
parseSource [] = ([], [])
parseSource ('+' :: xs) = 
   let (comm, rest) = parseSource xs in (Increment :: comm, rest)
parseSource ('-' :: xs) = 
   let (comm, rest) = parseSource xs in (Decrement :: comm, rest)
parseSource ('>' :: xs) = 
   let (comm, rest) = parseSource xs in (GoRight:: comm, rest)
parseSource ('<' :: xs) = 
   let (comm, rest) = parseSource xs in (GoLeft :: comm, rest)
parseSource ('.' :: xs) = 
   let (comm, rest) = parseSource xs in (Print :: comm, rest)
parseSource (',' :: xs) = 
   let (comm, rest) = parseSource xs in (Read :: comm, rest)
parseSource ('[' :: xs) = 
   let (comm, rest) = parseSource xs 
       (comm', rest') = parseSource rest
   in (Loop comm :: comm', rest')
parseSource (']' :: xs) = ([], xs)
parseSource (_ :: xs) =  parseSource xs
  
  

parseInput : String -> List BrainfuckCommand
parseInput str = fst (parseSource (unpack str))

main : IO ()
main = do
   _ <- tapeState emptyTape (parseInput "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.")
   return ()
