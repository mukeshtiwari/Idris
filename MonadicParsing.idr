module Main
-- import Classes.Verified

%default total

data Parser : Type -> Type where
  MkParser : (String -> List (a, String)) -> Parser a

parse : Parser a -> (String -> List (a, String))
parse (MkParser f) = f


instance Functor Parser where
  map f p = MkParser (\inp => [(f v, out) | (v, out) <- parse p inp])

{-
instance VerifiedFunctor Parser where
  functorIdentity (MkParser f) = cong {f = MkParser} ?foo
  functorComposition p g = ?ys
-}

instance Applicative Parser where
  pure v = MkParser (\inp => [(v, inp)])
  a <*> b = MkParser
    (\inp => [(f v, out) | (f, rest) <- parse a inp, (v, out) <- parse b rest])

{-}
instance VerifiedApplicative Parser where
  applicativeMap p g = ?xs
  applicativeIdentity p = ?ys
  applicativeComposition p f g = ?zs
  applicativeHomomorphism p g = ?vs
  applicativeInterchange p g = ?ws
-}
{-
instance Monad Parser where
  f >>= g = MkParser
    (\inp => [(u, out) | (x, rest) <- parse f inp, (u, out) <- parse (g x) rest])
-}

instance Monad Parser where
  f >>= g = MkParser (\inp => concat [parse (g v) out | (v, out) <- parse f inp])



instance Alternative Parser where
  empty = MkParser (\inp => [])
  f <|> g = MkParser (\inp => case parse f inp of
                               [] => parse g inp
                               xs => xs)


item : Parser Char
item = MkParser
     (\cs => case unpack cs of
         [] => []
         (c :: cs) => [(c, pack cs)])


sat : (Char -> Bool) -> Parser Char
sat f = item >>= \x => if f x then return x else empty

digit : Parser Char
digit = sat isDigit

lower : Parser Char
lower = sat isLower

upper : Parser Char
upper = sat isUpper

letter : Parser Char
letter = sat isAlpha

alphanum : Parser Char
alphanum = sat isAlphaNum

char : Char -> Parser Char
char x = sat ( == x)

string : String -> Parser String
string x = string' (unpack x) where
       string' : List Char -> Parser String
       string' [] = return ""  -- MkParser (\inp => [("", inp)])
       string' (y :: ys) =
         char y *>  string' ys *> pure (pack (y :: ys))


mutual
  partial
  many : Parser a -> Parser (List a)
  many p = manyOne p <|> pure []

  partial
  manyOne : Parser a -> Parser (List a)
  manyOne p = p >>= \v => many p >>= \vs => return (v :: vs)

  partial
  identifier : Parser String
  identifier = (++) <$> (singleton <$> lower) <*> (pack <$> many alphanum)

  partial
  space : Parser ()
  space = many (sat isSpace) *> return ()

  partial
  token : Parser a -> Parser a
  token p = space *> p <* space

  partial
  sepByOne : Parser a -> Parser b -> Parser (List a)
  sepByOne p s = (::) <$> p <*> many (s *> p)


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

{-
emptyTape : Tape
emptyTape = RTape ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]) 0
                  ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
-}

-- some problem with streams
emptyTape : Tape
emptyTape = RTape (repeat 0) 0 (repeat 0)


partial
tapeState : Tape -> List BrainfuckCommand -> IO Tape
tapeState x Nil = return x
tapeState (RTape ys r (x :: y)) (GoRight :: xs) = tapeState (RTape (r :: ys) x y) xs
tapeState (RTape (x :: y) r zs) (GoLeft :: xs) = tapeState (RTape y x (r :: zs)) xs
tapeState (RTape ys r zs) (Increment :: xs) = tapeState (RTape ys (r + 1) zs) xs
tapeState (RTape ys r zs) (Decrement :: xs) = tapeState (RTape ys (r - 1) zs) xs
tapeState (RTape ys r zs) (Print :: xs) =
  (putChar . chr $ r) *> tapeState (RTape ys r zs) xs
tapeState (RTape ys r zs) (Read :: xs) =
  getChar >>= \c =>  tapeState (RTape ys (ord c) zs) xs
tapeState (RTape ys r zs) ((Loop ins) :: xs) =
  if r == 0 then tapeState (RTape ys r zs) xs
  else tapeState (RTape ys r zs) ins >>= \tape => tapeState tape (Loop ins :: xs)


partial
inst : Parser BrainfuckCommand
inst =  (char '+' *> pure Increment)
    <|> (char '-' *> pure Decrement)
    <|> (char '>' *> pure GoRight)
    <|> (char '<' *> pure GoLeft)
    <|> (char ',' *> pure Read)
    <|> (char '.' *> pure Print)
    <|> (char '[' *> Loop <$> many inst <* char ']')


partial
prog : Parser (List BrainfuckCommand)
prog = many inst

partial
parseInput : String -> Either String (List BrainfuckCommand)
parseInput str =
  case parse prog str of
    [(cmd, "")] => Right cmd
    _  => Left "parsing error"



partial
main : IO ()
main = do
  str <- fread stdin
  case parseInput str of
     Right cmd => tapeState emptyTape cmd *>   return ()
     Left str => return ()
