module MonadicParsing

data Parser : Type -> Type where
  MkParser : (String -> List (a, String)) -> Parser a

parse : Parser a -> (String -> List (a, String))
parse (MkParser f) = f


instance Functor Parser where
  map f p = MkParser (\inp => [(f v, out) | (v, out) <- parse p inp])


instance Applicative Parser where
  pure v = MkParser (\inp => [(v, inp)])
  a <*> b = MkParser
    (\inp => [(f v, out) | (f, rest) <- parse a inp, (v, out) <- parse b rest])


instance Monad Parser where
  f >>= g = MkParser
    (\inp => [(u, out) | (x, rest) <- parse f inp, (u, out) <- parse (g x) rest])

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
alphanum =  sat isAlphaNum

char : Char -> Parser Char
char x = sat ( == x)

string : String -> Parser String
string x = string' (unpack x) where
       string' : List Char -> Parser String
       string' [] = return ""  -- MkParser (\inp => [("", inp)])
       string' (y :: ys) =
         char y >>= \_ =>  string' ys >>= \_ =>  return (pack (y :: ys))


mutual
  partial
  many : Parser a -> Parser (List a)
  many p = manyOne p <|> empty

  partial
  manyOne : Parser a -> Parser (List a)
  manyOne p = p >>= \v => many p >>= \vs => return (v :: vs)






{-
instance Applicative Parser where

    pure v = MkParser (\inp => [(v, inp)])
  a <*> b = MkParser (\inp =>
                         do
                           (f, rest) <- parse a inp
                           (v, out) <- parse b rest
                           pure (f v, out))



instance Applicative Parser where
  pure v = MkParser (\inp => [(v, inp)])
  a <$> b = MkParser (\inp =>
                     do (f, rest) <- parse a inp
                        (x, rest') <- parse b rest
                        pure((f x), rest'))


instance Monad Parser where
  m >>= f = MkParser (\s => [(x, y) | (u, v) <- parse m s, (x, y) <- parse (f u) v])
-}
