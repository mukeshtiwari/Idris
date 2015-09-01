module MonadicParsing

{-
data Parser a = P (List Char -> List (a, List Char))


item : Parser Char
item = P (\cs => case cs of
   [] => []
   (c :: cs) => [(c, cs)])




Parser : Type -> Type
Parser a = List Char -> List (a, List Char)

result : a -> Parser a
result v = \inp => [(v, inp)]

zero : Parser a
zero = \inp => []

item : Parser Char
item = \inp => case inp of
   [] => []
   (c :: cs) => [(c, cs)]

doParse : Parser a -> List Char -> List (a, List Char)
doParse f xs = f xs

seq : Parser a -> Parser b -> Parser (a, b)
seq p q = \inp => [((u, v), inp'') | (u, inp') <- p inp,
                                     (v, inp'') <- q inp]
bind : Parser a -> (a -> Parser b) -> Parser b
bind p f = \inp => concat [f v inp' | (v, inp') <- p inp]

sat : (Char -> Bool) -> Parser Char
sat p = bind item (\x =>
          if p x then result x else zero)

char : Char -> Parser Char
char c = sat (\y => y == c)

digit : Parser Char
digit = sat (\x => '0' <= x && x <= '9')

lower : Parser Char
lower = sat (\x => 'a' <= x && x <= 'z')

upper : Parser Char
upper = sat (\x => 'A' <= x && x <= 'Z')

plus : Parser a -> Parser a -> Parser a
plus p q = \inp => (p inp ++ q inp)

letter : Parser Char
letter = plus lower upper

alphanum : Parser Char
alphanum = plus letter digit

-}

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
    (\inp => [ (u, out) | (x, rest) <- parse f inp, (u, out) <- parse (g x) rest])

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
