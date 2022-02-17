import Data.Char

-- Data type expressing part of data stream processing
-- eg. string

data Part a b = Part b a
    deriving Show

-- Matcher is a cannonical way of using it. Get input
-- type and return Maybe (Part a b)
type Matcher a b = a -> Maybe (Part a b)
type OptPart a b = Maybe(Part a b)
type MatcherT a b = Matcher a b -> Matcher a b


-- Operator for moving output from one Matcher to the other
-- creating list of subsequent results
(+>) :: OptPart a [b] -> Matcher a [b] -> OptPart a [b]
opt +> f = opt >>= \(Part m r) ->
                        (f r) >>= \(Part m' r') -> Just (Part (m++m') r')

-- The same, but with optional second part.
(?>) :: OptPart a [b] -> Matcher a [b] -> OptPart a [b]
opt ?> f = opt >>= \(Part m r) ->
                        case (f r) of
                            Just (Part m' r') -> Just (Part (m++m') r')
                            Nothing -> Just (Part m r)

-- Transform intermediate result.
($>) :: OptPart a b -> (b -> c) -> OptPart a c
opt $> f = opt >>= \(Part m r) -> Just (Part (f m) r)

-- Provide alternative for maybe
(>>|) :: Maybe a -> a -> a
Nothing >>| a = a
Just a >>| _ = a

-- Extract result from Maybe(Part)
finishM :: OptPart [a] b -> Maybe b
finishM opt = opt >>= \(Part m r) ->
                        case r of
                            [] -> Just m
                            _ -> Nothing

-- Create matcher for list, using function that decide
-- for one element if it should be put.
unitM :: (a -> Bool) -> Matcher [a] [[a]]
unitM f [] = Nothing
unitM f (x:xs) = case (f x) of
                    True -> Just (Part [[x]] xs)
                    False -> Nothing

-- Matcher transformers:
-- make matcher optional.
opt :: MatcherT a [b]
opt matcher inp = case (matcher inp) of
                    Nothing -> Just(Part [] inp)
                    x -> x

-- make matcher that repeats matching of given matcher
rept :: MatcherT a [b]
rept matcher inp = matcher inp ?> \r -> rept matcher r

-- optional repeat
rept' :: MatcherT a [b]
rept' m = opt $ rept m

-- merge elements of intermediate result
flat :: OptPart a [[b]] -> OptPart a [[b]]
flat x = x $> \v -> [foldl (++) [] v]

flatM :: MatcherT a [[b]]
flatM m = \x -> flat $ m x

-- create matcher that makes alternative of given matchers
alt :: [Matcher a b] -> Matcher a b
alt [] inp = Nothing
alt (m:mx) inp = case (m inp) of
                    Nothing -> alt mx inp
                    x -> x

-- create matcher that matches sequence of given matchers
mseq :: [Matcher a [b]] -> Matcher a [b]
mseq (m:mx) inp = foldl (+>) (m inp) mx

-- create matcher that inverts matcher (it will match only
-- one unit).

neg :: MatcherT [a] [[a]]
neg _ [] = Nothing
neg matcher inp = case (matcher inp) of
                    Nothing -> Just $ Part [take 1 inp] (drop 1 inp)
                    Just _ -> Nothing

-- transform matcher so that it does not change result
quietM :: MatcherT a [b]
quietM m inp = m inp >>= \(Part _ tail) -> Just (Part [] tail)

---------------------
-- String regex part:

type RegexUnit = Matcher [Char] [Matcher [Char] [[Char]]] 

-- Make matcher producing another matcher
matchConv sm dm = \x -> sm x $> \_ -> [dm]

stringM str = mseq $ map (\x -> unitM (== x)) str
isPosixAlpha c = isLetter c || isDigit c || c == '_'

anyM = unitM (\_ -> True)

-- Then we have basic syntax
charRgxSyntax = [ matchConv (unitM (== '.')) anyM,
                  matchConv (stringM "\\s") (unitM isSpace),
                  matchConv (stringM "\\d") (unitM isDigit),
                  matchConv (stringM "\\w") (unitM isPosixAlpha),
                  (\x -> mseq [unitM(== '\\'), anyM] x $> \[_,[c]] -> [unitM (== c)]),
                  \x -> anyM x $> \[c] -> [stringM c] ]

-- And on that basis we implement modifiers
modRgxSyntax :: Char -> MatcherT [Char] [[Char]] -> RegexUnit -> RegexUnit
modRgxSyntax c mod matcher =
    \inp -> case (matcher inp) of
                Just (Part step tail) -> unitM (== c) tail >>= \(Part _ t) ->
                    Just $ Part [mod $ mseq step] t
                Nothing -> Nothing

-- We want easy way to negate character
withMods :: [(Char, MatcherT [Char] [[Char]])] -> [RegexUnit] -> [RegexUnit]
withMods mods syntax =
    let modsFor x = map (\(c, f) -> modRgxSyntax c f x) mods ++ [x]
    in foldl (++) [] (map modsFor syntax)

charRgxWithNeg = withMods [('!', neg),
                           ('`', quietM)] charRgxSyntax
                 
-- We implement basic modifiers: *, + and ?
regexSyntax = withMods [('*', rept'),
                        ('+', rept),
                        ('?', opt)] charRgxWithNeg

-- We want also group code with parenthesis
-- only groups appear in result, they are treated as units
muteS :: RegexUnit -> RegexUnit
muteS syntax src = syntax src $> \matchers -> map quietM matchers

groupingSyntax =
    let lp = '('
        rp = ')'
        bodyM x = case (unitM(== rp) x) of
                    Just (Part _ t) -> Just (Part [] t)
                    Nothing -> (alt regexSyntax) x +> bodyM
        groupSyntax :: RegexUnit
        groupSyntax x = case (unitM(== lp) x) of
                            Just (Part _ t) ->
                                bodyM t $> \xs -> [flatM $ mseq $ xs]
                            Nothing -> Nothing
    in groupSyntax : map muteS regexSyntax

-- Then we can declare regex in two kinds
-- with grouping or without.
regex' syntax finalizer src =
    finishM ((rept $ alt syntax) src) >>= \fs -> Just (finalizer $ mseq $ fs)

regex = regex' regexSyntax flatM
regexG = regex' groupingSyntax (\x->x)


-- Then we want to lex. So we will work with Symbols
-- Lexem is Matcher for Symbols
type Name = [Char]
data Symbol = Symbol Name [Char]
    deriving Show

type Lexem = Matcher [Char] [Symbol]

-- lexer is function that uses Lexem list to transform a string
-- into list of symbols; but it appears that parser is the same
-- but the type of Matcher. So I call it processor
processor :: [Matcher [a] [b]] -> [a] -> Maybe [b]
processor [] _ = Nothing
processor lx inp = finishM ((rept $ alt lx) inp)

-- to create lexem
type Regex = [Char]
lexem :: Regex -> Name -> Lexem
lexem rgx name inp = regex rgx >>= \t -> t inp $> \[v] -> [Symbol name v]

replLex = processor [
    quietM $ lexem "\\s+" "space",
    lexem "\\d+" "num",
    lexem "\"`\"!*\"`" "string", 
    lexem "'`'!*'`" "string", 
    lexem "\\w+" "word" ]

-- Then next step is parsing. In terms of above
-- Parser is Matcher for trees (nodes are keys, leafs are values)
-- from symbols.

data Tree a = Leaf a
            | Node a [Tree a]

instance Show a => Show (Tree a) where
    show (Leaf a) = show a
    show (Node k v) = show k ++ " -> " ++ show v

type Parser a b = Matcher [a] [Tree b]
token :: [Name] -> [Name] -> Parser Symbol [Char]
token types keys inp =
    let isType expected (Symbol t _) = expected == t
        selector :: Matcher [Symbol] [[Symbol]]
        selector = mseq $ map (\x -> unitM $ isType x) types
        getVal (Symbol _ val) = val
        matcher :: Matcher [Symbol] [[Char]]
        matcher = \x -> selector x $> \syms -> map getVal (foldl (++) [] syms)
        zipper :: [[Char]] -> [Tree [Char]]
        zipper values = map (\(key,val) -> Node key [Leaf val])
                            (zip keys values)
    in matcher inp $> zipper

replPars x = replLex x >>= \x' -> processor [
    token ["word", "string"] ["fun", "arg"]] x'
