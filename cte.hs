import Data.Char
import System.Environment
import Control.Exception (SomeException, try)

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
 
finishM' :: OptPart [a] b -> Maybe b
finishM' opt = opt >>= \(Part m r) -> Just m

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
                  matchConv (stringM "\\n") (unitM (== '\n')),
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
                        ('^', quietM),
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

-- Having regex, I want to be able to finalize Matcher usage
-- and separate result.

usage = do 
    putStrLn "cte\nusage: cte <file to open>"
    return Nothing

fileContent f = do
    fh <- try $ readFile f :: IO(Either SomeException [Char])
    case fh of
        Left x -> do
            putStrLn $ "Can't open file " ++ f ++ ": " ++ (show x)
            return Nothing
        Right txt -> return $ Just txt
        
replSubject = do
    args <- getArgs
    case args of
        [] -> usage
        [f] -> fileContent f
        _ -> usage

class HasNeutral x where
    neutral :: x

instance HasNeutral () where
    neutral = ()

instance HasNeutral (Maybe a) where
    neutral = Nothing

(&>=) :: HasNeutral b => IO (Maybe a) -> (a -> IO b) -> IO b
a &>= b = a >>= \x -> case x of
                        Just y -> b y
                        _ -> return $ neutral

matchOne :: Maybe (Matcher [Char] [[Char]]) -> [Char] -> Maybe [Char]
matchOne rgx input = rgx >>= \tst -> finishM(tst input)
                     >>= \x -> Just $ foldl (++) "" x

find :: Maybe (Matcher [a] [b]) -> [a] -> Maybe [b]
find rgx [] = Nothing
find rgx input = rgx >>= \tst -> case (tst input) of
                                    Just (Part m r) -> Just $ m ++ (find rgx r >>| [])
                                    Nothing -> case (find rgx (drop 1 input)) of
                                                  Nothing -> Nothing
                                                  x -> x
                                    

type Buffer = String
type BufferAct = Buffer -> IO (Maybe String)

repl :: BufferAct
repl input =
    let rgx input = matchOne (regex "/^/!+/^") input
    in getLine >>= \line -> return $ case (rgx line) of
                                        Nothing -> Just $ "can't compile " ++ line
                                        Just tst -> case (find (regex tst) input) of
                                                        Nothing -> Just $ ":( <" ++ tst ++ ">"
                                                        Just ms -> Just $ foldl (\a -> \v -> a ++ "\n" ++ v)
                                                                           (head ms) (drop 1 ms)

reptIO :: BufferAct -> (String -> IO()) -> (Buffer -> IO ())
reptIO inio outio buff = do
    step <- inio buff
    case step of
        Nothing -> return ()
        Just x -> do
            outio x
            reptIO inio outio buff

main = replSubject &>= reptIO repl putStrLn

