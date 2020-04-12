module Parser where

import Control.Applicative
import Data.Char
import MathLogicEssentials

newtype Parser a = Parser { runParser :: String -> [(a, String)] }
-- The return type of a function wrapped inside a Parser data type is not `Maybe`,
-- but rather a list to provide flexibility to the Parsing object. 

item :: Parser Char
item = Parser $ \input -> case input of
                              []     -> []
                              (x:xs) -> [(x,xs)]

instance Functor Parser where
--  fmap :: (a -> b) -> Parser a -> Parser b
    fmap f p = Parser $ \input -> case runParser p input of
                                      []          -> []
                                      [(v, rest)] -> [(f v, rest)]

instance Applicative Parser where
--  pure :: a -> Parser a
    pure x = Parser $ \input -> [(x, input)]
--     <*> :: Parser (a -> b) -> Parser a -> Parser b
    pf <*> pa = Parser $ \input -> case runParser pf input of
                                       []          -> []
                                       [(f, rest)] -> runParser (fmap f pa) rest

instance Monad Parser where
--  return :: a -> Parser a
    return = pure
--   (>>=) :: Parser a -> (a -> Parser b) -> Parser b
    p >>= f = Parser $ \input -> case runParser p input of
                                     []          -> []
                                     [(x, rest)] -> runParser (f x) rest

instance Alternative Parser where
--  empty :: Parser a
    empty = Parser $ \input -> []

--   (<|>) :: Parser a -> Parser a -> Parser a
    p <|> q = Parser $ \input -> case runParser p input of
                                     []         -> runParser q input
                                     [(x, out)] -> [(x, out)]

predicate :: (Char -> Bool) -> Parser Char
predicate p = do 
    x <- item
    if p x then return x else empty

upper :: Parser Char
upper = predicate isUpper

alphanum :: Parser Char
alphanum = predicate isAlphaNum

restVariable :: Parser Char
restVariable = predicate (\c -> isUpper c || isDigit c || c == '\'')

character :: Char -> Parser Char
character x = predicate (== x)

string :: String -> Parser String
string []     = return []
string (x:xs) = do 
    character x
    string xs
    return $ x:xs

chain :: Parser a -> Parser s -> Parser [a]
chain item separator = do
    i  <- item
    is <- many (do
        separator
        item)
    return $ i:is

leftAssociative :: (a -> a -> a) -> Parser a -> Parser s -> Parser a
leftAssociative f item separator = do
    is <- chain item separator
    return $ foldl1 f is

rightAssociative :: (a -> a -> a) -> Parser a -> Parser s -> Parser a
rightAssociative f item separator = do
    is <- chain item separator
    return $ foldr1 f is

-- =========================================== --

implication :: Parser PropFormula
implication = rightAssociative (:->) disjunction (string "->")

disjunction :: Parser PropFormula
disjunction = leftAssociative (:|) conjunction (character '|')

conjunction :: Parser PropFormula
conjunction = leftAssociative (:&) negation (character '&')

negation :: Parser PropFormula
negation = do
        character '!'
        y <- negation
        return $ Not y
    <|> variable 
    <|> do
        character '('
        x <- implication
        character ')'
        return x 

variable :: Parser PropFormula
variable = do 
    x  <- upper
    xs <- many restVariable
    return . PropString $ x:xs

-- =========================================== --

parse :: String -> PropFormula
parse given 
    = fst 
    . head 
    . runParser implication 
    . filter (not . isSpace) 
    $ given