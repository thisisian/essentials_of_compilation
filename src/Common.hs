module Common where

class PrettyPrint a where
  prettyPrint :: a -> String
