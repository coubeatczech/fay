module ClassContraVariance2 where

import           Prelude

class Foo a where
  foo :: String -> a -> String
