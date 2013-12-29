module InstDecl where

import           FFI
import           Prelude

class ShowX a where
  show :: a -> String

data X = X

instance ShowX X where
  show X = "X"
