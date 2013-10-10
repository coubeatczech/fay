module InstDecl where

import           FFI
import           Prelude

class ShowX a where
  show :: a -> String

instance ShowX Int where
  show i = undefined
