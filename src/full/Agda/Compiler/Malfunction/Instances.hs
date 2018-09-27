{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Agda.Compiler.Malfunction.Instances where

import           Agda.Syntax.Common
import qualified Agda.Syntax.Concrete        as C
import qualified Agda.Syntax.Fixity          as F
import           Agda.Syntax.Literal
import           Agda.Syntax.Notation
import           Agda.Syntax.Position
import           Agda.Syntax.Treeless
import           Agda.Utils.FileName
import           Data.Data
import           Data.Graph

deriving instance Typeable TTerm
