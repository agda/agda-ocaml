{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Agda.Compiler.Malfunction.Instances where

-- TODO Request to get upstream.
import Agda.Syntax.Treeless (TTerm)
import Data.Data (Typeable)

deriving instance Typeable TTerm
