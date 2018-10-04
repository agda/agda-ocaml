{- |
Module      :  Agda.Compiler.Malfunction.AST
Maintainer  :  janmasrovira@gmail.com, hanghj@student.chalmers.se

This module defines the abstract syntax of
<https://github.com/stedolan/malfunction Malfunction>. Please see the
<https://github.com/stedolan/malfunction/blob/master/docs/spec.md Malfunction
language specification>
-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Agda.Compiler.Malfunction.AST
  ( IntType(..)
  , IntConst(..)
  , UnaryIntOp(..)
  , BinaryIntOp(..)
  , VectorType(..)
  , Mutability(..)
  , BlockTag
  , Case(..)
  , Ident
  , Longident
  , Mod(..)
  , Term(..)
  , Binding(..)
  -- NOTE: I don't know which of these is preferable
  --  * Don't re-export anything from Agda.Utils.Pretty
  --  * export a few things (like we do currently)
  --  * Re-export the whole module
  , pretty
  , prettyShow
  ) where

import Prelude hiding ((<>))
import Data.Int
-- There does exist a definition of a type-class `Pretty` in the package
-- `pretty` but this is not the one used for Treeless terms, so for consistency,
-- let's go with Agda's choice.
import Agda.Utils.Pretty
import Data.Data (Data, Typeable)

-- | The integer types.
data IntType
  = TInt
  | TInt32
  | TInt64
  | TBigint

deriving stock instance Show IntType
deriving stock instance Eq IntType
deriving stock instance Data IntType
deriving stock instance Typeable IntType

-- | An integer value tagged with its corresponding type.
data IntConst
  -- Int may be the wrong type.
  --
  -- In malfunction Int is:
  --
  -- > `int` uses either 31- or 63- bit two's complement arithmetic
  -- > (depending on system word size, and also wrapping on overflow)
  -- > https://github.com/stedolan/malfunction/blob/master/docs/spec.md
  --
  -- And in Haskell:
  -- > A fixed-precision integer type with at least the range
  -- > [-2^29 .. 2^29-1]
  -- > https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Int.html
  --
  -- Jan: Just run
  -- logBase 2 ((fromIntegral (maxBound :: Int)) :: Double)
  -- in my computer (64 bits) --> 2 ^ 63 - 1 == (maxBound :: Int)
  = CInt Int
  | CInt32 Int32
  | CInt64 Int64
  | CBigint Integer

deriving stock instance Show IntConst
deriving stock instance Eq IntConst
deriving stock instance Data IntConst
deriving stock instance Typeable IntConst

-- | A unary operator.
data UnaryIntOp = Neg | Not

deriving stock instance Show UnaryIntOp
deriving stock instance Eq UnaryIntOp
deriving stock instance Data UnaryIntOp
deriving stock instance Typeable UnaryIntOp

-- | A binary operator.
data BinaryIntOp
  = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lsl | Lsr | Asr
  | Lt | Gt | Lte | Gte | Eq

deriving stock instance Show BinaryIntOp
deriving stock instance Eq BinaryIntOp
deriving stock instance Data BinaryIntOp
deriving stock instance Typeable BinaryIntOp

-- | Vector types.
data VectorType = Array | Bytevec

deriving stock instance Show VectorType
deriving stock instance Eq VectorType
deriving stock instance Data VectorType
deriving stock instance Typeable VectorType

-- | Mutability
data Mutability = Inm | Mut

deriving stock instance Show Mutability
deriving stock instance Eq Mutability
deriving stock instance Data Mutability
deriving stock instance Typeable Mutability

-- NOTE: Any tag value above 200 is an error in malfunction.
--
-- For this reason we may want to make BlockTag a newtype and only export a constructor.
--
-- | A tag used in the construction of $Block@s.
type BlockTag = Int

-- The spec and the ocaml implementation are inconsistent when defining Case.
-- I'll use the definition (examples) from the spec to guide this implementation.
-- I know I could've used Maybe's here, but not doing so was a concious choice.
--
-- | Used in switch-statements. See
-- <https://github.com/stedolan/malfunction/blob/master/docs/spec.md#conditionals>
data Case
  -- (tag _)
  = Deftag
  -- (tag n)
  | Tag Int
  -- _
  | CaseAnyInt
  -- n
  | CaseInt Int
  -- (n m)
  | Intrange (Int, Int)

deriving stock instance Show Case
deriving stock instance Eq Case
deriving stock instance Data Case
deriving stock instance Typeable Case

-- | An identifier used to reference other values in the malfunction module.
type Ident = String

-- | A long identifier is used to reference OCaml values (using @Mglobal@).
type Longident = [Ident]

--data Longident
--  = Lident String
--  | Ldot   Longident String
--  | Lapply Longident Longident

-- "The top-level sexp must begin with the atom module, followed by a
-- list of bindings (described under let, below), followed by an sexp
-- beginning with the atom export."
--
-- | Defines a malfunction module.
data Mod = MMod [Binding] [Term]

deriving stock instance Show Mod
deriving stock instance Eq Mod
deriving stock instance Data Mod
deriving stock instance Typeable Mod

-- | The overall syntax of malfunction terms.
data Term
  = Mvar Ident
  | Mlambda [Ident] Term
  | Mapply Term [Term]
  | Mlet [Binding] Term
  | Mint IntConst
  | Mstring String
  | Mglobal Longident
  | Mswitch Term [([Case], Term)]
  -- Integers
  | Mintop1 UnaryIntOp IntType Term
  | Mintop2 BinaryIntOp IntType Term Term
  | Mconvert IntType IntType Term
  -- Vectors
  | Mvecnew VectorType Term Term
  | Mvecget VectorType Term Term
  | Mvecset VectorType Term Term Term
  | Mveclen VectorType Term
  -- Blocks
  | Mblock Int [Term]
  | Mfield Int Term

deriving stock instance Show Term
deriving stock instance Eq Term
deriving stock instance Data Term
deriving stock instance Typeable Term

-- instance Uniplate Term where
--   uniplate = \case
--     Mvar i              -> plate Mvar     |- i
--     Mlambda is t0       -> plate Mlambda  |- is  |* t0
--     Mapply t ts         -> plate Mapply   |* t   ||* ts
--     Mlet bs t           -> plate Mlet     |- bs  |*  t
--     Mint c              -> plate Mint     |- c
--     Mstring s           -> plate Mstring  |- s
--     Mglobal i           -> plate Mglobal  |- i
--     Mswitch t xs        -> plate Mswitch  |* t   ||+ xs
--     Mintop1 op tp t     -> plate Mintop1  |- op  |- tp |* t
--     Mintop2 op tp t0 t1 -> plate Mintop2  |- op  |- tp |* t0 |* t1
--     Mconvert src trg t  -> plate Mconvert |- src |- trg |* t
--     Mvecnew tp t0 t1    -> plate Mvecnew  |- tp  |* t0 |* t1
--     Mvecget tp t0 t1    -> plate Mvecget  |- tp  |* t0 |* t1
--     Mvecset tp t0 t1 t2 -> plate Mvecset  |- tp  |* t0 |* t1 |* t2
--     Mveclen tp t0       -> plate Mveclen  |- tp  |* t0
--     Mblock n ts         -> plate Mblock   |- n   ||* ts
--     Mfield n t          -> plate Mfield   |- n   |* t

-- | Bindings
--
-- The atom `let` introduces a sequence of bindings:
--
--     (let BINDING BINDING BINDING ... BODY)
--
-- Each binding is of one of the forms:
--
--   - @Named@: @($var EXP)@: binds @$var@ to the result of evaluating @EXP@.
--              @$var@ scopes over subsequent bindings and the body.
--
--   - @Unnamed@: @(_ EXP)@: evaluates @EXP@ and ignores the result.
--
--   - @Recursive@: @(rec ($VAR1 EXP1) ($VAR2 EXP2) ...)@: binds each @$VAR@ mutually
--                  recursively. Each @EXP@ must be of the form @(lambda ...)@.
--                  Bindings scope over themselves, each other, subsequent
--                  bindings, and the body.
data Binding
  = Unnamed Term
  | Named Ident Term
  | Recursive [(Ident, Term)]

deriving stock instance Show Binding
deriving stock instance Eq Binding
deriving stock instance Data Binding
deriving stock instance Typeable Binding

textShow :: Show a => a -> Doc
textShow = text . show

nst :: Doc -> Doc
nst = nest 2

(<.>) :: Doc -> Doc -> Doc
a <.> b = a <> "." <> b

level :: Doc -> Doc -> Doc
level a b = sep [ "(" <+> a, nst b, ")" ]

levelPlus :: Doc -> [Doc] -> Doc
levelPlus a bs = sep $ [ "(" <+> a ] ++ map nst bs ++ [")"]

-- This is a list that has no comma or brackets.
prettyList__ :: Pretty a => [ a ] -> Doc
prettyList__ = fsep . map pretty

instance Pretty Mod where
  pretty (MMod bs ts) = levelPlus "module" (map pretty bs ++ [levelPlus "export" (map pretty ts)])
  prettyPrec _ = pretty

instance Pretty Term where
  pretty tt = case tt of
    Mvar i              -> prettyIdent i
    Mlambda is t        -> level ("lambda" <+> parens (hsep (map prettyIdent is))) (pretty t)
    Mapply t ts         -> levelPlus ("apply " <> pretty t) (map pretty ts)
    Mlet bs t           -> level "let" (prettyList__ bs $$ pretty t)
    Mint ic             -> pretty ic
    Mstring s           -> textShow s
    Mglobal li          -> parens $ "global" <+> prettyLongident li
    Mswitch t cexps     -> levelPlus ("switch" <+> pretty t) (map prettyCaseExpression cexps)
    -- Integers
    Mintop1 op tp t0    -> pretty op <+> prettyTypedTerm tp t0
    Mintop2 op tp t0 t1 -> levelPlus (pretty op) [prettyTypedTerm tp t0, prettyTypedTerm tp t1]
    Mconvert tp0 tp1 t0 -> parens $ "convert" <.> pretty tp0 <.> pretty tp1 <+> pretty t0
    -- Vectors
    Mvecnew _tp t0 t1    -> levelPlus "makevec" [pretty t0, pretty t1]
    Mvecget _tp t0 t1    -> levelPlus "load" [pretty t0, pretty t1]
    Mvecset _tp t0 t1 t2 -> levelPlus "store" [pretty t0, pretty t1, pretty t2]
    Mveclen _tp t0       -> level "length" (pretty t0)
    -- Blocks
    Mblock i ts         -> level ("block" <+> parens ("tag" <+> pretty i)) (prettyList__ ts)
    Mfield i t0         -> parens $ "field" <+> pretty i <+> pretty t0
  prettyPrec _ = pretty

instance Pretty Binding where
  pretty b = case b of
    Unnamed t    -> level "_" (pretty t)
    Named i t    -> level (prettyIdent i) (pretty t)
    Recursive bs -> levelPlus "rec" (map showIdentTerm bs)
    where
      showIdentTerm :: (Ident, Term) -> Doc
      showIdentTerm (i, t) = level (prettyIdent i) (pretty t)

instance Pretty IntConst where
  pretty ic = case ic of
    CInt    i -> pretty i
    CInt32  i -> pretty i <.> "i32"
    CInt64  i -> textShow i <.> "i64"
    CBigint i -> pretty i <.> "ibig"

prettyLongident :: Longident -> Doc
prettyLongident = hsep . map prettyIdent

prettyIdent :: Ident -> Doc
prettyIdent = text . ('$':)

prettyCaseExpression :: ([Case], Term) -> Doc
prettyCaseExpression (cs, t) = level (prettyList__ cs) (pretty t)

instance Pretty Case where
  pretty c = case c of
    Deftag          -> "(tag _)"
    Tag n           -> "(tag " <> pretty n <> ")"
    CaseAnyInt      -> "_"
    CaseInt n       -> pretty n
    Intrange (i, j) -> "(" <> pretty i <+> pretty j <> ")"

instance Pretty UnaryIntOp where
  pretty op = case op of
    Neg -> "?.ibig"
    Not -> "?.ibig"

instance Pretty BinaryIntOp where
  pretty op = case op of
    Add -> "+.ibig"
    Sub -> "-.ibig"
    Mul -> "*.ibig"
    Div -> "/.ibig"
    Mod -> "%.ibig"
    And -> "&.ibig"
    Or  -> "|.ibig"
    Xor -> "^.ibig"
    Lsl -> "<<.ibig"
    Lsr -> ">>.ibig"
    Asr -> "a>>.ibig"
    Lt  -> "<.ibig"
    Gt  -> ">.ibig"
    Lte -> "<=.ibig"
    Gte -> ">=.ibig"
    Eq  -> "==.ibig"


prettyTypedTerm :: IntType -> Term -> Doc
prettyTypedTerm tp t = case tp of
  TInt -> pretty t
  _    -> pretty t <.> pretty tp

instance Pretty IntType where
  pretty tp = case tp of
    TInt    -> "int"
    TInt32  -> "int32"
    TInt64  -> "int64"
    TBigint -> "bigint"
