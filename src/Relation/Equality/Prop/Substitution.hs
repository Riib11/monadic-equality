{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--max-case-expand=0" @-}

module Relation.Equality.Prop.Substitution where

import Control.Monad
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.TH
import Relation.Equality.Prop

-- TODO: for some reason it takes a long time for LH to load this...

-- e:c -> x:a -> y:a -> EqualProp a {x} {y} -> EqualProp b {f x} {f y}
-- where f is extracted from e by abstracting out the appearances of x
{-@ lazy substitute @-}
substitute :: Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp
substitute eQ xQ yQ exyQ = do
  x <- xQ
  e <- eQ
  hole <- newName "hole"
  let {-@ lazy extract @-}
      extract :: Exp -> Q Exp
      extract _e =
        if _e == x
          then varE hole
          else case _e of
            AppE e1 e2 -> AppE <$> extract e1 <*> extract e2
            AppTypeE e t -> AppTypeE <$> extract e <*> return t
            InfixE mb_e1 e2 mb_e3 -> InfixE <$> traverse extract mb_e1 <*> extract e2 <*> traverse extract mb_e3
            UInfixE e1 e2 e3 -> UInfixE <$> extract e1 <*> extract e2 <*> extract e3
            ParensE e -> ParensE <$> extract e
            LamE pats e -> LamE pats <$> extract e
            LamCaseE mats -> LamCaseE <$> traverse extractMatch mats
            TupE mb_es -> TupE <$> (traverse . traverse) extract mb_es
            UnboxedTupE mb_es -> UnboxedTupE <$> (traverse . traverse) extract mb_es
            UnboxedSumE e i1 i2 -> UnboxedSumE <$> extract e <*> return i1 <*> return i2
            CondE e1 e2 e3 -> CondE <$> extract e1 <*> extract e2 <*> extract e3
            MultiIfE grds_es -> MultiIfE <$> traverse extractGuardExp grds_es
            LetE decs e -> LetE <$> traverse extractDec decs <*> extract e
            CaseE e mats -> CaseE <$> extract e <*> traverse extractMatch mats
            DoE stmts -> DoE <$> traverse extractStmt stmts
            MDoE stmts -> MDoE <$> traverse extractStmt stmts
            CompE stmts -> CompE <$> traverse extractStmt stmts
            ArithSeqE rng -> ArithSeqE <$> extractRange rng
            ListE es -> ListE <$> traverse extract es
            SigE e t -> SigE <$> extract e <*> return t
            RecConE n ns_es -> RecConE n <$> (traverse . traverse) extract ns_es
            RecUpdE e ns_es -> RecUpdE <$> extract e <*> (traverse . traverse) extract ns_es
            StaticE e -> StaticE <$> extract e
            _ -> return _e
      {-@ lazy extractStmt @-}
      extractStmt :: Stmt -> Q Stmt
      extractStmt = \case
        BindS pat e -> BindS pat <$> extract e
        LetS decs -> LetS <$> traverse extractDec decs
        NoBindS e -> NoBindS <$> extract e
        ParS stmtss -> ParS <$> (traverse . traverse) extractStmt stmtss
        RecS stmts -> RecS <$> traverse extractStmt stmts
      {-@ lazy extractDec @-}
      extractDec :: Dec -> Q Dec
      extractDec = \case
        FunD n clauses -> FunD n <$> traverse extractClause clauses
        ValD pat bod decs -> ValD pat <$> extractBody bod <*> traverse extractDec decs
        ClassD cxt n tybs fundeps decs -> ClassD cxt n tybs fundeps <$> traverse extractDec decs
        InstanceD overlap cxt ty decs -> InstanceD overlap cxt ty <$> traverse extractDec decs
        ImplicitParamBindD str e -> ImplicitParamBindD str <$> extract e
        dec -> return dec
      {-@ lazy extractBody @-}
      extractBody :: Body -> Q Body
      extractBody = \case
        GuardedB grds_es -> GuardedB <$> traverse extractGuardExp grds_es
        NormalB e -> NormalB <$> extract e
      {-@ lazy extractGuard @-}
      extractGuard :: Guard -> Q Guard
      extractGuard = \case
        NormalG e -> NormalG <$> extract e
        PatG stmts -> PatG <$> traverse extractStmt stmts
      {-@ lazy extractRange @-}
      extractRange :: Range -> Q Range
      extractRange = \case
        FromR e -> FromR <$> extract e
        FromThenR e1 e2 -> FromThenR <$> extract e1 <*> extract e2
        FromToR e1 e2 -> FromToR <$> extract e1 <*> extract e2
        FromThenToR e1 e2 e3 -> FromThenToR <$> extract e1 <*> extract e2 <*> extract e3
      {-@ lazy extractClause @-}
      extractClause :: Clause -> Q Clause
      extractClause (Clause pats bod decs) = Clause pats <$> extractBody bod <*> traverse extractDec decs
      {-@ lazy extractMatch @-}
      extractMatch :: Match -> Q Match
      extractMatch (Match pat bod decs) = Match pat <$> extractBody bod <*> traverse extractDec decs
      {-@ lazy extractGuardExp @-}
      extractGuardExp :: (Guard, Exp) -> Q (Guard, Exp)
      extractGuardExp (grd, e) = (,) <$> extractGuard grd <*> extract e
  --
  [|substitutability $(lamE [varP hole] (extract e)) $xQ $yQ $exyQ|]
