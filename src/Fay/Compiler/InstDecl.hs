{-# OPTIONS -fno-warn-name-shadowing #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ViewPatterns          #-}

-- | Compile declarations.

module Fay.Compiler.InstDecl
  (compileClassDecl
  ,compileInstDecl
  ) where

import           Fay.Compiler.Exp
import           Fay.Compiler.FFI
import           Fay.Compiler.Misc
import           Fay.Compiler.Pattern
import           Fay.Compiler.State              ()
import           Fay.Data.List.Extra             ()
import           Fay.Exts.NoAnnotation           (unAnn)
import qualified Fay.Exts.NoAnnotation           as N
import qualified Fay.Exts.Scoped                 as S
import           Fay.Types

import           Control.Applicative
import           Control.Monad.Error
import           Control.Monad.RWS
import           Language.Haskell.Exts.Annotated

compileClassDecl :: S.DeclHead -> [S.ClassDecl] -> Compile [JsStmt]
compileClassDecl ih cd = concat <$> mapM aux cd
  where
    aux :: S.ClassDecl -> Compile [JsStmt]
    aux cd' = case cd' of
      ClsDecl _ decl -> do
        return []
      _ -> return []

className' (DHead _ n _) = n
className' _ = error "className' should have been desugared"

data Hole = Hole
hole = undefined

compileInstDecl :: S.QName -> [S.Type] -> [S.InstDecl] -> Compile [JsStmt]
compileInstDecl n ts idecls = do
  qn <- qualifyQName n
  liftM concat $ forM idecls $ \(InsDecl _ dls) -> case dls of
    pat@PatBind{} -> compilePatBind hole Nothing pat
    FunBind _ matches -> compileFunCase hole matches

-- | Compile a top-level pattern bind.
compilePatBind :: hole -> Maybe S.Type -> S.Decl -> Compile [JsStmt]
compilePatBind con sig patDecl = case patDecl of
  PatBind srcloc (PVar _ ident) Nothing (UnGuardedRhs _ rhs) Nothing ->
    case ffiExp rhs of
      Just formatstr -> case sig of
        Just sig -> compileFFI ident formatstr sig
        Nothing  -> throwError $ FfiNeedsTypeSig patDecl
      _ -> compileUnguardedRhs con srcloc ident rhs
  -- TODO: Generalize to all patterns
  PatBind srcloc (PVar _ ident) Nothing (UnGuardedRhs _ rhs) (Just bdecls) ->
    compileUnguardedRhs con srcloc ident (Let S.noI bdecls rhs)
  PatBind _ pat Nothing (UnGuardedRhs _ rhs) _bdecls -> case pat of
    PList {} -> compilePatBind' pat rhs
    PTuple{} -> compilePatBind' pat rhs
    PApp  {} -> compilePatBind' pat rhs
    _        -> throwError $ UnsupportedDeclaration patDecl
  _ -> throwError $ UnsupportedDeclaration patDecl
  where
    compilePatBind' :: S.Pat -> S.Exp -> Compile [JsStmt]
    compilePatBind' pat rhs = do
      exp <- compileExp rhs
      name <- withScopedTmpJsName return
      [JsIf t b1 []] <- compilePat (JsName name) pat []
      let err = [throw ("Irrefutable pattern failed for pattern: " ++ prettyPrint pat) (JsList [])]
      return [JsVar name exp, JsIf t b1 err]

-- | Compile a normal simple pattern binding.
compileUnguardedRhs :: hole -> S.X -> S.Name -> S.Exp -> Compile [JsStmt]
compileUnguardedRhs con srcloc ident rhs = do
  body <- compileExp rhs
  bind <- bindName (Just (srcInfoSpan (S.srcSpanInfo srcloc))) con ident (thunk body)
  return [bind]

-- | Compile a function which pattern matches (causing a case analysis).
compileFunCase :: hole -> [S.Match] -> Compile [JsStmt]
compileFunCase _ [] = return []
compileFunCase con (InfixMatch l pat name pats rhs binds : rest) =
  compileFunCase con (Match l name (pat:pats) rhs binds : rest)
compileFunCase con matches@(Match srcloc name argslen _ _:_) = do
  pats <- fmap optimizePatConditions (mapM compileCase matches)
  bind <- bindName (Just (srcInfoSpan (S.srcSpanInfo srcloc)))
                   con
                   name
                   (foldr (\arg inner -> JsFun Nothing [arg] [] (Just inner))
                          (stmtsThunk (concat pats ++ basecase))
                          args)
  return [bind]
  where
    args = zipWith const uniqueNames argslen

    isWildCardMatch (Match _ _ pats          _ _) = all isWildCardPat pats
    isWildCardMatch (InfixMatch _ pat _ pats _ _) = all isWildCardPat (pat:pats)

    compileCase :: S.Match -> Compile [JsStmt]
    compileCase (InfixMatch l pat name pats rhs binds) =
      compileCase $ Match l name (pat:pats) rhs binds
    compileCase match@(Match _ _ pats rhs _) = do
      whereDecls' <- whereDecls match
      rhsform <- compileRhs rhs
      body <- if null whereDecls'
                then return [either id JsEarlyReturn rhsform]
                else do
                    binds <- mapM compileLetDecl whereDecls'
                    case rhsform of
                      Right exp ->
                        return [JsEarlyReturn $ JsApp (JsFun Nothing [] (concat binds) (Just exp)) []]
                      Left stmt ->
                        withScopedTmpJsName $ \n -> return
                          [ JsVar n (JsApp (JsFun Nothing [] (concat binds ++ [stmt]) Nothing) [])
                          , JsIf (JsNeq JsUndefined (JsName n)) [JsEarlyReturn (JsName n)] []
                          ]
      foldM (\inner (arg,pat) ->
              compilePat (JsName arg) pat inner)
            body
            (zip args pats)

    whereDecls :: S.Match -> Compile [S.Decl]
    whereDecls (Match _ _ _ _ (Just (BDecls _ decls))) = return decls
    whereDecls (Match _ _ _ _ Nothing) = return []
    whereDecls match = throwError (UnsupportedWhereInMatch match)

    basecase :: [JsStmt]
    basecase = if any isWildCardMatch matches
                  then []
                  else [throw ("unhandled case in " ++ prettyPrint name)
                              (JsList (map JsName args))]

-- | Compile a right-hand-side expression.
compileRhs :: S.Rhs -> Compile (Either JsStmt JsExp)
compileRhs (UnGuardedRhs _ exp) = Right <$> compileExp exp
compileRhs (GuardedRhss _ rhss) = Left <$> compileGuards rhss

bindName :: Maybe SrcSpan -> hole -> Name l -> JsExp -> Compile JsStmt
bindName msrcloc con (unAnn -> name) expr = do
  mod <- gets stateModuleName
  return $ JsSetQName msrcloc (Qual () (f mod (g con)) name) expr

f :: N.ModuleName -> String -> N.ModuleName
f (ModuleName () m) n = ModuleName () $ m ++ "." ++ g n ++ "." ++ "prototype"
g :: hole -> String
g = hole
