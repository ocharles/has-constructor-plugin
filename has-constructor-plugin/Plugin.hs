{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}

module Plugin where

import Data.Generics.Uniplate.Data
import Control.Monad ( guard )
import Bag
import HsSyn
import HsExtension
import GhcPlugins
import TcEvidence
import RnEnv
import RnExpr

plugin :: Plugin
plugin =
  defaultPlugin
    { parsedResultAction = \_cliOptions _modSummary x ->
        pure x { hpm_module = onModule <$> hpm_module x }
    , renamedResultAction = \_cliOptions tcGblEnv x -> do
        (constructorExpr, _) <-
          rnLExpr $ noLoc $ HsVar noExt $ noLoc $ mkRdrQual hasConstructorModule $ mkVarOcc "constructor"
        pure ( tcGblEnv, descendBi (generaliseConstructorApplications2 constructorExpr) x )
    , pluginRecompile =
        purePlugin
    }


onModule :: HsModule GhcPs -> HsModule GhcPs
onModule x =
  x { hsmodImports =
        onImports $ hsmodImports x
    , hsmodDecls =
        concatMap hasConstructorInstances (hsmodDecls x) ++
        map (descendBi generaliseConstructorApplications) (hsmodDecls x)
    }


onImports :: [LImportDecl GhcPs] -> [LImportDecl GhcPs]
onImports =
  (hasConstructorImport :)


hasConstructorImport :: LImportDecl GhcPs
hasConstructorImport =
  qualifiedImplicitImport hasConstructorModule


hasConstructorModule =
  mkModuleName "HasConstructor"


qualifiedImplicitImport :: ModuleName -> LImportDecl GhcPs
qualifiedImplicitImport x =
  noLoc $ ImportDecl noExt NoSourceText (noLoc x) Nothing False False True True Nothing Nothing


hasConstructorInstances :: LHsDecl GhcPs -> [LHsDecl GhcPs]
hasConstructorInstances (L _ (TyClD _ (DataDecl _ tname vars _fixity defn))) = do
  guard (dd_ND defn == DataType)

  L _ conDecl <- dd_cons defn

  L _ name <-
    case conDecl of
      ConDeclGADT{ con_names } -> con_names
      ConDeclH98{ con_name } -> [ con_name ]

  let argTypes =
        case con_args conDecl of
          PrefixCon prefixArgs -> prefixArgs
          RecCon (L _ fields) ->
            concatMap
              (\(L _ field) ->
                 zipWith
                   const
                   (repeat (cd_fld_type field))
                   (cd_fld_names field)
              )
              fields

  let dataTy = noLoc (HsTyVar noExt NotPromoted tname)

  let argNames = map (mkRdrUnqual . mkVarOcc . ("x" ++) . show) (zipWith const [1..] argTypes )

  return $ noLoc $ InstD noExt $ ClsInstD noExt $ ClsInstDecl
      { cid_ext = noExt
      , cid_poly_ty = HsIB noExt $
          mkHsAppTys
            (noLoc $ HsTyVar noExt NotPromoted (noLoc $ mkRdrQual hasConstructorModule $ mkClsOcc "HasConstructor"))
            [ noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ rdrNameOcc name
            , dataTy
            , foldr
                (\x y -> noLoc $ HsFunTy noExt x y)
                dataTy
                argTypes
            ]
      , cid_binds =
        unitBag $ noLoc $ FunBind
          { fun_ext = noExt
          , fun_id = noLoc $ mkRdrUnqual $ mkVarOcc "constructor"
          , fun_matches = MG
              { mg_ext = noExt
              , mg_alts = noLoc $ pure $ noLoc $ Match
                  { m_ext = noExt
                  , m_ctxt = FunRhs
                      { mc_fun = noLoc $ mkRdrUnqual $ mkVarOcc "constructor"
                      , mc_fixity = Prefix
                      , mc_strictness = NoSrcStrict
                      }
                  , m_pats = []
                  , m_grhss = GRHSs
                      { grhssExt = noExt
                      , grhssGRHSs =
                          pure $
                          noLoc $
                          GRHS noExt [] $
                          noLoc $ HsVar noExt $ noLoc name
                      , grhssLocalBinds = noLoc $ EmptyLocalBinds noExt
                      }
                  }
              , mg_origin = Generated
              }
          , fun_co_fn = WpHole
          , fun_tick = []
          }
      , cid_sigs = []
      , cid_tyfam_insts = []
      , cid_datafam_insts = []
      , cid_overlap_mode = Nothing
      }
hasConstructorInstances _ =
  []


generaliseConstructorApplications :: LHsExpr GhcPs -> LHsExpr GhcPs
generaliseConstructorApplications = \case
  L l1 (HsApp l2 (L l3 (HsVar _ (L _ name))) x) | isRdrDataCon name ->
    L l1 $
    HsApp l2
      ( L l3 $
        HsAppType
          ( HsWC noExt $ noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ rdrNameOcc name )
          ( noLoc $ HsVar noExt $
            noLoc $ mkRdrQual hasConstructorModule $ mkVarOcc "constructor"
          )
      )
      x

  x ->
    descend generaliseConstructorApplications x

generaliseConstructorApplications2 :: LHsExpr GhcRn -> LHsExpr GhcRn -> LHsExpr GhcRn
generaliseConstructorApplications2 constructor = \case
  L l1 (RecordCon _ (L conLoc conName) fields) ->
    foldl
      (\x y -> noLoc $ HsApp noExt x y)
      ( L conLoc $
        HsAppType
          ( HsWC [] $ noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ nameOccName conName )
          constructor
          --     -- noLoc $ mkRdrQual hasConstructorModule $ mkVarOcc "constructor"
          -- )
      )
      (map (recFldExpr . unLoc) $ rec_flds fields)
      where
        recFldExpr HsRecField{ hsRecFieldLbl, hsRecPun, hsRecFieldArg } =
          -- if hsRecPun then
          --   fmap (HsVar noExt . noLoc) $ rdrNameFieldOcc $ unLoc hsRecFieldLbl

          -- else
            hsRecFieldArg

  x -> descend (generaliseConstructorApplications2 constructor) x
