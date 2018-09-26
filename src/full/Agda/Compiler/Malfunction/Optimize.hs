module Agda.Compiler.Malfunction.Optimize where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Common
import Data.List
import qualified Data.Map.Strict as M

import Control.Monad.State

--- TODO First We need to remove all let statements.



type UIDState = State (Integer , Integer)

newUID :: UIDState String
newUID = do
  s <- gets (show . fst)
  modify (\(a , b) -> (1 + a , b))
  pure s

-- newOID must be called after the recursive part, so that first MApplys will get a lower number.
newOID :: UIDState Integer
newOID = do
  s <- gets snd
  modify (\(a , b) -> (a , (1 + b)))
  pure s


-- IMPORTANT ALGORITHM
-- We search and pick all applications. We need to remember the order that we picked them because
-- the this is the order that we will write our let statements.
-- An application might have other applications that we have found in a previous step.
-- When we create the let statements, those applications will also be replaced with the new variable name."

-- TODO This could be simplified. Careful , the algorithm is very tricky.

-- The key Term on the map is unchanged. The snd Term on the Map is changing and it is to be used at the let statement.
-- The term on the product is the changed one which we will use to assemble the result.
-- The integer represents the order of arrival. We will use this to order the let statements.
findCF :: Term -> UIDState (M.Map Term (Term , Integer , Bool) , Term)
findCF self@(Mvar i) = pure (M.empty , self)
findCF self@(Mlambda ids t) = do
                                (tms , nself) <- findCF t
                                pure (tms , Mlambda ids nself)
-- We need to perform findCF on a and bs when we create the let statement.
findCF self@(Mapply a bs) = do
                              rs <- mapM findCF (a : bs)
                              
                              let inters = foldr (\a b -> M.intersection (fst a) b)  M.empty rs
                                  newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                  all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                  nall = newInters `M.union` all
                                  (na , nbs) = (snd $ head rs , map snd (tail rs))
                                  nself = Mapply na nbs
                              noid <- newOID
                              pure (M.insert self (nself , noid , False) nall , nself )
                                        -- case (elemIndex (False , self)  of
findCF self@(Mlet bs t) = error "We have removed all let statements"

-- We have to put all new let statements after the switch.
findCF self@(Mswitch ta tb) = pure (M.empty , self) where
 
  singleCase :: Term -> UIDState Term
  singleCase t = do
                    r <- findCF t
                    
                    let psLets = M.filter (\(a , b , c) -> c) (fst r)
                        lo = map snd $ sort $ M.foldr (\(a , b , c) l -> (b , a) : l) [] psLets
                        all = lo ++ [snd r]
                    rs <- replaceRec all
                    let bs = createBinds (init rs)
                    pure $ Mlet bs (snd (last rs))

findCF  self@(Mintop1 x y t) = do (tms , nself) <- findCF  t
                                  pure (tms , (Mintop1 x y nself))
findCF  self@(Mintop2 x y ta tb ) = do (tmsa , nta) <- findCF  ta
                                       (tmsb , ntb) <- findCF  tb
                                       let inters = M.intersection tmsa tmsb
                                           newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                           all = M.union tmsa tmsb
                                           nall = newInters `M.union` all
                                       pure (nall , (Mintop2 x y nta ntb ))
findCF  self@(Mconvert x y t) = do (tms , nself) <- findCF  t
                                   pure (tms , (Mconvert x y nself))
findCF  self@(Mvecnew x ta tb) =  do (tmsa , nta) <- findCF  ta
                                     (tmsb , ntb) <- findCF  tb
                                     let inters = M.intersection tmsa tmsb
                                         newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                         all = M.union tmsa tmsb
                                         nall = newInters `M.union` all
                                     pure (nall , (Mvecnew x nta ntb))
findCF  self@(Mvecget x ta tb) = do (tmsa , nta) <- findCF  ta
                                    (tmsb , ntb) <- findCF  tb
                                    let inters = M.intersection tmsa tmsb
                                        newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                        all = M.union tmsa tmsb
                                        nall = newInters `M.union` all
                                    pure (nall , (Mvecget x nta ntb))
findCF  self@(Mvecset x ta tb tc) =  do (tmsa , nta) <- findCF  ta
                                        (tmsb , ntb) <- findCF  tb
                                        (tmsc , ntc) <- findCF  tc
                                        let inters = M.intersection (M.intersection tmsa tmsb) tmsc
                                            newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                            all = M.union (M.union tmsa tmsb) tmsc
                                            nall = newInters `M.union` all
                                        pure (nall , (Mvecset x nta ntb ntc))
findCF  self@(Mveclen x t) =  do (tms , nself) <- findCF  t
                                 pure (tms , (Mveclen x nself))
findCF  self@(Mblock x bs) =  do
                                 rs <- mapM findCF bs
                              
                                 let inters = foldr (\a b -> M.intersection (fst a) b)  M.empty rs
                                     newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                     all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                     nall = newInters `M.union` all
                                 pure (nall , (Mblock x (map snd rs)))
findCF  self@(Mfield x t) =   do (tms , nself) <- findCF  t
                                 pure (tms , (Mfield x nself))
findCF  x = pure (M.empty , x)





createBinds :: [(String ,Term)] -> [Binding]
createBinds [] = []
createBinds ((var , term) : ns) = Named var term : createBinds ns

replaceRec :: [Term] -> UIDState [(String ,Term)]
replaceRec (t : []) = pure $ ("ERROR" , t) : []
replaceRec (t : ts) =  do ar <- newUID
                          let rs = map (replaceTr t (Mvar ar)) ts
                          nvs <- replaceRec rs
                          pure $ (ar , t) : nvs

replaceTr :: Term -> Term -> Term -> Term
replaceTr rt ar self@(Mvar i) = self
replaceTr rt ar self@(Mlambda a t) = Mlambda a (replaceTr rt ar t)
replaceTr rt ar self@(Mapply a bs) = case rt == self of
                                    True -> ar
                                    False -> let (na : nbs) = map (replaceTr rt ar) (a : bs)
                                             in (Mapply na nbs) 
-- Let statements here exist because we put them. We should never reach here.
replaceTr rt ar self@(Mlet bs t) = error "We are not supposed to search that far. We put lets after a Mswitch term."
-- We can change the conditional expression.
replaceTr rt ar self@(Mswitch ta tb) = let nta = replaceTr rt ar ta
                                    in Mswitch nta tb
replaceTr rt ar self@(Mintop1 x y t) = let nt = replaceTr rt ar t
                                    in (Mintop1 x y nt)
replaceTr rt ar self@(Mintop2 x y ta tb ) = let nta = replaceTr rt ar ta
                                                ntb = replaceTr rt ar tb
                                            in (Mintop2 x y nta ntb )
replaceTr rt ar self@(Mconvert x y t) = let nt = replaceTr rt ar t
                                        in (Mconvert x y nt)
replaceTr rt ar self@(Mvecnew x ta tb) = let nta = replaceTr rt ar ta
                                             ntb = replaceTr rt ar tb
                                         in (Mvecnew x nta ntb)
replaceTr rt ar self@(Mvecget x ta tb) = let nta = replaceTr rt ar ta
                                             ntb = replaceTr rt ar tb
                                         in (Mvecget x nta ntb)
replaceTr rt ar self@(Mvecset x ta tb tc) = let nta = replaceTr rt ar ta
                                                ntb = replaceTr rt ar tb
                                                ntc = replaceTr rt ar tc
                                            in (Mvecset x nta ntb ntc)
replaceTr rt ar self@(Mveclen x t) = let nt = replaceTr rt ar t
                                     in (Mveclen x nt)
replaceTr rt ar self@(Mblock x bs) = let nbs = map (replaceTr rt ar) bs
                                     in (Mblock x nbs)
replaceTr rt ar self@(Mfield x t) = let nt = replaceTr rt ar t
                                   in (Mfield x t)
replaceTr rt ar x = x
