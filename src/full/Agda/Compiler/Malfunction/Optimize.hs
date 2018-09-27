module Agda.Compiler.Malfunction.Optimize where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.EraseDefs
import Agda.Compiler.Common
import Data.List
import Data.Bool
import qualified Data.Map.Strict as M

import Control.Monad.State

--- TODO First We need to remove all let statements.

-- First Bool is for general Let
-- Second for recursive let

doLetExist :: Term -> (Bool , Bool)
doLetExist self@(Mvar i) = (False , False)
doLetExist self@(Mlambda a t) = doLetExist t
doLetExist self@(Mapply a bs) = fst $
  until (\(x , bs) -> snd x) (\(x , (b : bs)) -> let r = doLetExist b
                                                 in ((fst x && fst r , snd x && snd r) , bs)) ((False , False) , bs)
-- We are going to remove lets, so we do not care about idents inside them.
doLetExist self@(Mlet bs t) = let x = foldr (\b x -> case b of
                                                       Recursive _ -> True || x
                                                       _   -> x ) False bs
                              in (True , x)
doLetExist self@(Mswitch ta tb) = fst $
  until (\(x , bs) -> snd x) (\(x , (b : bs)) -> let r = doLetExist b
                                                 in ((fst x && fst r , snd x && snd r) , bs)) ((False , False) , (ta : (map snd tb)))  
doLetExist self@(Mintop1 x y t) = doLetExist t
doLetExist self@(Mintop2 x y ta tb ) = let nta = doLetExist ta
                                           ntb = doLetExist tb
                                       in (fst nta && fst ntb , snd nta && snd ntb)
doLetExist self@(Mconvert x y t) = doLetExist t
doLetExist self@(Mvecnew x ta tb) = let nta = doLetExist ta
                                        ntb = doLetExist tb
                                    in (fst nta && fst ntb , snd nta && snd ntb)
doLetExist self@(Mvecget x ta tb) = let nta = doLetExist ta
                                        ntb = doLetExist tb
                                    in (fst nta && fst ntb , snd nta && snd ntb)
doLetExist self@(Mvecset x ta tb tc) = let nta = doLetExist ta
                                           ntb = doLetExist tb
                                           ntc = doLetExist tc
                                       in (fst nta && fst ntb && fst ntc , snd nta && snd ntb && fst ntc)
doLetExist self@(Mveclen x t) = doLetExist t
doLetExist self@(Mblock x bs) = fst $
  until (\(x , bs) -> snd x) (\(x , (b : bs)) -> let r = doLetExist b
                                                 in ((fst x && fst r , snd x && snd r) , bs)) ((False , False) , bs)
doLetExist self@(Mfield x t) = doLetExist t
doLetExist x = (False , False)




-- We find all local Idents (in lambdas) that are not let bindings. We do that because when we remove the let binding,
-- we need to make it a function that will pass those idents if they exist in the let term.

findLocalIdents :: Term -> [Ident]
findLocalIdents self@(Mvar i) = []
findLocalIdents self@(Mlambda a t) = a ++ (findLocalIdents t)
findLocalIdents self@(Mapply a bs) = concat $ map (findLocalIdents) (a : bs)
-- We are going to remove lets, so we do not care about idents inside them.
findLocalIdents self@(Mlet bs t) = []
findLocalIdents self@(Mswitch ta tb) = concat $ map (findLocalIdents) (ta : (map snd tb))   
findLocalIdents self@(Mintop1 x y t) = findLocalIdents t
findLocalIdents self@(Mintop2 x y ta tb ) = let nta = findLocalIdents ta
                                                ntb = findLocalIdents tb
                                            in nta ++ ntb
findLocalIdents self@(Mconvert x y t) = findLocalIdents t
findLocalIdents self@(Mvecnew x ta tb) = let nta = findLocalIdents ta
                                             ntb = findLocalIdents tb
                                         in nta ++ ntb
findLocalIdents self@(Mvecget x ta tb) = let nta = findLocalIdents ta
                                             ntb = findLocalIdents tb
                                         in nta ++ ntb
findLocalIdents self@(Mvecset x ta tb tc) = let nta = findLocalIdents ta
                                                ntb = findLocalIdents tb
                                                ntc = findLocalIdents tc
                                            in nta ++ ntb ++ ntc
findLocalIdents self@(Mveclen x t) = findLocalIdents t
findLocalIdents self@(Mblock x bs) = concat $ map findLocalIdents bs
findLocalIdents self@(Mfield x t) = findLocalIdents t
findLocalIdents x = []

type TPUIDState =  State Integer

-- newTPUID :: TPUIDState String
-- newTPUID = do
--   s <- gets (show . fst)
--   modify (\(a , b) -> (1 + a , b))
--   pure $ "topId" ++ s


newLUID :: TPUIDState String
newLUID = do
  s <- gets show
  modify (\a -> 1 + a)
  pure $ "lamb" ++ s


replaceIdent :: Ident -> Ident -> Term -> Term
replaceIdent id nid self@(Mvar i) = case i == id of
                                      True -> Mvar nid
                                      False -> self
replaceIdent id nid self@(Mlambda a t) = Mlambda a (replaceIdent id nid t)
replaceIdent id nid self@(Mapply a bs) = let (na : nbs) = map (replaceIdent id nid) (a : bs)
                                         in (Mapply na nbs)
--- TODO  Fix that.
replaceIdent id nid self@(Mlet bs t) = let nt = replaceIdent id nid t
                                       in Mlet (map (rpl id nid) bs) nt where
  rpl :: Ident -> Ident -> Binding -> Binding
  rpl  id nid (Unnamed t) = Unnamed $ replaceIdent id nid t
  rpl  id nid (Named x t) = Named x $ replaceIdent id nid t
  rpl  id nid (Recursive rs) = Recursive (zipWith (\x y -> (fst x , y)) rs (map (replaceIdent id nid . snd) rs))
replaceIdent id nid self@(Mswitch ta tb) = let nta = replaceIdent id nid ta
                                               ntb = map (replaceIdent id nid) (map snd tb)
                                           in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
replaceIdent id nid self@(Mintop1 x y t) = let nt = replaceIdent id nid t
                                           in (Mintop1 x y nt)
replaceIdent id nid self@(Mintop2 x y ta tb ) = let nta = replaceIdent id nid ta
                                                    ntb = replaceIdent id nid tb
                                                in (Mintop2 x y nta ntb )
replaceIdent id nid self@(Mconvert x y t) = let nt = replaceIdent id nid t
                                            in (Mconvert x y nt)
replaceIdent id nid self@(Mvecnew x ta tb) = let nta = replaceIdent id nid ta
                                                 ntb = replaceIdent id nid tb
                                             in (Mvecnew x nta ntb)
replaceIdent id nid self@(Mvecget x ta tb) = let nta = replaceIdent id nid ta
                                                 ntb = replaceIdent id nid tb
                                             in (Mvecget x nta ntb)
replaceIdent id nid self@(Mvecset x ta tb tc) = let nta = replaceIdent id nid ta
                                                    ntb = replaceIdent id nid tb
                                                    ntc = replaceIdent id nid tc
                                                in (Mvecset x nta ntb ntc)
replaceIdent id nid self@(Mveclen x t) = let nt = replaceIdent id nid t
                                         in (Mveclen x nt)
replaceIdent id nid self@(Mblock x bs) = let nbs = map (replaceIdent id nid) bs
                                         in (Mblock x nbs)
replaceIdent id nid self@(Mfield x t) = let nt = replaceIdent id nid t
                                        in (Mfield x t)
replaceIdent id nid x = x

-- First term is the lambda , second one is the Mapply.
createTL:: [Ident] -> Ident -> Term -> TPUIDState (Term , Term)
createTL lids id tm = do
                         let r = findUsedIdents tm -- the idents inside Let.
                             ol = intersect r lids -- those that are local to the function.
                         (nidt , ntm) <- foldM (\(l , t) id -> do nid <- newLUID
                                                                  pure (nid : l , replaceIdent id nid t)) ([] , tm) ol
                         pure (Mlambda nidt ntm , Mapply (Mvar id) (map Mvar ol))
                      

--- We remove let statements and return recursive let statements turned into top-level bindings.
--- We know if Recursive let exists, so we only provide local idents if it does.
-- Assuming that idents are unique, we reuse the ident for the Recursive bindings.

removeLets' :: [Ident] -> Term -> ([Binding] , Term)
removeLets' lids self@(Mvar i) = ([] , self)
removeLets' lids self@(Mlambda a t) = let rm = removeLets' lids t
                                      in (fst rm , Mlambda a (snd rm))
removeLets' lids self@(Mapply a bs) = let (na : nbs) = map (removeLets' lids) (a : bs)
                                      in (fst na ++ (concat $ map fst nbs) , (Mapply (snd na) (map snd nbs))) 
removeLets' lids self@(Mlet bs t) =  let mt = foldr (\x y -> let g = rpl x (snd y)
                                                             in (fst y ++ fst g , snd g)) ([] , t) bs
                                         nt = removeLets' lids (snd mt)
                                     in (fst mt ++ fst nt , snd nt) where
  rpl :: Binding -> Term -> ([Binding] , Term)
  rpl (Unnamed t) tm = ([] , tm)
  rpl (Named x t) tm = ([] , replaceTr (Mvar x) t tm)
  rpl (Recursive rs) tm = let ds = map (\(id , t) -> fst $ runState (createTL lids id t) 0) rs
                          in ( [Recursive (zip (map fst rs) (map fst ds))]
                             , foldr (\(pid , ntm) y -> replaceTr (Mvar pid) ntm y) tm (zip (map fst rs)$ map snd ds))
removeLets' lids self@(Mswitch ta tb) = let nta = removeLets' lids ta
                                            ntb = map (removeLets' lids) (map snd tb)
                                        in (fst nta ++ (concat $ map fst ntb)
                                           , Mswitch (snd nta) (zipWith (\(c , _) nb -> (c , snd nb)) tb ntb))
removeLets' lids self@(Mintop1 x y t) = let nt = removeLets' lids t
                                        in (fst nt  , Mintop1 x y (snd nt))
removeLets' lids self@(Mintop2 x y ta tb ) = let nta = removeLets' lids ta
                                                 ntb = removeLets' lids tb
                                             in (fst nta ++ fst ntb , Mintop2 x y (snd  nta) (snd ntb))
removeLets' lids self@(Mconvert x y t) = let nt = removeLets' lids t
                                         in (fst nt , Mconvert x y (snd nt))
removeLets' lids self@(Mvecnew x ta tb) = let nta = removeLets' lids ta
                                              ntb = removeLets' lids tb
                                          in (fst nta ++ fst ntb , Mvecnew x (snd nta) (snd ntb))
removeLets' lids self@(Mvecget x ta tb) = let nta = removeLets' lids ta
                                              ntb = removeLets' lids tb
                                          in (fst nta ++ fst ntb , Mvecget x (snd nta) (snd ntb))
removeLets' lids self@(Mvecset x ta tb tc) = let nta = removeLets' lids ta
                                                 ntb = removeLets' lids tb
                                                 ntc = removeLets' lids tc
                                             in (fst nta ++ fst ntb ++ fst ntc , Mvecset x (snd nta) (snd ntb) (snd ntc))
removeLets' lids self@(Mveclen x t) = let nt = removeLets' lids t
                                      in (fst nt , Mveclen x (snd nt))
removeLets' lids self@(Mblock x bs) = let nbs = map (removeLets' lids) bs
                                      in (concat (map fst nbs) , Mblock x (map snd nbs))
removeLets' lids self@(Mfield x t) = let nt = removeLets' lids t
                                     in (fst nt , Mfield x (snd nt))
removeLets' lids x = ([] , x)
 

-- [Binding] is not necessary at all since the treeless syntax does not have recursive let statements.
removeLet :: Term -> ([Binding] , Term)
removeLet tm = case (doLetExist tm) of
                (False , _) -> ([] , tm)
                (True , False) -> removeLets' [] tm
                (True , True) -> removeLets' (findLocalIdents tm) tm





----------------------------------------------------------------------------

type UIDState = State (Integer , Integer)

newUID :: UIDState String
newUID = do
  s <- gets (show . fst)
  modify (\(a , b) -> (1 + a , b))
  pure $ "letId" ++ s

-- newOID must be called after the recursive part, so that first MApplys will get a lower number.
newOID :: UIDState Integer
newOID = do
  s <- gets snd
  modify (\(a , b) -> (a , (1 + b)))
  pure s

-- TODO The algorithm can be better.
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
replaceTr rt ar self@(Mlet bs t) =  let nt = replaceTr rt ar t
                                       in Mlet (map (rpl rt ar) bs) nt where
  rpl :: Term -> Term -> Binding -> Binding
  rpl rt ar (Unnamed t) = Unnamed $ replaceTr rt ar t
  rpl rt ar (Named x t) = Named x $ replaceTr rt ar t
  rpl rt ar (Recursive rs) = Recursive (zipWith (\x y -> (fst x , y)) rs (map (replaceTr rt ar . snd) rs))
replaceTr rt ar self@(Mswitch ta tb) = let nta = replaceTr rt ar ta
                                           ntb = map (replaceTr rt ar) (map snd tb)
                                       in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
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
                                    in (Mfield x nt)
replaceTr rt ar x = x
