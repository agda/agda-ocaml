module Agda.Compiler.Malfunction.Optimize where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Malfunction.EraseDefs
import Agda.Compiler.Common
import Data.List
import Data.Bool
import qualified Data.Map.Strict as M

import Control.Monad.State


--- We remove let statements . According to a treeless comment https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Treeless.hs#L44 , this is perfectly reasonable.

removeLets :: Term -> Term
removeLets self@(Mvar i) = self
removeLets self@(Mlambda a t) = let rm = removeLets t
                                in Mlambda a rm
removeLets self@(Mapply a bs) = let (na : nbs) = map removeLets (a : bs)
                                in Mapply na nbs 
removeLets self@(Mlet bs t) =  let mt = foldr (\x y -> let g = rpl x y
                                                       in g            ) t bs
                                   nt = removeLets mt
                               in nt where
  rpl :: Binding -> Term -> Term
  rpl (Unnamed t) tm = error "Let bindings should have a name."
  rpl (Named x t) tm = replaceTr (Mvar x) t tm
  rpl (Recursive rs) tm = error "Let bindings cannot be recursive."
  
removeLets self@(Mswitch ta tb) = let nta = removeLets ta
                                      ntb = map removeLets (map snd tb)
                                  in Mswitch nta (zipWith (\(c , _) nb -> (c , nb)) tb ntb)
removeLets self@(Mintop1 x y t) = let nt = removeLets t
                                  in Mintop1 x y nt
removeLets self@(Mintop2 x y ta tb ) = let nta = removeLets ta
                                           ntb = removeLets tb
                                       in Mintop2 x y nta ntb
removeLets self@(Mconvert x y t) = let nt = removeLets t
                                   in Mconvert x y nt
removeLets self@(Mvecnew x ta tb) = let nta = removeLets ta
                                        ntb = removeLets tb
                                    in Mvecnew x nta ntb
removeLets self@(Mvecget x ta tb) = let nta = removeLets ta
                                        ntb = removeLets tb
                                    in Mvecget x nta ntb
removeLets self@(Mvecset x ta tb tc) = let nta = removeLets ta
                                           ntb = removeLets tb
                                           ntc = removeLets tc
                                       in Mvecset x nta ntb ntc
removeLets self@(Mveclen x t) = let nt = removeLets t
                                in Mveclen x nt
removeLets self@(Mblock x bs) = let nbs = map removeLets bs
                                in Mblock x nbs
removeLets self@(Mfield x t) = let nt = removeLets t
                               in Mfield x nt
removeLets x =  x
 





----------------------------------------------------------------------------

type UIDState = State (Integer , Integer)

-- We use this for the new Let vars.
newUID :: UIDState String
newUID = do
  s <- gets (show . fst)
  modify (\(a , b) -> (1 + a , b))
  pure $ "letId" ++ s

-- newOID must be called after the recursive part, so that first MApplys will get a lower number.
-- We use this to order possible lets. (ie MApplys).
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

lintersect :: [M.Map Term (Term , Integer , Bool)] -> M.Map Term (Term , Integer , Bool)
lintersect (m : ms@(m2 : ms2)) = M.union (foldr (\a b -> M.intersection a b) m ms) (lintersect ms)
lintersect (m : []) = M.empty
lintersect [] = M.empty



findCF :: Term -> UIDState (M.Map Term (Term , Integer , Bool) , Term)
findCF self@(Mvar i) = pure (M.empty , self)
findCF self@(Mlambda ids t) = do
                                (tms , nself) <- findCF t
                                pure (tms , Mlambda ids nself)
-- We need to perform findCF on a and bs when we create the let statement.
findCF self@(Mapply a bs) = do
                              rs <- mapM findCF (a : bs)
                              let inters = lintersect (map fst rs)
                                  newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                  all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                  -- newInters replaces inters here.
                                  nall = newInters `M.union` all
                                  (na , nbs) = (snd $ head rs , map snd (tail rs))
                                  nself = Mapply na nbs
                              noid <- newOID
                              pure (M.insert self (nself , noid , False) nall , nself )
findCF self@(Mlet bs t) = error "We have removed all let statements"

-- We have to put all new let statements after the switch.
findCF self@(Mswitch ta tb) =  do
  (tmsa , nta) <- findCF ta
  rb <- mapM (findCF . snd) tb
  let inters = lintersect (tmsa : (map fst rb))
      newInters = M.map (\(a , b , c) -> (a , b , True)) inters
      all = foldr (\a b -> M.union (fst a) b)  M.empty rb
      -- newInters replaces inters here.
      nall = newInters `M.union` all
      ntb = zip (map fst tb) (map snd rb)
  pure (nall , Mswitch nta ntb)
  where
 
  singleCase :: Term -> UIDState (M.Map Term (Term , Integer , Bool) , Term)
  singleCase t = do
                    r <- findCF t
                    let psLets = M.filter (\(a , b , c) -> c) (fst r)
                        lo = sort $ M.foldrWithKey (\k (a , b , c) l -> (b , a , k) : l) [] psLets
                        all = lo ++ [(0 , snd r , snd r)] -- last and first term should never be used for r.
                    rs <- replaceRec all
                    let bs = createBinds (zip (map fst rs) (map (\(_ , (_ , t , _)) -> t) rs))
                    -- Return them with false so as to be possibly matched with higher statements.
                    let nr = M.union (M.fromList $ map (\(_ , (i , t , k)) -> (k , (t , i , False))) rs) (fst r)
                    pure $ (nr , Mlet bs ((\(_ , (_ , t , _)) -> t) (last rs)))

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
                              
                                 let inters = lintersect (map fst rs)
                                     newInters = M.map (\(a , b , c) -> (a , b , True)) inters
                                     all = foldr (\a b -> M.union (fst a) b)  M.empty rs
                                     nall = newInters `M.union` all
                                 pure (nall , (Mblock x (map snd rs)))
findCF  self@(Mfield x t) =   do (tms , nself) <- findCF  t
                                 pure (tms , (Mfield x nself))
findCF  x = pure (M.empty , x)



introduceLets' :: Term -> Term
introduceLets' t = fst $
  runState (do 
               r <- findCF t
               -- All the remaining matches are introduced at the top.
               let psLets = M.filter (\(a , b , c) -> c) (fst r)
                   lo = sort $ M.foldrWithKey (\k (a , b , c) l -> (b , a , k) : l) [] psLets
                   all = lo ++ [(0 , snd r , snd r)] -- last and first term should never be used for r.
               rs <- replaceRec all
               let bs = createBinds (zip (map fst rs) (map (\(_ , (_ , t , _)) -> t) rs))
               pure $ Mlet bs ((\(_ , (_ , t , _)) -> t) (last rs))
           ) (0 , 0)



-- Used in Functions.
introduceLets :: Term -> Term
introduceLets (Mlambda ids t) = Mlambda ids (introduceLets' t)
introduceLets _ = error "This is a supposed to be a function."




createBinds :: [(String , Term)] -> [Binding]
createBinds [] = []
createBinds ((var , term) : ns) = Named var term : createBinds ns

-- Second Term is the initial one and we need it to use it as a key, so we pass it at the result.
replaceRec :: [(Integer , Term , Term)] -> UIDState [(String , (Integer , Term , Term))]
replaceRec ((i , t , k) : []) = pure $ ("ERROR" , (i , t , k)) : []
replaceRec ((i , t , k) : ts) =  do ar <- newUID
                                    let rs = map (replaceTr t (Mvar ar)) (map (\(i , t , k) -> t)  ts)
                                    nvs <- replaceRec
                                             (zip3 (map (\(i , _ , _) -> i) ts) rs (map (\(_ , _ , k) -> k) ts))
                                    pure $ (ar , (i , t , k)) : nvs



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
