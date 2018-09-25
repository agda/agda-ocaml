module Agda.Compiler.Malfunction.EraseDefs (eraseB) where

import Agda.Compiler.Malfunction.AST
import Agda.Compiler.Common
import Data.List
import qualified Data.Map.Strict as M

findAllIdents :: [Binding] -> [(Ident , Term)]
findAllIdents ((Named id t) : xs) = (id , t) : findAllIdents xs
findAllIdents (Recursive ys : xs) = ys ++ findAllIdents xs
findAllIdents (_ : xs) = findAllIdents xs
findAllIdents [] = []

toTerm :: Binding -> Term
toTerm (Named _ t) = t
toTerm _ = undefined

findMain :: [(Ident , Term)] -> Maybe (Ident , Term)
findMain ms = let fms = filter (\(x , t) -> "main" `isSuffixOf` x) ms
              in case fms of
                  [] -> Nothing
                  [x] -> Just x
                  (_ : _) -> error "Multiple functions with the name main exist."


findAllUsedBindings :: M.Map Ident Term -> Term -> M.Map Ident Term
findAllUsedBindings env t = let nid = foldr (++) [] (map (\x -> case (M.lookup x env) of
                                                                  Just a -> [(x , a)]
                                                                  _ -> []) (findUsedIdents t))
                                newItems = M.fromList nid
                                nEnv = M.difference env newItems
                            in  snd $ foldr (\(id , t) (env , items) -> let ni = findAllUsedBindings env t in (M.difference env ni , M.union ni items)) (nEnv , newItems) nid
                                

-- The list is greater than the global lists because we have local identifiers.
findUsedIdents :: Term -> [Ident]
findUsedIdents (Mvar i) = i : []
findUsedIdents (Mlambda _ t) = findUsedIdents t
findUsedIdents (Mapply a bs) = findUsedIdents a ++ (foldr (++) [] (map findUsedIdents bs))
findUsedIdents (Mlet bs t) =  foldr (++) (findUsedIdents t) (map (\x -> findUsedIdents $ toTerm x) bs)
findUsedIdents (Mswitch ta tb) = foldr (++) (findUsedIdents ta) (map (\x -> findUsedIdents $ snd x) tb)
findUsedIdents (Mintop1 _ _ t) = findUsedIdents t
findUsedIdents (Mintop2 _ _ ta tb ) = findUsedIdents ta ++ findUsedIdents tb
findUsedIdents (Mconvert _ _ t) = findUsedIdents t
findUsedIdents (Mvecnew _ ta tb) = findUsedIdents ta ++ findUsedIdents tb
findUsedIdents (Mvecget _ ta tb) = findUsedIdents ta ++ findUsedIdents tb
findUsedIdents (Mvecset _ ta tb tc) = findUsedIdents ta ++ findUsedIdents tb ++ findUsedIdents tc
findUsedIdents (Mveclen _ t) = findUsedIdents t
findUsedIdents (Mblock _ bs) = foldr (++) [] (map findUsedIdents bs)
findUsedIdents (Mfield _ t) = findUsedIdents t
findUsedIdents _ = []


eraseB :: [Binding] -> (IsMain , [Binding])
eraseB bs = let allIds = findAllIdents bs
                mmain = findMain allIds
            in case mmain of
                 Just main ->
                   let env = M.delete (fst main) (M.fromList allIds)
                       allUM = M.insert (fst main) (snd main) (findAllUsedBindings env (snd main))
                       -- We order them according to the original Order.
                   in (IsMain , foldr (\x osum -> case x of
                                          Named id t ->  case (M.lookup id allUM) of
                                                           Just _ -> x : osum
                                                           _ -> osum
                                          Recursive ys -> let rs = filter (\(id , _) -> case (M.lookup id allUM) of
                                                                                         Just _ -> True
                                                                                         _ -> False ) ys in case rs of
                                                                                                              [] -> osum
                                                                                                              _ -> Recursive rs : osum) [] bs )
                 Nothing -> (NotMain , bs)
