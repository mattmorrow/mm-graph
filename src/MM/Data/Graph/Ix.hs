{-# OPTIONS -pgmP cpp -optP-w #-}
{-# LANGUAGE
      CPP,
      MagicHash,
      BangPatterns,
      OverlappingInstances,
      UndecidableInstances,
      IncoherentInstances #-}
#define __D deriving(Eq,Ord,Read,Show)
#define __D_BE deriving(Eq,Ord,Read,Show,Bounded,Enum)
#ifdef __DEBUG_ON
#define __IF_DEBUG(on,off) on
#else
#define __IF_DEBUG(on,off) off
#endif
#define __DEBUG(o)  __IF_DEBUG(o,)
#define __PANIC(what,note)\
  (error(concat[__FILE__,":",show(__LINE__),":[",(what),"]:",(note)]))
#define __BUG(note)     __PANIC("BUG",note)
#define __FIXME(note)   __PANIC("FIXME",note)
#define __IMPOSSIBLE    __BUG("impossible")
#define __ASSERT(cond)  __IF_DEBUG(__ASSERT_DO(cond),True)
#define __ASSERT_FAIL(note) __PANIC("ASSERT",note)
#define __ASSERT_DO(cond)\
  (if (cond) then True else (__ASSERT_FAIL(#cond)))
#define HASH #
#define __INLINE(x) {-HASH INLINE x HASH-}

module MM.Data.Graph.Ix (
   Graph,PredGraph,Node,NodeMap,NodeSet

  ,Cover(..),Partition(..),IsPartition(..),Injection(..)
  ,Components(..)

  ,isLegal,legalize,nodes
  ,invert,predGraph,succGraph,invertForest
  ,fromAdj,toAdj
  ,quotientGraph,inducedSubgraph,inducedSubgraphs

  ,DomTree(..),domTreeInit,domTreeRevPostOrder
  ,DomFront,domFrontInit,domFront
  ,DomFrontPlus,domFrontPlusInit,domFrontPlus

  ,CC
  ,ccInit
  ,ccGetCompNodes,ccGetNodeComp,ccGetCompGraph

  ,SCC,Cyclicity(..)
  ,sccInit
  ,sccTopo,sccTopoAssertAcyclic
  ,sccGetCompNodes,sccGetNodeComp
  ,sccAcyclicComps,sccCyclicComps,sccCompsWithCyclicity
  ,sccAcyclicNodes,sccCyclicNodes,sccNodesWithCyclicity

  ,DFN,DFNEdge(..)
  ,dfnInit
  ,dfnClassifyEdge
  ,dfnN2Pre,dfnN2Post,dfnPre2N,dfnPost2N
  ,dfnPre,dfnPost
  ,dfnPreOrder,dfnPostOrder,dfnRevPreOrder,dfnRevPostOrder

  ,PartRefine,EdgeLbl,EdgeLblMap,DeltaInv,updateDeltaInv
  ,PartRefinePrep(..)
  ,partRefineInit -- :: Partition -> DeltaInv -> PartRefine
  ,partRefinePartition
  ,partRefineDeltaInv
  ,partRefineRefine -- :: PartRefine -> PartRefine

  ,NodeKeyed(..),NodeKey(..)

  ,shareOneLevel
  ,shareAcyclic
  ,shareCyclic
  ,flattenAcyclicToOneLevel
) where

import Prelude hiding(null)
import qualified Prelude as P
import Data.Int
import Data.Word
import Data.Bits
import MM.Data.Map.Ord(Map)
import MM.Data.Set.Ord(Set)
import MM.Data.Map.Int(IntMap)
import MM.Data.Set.Int(IntSet)
import qualified MM.Data.Map.Ord as OM
import qualified MM.Data.Set.Ord as OS
import qualified MM.Data.Map.Int as IM
import qualified MM.Data.Set.Int as IS
import Data.Monoid(Monoid(..))
import Control.Applicative(Applicative(..))
import Control.Monad
import Data.Function
import Data.List(foldl')
import MM.Data.Tree.Rose(Tree(..))
import qualified MM.Control.Monad.S.U as SU
import qualified MM.Control.Monad.S.U2 as SU2
import qualified MM.Control.Monad.Class as N
import MM.Data.Types.Ix
import MM.Data.Map.Ix(IxMap)
import MM.Data.Set.Ix(IxSet)
import MM.Data.Trie.Ix(IxTrie)
import qualified MM.Data.Map.Ix as Ix
import qualified MM.Data.Set.Ix as IxS
import qualified MM.Data.Trie.Ix as IxT
import MM.Data.UnionFind.Ix(UF)
import qualified MM.Data.UnionFind.Ix as U
import qualified MM.Data.Class.UnionFind.Ix as UF
import MM.Data.Class.Base
import qualified MM.Data.Class.Maps as M

-----------------------------------------------------------------------------

-- | .
type Node a = Ix a
type NodeMap a b = IxMap a b
type NodeSet a = NodeMap a ()
type Graph a = NodeMap a (NodeSet a)
type PredGraph a = Graph a

data Components a b x = Comps
  {compsPart :: Partition a b
  ,compsData :: x}
  __D

type Cover a b = (NodeMap a (NodeSet b), NodeMap b (NodeSet a))
type Partition a b  = (NodeMap a (Node b), NodeMap b (NodeSet a))
type Injection a b = (NodeMap a (Node b), NodeMap b (Node a), NodeMap b ())

class IsPartition a b x where
  toPartition :: x -> Partition a b
  fromPartition :: Partition a b -> x
instance IsPartition a b (NodeMap a (Node b)) where
  fromPartition = fst
  toPartition n2i
    | i2ns <- Ix.foldWithKey go mempty n2i
    = (n2i, i2ns)
    where go n i o = Ix.insertWith (\/) i (Ix.singleton n ()) o
instance IsPartition a b (NodeMap b (NodeSet a)) where
  fromPartition = snd
  toPartition i2ns
    | n2i <- Ix.foldWithKey go mempty i2ns
    = (n2i, i2ns)
    where go i ns o = Ix.foldWithKey (\n _ o-> Ix.insert n i o) o ns
instance IsPartition a b [NodeSet a] where
  fromPartition p
    | i2ns <- fromPartition p :: NodeMap b (NodeSet a)
    = Ix.elems i2ns
  toPartition xs
    | i2ns <- Ix.fromList (zip [0..] xs) :: NodeMap b (NodeSet a)
    = toPartition i2ns

-----------------------------------------------------------------------------

-- | All graph algorithms ASSUME a "legal" graph. See @legalize@.
isLegal :: Graph a -> Bool
isLegal g = Ix.size (g `Ix.difference` nodes g) == 0

-- | Ensures every node is present in the domain of the map.
legalize :: Graph a -> Graph a
legalize g = g \/ fmap (const mempty) (nodes g)

nodes :: Graph a -> NodeSet a
nodes g = Ix.foldWithKey go mempty g
  where go i is acc = Ix.insert i () (acc \/ is)

-----------------------------------------------------------------------------

invert :: Graph a -> Graph a
invert g = Ix.foldWithKey go (fmap (const mempty) g) g
  where go :: Node a -> NodeSet a -> Graph a -> Graph a
        go i js acc
          | !is <- Ix.singleton i ()
          , !acc <- Ix.insertWith (\/) i mempty acc
          = Ix.foldWithKey (\j _ acc-> Ix.insertWith (\/) j is acc) acc js

predGraph :: Graph a -> PredGraph a
succGraph :: PredGraph a -> Graph a
predGraph = invert
succGraph = invert

invertForest :: NodeMap a (Node a) -> Graph a
invertForest = Ix.foldWithKey go mempty
  where go i j o = Ix.insertWith (\/) j (Ix.singleton i ()) o

-----------------------------------------------------------------------------

fromAdj :: [(Node a, [Node a])] -> Graph a
fromAdj = fmap (\is-> Ix.fromList (zip is (repeat ()))) . Ix.fromList

toAdj :: Graph a -> [(Node a, [Node a])]
toAdj = Ix.toList . fmap Ix.keys

-----------------------------------------------------------------------------

quotientGraph :: Graph a -> Partition a b -> Graph a
quotientGraph g _ = __FIXME("quotientGraph")

inducedSubgraph :: Graph a -> NodeSet a -> Graph a
inducedSubgraph g ns = Ix.foldWithKey (\i is acc->
    let !js = is`Ix.intersection`ns
    in Ix.insert i js acc
  ) mempty (g`Ix.intersection`ns)

inducedSubgraphs :: Graph a -> Partition a b -> IxMap b (Graph a)
inducedSubgraphs g = fmap (inducedSubgraph g) . fromPartition

-----------------------------------------------------------------------------

newtype CC a = CC {unCC :: Components a (CC a) (CCData a)} __D
newtype CCData a = CCData
  {ccDataTo :: NodeMap (CC a) (Graph a)} __D
instance Empty (CCData a) where
  empty = CCData empty
  isEmpty o = o==empty
instance Monoid (CCData a) where
  mempty = CCData mempty
  mappend (CCData a1) (CCData a2)
    | !a <- mappend a1 a2
    = CCData a

ccInit :: forall a. Graph a -> CC a
ccInit g
  | uf <- singletons g
  , (_,uf) <- Ix.foldWithKey (go g) (mempty,uf) g
  , (i2x,x2g) <- UF.quotient uf
  , i2x <- Ix.castIxMap i2x :: IxMap a (Ix (CC a))
  , compsPart <- toPartition i2x
  , compsData <- CCData x2g
  = CC Comps{..}
  where go
          :: Graph a
          -> Ix a
          -> dontcare
          -> (IxMap a (), UF (CC a) (Graph a))
          -> (IxMap a (), UF (CC a) (Graph a))
        go g i _ (seen,uf)
          | i`Ix.member`seen
          = (seen,uf)
          | is <- g Ix.! i
          , xi <- castIx i :: Ix (CC a)
          , !seen <- Ix.insert i () seen
          , !uf <- Ix.foldWithKey (\j _ uf->
              UF.unionWith_ (\/) uf xi (castIx j)) uf is
          = Ix.foldWithKey (go g) (seen,uf) is
        singletons :: Graph a -> UF (CC a) (Graph a)
        singletons = flip Ix.foldWithKey mempty
          (\i is acc-> UF.unsafeInsert acc (castIx i::Ix (CC a))
            (Ix.singleton i is))

ccGetCompNodes :: CC a -> Node (CC a) -> NodeSet a
ccGetCompNodes (CC Comps{compsPart=(_,c2ns)}) comp = c2ns Ix.! comp

ccGetNodeComp :: CC a -> Node a -> Node (CC a)
ccGetNodeComp (CC Comps{compsPart=(n2c,_)}) node = n2c Ix.! node

ccGetCompGraph :: CC a -> Node (CC a) -> Graph a
ccGetCompGraph (CC Comps{compsData=CCData{..}}) comp
  = Ix.findWithDefault mempty comp ccDataTo

-----------------------------------------------------------------------------

#if 0
data NCA a = NCA
  {ncaDFN :: DFN a
  ,ncaRoot :: !(Ix a)
  ,ncaParent :: UF a (Ix a)
  ,ncaDFNPostLo :: IxMap a Int
  ,ncaDFNPostHi :: IxMap a Int
  } __D
ncaInit :: Tree a -> Ix a -> NCA a
ncaInit g root = undefined
-- |
-- > nca(i,j)
-- > {
-- >   cases
-- >     i==j-> return i
-- >     dfnpost[i] < dfnpost[j]-> go(i,j,dfnpost[i],dfnpost[j])
-- >     dfnpost[i] > dfnpost[j]-> go(j,i,dfnpost[j],dfnpost[i])
-- > }
-- > go(i,j,ni,nj)
-- > {
-- >   assert(i != j)
-- >   assert(ni < nj)
-- >   if(dfnlo[j] <= ni && ni <= dfnhi[j])
-- >     return j
-- >   fi <- i
-- >   fj <- j
-- >   while(fi != fj)
-- >   {
-- >     while(fi < fj)
-- >       fi <- FIND(parent,fi)
-- >     while(fj < fi)
-- >       fj <- FIND(parent,fj)
-- >   }
-- >   return fi
-- > }
nca :: NCA a -> Ix a -> Ix a -> (Ix a, NCA a)
nca NCA{..} i j = undefined
#endif

-----------------------------------------------------------------------------

data DomTree a = DomTree
  {domTreeDFN :: DFN a
  ,domTreeRoot :: !(Node a)
  ,domTreeParent :: NodeMap a (Node a)
  ,domTreeChildren :: Graph a
  } __D

domTreeInit :: PredGraph a -> DFN a -> Node a -> DomTree a
domTreeInit preds dfn root
  | domTreeRoot <- root
  , domTreeParent <- idomInit preds dfn root
  , domTreeChildren <- legalize (invertForest domTreeParent)
  , domTreeDFN <- dfnInit domTreeChildren domTreeRoot
  = DomTree{..}

domTreeRevPostOrder :: DomTree a -> [Node a]
domTreeRevPostOrder DomTree{domTreeDFN=o} = dfnRevPostOrder o

idomInit_ :: Graph a -> Node a -> NodeMap a (Node a)
idomInit_ succs root
  | dfn <- dfnInit succs root
  , preds <- invert succs
  = idomInit preds dfn root

-- | The "Simple Fast" immediate dominators algorithm.
idomInit :: forall a. PredGraph a -> DFN a -> Node a -> NodeMap a (Node a)
idomInit preds dfn root
  | dfnpost <- dfnN2Post dfn
  , dfnpostinv <- dfnPost2N dfn
  = idom dfnpost dfnpostinv preds root
  where idom
          :: NodeMap a Int      -- PostDfn
          -> IntMap (Node a)    -- PostDfnInv
          -> PredGraph a        -- PREDECESSORS
          -> Node a             -- root
          -> NodeMap a (Node a) -- idom
        idom dfn dfninv preds root = while (Ix.singleton root root)
          where rpo = drop 1 (reverse (IM.elems dfninv))
                while :: NodeMap a (Node a) -> NodeMap a (Node a)
                while idom
                  | (changed,idom) <- foldl' go (False,idom) rpo
                  = if changed then while idom else idom
                go :: (Bool, NodeMap a (Node a)) -> Node a -> (Bool, NodeMap a (Node a))
                go acc@(changed,idom) i
                  | ps <- (preds Ix.! i)`Ix.intersection`idom
                  , not (Ix.null ps)
                  , j <- minKeyWithDefault 0 ps
                  , js <- Ix.delete j ps
                  , let loop k _ newidom = intersect dfn idom k newidom
                  , newidom <- Ix.foldWithKey loop j js
                  , case Ix.lookup i idom of
                      Just x-> x/=newidom
                      Nothing-> True
                  , !idom <- Ix.insert i newidom idom
                  = (True,idom)
                  | otherwise = acc
                minKeyWithDefault dflt m
                  | Just ((k,_),_) <- Ix.minViewWithKey m = k
                  | otherwise = dflt
                intersect
                  :: NodeMap a Int      -- PostDfn
                  -> NodeMap a (Node a) -- parent
                  -> Node a -> Node a -> Node a
                intersect dfn parent i j = go i j
                  where go :: Node a -> Node a -> Node a
                        go i j
                          | i==j = i
                          | i <- walk i j
                          , j <- walk j i
                          = go i j
                        walk :: Node a -> Node a -> Node a
                        walk i j = loop (dfn Ix.! j) i
                          where loop !nj !i
                                  | ni <- dfn Ix.! i
                                  , ni < nj
                                  = loop nj (parent Ix.! i)
                                  | otherwise = i

-----------------------------------------------------------------------------

data DomFront a = DomFront
  {domFrontDF :: NodeMap a (NodeSet a)}
  __D

-- |
-- > domFrontInit()
-- > {
-- >   df :: Map Node (Set Node)
-- >   for(each X in a bottom-up traversal of the domTree)
-- >   {
-- >     df[X] <- {}
-- >     for(each Y in succ(X))
-- >       if idom[Y] != X
-- >         df[X] <- df[X] \/ {Y}   //local
-- >     for(each Z in children(X))
-- >       for(each Y in df[Z])
-- >         if(idom[Y] != X)
-- >           df[X] <- df[X] \/ {Y} //up
-- >   }
-- >   return df
-- > }
domFrontInit :: DomTree a -> Graph a -> DomFront a
domFrontInit DomTree{..} g
  | todo <- dfnRevPreOrder domTreeDFN
  , domFrontDF <- foldl' loop (fmap (const mempty) g) todo
  = DomFront{..}
  where loop o x = up x (local x o)
        local x o = Ix.foldWithKey go o (g Ix.! x)
          where go y _ o
                  | x /= domTreeParent Ix.! y
                  , new <- Ix.insert y () (o Ix.! x)
                  = Ix.insert x new o
                  | otherwise = o
        up x o = Ix.foldWithKey fold o (domTreeChildren Ix.! x)
          where fold z _ o = Ix.foldWithKey go o (o Ix.! z)
                  where go y _ o
                          | x /= domTreeParent Ix.! y
                          , new <- Ix.insert y () (o Ix.! x)
                          = Ix.insert x new o
                          | otherwise = o

domFront :: DomFront a -> Node a -> NodeSet a
domFront DomFront{..} i = Ix.findWithDefault mempty i domFrontDF

-----------------------------------------------------------------------------

data DomFrontPlus a = DomFrontPlus
  {domFrontPlusDF :: DomFront a
  ,domFrontPlusDFPlus :: NodeMap a (NodeSet a)}
  __D

-- |
-- > ghci> let g = fromAdj [(1,[2]),(2,[3,4]),(3,[5]),(4,[5,6]),(5,[6,2]),(6,[])]
-- > ghci> isLegal g == (g == legalize g)
-- > True
-- > ghci> let domtree = domTreeInit (predGraph g) (dfnInit g 1) 1
-- > ghci> let df = domFrontInit domtree g
-- > ghci> let dfplus n DomFront{..} | domFrontDF <- loop n domFrontDF = DomFront{..} where {loop n df | n <= 1 = df | df <- Ix.foldWithKey go df df = loop (n - 1) df where {go x ys df | zs <- Ix.foldWithKey (\y _ o-> o \/ (df Ix.! y)) ys ys = Ix.insert x zs df}}
-- > ghci> mapM_ print $ fmap (\x-> (unIx x, fmap unIx $ Ix.keys $ domFront (dfplus 1df) x)) [1..6]
-- > (1,[])
-- > (2,[2])
-- > (3,[5])
-- > (4,[5,6])
-- > (5,[2,6])
-- > (6,[])
-- > ghci> mapM_ print $ fmap (\x-> (unIx x, fmap unIx $ Ix.keys $ domFront (dfplus 2 df) x)) [1..6]
-- > (1,[])
-- > (2,[2])
-- > (3,[2,5,6])
-- > (4,[2,5,6])
-- > (5,[2,6])
-- > (6,[])
-- > ghci> mapM_ print $ fmap (\x-> (unIx x, fmap unIx $ Ix.keys $ domFront (dfplus 3 df) x)) [1..6]
-- > (1,[])
-- > (2,[2])
-- > (3,[2,5,6])
-- > (4,[2,5,6])
-- > (5,[2,6])
-- > (6,[])
--
domFrontPlusInit :: DomFront a -> DomFrontPlus a
domFrontPlusInit df = __FIXME("domFrontPlusInit")

domFrontPlus :: DomFrontPlus a -> Node a -> (NodeSet a, DomFrontPlus a)
domFrontPlus dfp i = __FIXME("domFrontPlus")

-----------------------------------------------------------------------------

newtype SCC a = SCC {unSC :: Components a (SCC a) (SCCData a)} __D
data SCCData a = SCCData
  {sccDataTo :: NodeMap (SCC a) Cyclicity
  ,sccDataFrom :: Map Cyclicity (NodeSet (SCC a))} __D
data Cyclicity = Acyclic | Cyclic __D_BE
instance Empty (SCCData a) where
  empty = SCCData empty empty
  isEmpty o = o==empty
instance Monoid (SCCData a) where
  mempty = SCCData mempty mempty
  mappend (SCCData a1 b1) (SCCData a2 b2)
    | !a <- mappend a1 a2
    , !b <- mappend b1 b2
    = SCCData a b

sccInit :: forall a. Graph a -> SCC a
sccInit g
  | sccs <- sccEnvSCCs (execSccM sccTarjanM (initSCCEnv g))
  , comps <- Ix.fromList . zip [0..] . reverse $ sccs
  , compsPart <- toPartition comps
  , compsData <- Ix.foldWithKey go mempty comps
  = SCC Comps{..}
  where go :: Node (SCC a) -> NodeSet a -> SCCData a -> SCCData a
        go comp ns SCCData{..}
          | cyc <- cyclicity ns
          , sccDataTo <- Ix.insert comp cyc sccDataTo
          , sccDataFrom <- OM.insertWith (\/) cyc
              (Ix.singleton comp ()) sccDataFrom
          = SCCData{..}
        cyclicity :: NodeSet a -> Cyclicity
        cyclicity ns
          | Just ((n,_),rest) <- Ix.minViewWithKey ns
          = case Ix.null rest of
              False-> Cyclic
              True
                | n`Ix.member`(Ix.findWithDefault mempty n g)-> Cyclic
                | otherwise-> Acyclic
          | otherwise = __IMPOSSIBLE

sccGetCompNodes :: SCC a -> Node (SCC a) -> NodeSet a
sccGetCompNodes (SCC Comps{compsPart=(_,c2ns)}) comp = c2ns Ix.! comp

sccGetNodeComp :: SCC a -> Node a -> Node (SCC a)
sccGetNodeComp (SCC Comps{compsPart=(n2c,_)}) node = n2c Ix.! node

sccAcyclicComps :: SCC a -> NodeSet (SCC a)
sccAcyclicComps = sccCompsWithCyclicity Acyclic

sccCyclicComps :: SCC a -> NodeSet (SCC a)
sccCyclicComps = sccCompsWithCyclicity Cyclic

sccCompsWithCyclicity :: Cyclicity -> SCC a -> NodeSet (SCC a)
sccCompsWithCyclicity cyc (SCC Comps{compsData=SCCData{..}})
  = OM.findWithDefault mempty cyc sccDataFrom

sccAcyclicNodes :: SCC a -> NodeSet a
sccAcyclicNodes = sccNodesWithCyclicity Acyclic

sccCyclicNodes :: SCC a -> NodeSet a
sccCyclicNodes = sccNodesWithCyclicity Cyclic

sccNodesWithCyclicity :: Cyclicity -> SCC a -> NodeSet a
sccNodesWithCyclicity cyc (SCC Comps{compsData=SCCData{..},..})
  | comps <- OM.findWithDefault mempty cyc sccDataFrom
  , (_,c2ns) <- compsPart
  , let go i _ o = o \/ (c2ns Ix.! i)
  = Ix.foldWithKey go mempty comps

sccTopo :: SCC a -> [NodeSet a]
sccTopo (SCC Comps{compsPart}) = fromPartition compsPart

sccTopoAssertAcyclic :: SCC a -> Either (NodeSet (SCC a)) [Node a]
sccTopoAssertAcyclic scc
  | cyclic <- sccCyclicComps scc
  = case Ix.null cyclic of
      True-> Right (Ix.keys =<< sccTopo scc)
      False-> Left cyclic

-- {{{
type SccM x a = SU.S (SCCEnv x) a
data SCCEnv x = SCCEnv
  {sccEnvGraph   :: Graph x
  ,sccEnvIndex   :: NodeMap x Int
  ,sccEnvLowLink :: NodeMap x Int
  ,sccEnvStacked :: NodeSet x
  ,sccEnvStack   :: [Node x]
  ,sccEnvSCCs    :: [NodeSet x]}
execSccM :: SccM x a -> SCCEnv x -> SCCEnv x
execSccM m env | (_,(_,env)) <- N.runM m 0 env = env
initSCCEnv :: Graph x -> SCCEnv x
initSCCEnv g = SCCEnv
  {sccEnvGraph   = g
  ,sccEnvIndex   = mempty
  ,sccEnvLowLink = mempty
  ,sccEnvStacked = mempty
  ,sccEnvStack   = []
  ,sccEnvSCCs    = []}
sccTarjanM :: SccM x ()
sccTarjanM = mapM_ go =<< N.gets (Ix.keys . nodes . sccEnvGraph)
  where go i = do
          o <- sccSeenM i
          case o of
            False-> sccM i
            True-> return ()
sccM :: Node x -> SccM x ()
sccM i = do
  sccPushM i
  ss <- sccSuccsM i
  mapM_ (sccDoSuccM i) (Ix.keys ss)
  ix <- sccIndexM i
  ll <- sccLowLinkM i
  case ix==ll of
    True-> sccPopToAndAddSccM i
    False-> return ()
sccDoSuccM :: Node x -> Node x -> SccM x ()
sccDoSuccM i j = do
  o <- sccSeenM j
  case o of
    False-> do
      sccM j
      sccSetLowLinkToMin i =<< sccLowLinkM j
    True-> do
      o <- sccStackedM j
      case o of
        False-> return ()
        True-> sccSetLowLinkToMin i =<< sccIndexM j
sccPopToAndAddSccM :: Node x -> SccM x ()
sccPopToAndAddSccM i = do
  SCCEnv{..} <- N.get
  case () of
    _ | (comp,sccEnvStack) <- split i sccEnvStack
      , !sccEnvStacked <- foldl' (flip Ix.delete) sccEnvStacked comp
      , sccEnvSCCs <- Ix.fromList (zip comp (repeat ())):sccEnvSCCs
      , !new <- SCCEnv{..}
      -> N.set new
  where split i js = go [] js
          where go acc [] = (acc,[])
                go acc (j:js)
                  | i==j = (i:acc,js)
                  | otherwise = go (j:acc) js
sccIndexM :: Node x -> SccM x Int
sccIndexM i = N.gets ((Ix.! i) . sccEnvIndex)
sccLowLinkM :: Node x -> SccM x Int
sccLowLinkM i = N.gets ((Ix.! i) . sccEnvLowLink)
sccSetLowLinkToMin :: Node x -> Int -> SccM x ()
sccSetLowLinkToMin i m = do
  lowlink <- N.gets sccEnvLowLink
  let !new = Ix.adjust (min m) i lowlink
  N.modify(\e->e{sccEnvLowLink=new})
sccPushM :: Node x -> SccM x ()
sccPushM i = do
  m <- N.newUniqM
  SCCEnv{..} <- N.get
  case () of
    _ | !index      <- m - 1
      , !sccEnvIndex   <- Ix.insert i index sccEnvIndex
      , !sccEnvLowLink <- Ix.insert i index sccEnvLowLink
      , !sccEnvStacked <- Ix.insert i () sccEnvStacked
      , !sccEnvStack   <- i:sccEnvStack
      , !new        <- SCCEnv{..}
      -> N.set new
sccSeenM :: Node x -> SccM x Bool
sccSeenM i = N.gets (Ix.member i . sccEnvIndex)
sccSuccsM :: Node x -> SccM x (NodeSet x)
sccSuccsM i = N.gets ((Ix.! i) . sccEnvGraph)
sccStackedM :: Node x -> SccM x Bool
sccStackedM i = N.gets (Ix.member i . sccEnvStacked)
-- }}}

-----------------------------------------------------------------------------

data DFN a = DFN
  {dfnN2Pre :: NodeMap a Int
  ,dfnN2Post :: NodeMap a Int
  ,dfnPre2N :: IntMap (Node a)
  ,dfnPost2N :: IntMap (Node a)}
  __D

data DFNEdge
  = TreeDFNEdge
  | ForwardDFNEdge
  | BackwardDFNEdge
  | CrossDFNEdge
  __D_BE

dfnInit :: Graph a -> Node a -> DFN a
dfnInit g root
  | Dfs{..} <- dfs (root,g)
  , !dfnN2Pre <- dfsCallNum
  , !dfnN2Post <- dfsCompNum
  , !dfnPre2N <- Ix.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Pre
  , !dfnPost2N <- Ix.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Post
  = DFN{..}

dfnClassifyEdge :: DFN a -> Node a -> Node a -> DFNEdge
dfnClassifyEdge DFN{..} i j
  | idn <- dfnN2Pre Ix.! i
  , jdn <- dfnN2Pre Ix.! j
  , icn <- dfnN2Post Ix.! i
  , jcn <- dfnN2Post Ix.! j
  , p1 <- idn < jdn
  , p2 <- icn < jcn
  = case (p1,p2) of
      (True,True)-> TreeDFNEdge
      (True,False)-> ForwardDFNEdge
      (False,True)-> BackwardDFNEdge
      (False,False)-> CrossDFNEdge

dfnPre :: DFN a -> Node a -> Int
dfnPost :: DFN a -> Node a -> Int
dfnPre DFN{dfnN2Pre} i = dfnN2Pre Ix.! i
dfnPost DFN{dfnN2Post} i = dfnN2Post Ix.! i

dfnPreOrder :: DFN a -> [Node a]
dfnPostOrder :: DFN a -> [Node a]
dfnRevPreOrder :: DFN a -> [Node a]
dfnRevPostOrder :: DFN a -> [Node a]
dfnPreOrder DFN{dfnPre2N} = IM.elems dfnPre2N
dfnPostOrder DFN{dfnPost2N} = IM.elems dfnPost2N
dfnRevPreOrder dfn = reverse (dfnPreOrder dfn)
dfnRevPostOrder dfn = reverse (dfnPostOrder dfn)

-- {{{
data Dfs a = Dfs
  {dfsSpanning  :: (Node a, Graph a)
  ,dfsCallNum   :: NodeMap a Int
  ,dfsCompNum   :: NodeMap a Int} __D
dfs :: (Node a, Graph a) -> Dfs a
dfs rg@(r,g)
  | DfsEnv{..}  <- execDfsM (dfsM r) (initDfsEnv rg)
  = Dfs
      (dfsEnvRoot,dfsEnvSpanning)
      (dfsEnvCallMap)
      (dfsEnvCompMap)
type DfsM t a = SU2.S (DfsEnv t) a
data DfsEnv a = DfsEnv
  {dfsEnvRoot :: !(Node a) -- RO
  ,dfsEnvGraph :: Graph a -- RO
  ,dfsEnvSpanning :: Graph a -- WO
  ,dfsEnvSeenNodes :: NodeSet a -- RW
  ,dfsEnvCallMap :: NodeMap a Int -- WO
  ,dfsEnvCompMap :: NodeMap a Int} -- WO
dfsM :: Node a -> DfsM a ()
dfsM v = do
  dfsSetCallM v
  dfsAddSeenM v
  vs <- dfsSuccsM v
  mapM_ (go v) (Ix.keys vs)
  dfsSetCompM v
  return ()
  where go :: Node a -> Node a -> DfsM a ()
        go u v = do
          seen <- dfsSeenM v
          case seen of
            True-> return ()
            False-> do
              dfsSetCallM v
              dfsAddSeenM v
              addTreeEdgesM u (Ix.singleton v ())
              vs <- dfsSuccsM v
              mapM_ (go v) (Ix.keys vs)
              dfsSetCompM v
              return ()
execDfsM :: DfsM t a -> DfsEnv t -> DfsEnv t
execDfsM m env | (_,(_,_,env)) <- N.runM m 1 1 env = env
initDfsEnv :: (Node a, Graph a) -> DfsEnv a
initDfsEnv (r,g) = DfsEnv
  {dfsEnvRoot = r
  ,dfsEnvGraph = g
  ,dfsEnvSpanning = mempty
  ,dfsEnvSeenNodes = mempty
  ,dfsEnvCallMap = mempty
  ,dfsEnvCompMap = mempty}
addTreeEdgesM :: Node a -> NodeSet a -> DfsM a ()
addTreeEdgesM v ws = do
  spant <- N.gets dfsEnvSpanning
  N.modify(\e->e{dfsEnvSpanning
    =Ix.insertWith Ix.union v ws spant})
dfsSeenM :: Node a -> DfsM a Bool
dfsSeenM v = N.gets ((v`Ix.member`) . dfsEnvSeenNodes)
dfsSuccsM :: Node a -> DfsM a (NodeSet a)
dfsSuccsM v = N.gets ((Ix.! v) . dfsEnvGraph)
dfsUnSeenM :: NodeSet a -> DfsM a (NodeSet a)
dfsUnSeenM s = N.gets
  ((s `Ix.difference`)
    . dfsEnvSeenNodes)
dfsAddSeenM :: Node a -> DfsM a ()
dfsAddSeenM i = dfsUnionSeenM (Ix.singleton i ())
dfsUnionSeenM :: NodeSet a -> DfsM a ()
dfsUnionSeenM s = do
  seen <- N.gets dfsEnvSeenNodes
  N.modify(\e->e{dfsEnvSeenNodes=seen`Ix.union`s})
dfsNextCallM :: DfsM a Int
dfsNextCallM = N.newUniq1M
dfsNextCompM :: DfsM a Int
dfsNextCompM = N.newUniq2M
dfsSetCallM :: Node a -> DfsM a ()
dfsSetCallM v = do
  dn <- dfsNextCallM
  dnm <- N.gets dfsEnvCallMap
  N.modify(\e->e{dfsEnvCallMap=Ix.insert v dn dnm})
dfsSetCompM :: Node a -> DfsM a ()
dfsSetCompM v = do
  cn <- dfsNextCompM
  cnm <- N.gets dfsEnvCompMap
  N.modify(\e->e{dfsEnvCompMap=Ix.insert v cn cnm})
-- }}}

-----------------------------------------------------------------------------

-- | Partition-Refinement. Abstract datatype.
data PartRefine a b = PartRefine
  {partRefinePart :: PartRefinePart a b
  ,partRefineDeltaInv :: DeltaInv a}
  __D
type EdgeLbl = Int
type EdgeLblMap = IntMap
type DeltaInv a = EdgeLblMap (NodeMap a (NodeSet a))
-- hidden
type PartRefineSize = Int
data PartRefinePart a b = PRP
  {prpNext   :: !(Node b)
  ,prpC2Size :: NodeMap b PartRefineSize
  ,prpN2C    :: NodeMap a (Node b)
  ,prpClass  :: NodeMap b (NodeSet a)}
  __D

updateDeltaInv :: Node a -> [Node a] -> DeltaInv a -> DeltaInv a
updateDeltaInv i js dinv
  = IM.foldWithKey go dinv (IM.fromList . zip [0..] $ js)
  where !iset = Ix.singleton i ()
        go pos j dinv = IM.insertWith (\/)
          pos (Ix.singleton j iset) dinv

class PartRefinePrep a b x where
  partRefinePrep :: x -> (Partition a b , DeltaInv a)
instance PartRefinePrep a b (Partition a b, DeltaInv a) where
  partRefinePrep = id

partRefineInit :: forall a b x . (PartRefinePrep a b x) => x -> PartRefine a b
partRefineInit a
  | (part, dinv) <- partRefinePrep a
  = go part dinv
  where go :: Partition a b -> DeltaInv a -> PartRefine a b
        go (n2i,i2ns) dinv
          | Ix.null n2i || Ix.null i2ns || IM.null dinv
          = PartRefine
              {partRefinePart=PRP 0 mempty mempty mempty
              ,partRefineDeltaInv=mempty}
          | prpNext <- 1 + maxKey i2ns
          , prpC2Size <- fmap Ix.size i2ns
          , prpN2C <- n2i
          , prpClass <- i2ns
          , partRefinePart <- PRP{..}
          , partRefineDeltaInv <- dinv
          = PartRefine{..}
          where maxKey m
                  | Just ((k,_),_) <- Ix.maxViewWithKey m = k
                  | otherwise = __IMPOSSIBLE

partRefinePartition :: PartRefine a b -> Partition a b
partRefinePartition PartRefine{partRefinePart=PRP{..}}
  | (c2ns,rn) <- Ix.foldWithKey go mempty prpClass
  , n2c <- fmap (rn Ix.!) prpN2C
  = (n2c, c2ns)
  where go
          :: Node b
          -> NodeSet a
          -> (NodeMap b (NodeSet a), NodeMap b (Node b))
          -> (NodeMap b (NodeSet a), NodeMap b (Node b))
        go b as acc@(b2as,rn)
          | new <- castIx (Ix.minKeyWithDefault 0 as)
          , b2as <- Ix.insert new as b2as
          , rn <- Ix.insert b new rn
          = (b2as,rn)
          | otherwise
          = acc
#if 0
        go b as acc@(b2as,rn)
          | n <- prpC2Size Ix.! b
          , n > 1
          , new <- castIx (Ix.minKeyWithDefault 0 as)
          , b2as <- Ix.insert new as b2as
          , rn <- Ix.insert b new
          = (b2as,rn)
          | otherwise
          = acc
#endif

-- | Hopcroft's Partition-Refinement Algorithm
partRefineRefine :: forall a b. PartRefine a b -> PartRefine a b
partRefineRefine PartRefine{..}
  | partRefinePart <- hopcroft partRefineDeltaInv partRefinePart
  = PartRefine{..}
  where hopcroft :: DeltaInv a -> PartRefinePart a b -> PartRefinePart a b
        hopcroft dinv part = go (part, toSets part)
          where elbls = edgeLbls dinv
                go :: PartRefineStepState a b -> PartRefinePart a b
                go (ps,[]) = ps
                go (ps,l:ls) = go (fold l (ps,ls))
                fold l s = foldl' (\s elbl->
                  partRefineStep s (deltaInv dinv elbl l)
                  ) s elbls
                toSets :: PartRefinePart a b -> [NodeSet a]
                toSets PRP{..} = Ix.elems prpClass
                edgeLbls :: DeltaInv a -> [EdgeLbl]
                edgeLbls = IM.keys
                deltaInv :: DeltaInv a -> EdgeLbl -> NodeSet a -> NodeSet a
                deltaInv dinv e ns
                  = Ix.fold (\/) mempty
                      ((IM.findWithDefault mempty e dinv) `Ix.intersection` ns)

type PartRefineStepState a b = (PartRefinePart a b, [NodeSet a])
partRefineStep :: forall a b . PartRefineStepState a b -> NodeSet a -> PartRefineStepState a b
partRefineStep s a = go s a
  where go s@(PRP{prpN2C},_) a
          | Ix.null a = s
          | i <- minKey a
          , cls <- prpN2C Ix.! i
          , (snew, anew) <- refineOne s cls a
          = go snew anew
        minKey m
          | Just ((k,_),_) <- Ix.minViewWithKey m = k
          | otherwise = __IMPOSSIBLE
        refineOne
          :: PartRefineStepState a b -> Node b
          -> NodeSet a -> (PartRefineStepState a b, NodeSet a)
        refineOne s@(part@PRP{prpClass},ls) cls dinv
          | p <- prpClass Ix.! cls
          , p1 <- p/\dinv
          , p2 <- p\\p1
          , xdinv <- dinv\\p -- this is an optimization
          , o1 <- Ix.null p1
          , o2 <- Ix.null p2
          = case (o1,o2) of
              (True,True)-> __IMPOSSIBLE
              (True,False) | __ASSERT(p == p2)-> (s, xdinv)
              (False,True) | __ASSERT(p == p1)-> (s, xdinv)
              (False,False)
                | (part, p0) <- split part cls p1 p2
                -> ((part, p0:ls), xdinv)
        split
          :: PartRefinePart a b -> Node b
          -> NodeSet a -> NodeSet a
          -> (PartRefinePart a b, NodeSet a)
        -- Splits the smaller of the two sets into a new class, and
        -- returns the smaller one. It MUST be the case and is UNCHECKED
        -- that the two sets are NONMEMPTY. And it MUST be the case and
        -- is UNCHECKED that the two sets form a partition of the class
        -- identified by the @Int@.
        split PRP{..} cls p1 p2
          | n1 <- Ix.size p1 -- XXX: O(n)
          , n2 <- (prpC2Size Ix.! cls) - n1
          , let go x1 x2 m1 m2
                  | !new <- prpNext
                  , !prpNext <- prpNext + 1
                  , !prpN2C <- fmap (const new) x2`Ix.union`prpN2C
                  , !prpC2Size <- Ix.insert cls m1 prpC2Size
                  , !prpC2Size <- Ix.insert new m2 prpC2Size
                  , !prpClass <- Ix.insert cls x1 prpClass
                  , !prpClass <- Ix.insert new x2 prpClass
                  = PRP{..}
          = case n1 <= n2 of
              True  | !out <- go p1 p2 n1 n2-> (out, p1)
              False | !out <- go p2 p1 n2 n1-> (out, p2)

-----------------------------------------------------------------------------

data NodeKey k = UniqKey | NodeKey k __D
class (Ord k) => NodeKeyed k a | a -> k where
  nodeKey :: a -> NodeKey k

-----------------------------------------------------------------------------

-- | @partRefinePartition . partRefineRefine . partRefineInit@
shareCyclic :: (Ord k) => NodeMap a (k, [Node a]) -> Partition a a
shareCyclic dfa
  | o <- partRefineInit dfa
  , o <- partRefineRefine o
  = partRefinePartition o

-- | There is a lot of copy-paste duplication in the next threee instances:
instance (Ord k) => PartRefinePrep a a (NodeMap a (k, EdgeLblMap (Node a))) where
  partRefinePrep dfa
    | (dinv,kpart) <- Ix.foldWithKey go mempty dfa
    , part <- toPartition (OM.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | part <- OM.insertWith (\/) key (Ix.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)
          updateDeltaInv :: Node a -> EdgeLblMap (Node a) -> DeltaInv a -> DeltaInv a
          updateDeltaInv i js dinv = IM.foldWithKey go dinv js
            where !iset = Ix.singleton i ()
                  go pos j dinv = IM.insertWith (\/)
                    pos (Ix.singleton j iset) dinv

instance (Ord k) => PartRefinePrep a a (NodeMap a (k, [Node a])) where
  partRefinePrep dfa
    | (dinv,kpart) <- Ix.foldWithKey go mempty dfa
    , part <- toPartition (OM.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | part <- OM.insertWith (\/) key (Ix.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)

data MyNodeKey a k = MyUniqKey !(Node a) | MyNodeKey k deriving(Eq,Ord)
instance (Ord k) => PartRefinePrep a a (NodeMap a (NodeKey k, [Node a])) where
  partRefinePrep dfa
    | (dinv,kpart) <- Ix.foldWithKey go mempty dfa
    , part <- toPartition (OM.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | newkey <- case key of
                UniqKey-> MyUniqKey i
                NodeKey k-> MyNodeKey k
            , part <- OM.insertWith (\/) newkey (Ix.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)

-----------------------------------------------------------------------------

flattenAcyclicToOneLevel
  :: Graph a
  -> NodeMap a dontcare
  -> Either (NodeMap (SCC a) (NodeSet a)) (Graph a)
flattenAcyclicToOneLevel g keep
  | o <- go g
  = case o of
      Left{}-> o
      Right g
        | g  <- g`Ix.intersection`keep
        , g <- fmap (`Ix.difference`keep) g
        -> Right g
  where go g
          | scc <- sccInit g
          , topo <- sccTopoAssertAcyclic scc
          = case topo of
              Left comps
                | let go c _ = sccGetCompNodes scc c
                -> Left (Ix.mapWithKey go comps)
              Right ns
                | tclos <- foldl' step g ns
                -> Right tclos
          where step acc i
                  | js <- g Ix.! i
                  , ks <- Ix.foldWithKey (\j _ o-> o \/ (acc Ix.! j)) js js
                  = Ix.insert i ks acc

-----------------------------------------------------------------------------

shareOneLevel :: (Ord k) => NodeMap a (k, [Node a]) -> Partition a a
shareOneLevel = toPartition . fst . flip shareOneLevelWith mempty

shareAcyclic :: (Ord k) => NodeMap a (k, [Node a]) -> Partition a a
shareAcyclic = toPartition . fst . flip shareAcyclicWith mempty

type MemoTrie a b k = Map k (IxTrie b (Node a))

shareOneLevelWith :: (Ord k) => NodeMap a (k, [Node a]) -> MemoTrie a a k -> (NodeMap a (Node a), MemoTrie a a k)
shareOneLevelWith g memo = Ix.foldWithKey go (mempty,memo) g
  where go i (k,js) (rn,memo)
          | Just trie <- OM.lookup k memo
          = case IxT.lookup js trie of
              Just new-> rnTo i new rn memo
              Nothing-> add i k js rn memo trie
          | otherwise = add i k js rn memo IxT.empty
        add old k js rn memo trie
          | !trie <- IxT.insert js old trie
          , !memo <- OM.insert k trie memo
          , !rn   <- Ix.insert old old rn
          = (rn,memo)
        rnTo old new rn memo
          | !rn <- Ix.insert old new rn
          = (rn,memo)

shareAcyclicWith :: (Ord k) => NodeMap a (k, [Node a]) -> MemoTrie a a k -> (NodeMap a (Node a), MemoTrie a a k)
shareAcyclicWith dfa memo
  | ns <- topo dfa
  , (rn,memo) <- foldl' go (mempty,memo) ns
  = (rn,memo)
  where topo dfa
          | g <- fmap (fromList . flip zip (repeat ()) . snd) $ dfa
          , nss <- sccTopo . sccInit . legalize $ g
          = concatMap (Ix.keys . (`Ix.intersection` dfa)) nss
        go (rn,memo) i
          | (k,js) <- dfa Ix.! i
          , js <- rename rn js
          = case () of
              _ | Just trie <- OM.lookup k memo
                -> case IxT.lookup js trie of
                    Just new-> rnTo i new rn memo
                    Nothing-> add i k js rn memo trie
                | otherwise-> add i k js rn memo IxT.empty
        rename rn js = fmap go js
          where go j = maybe j id (Ix.lookup j rn)
        add old k js rn memo trie
          | !trie <- IxT.insert js old trie
          , !memo <- OM.insert k trie memo
          , !rn   <- Ix.insert old old rn
          = (rn,memo)
        rnTo old new rn memo
          | !rn <- Ix.insert old new rn
          = (rn,memo)

-----------------------------------------------------------------------------
