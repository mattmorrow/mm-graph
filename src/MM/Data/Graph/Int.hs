{-# OPTIONS -pgmP cpp -optP-w #-}
{-# LANGUAGE
      CPP,
      MagicHash,
      BangPatterns,
      OverlappingInstances,
      UndecidableInstances #-}
#undef __DEBUG_ON
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
#define __INLINE(x)   {-HASH INLINE x HASH-}

module MM.Data.Graph.Int (
   Graph,PredGraph,Node,NodeMap,NodeSet
  ,Partition,Cover,IsPartition(..)

  ,isLegal,legalize,nodes
  ,invert,predGraph,succGraph,invertForest
  ,fromAdj,toAdj
  ,quotientGraph,inducedSubgraph,inducedSubgraphs

  ,DomTree(..),domTreeInit,domTreeRevPostOrder
  ,DomFront,domFrontInit,domFront
  ,DomFrontPlus,domFrontPlusInit,domFrontPlus

  ,SCC,SCCData,Cyclicity(..)
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

  ,PartRefine,EdgeLbl,EdgeLblMap,DeltaInv
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
import qualified MM.Data.Map.Ord as M
import qualified MM.Data.Set.Ord as S
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
import MM.Data.Class.Empty
import MM.Data.Class.List
import MM.Data.Class.O

-----------------------------------------------------------------------------

-- | .
type Node       = Int
type NodeMap b  = IntMap b
type NodeSet    = NodeMap ()
type Graph      = NodeMap NodeSet
type PredGraph  = Graph

data Components a = Comps
  {compsPart :: Partition
  ,compsData :: a}
  __D

type Partition  = (NodeMap Int, IntMap NodeSet)
type Cover      = (NodeMap (IntMap ()), IntMap Node)

class IsPartition a where
  toPartition :: a -> Partition
  fromPartition :: Partition -> a
instance IsPartition (NodeMap Int) where
  fromPartition = fst
  toPartition n2i
    | i2ns <- IM.foldWithKey go mempty n2i
    = (n2i, i2ns)
    where go n i o = IM.insertWith (\/) i (IM.singleton n ()) o
instance IsPartition (IntMap NodeSet) where
  fromPartition = snd
  toPartition i2ns
    | n2i <- IM.foldWithKey go mempty i2ns
    = (n2i, i2ns)
    where go i ns o = IM.foldWithKey (\n _ o-> IM.insert n i o) o ns
instance IsPartition [NodeSet] where
  fromPartition = IM.elems . fromPartition
  toPartition = toPartition . IM.fromList . zip [0..]

-----------------------------------------------------------------------------

-- | All graph algorithms ASSUME a "legal" graph. See @legalize@.
isLegal :: Graph -> Bool
isLegal g = IM.size (g `IM.difference` nodes g) == 0

-- | Ensures every node is present in the domain of the map.
legalize :: Graph -> Graph
legalize g = g \/ fmap (const mempty) (nodes g)

nodes :: Graph -> NodeSet
nodes g = IM.foldWithKey go mempty g
  where go i is acc = IM.insert i () (acc \/ is)

-----------------------------------------------------------------------------

invert :: Graph -> Graph
invert g = IM.foldWithKey go (fmap (const mempty) g) g
  where go :: Node -> NodeSet -> Graph -> Graph
        go i js acc
          | !is <- IM.singleton i ()
          , !acc <- IM.insertWith (\/) i mempty acc
          = IM.foldWithKey (\j _ acc-> IM.insertWith (\/) j is acc) acc js

predGraph :: Graph -> PredGraph
succGraph :: PredGraph -> Graph
predGraph = invert
succGraph = invert

invertForest :: NodeMap Node -> Graph
invertForest = IM.foldWithKey go mempty
  where go i j o = IM.insertWith (\/) j (IM.singleton i ()) o

-----------------------------------------------------------------------------

fromAdj :: [(Node, [Node])] -> Graph
fromAdj = fmap (\is-> IM.fromList (zip is (repeat ()))) . IM.fromList

toAdj :: Graph -> [(Node, [Node])]
toAdj = IM.toList . fmap IM.keys

-----------------------------------------------------------------------------

quotientGraph :: Graph -> Partition -> Graph
quotientGraph g _ = __FIXME("quotientGraph")

inducedSubgraph :: Graph -> NodeSet -> Graph
inducedSubgraph g ns = IM.foldWithKey (\i is acc->
    let !js = is`IM.intersection`ns
    in IM.insert i js acc
  ) mempty (g`IM.intersection`ns)

inducedSubgraphs :: Graph -> Partition -> IntMap Graph
inducedSubgraphs g = fmap (inducedSubgraph g) . fromPartition

-----------------------------------------------------------------------------
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

data DomTree = DomTree
  {domTreeDFN :: DFN
  ,domTreeRoot :: !Node
  ,domTreeParent :: NodeMap Node
  ,domTreeChildren :: Graph
  } __D

domTreeInit :: PredGraph -> DFN -> Node -> DomTree
domTreeInit preds dfn root
  | domTreeRoot <- root
  , domTreeParent <- idomInit preds dfn root
  , domTreeChildren <- legalize (invertForest domTreeParent)
  , domTreeDFN <- dfnInit domTreeChildren domTreeRoot
  = DomTree{..}

domTreeRevPostOrder :: DomTree -> [Node]
domTreeRevPostOrder DomTree{domTreeDFN=o} = dfnRevPostOrder o

idomInit_ :: Graph -> Node -> NodeMap Node
idomInit_ succs root
  | dfn <- dfnInit succs root
  , preds <- invert succs
  = idomInit preds dfn root

-- | The "Simple Fast" immediate dominators algorithm.
idomInit :: PredGraph -> DFN -> Node -> NodeMap Node
idomInit preds dfn root
  | dfnpost <- dfnN2Post dfn
  , dfnpostinv <- dfnPost2N dfn
  = idom dfnpost dfnpostinv preds root
  where idom
          :: NodeMap Int    -- PostDfn
          -> IntMap Node    -- PostDfnInv
          -> PredGraph      -- PREDECESSORS
          -> Node           -- root
          -> NodeMap Node   -- idom
        idom dfn dfninv preds root = while (IM.singleton root root)
          where rpo = drop 1 (reverse (IM.elems dfninv))
                while :: NodeMap Node -> NodeMap Node
                while idom
                  | (changed,idom) <- foldl' go (False,idom) rpo
                  = if changed then while idom else idom
                go :: (Bool, NodeMap Node) -> Node -> (Bool, NodeMap Node)
                go acc@(changed,idom) i
                  | ps <- (preds IM.! i)`IM.intersection`idom
                  , not (IM.null ps)
                  , j <- minKeyWithDefault 0 ps
                  , js <- IM.delete j ps
                  , let loop k _ newidom = intersect dfn idom k newidom
                  , newidom <- IM.foldWithKey loop j js
                  , case IM.lookup i idom of
                      Just x-> x/=newidom
                      Nothing-> True
                  , !idom <- IM.insert i newidom idom
                  = (True,idom)
                  | otherwise = acc
                minKeyWithDefault dflt m
                  | Just ((k,_),_) <- IM.minViewWithKey m = k
                  | otherwise = dflt
                intersect
                  :: NodeMap Int -- PostDfn
                  -> NodeMap Node -- parent
                  -> Node -> Node -> Node
                intersect dfn parent i j = go i j
                  where go :: Node -> Node -> Node
                        go i j
                          | i==j = i
                          | i <- walk i j
                          , j <- walk j i
                          = go i j
                        walk :: Node -> Node -> Node
                        walk i j = loop (dfn IM.! j) i
                          where loop !nj !i
                                  | ni <- dfn IM.! i
                                  , ni < nj
                                  = loop nj (parent IM.! i)
                                  | otherwise = i

-----------------------------------------------------------------------------

data DomFront = DomFront
  {domFrontDF :: NodeMap NodeSet}
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
domFrontInit :: DomTree -> DomFront
domFrontInit dt = __FIXME("domFrontInit")

domFront :: DomFront -> Node -> NodeSet
domFront df i = __FIXME("domFront")

#if 0
NOTE:
Nodes a and b have the same control depencies iff a and b are cycle
equivalent in the strongly connected component formed by adding end->start
to the CFG.
#endif

-----------------------------------------------------------------------------

data DomFrontPlus = DomFrontPlus
  {domFrontPlusDF :: DomFront
  ,domFrontPlusDFPlus :: NodeMap NodeSet}
  __D

domFrontPlusInit :: DomFront -> DomFrontPlus
domFrontPlusInit df = __FIXME("domFrontPlusInit")

domFrontPlus :: DomFrontPlus -> Node -> (NodeSet, DomFrontPlus)
domFrontPlus dfp i = __FIXME("domFrontPlus")

-----------------------------------------------------------------------------

type SCC = Components SCCData
data SCCData = SCCData
  {sccDataTo :: IntMap Cyclicity
  ,sccDataFrom :: Map Cyclicity (IntMap ())} __D
data Cyclicity = Acyclic | Cyclic __D_BE
instance Empty SCCData where
  empty = SCCData empty empty
  isEmpty o = o==empty
instance Monoid SCCData where
  mempty = SCCData mempty mempty
  mappend (SCCData a1 b1) (SCCData a2 b2)
    | !a <- mappend a1 a2
    , !b <- mappend b1 b2
    = SCCData a b

sccInit :: Graph -> SCC
sccInit g
  | sccs <- sccEnvSCCs (execSccM sccTarjanM (initSCCEnv g))
  , comps <- IM.fromList . zip [0..] . reverse $ sccs
  , compsPart <- toPartition comps
  , compsData <- IM.foldWithKey go mempty comps
  = Comps{..}
  where go :: Int -> NodeSet -> SCCData -> SCCData
        go comp ns SCCData{..}
          | cyc <- cyclicity ns
          , sccDataTo <- IM.insert comp cyc sccDataTo
          , sccDataFrom <- M.insertWith (\/) cyc
              (IM.singleton comp ()) sccDataFrom
          = SCCData{..}
        cyclicity :: NodeSet -> Cyclicity
        cyclicity ns
          | Just ((n,_),rest) <- IM.minViewWithKey ns
          = case IM.null rest of
              False-> Cyclic
              True
                | n`IM.member`(IM.findWithDefault mempty n g)-> Cyclic
                | otherwise-> Acyclic
          | otherwise = __IMPOSSIBLE

sccGetCompNodes :: SCC -> Int -> NodeSet
sccGetCompNodes Comps{compsPart=(_,c2ns)} comp = c2ns IM.! comp

sccGetNodeComp :: SCC -> Node -> Int
sccGetNodeComp Comps{compsPart=(n2c,_)} node = n2c IM.! node

sccAcyclicComps :: SCC -> IntMap ()
sccAcyclicComps = sccCompsWithCyclicity Acyclic

sccCyclicComps :: SCC -> IntMap ()
sccCyclicComps = sccCompsWithCyclicity Cyclic

sccCompsWithCyclicity :: Cyclicity -> SCC -> IntMap ()
sccCompsWithCyclicity cyc Comps{compsData=SCCData{..}}
  = M.findWithDefault mempty cyc sccDataFrom

sccAcyclicNodes :: SCC -> NodeSet
sccAcyclicNodes = sccNodesWithCyclicity Acyclic

sccCyclicNodes :: SCC -> NodeSet
sccCyclicNodes = sccNodesWithCyclicity Cyclic

sccNodesWithCyclicity :: Cyclicity -> SCC -> NodeSet
sccNodesWithCyclicity cyc Comps{compsData=SCCData{..},..}
  | comps <- M.findWithDefault mempty cyc sccDataFrom
  , (_,c2ns) <- compsPart
  , let go i _ o = o \/ (c2ns IM.! i)
  = IM.foldWithKey go mempty comps

sccTopo :: SCC -> [NodeSet]
sccTopo Comps{compsPart} = fromPartition compsPart

sccTopoAssertAcyclic :: SCC -> Either (IntMap ()) [Node]
sccTopoAssertAcyclic scc
  | cyclic <- sccCyclicComps scc
  = case IM.null cyclic of
      True-> Right (IM.keys =<< sccTopo scc)
      False-> Left cyclic

-- {{{
type SccM a = SU.S SCCEnv a
data SCCEnv = SCCEnv
  {sccEnvGraph   :: Graph
  ,sccEnvIndex   :: NodeMap Int
  ,sccEnvLowLink :: NodeMap Int
  ,sccEnvStacked :: NodeSet
  ,sccEnvStack   :: [Node]
  ,sccEnvSCCs    :: [NodeSet]}
execSccM :: SccM a -> SCCEnv -> SCCEnv
execSccM m env | (_,(_,env)) <- N.runM m 0 env = env
initSCCEnv :: Graph -> SCCEnv
initSCCEnv g = SCCEnv
  {sccEnvGraph   = g
  ,sccEnvIndex   = mempty
  ,sccEnvLowLink = mempty
  ,sccEnvStacked = mempty
  ,sccEnvStack   = []
  ,sccEnvSCCs    = []}
sccTarjanM :: SccM ()
sccTarjanM = mapM_ go =<< N.gets (IM.keys . nodes . sccEnvGraph)
  where go i = do
          o <- sccSeenM i
          case o of
            False-> sccM i
            True-> return ()
sccM :: Node -> SccM ()
sccM i = do
  sccPushM i
  ss <- sccSuccsM i
  mapM_ (sccDoSuccM i) (IM.keys ss)
  ix <- sccIndexM i
  ll <- sccLowLinkM i
  case ix==ll of
    True-> sccPopToAndAddSccM i
    False-> return ()
sccDoSuccM :: Node -> Node -> SccM ()
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
sccPopToAndAddSccM :: Node -> SccM ()
sccPopToAndAddSccM i = do
  SCCEnv{..} <- N.get
  case () of
    _ | (comp,sccEnvStack) <- split i sccEnvStack
      , !sccEnvStacked <- foldl' (flip IM.delete) sccEnvStacked comp
      , sccEnvSCCs <- IM.fromList (zip comp (repeat ())):sccEnvSCCs
      , !new <- SCCEnv{..}
      -> N.set new
  where split i js = go [] js
          where go acc [] = (acc,[])
                go acc (j:js)
                  | i==j = (i:acc,js)
                  | otherwise = go (j:acc) js
sccIndexM :: Node -> SccM Int
sccIndexM i = N.gets ((IM.! i) . sccEnvIndex)
sccLowLinkM :: Node -> SccM Int
sccLowLinkM i = N.gets ((IM.! i) . sccEnvLowLink)
sccSetLowLinkToMin :: Node -> Int -> SccM ()
sccSetLowLinkToMin i m = do
  lowlink <- N.gets sccEnvLowLink
  let !new = IM.adjust (min m) i lowlink
  N.modify(\e->e{sccEnvLowLink=new})
sccPushM :: Node -> SccM ()
sccPushM i = do
  m <- N.newUniqM
  SCCEnv{..} <- N.get
  case () of
    _ | !index      <- m - 1
      , !sccEnvIndex   <- IM.insert i index sccEnvIndex
      , !sccEnvLowLink <- IM.insert i index sccEnvLowLink
      , !sccEnvStacked <- IM.insert i () sccEnvStacked
      , !sccEnvStack   <- i:sccEnvStack
      , !new        <- SCCEnv{..}
      -> N.set new
sccSeenM :: Node -> SccM Bool
sccSeenM i = N.gets (IM.member i . sccEnvIndex)
sccSuccsM :: Node -> SccM NodeSet
sccSuccsM i = N.gets ((IM.! i) . sccEnvGraph)
sccStackedM :: Node -> SccM Bool
sccStackedM i = N.gets (IM.member i . sccEnvStacked)
-- }}}

-----------------------------------------------------------------------------

data DFN = DFN
  {dfnN2Pre :: NodeMap Int
  ,dfnN2Post :: NodeMap Int
  ,dfnPre2N :: IntMap Node
  ,dfnPost2N :: IntMap Node}
  __D

data DFNEdge
  = TreeDFNEdge
  | ForwardDFNEdge
  | BackwardDFNEdge
  | CrossDFNEdge
  __D_BE

dfnInit :: Graph -> Node -> DFN
dfnInit g root
  | Dfs{..} <- dfs (root,g)
  , !dfnN2Pre <- dfsCallNum
  , !dfnN2Post <- dfsCompNum
  , !dfnPre2N <- IM.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Pre
  , !dfnPost2N <- IM.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Post
  = DFN{..}

dfnClassifyEdge :: DFN -> Node -> Node -> DFNEdge
dfnClassifyEdge DFN{..} i j
  | idn <- dfnN2Pre IM.! i
  , jdn <- dfnN2Pre IM.! j
  , icn <- dfnN2Post IM.! i
  , jcn <- dfnN2Post IM.! j
  , p1 <- idn < jdn
  , p2 <- icn < jcn
  = case (p1,p2) of
      (True,True)-> TreeDFNEdge
      (True,False)-> ForwardDFNEdge
      (False,True)-> BackwardDFNEdge
      (False,False)-> CrossDFNEdge

dfnPre :: DFN -> Node -> Int
dfnPost :: DFN -> Node -> Int
dfnPre DFN{dfnN2Pre} i = dfnN2Pre IM.! i
dfnPost DFN{dfnN2Post} i = dfnN2Post IM.! i

dfnPreOrder :: DFN -> [Node]
dfnPostOrder :: DFN -> [Node]
dfnRevPreOrder :: DFN -> [Node]
dfnRevPostOrder :: DFN -> [Node]
dfnPreOrder DFN{dfnPre2N} = IM.elems dfnPre2N
dfnPostOrder DFN{dfnPost2N} = IM.elems dfnPost2N
dfnRevPreOrder dfn = reverse (dfnPreOrder dfn)
dfnRevPostOrder dfn = reverse (dfnPostOrder dfn)

-- {{{
data Dfs a = Dfs
  {dfsSpanning  :: (Node, Graph)
  ,dfsCallNum   :: NodeMap Int
  ,dfsCompNum   :: NodeMap Int} __D
dfs :: (Node, Graph) -> Dfs a
dfs rg@(r,g)
  | DfsEnv{..}  <- execDfsM (dfsM r) (initDfsEnv rg)
  = Dfs
      (dfsEnvRoot,dfsEnvSpanning)
      (dfsEnvCallMap)
      (dfsEnvCompMap)
type DfsM t a = SU2.S (DfsEnv t) a
data DfsEnv a = DfsEnv
  {dfsEnvRoot :: !(Node) -- RO
  ,dfsEnvGraph :: Graph -- RO
  ,dfsEnvSpanning :: Graph -- WO
  ,dfsEnvSeenNodes :: NodeSet -- RW
  ,dfsEnvCallMap :: NodeMap Int -- WO
  ,dfsEnvCompMap :: NodeMap Int} -- WO
dfsM :: Node -> DfsM a ()
dfsM v = do
  dfsSetCallM v
  dfsAddSeenM v
  vs <- dfsSuccsM v
  mapM_ (go v) (IM.keys vs)
  dfsSetCompM v
  return ()
  where go :: Node -> Node -> DfsM a ()
        go u v = do
          seen <- dfsSeenM v
          case seen of
            True-> return ()
            False-> do
              dfsSetCallM v
              dfsAddSeenM v
              addTreeEdgesM u (IM.singleton v ())
              vs <- dfsSuccsM v
              mapM_ (go v) (IM.keys vs)
              dfsSetCompM v
              return ()
execDfsM :: DfsM t a -> DfsEnv t -> DfsEnv t
execDfsM m env | (_,(_,_,env)) <- N.runM m 1 1 env = env
initDfsEnv :: (Node, Graph) -> DfsEnv a
initDfsEnv (r,g) = DfsEnv
  {dfsEnvRoot = r
  ,dfsEnvGraph = g
  ,dfsEnvSpanning = mempty
  ,dfsEnvSeenNodes = mempty
  ,dfsEnvCallMap = mempty
  ,dfsEnvCompMap = mempty}
addTreeEdgesM :: Node -> NodeSet -> DfsM a ()
addTreeEdgesM v ws = do
  spant <- N.gets dfsEnvSpanning
  N.modify(\e->e{dfsEnvSpanning
    =IM.insertWith IM.union v ws spant})
dfsSeenM :: Node -> DfsM a Bool
dfsSeenM v = N.gets ((v`IM.member`) . dfsEnvSeenNodes)
dfsSuccsM :: Node -> DfsM a (NodeSet)
dfsSuccsM v = N.gets ((IM.! v) . dfsEnvGraph)
dfsUnSeenM :: NodeSet -> DfsM a (NodeSet)
dfsUnSeenM s = N.gets
  ((s `IM.difference`)
    . dfsEnvSeenNodes)
dfsAddSeenM :: Node -> DfsM a ()
dfsAddSeenM i = dfsUnionSeenM (IM.singleton i ())
dfsUnionSeenM :: NodeSet -> DfsM a ()
dfsUnionSeenM s = do
  seen <- N.gets dfsEnvSeenNodes
  N.modify(\e->e{dfsEnvSeenNodes=seen`IM.union`s})
dfsNextCallM :: DfsM a Int
dfsNextCallM = N.newUniq1M
dfsNextCompM :: DfsM a Int
dfsNextCompM = N.newUniq2M
dfsSetCallM :: Node -> DfsM a ()
dfsSetCallM v = do
  dn <- dfsNextCallM
  dnm <- N.gets dfsEnvCallMap
  N.modify(\e->e{dfsEnvCallMap=IM.insert v dn dnm})
dfsSetCompM :: Node -> DfsM a ()
dfsSetCompM v = do
  cn <- dfsNextCompM
  cnm <- N.gets dfsEnvCompMap
  N.modify(\e->e{dfsEnvCompMap=IM.insert v cn cnm})
-- }}}

-----------------------------------------------------------------------------

-- | Partition-Refinement. Abstract datatype.
data PartRefine = PartRefine
  {partRefinePart :: PartRefinePart
  ,partRefineDeltaInv :: DeltaInv}
  __D
type EdgeLbl = Int
type EdgeLblMap = IntMap
type DeltaInv = EdgeLblMap (NodeMap NodeSet)
-- hidden
type PartRefineSize = Int
data PartRefinePart = PRP
  {prpNext   :: !Node
  ,prpC2Size :: NodeMap PartRefineSize
  ,prpN2C    :: NodeMap Int
  ,prpClass  :: IntMap NodeSet}
  __D

class PartRefinePrep a where
  partRefinePrep :: a -> (Partition, DeltaInv)
instance PartRefinePrep (Partition, DeltaInv) where
  partRefinePrep = id

partRefineInit :: (PartRefinePrep a) => a -> PartRefine
partRefineInit a
  | (part, dinv) <- partRefinePrep a
  = go part dinv
  where go :: Partition -> DeltaInv -> PartRefine
        go (n2i,i2ns) dinv
          | IM.null n2i || IM.null i2ns || IM.null dinv
          = PartRefine
              {partRefinePart=PRP 0 mempty mempty mempty
              ,partRefineDeltaInv=mempty}
          | prpNext <- 1 + maxKey i2ns
          , prpC2Size <- fmap IM.size i2ns
          , prpN2C <- n2i
          , prpClass <- i2ns
          , partRefinePart <- PRP{..}
          , partRefineDeltaInv <- dinv
          = PartRefine{..}
          where maxKey m
                  | Just ((k,_),_) <- IM.maxViewWithKey m = k
                  | otherwise = __IMPOSSIBLE

partRefinePartition :: PartRefine -> Partition
partRefinePartition PartRefine{..}
  | PRP{..} <- partRefinePart
  = (prpN2C, prpClass)

-- | Hopcroft's Partition-Refinement Algorithm
partRefineRefine :: PartRefine -> PartRefine
partRefineRefine PartRefine{..}
  | partRefinePart <- hopcroft partRefineDeltaInv partRefinePart
  = PartRefine{..}
  where hopcroft :: DeltaInv -> PartRefinePart -> PartRefinePart
        hopcroft dinv part = go (part, toSets part)
          where elbls = edgeLbls dinv
                go :: PartRefineStepState -> PartRefinePart
                go (ps,[]) = ps
                go (ps,l:ls) = go (fold l (ps,ls))
                fold l s = foldl' (\s elbl->
                  partRefineStep s (deltaInv dinv elbl l)
                  ) s elbls
                toSets :: PartRefinePart -> [NodeSet]
                toSets PRP{..} = IM.elems prpClass
                edgeLbls :: DeltaInv -> [EdgeLbl]
                edgeLbls = IM.keys
                deltaInv :: DeltaInv -> EdgeLbl -> NodeSet -> NodeSet
                deltaInv dinv e ns
                  = IM.fold (\/) mempty
                      ((IM.findWithDefault mempty e dinv) `IM.intersection` ns)

type PartRefineStepState = (PartRefinePart, [NodeSet])
partRefineStep :: PartRefineStepState -> NodeSet -> PartRefineStepState
partRefineStep s a = go s a
  where go s@(PRP{prpN2C},_) a
          | IM.null a = s
          | i <- minKey a
          , cls <- prpN2C IM.! i
          , (snew, anew) <- refineOne s cls a
          = go snew anew
        minKey m
          | Just ((k,_),_) <- IM.minViewWithKey m = k
          | otherwise = __IMPOSSIBLE
        refineOne
          :: PartRefineStepState -> Int
          -> NodeSet -> (PartRefineStepState, NodeSet)
        refineOne s@(part@PRP{prpClass},ls) cls dinv
          | p <- prpClass IM.! cls
          , p1 <- p/\dinv
          , p2 <- p\\p1
          , xdinv <- dinv\\p -- this is an optimization
          , o1 <- IM.null p1
          , o2 <- IM.null p2
          = case (o1,o2) of
              (True,True)-> __IMPOSSIBLE
              (True,False) | __ASSERT(p == p2)-> (s, xdinv)
              (False,True) | __ASSERT(p == p1)-> (s, xdinv)
              (False,False)
                | (part, p0) <- split part cls p1 p2
                -> ((part, p0:ls), xdinv)
        split
          :: PartRefinePart -> Int
          -> NodeSet -> NodeSet
          -> (PartRefinePart, NodeSet)
        -- Splits the smaller of the two sets into a new class, and
        -- returns the smaller one. It MUST be the case and is UNCHECKED
        -- that the two sets are NONMEMPTY. And it MUST be the case and
        -- is UNCHECKED that the two sets form a partition of the class
        -- identified by the @Int@.
        split PRP{..} cls p1 p2
          | n1 <- IM.size p1 -- XXX: O(n)
          , n2 <- (prpC2Size IM.! cls) - n1
          , let go x1 x2 m1 m2
                  | !new <- prpNext
                  , !prpNext <- prpNext + 1
                  , !prpN2C <- fmap (const new) x2`IM.union`prpN2C
                  , !prpC2Size <- IM.insert cls m1 prpC2Size
                  , !prpC2Size <- IM.insert new m2 prpC2Size
                  , !prpClass <- IM.insert cls x1 prpClass
                  , !prpClass <- IM.insert new x2 prpClass
                  = PRP{..}
          = case n1 <= n2 of
              True  | !out <- go p1 p2 n1 n2-> (out, p1)
              False | !out <- go p2 p1 n2 n1-> (out, p2)

-----------------------------------------------------------------------------

#if 0
class Linked a where
  getMinks :: a -> [Node]
  setMinks :: a -> [Node] -> a
class (Ord k) => KeyOf a k where
  keyOf :: a -> k
class SuccsOf a where
  succsOf :: a -> NodeSet
#endif

data NodeKey k = UniqKey | NodeKey k __D
class (Ord k) => NodeKeyed k a | a -> k where
  nodeKey :: a -> NodeKey k

-----------------------------------------------------------------------------

-- | @partRefinePartition . partRefineRefine . partRefineInit@
shareCyclic :: (Ord k) => NodeMap (k, [Node]) -> Partition
shareCyclic dfa
  | o <- partRefineInit dfa
  , o <- partRefineRefine o
  = partRefinePartition o

-- | There is a lot of copy-paste duplication in the next threee instances:
instance (Ord k) => PartRefinePrep (NodeMap (k, EdgeLblMap Node)) where
  partRefinePrep dfa
    | (dinv,kpart) <- IM.foldWithKey go mempty dfa
    , part <- toPartition (M.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | part <- M.insertWith (\/) key (IM.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)
          updateDeltaInv :: Node -> EdgeLblMap Node -> DeltaInv -> DeltaInv
          updateDeltaInv i js dinv
            = IM.foldWithKey go dinv js
            where !iset = IM.singleton i ()
                  go pos j dinv = IM.insertWith (\/)
                    pos (IM.singleton j iset) dinv
instance (Ord k) => PartRefinePrep (NodeMap (k, [Node])) where
  partRefinePrep dfa
    | (dinv,kpart) <- IM.foldWithKey go mempty dfa
    , part <- toPartition (M.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | part <- M.insertWith (\/) key (IM.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)
          updateDeltaInv :: Node -> [Node] -> DeltaInv -> DeltaInv
          updateDeltaInv i js dinv
            = IM.foldWithKey go dinv (IM.fromList . zip [0..] $ js)
            where !iset = IM.singleton i ()
                  go pos j dinv = IM.insertWith (\/)
                    pos (IM.singleton j iset) dinv
data MyNodeKey k = MyUniqKey !Int | MyNodeKey k deriving(Eq,Ord)
instance (Ord k) => PartRefinePrep (NodeMap (NodeKey k, [Node])) where
  partRefinePrep dfa
    | (dinv,kpart) <- IM.foldWithKey go mempty dfa
    , part <- toPartition (M.elems kpart)
    = (part, dinv)
    where go i (key,js) (dinv,part)
            | newkey <- case key of
                UniqKey-> MyUniqKey i
                NodeKey k-> MyNodeKey k
            , part <- M.insertWith (\/) newkey (IM.singleton i ()) part
            , dinv <- updateDeltaInv i js dinv
            = (dinv,part)
          updateDeltaInv :: Node -> [Node] -> DeltaInv -> DeltaInv
          updateDeltaInv i js dinv
            = IM.foldWithKey go dinv (IM.fromList . zip [0..] $ js)
            where !iset = IM.singleton i ()
                  go pos j dinv = IM.insertWith (\/)
                    pos (IM.singleton j iset) dinv

-----------------------------------------------------------------------------

flattenAcyclicToOneLevel :: Graph -> Either (IntMap NodeSet) (NodeMap NodeSet)
flattenAcyclicToOneLevel g
  | scc <- sccInit g
  , topo <- sccTopoAssertAcyclic scc
  = case topo of
      Left comps
        | let go c _ = sccGetCompNodes scc c
        -> Left (IM.mapWithKey go comps)
      Right ns
        | tclos <- foldl' step g ns
        -> Right tclos
  where step acc i
          | js <- g IM.! i
          , ks <- IM.foldWithKey (\j _ o-> o \/ (acc IM.! j)) js js
          = IM.insert i ks acc

shareOneLevel :: (Ord k) => NodeMap (k, [Node]) -> Partition
shareOneLevel = toPartition . fst . flip shareOneLevelWith mempty

shareAcyclic :: (Ord k) => NodeMap (k, [Node]) -> Partition
shareAcyclic = toPartition . fst . flip shareAcyclicWith mempty

shareOneLevelWith :: (Ord k) => NodeMap (k, [Node]) -> MemoTrie k -> (NodeMap Node, MemoTrie k)
shareOneLevelWith g memo = IM.foldWithKey go (mempty,memo) g
  where go i (k,js) (rn,memo)
          | Just trie <- M.lookup k memo
          = case lookupIT js trie of
              Just new-> rnTo i new rn memo
              Nothing-> add i k js rn memo trie
          | otherwise = add i k js rn memo mempty
        add old k js rn memo trie
          | !trie <- insertIT js old trie
          , !memo <- M.insert k trie memo
          , !rn   <- IM.insert old old rn
          = (rn,memo)
        rnTo old new rn memo
          | !rn <- IM.insert old new rn
          = (rn,memo)

shareAcyclicWith :: (Ord k) => NodeMap (k, [Node]) -> MemoTrie k -> (NodeMap Node, MemoTrie k)
shareAcyclicWith dfa memo
  | ns <- topo dfa
  , (rn,memo) <- foldl' go (mempty,memo) ns
  = (rn,memo)
  where topo dfa
          | g <- fmap (fromList . flip zip (repeat ()) . snd) $ dfa
          , nss <- sccTopo . sccInit . legalize $ g
          = concatMap (IM.keys . (`IM.intersection` dfa)) nss
        go (rn,memo) i
          | (k,js) <- dfa IM.! i
          , js <- rename rn js
          = case () of
              _ | Just trie <- M.lookup k memo
                -> case lookupIT js trie of
                    Just new-> rnTo i new rn memo
                    Nothing-> add i k js rn memo trie
                | otherwise-> add i k js rn memo mempty
        rename rn js = fmap go js
          where go j = maybe j id (IM.lookup j rn)
        add old k js rn memo trie
          | !trie <- insertIT js old trie
          , !memo <- M.insert k trie memo
          , !rn   <- IM.insert old old rn
          = (rn,memo)
        rnTo old new rn memo
          | !rn <- IM.insert old new rn
          = (rn,memo)
type MemoTrie k = Map k (IntTrie Node)
data IntTrie b = Trie
  !(Maybe b)
  !(IntMap (IntTrie b))
  deriving(Eq,Ord,Read,Show)
instance Functor IntTrie where
  fmap f (Trie a m) = Trie (fmap f a)
                           ((fmap . fmap) f m)
instance Monoid (IntTrie b) where
  mempty = Trie Nothing IM.empty
  mappend _ _ = __IMPOSSIBLE("mappend<IntTrie<_>>")
nullIT :: IntTrie b -> Bool
nullIT (Trie Nothing m) = IM.null m
nullIT _ = False
fromListIT :: [([Int], b)] -> IntTrie b
fromListIT = foldl' ((flip . uncurry) insertIT) mempty
toListIT :: IntTrie b -> [([Int], b)]
toListIT trie = maybe [] (\a->[([],a)]) a ++ (go [] =<< ts)
  where (a, ts) = toTreeIT trie
        go acc (Node (a,c) ts)
          = maybe (go (c:acc) =<< ts)
                  (\a -> (reverse (c:acc),a)
                          : (go (c:acc) =<< ts)) a
elemsIT :: IntTrie b -> [b]
elemsIT (Trie Nothing m) = elemsIT =<< IM.elems m
elemsIT (Trie (Just b) m) = b : (elemsIT =<< IM.elems m)
toTreeIT :: IntTrie b -> (Maybe b, [Tree (Maybe b,Int)])
toTreeIT (Trie a m) = (a, go m)
  where reassoc (k, Trie a m) = Node (a,k) (go m)
        go = fmap reassoc . IM.toList
insertIT :: [Int] -> b -> IntTrie b -> IntTrie b
insertIT [] a (Trie _ m) = Trie (Just a) m
insertIT (k:ks) a (Trie x m)
  | t <- maybe mempty id (IM.lookup k m)
  , t <- insertIT ks a t
  , m <- IM.insert k t m
  = Trie x m
insertWithIT :: (b -> b -> b) -> [Int] -> b -> IntTrie b -> IntTrie b
insertWithIT f = go
  where go [] new (Trie Nothing m)
          = Trie (Just new) m
        go [] new (Trie (Just old) m)
          | new <- f new old
          = Trie (Just new) m
        go (k:ks) new (Trie x m)
          | t <- maybe mempty id (IM.lookup k m)
          , t <- go ks new t
          , m <- IM.insert k t m
          = Trie x m
lookupIT :: [Int] -> IntTrie b -> Maybe b
lookupIT [] (Trie a _) = a
lookupIT (k:ks) (Trie _ m) = lookupIT ks =<< IM.lookup k m

-----------------------------------------------------------------------------
