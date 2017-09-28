{-# OPTIONS -pgmP cpp -optP-w #-}
{-# LANGUAGE
      CPP,
      MagicHash,
      BangPatterns,
      OverlappingInstances,
      UndecidableInstances #-}
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

module MM.Data.Graph.Int (
   Graph,PredGraph,Node,NodeMap,NodeSet
  ,Partition,Cover,IsPartition(..)

  ,isLegal,legalize,nodes
  ,invert,predGraph,succGraph,invertForest
  ,fromAdj,toAdj
  ,quotientGraph,inducedSubgraph,inducedSubgraphs

  ,PartRefine,EdgeLbl,EdgeLblMap,DeltaInv
  ,partRefineInit -- :: Partition -> DeltaInv -> PartRefine
  ,partRefineRefine -- :: PartRefine -> PartRefine

  ,DomTree(..),domTreeInit,domTreeRevPostOrder
  ,DomFront,domFrontInit,domFront
  ,DomFrontPlus,domFrontPlusInit,domFrontPlus

  ,SCC,SCCData,Cyclicity(..)
  ,sccInit
  ,sccTopo
  ,sccCyclicity,sccAcyclic,sccCyclic

  ,DFN,DFNEdge(..)
  ,dfnInit
  ,dfnClassifyEdge
  ,dfnN2Pre,dfnN2Post,dfnPre2N,dfnPost2N
  ,dfnPre,dfnPost
  ,dfnPreOrder,dfnPostOrder,dfnRevPreOrder,dfnRevPostOrder
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
import MM.Data.Class.Lattice
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
  ,compsData :: IntMap a}
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
quotientGraph g _ = undefined

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
domFrontInit dt = undefined

domFront :: DomFront -> Node -> NodeSet
domFront df i = undefined

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
domFrontPlusInit df = undefined

domFrontPlus :: DomFrontPlus -> Node -> (NodeSet, DomFrontPlus)
domFrontPlus dfp i = undefined

-----------------------------------------------------------------------------

type SCC = Components SCCData
type SCCData = Cyclicity
data Cyclicity = Acyclic | Cyclic __D_BE

sccInit :: Graph -> SCC
sccInit g
  | sccs <- sccEnvSCCs (execSccM sccTarjanM (initSCCEnv g))
  , comps <- IM.fromList . zip [0..] . reverse $ sccs
  , compsPart <- toPartition comps
  , compsData <- fmap go comps
  = Comps{..}
  where go :: NodeSet -> SCCData
        go ns
          | Just ((n,_),rest) <- IM.minViewWithKey ns
          = case IM.null rest of
              False-> Cyclic
              True
                | n`IM.member`(IM.findWithDefault mempty n g)-> Cyclic
                | otherwise-> Acyclic
          | otherwise = __IMPOSSIBLE

sccTopo :: SCC -> [NodeSet]
sccTopo Comps{compsPart} = fromPartition compsPart

sccCyclicity :: SCC -> Map Cyclicity NodeSet
sccCyclicity scc
  | xa <- sccAcyclic scc
  , xc <- sccCyclic scc
  = M.fromList [(Acyclic, xa), (Cyclic, xc)]

sccAcyclic :: SCC -> NodeSet
sccAcyclic Comps{compsData} = IM.foldWithKey go mempty compsData
  where go i Acyclic o = IM.insert i () o
        go i _ o = o

sccCyclic :: SCC -> NodeSet
sccCyclic Comps{compsData} = IM.foldWithKey go mempty compsData
  where go i Cyclic o = IM.insert i () o
        go i _ o = o

-- {{{
type SccM a = SU SCCEnv a
data SCCEnv = SCCEnv
  {sccEnvGraph   :: Graph
  ,sccEnvIndex   :: NodeMap Int
  ,sccEnvLowLink :: NodeMap Int
  ,sccEnvStacked :: NodeSet
  ,sccEnvStack   :: [Node]
  ,sccEnvSCCs    :: [NodeSet]}
execSccM :: SccM a -> SCCEnv -> SCCEnv
execSccM m env | (_,env) <- execSU m 0 env = env
initSCCEnv :: Graph -> SCCEnv
initSCCEnv g = SCCEnv
  {sccEnvGraph   = g
  ,sccEnvIndex   = mempty
  ,sccEnvLowLink = mempty
  ,sccEnvStacked = mempty
  ,sccEnvStack   = []
  ,sccEnvSCCs    = []}
sccTarjanM :: SccM ()
sccTarjanM = mapM_ go =<< gets (IM.keys . nodes . sccEnvGraph)
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
  SCCEnv{..} <- get
  case () of
    _ | (comp,sccEnvStack) <- split i sccEnvStack
      , !sccEnvStacked <- foldl' (flip IM.delete) sccEnvStacked comp
      , sccEnvSCCs <- IM.fromList (zip comp (repeat ())):sccEnvSCCs
      , !new <- SCCEnv{..}
      -> set new
  where split i js = go [] js
          where go acc [] = (acc,[])
                go acc (j:js)
                  | i==j = (i:acc,js)
                  | otherwise = go (j:acc) js
sccIndexM :: Node -> SccM Int
sccIndexM i = gets ((IM.! i) . sccEnvIndex)
sccLowLinkM :: Node -> SccM Int
sccLowLinkM i = gets ((IM.! i) . sccEnvLowLink)
sccSetLowLinkToMin :: Node -> Int -> SccM ()
sccSetLowLinkToMin i m = do
  lowlink <- gets sccEnvLowLink
  let !new = IM.adjust (min m) i lowlink
  modify(\e->e{sccEnvLowLink=new})
sccPushM :: Node -> SccM ()
sccPushM i = do
  m <- newUniqM
  SCCEnv{..} <- get
  case () of
    _ | !index      <- m - 1
      , !sccEnvIndex   <- IM.insert i index sccEnvIndex
      , !sccEnvLowLink <- IM.insert i index sccEnvLowLink
      , !sccEnvStacked <- IM.insert i () sccEnvStacked
      , !sccEnvStack   <- i:sccEnvStack
      , !new        <- SCCEnv{..}
      -> set new
sccSeenM :: Node -> SccM Bool
sccSeenM i = gets (IM.member i . sccEnvIndex)
sccSuccsM :: Node -> SccM NodeSet
sccSuccsM i = gets ((IM.! i) . sccEnvGraph)
sccStackedM :: Node -> SccM Bool
sccStackedM i = gets (IM.member i . sccEnvStacked)
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
type DfsM t a = SU2 (DfsEnv t) a
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
execDfsM m env | (_,_,env) <- execSU2 m 1 1 env = env
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
  spant <- gets dfsEnvSpanning
  modify(\e->e{dfsEnvSpanning
    =IM.insertWith IM.union v ws spant})
dfsSeenM :: Node -> DfsM a Bool
dfsSeenM v = gets ((v`IM.member`) . dfsEnvSeenNodes)
dfsSuccsM :: Node -> DfsM a (NodeSet)
dfsSuccsM v = gets ((IM.! v) . dfsEnvGraph)
dfsUnSeenM :: NodeSet -> DfsM a (NodeSet)
dfsUnSeenM s = gets
  ((s `IM.difference`)
    . dfsEnvSeenNodes)
dfsAddSeenM :: Node -> DfsM a ()
dfsAddSeenM i = dfsUnionSeenM (IM.singleton i ())
dfsUnionSeenM :: NodeSet -> DfsM a ()
dfsUnionSeenM s = do
  seen <- gets dfsEnvSeenNodes
  modify(\e->e{dfsEnvSeenNodes=seen`IM.union`s})
dfsNextCallM :: DfsM a Int
dfsNextCallM = newUniq1M
dfsNextCompM :: DfsM a Int
dfsNextCompM = newUniq2M
dfsSetCallM :: Node -> DfsM a ()
dfsSetCallM v = do
  dn <- dfsNextCallM
  dnm <- gets dfsEnvCallMap
  modify(\e->e{dfsEnvCallMap=IM.insert v dn dnm})
dfsSetCompM :: Node -> DfsM a ()
dfsSetCompM v = do
  cn <- dfsNextCompM
  cnm <- gets dfsEnvCompMap
  modify(\e->e{dfsEnvCompMap=IM.insert v cn cnm})
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

partRefineInit :: Partition -> DeltaInv -> PartRefine
partRefineInit (n2i,i2ns) dinv
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
                deltaInv dinv e ns = IM.fold (\/) mempty
                  ((dinv IM.! e) `IM.intersection` ns)

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
          , p2 <- p\\dinv
          , xdinv <- dinv\\p
          , o1 <- IM.null p1
          , o2 <- IM.null p2
          = case (o1,o2) of
              (True,True)-> __IMPOSSIBLE
              (True,False) | __ASSERT(p == p2)-> (s, xdinv)
              (False,True) | __ASSERT(p == p1)-> (s, xdinv)
              (False,False)
                | (part, p0) <- split part cls p1 p2
                -> ((part, p0:ls), xdinv)
        -- Splits the smaller of the two sets into a new class, and
        -- returns the smaller one. It MUST be the case and is UNCHECKED
        -- that the two sets are NONMEMPTY. And it MUST be the case and
        -- is UNCHECKED that the two sets form a partition of the class
        -- identified by the @Ix CLASS@.
        split
          :: PartRefinePart -> Int
          -> NodeSet -> NodeSet
          -> (PartRefinePart, NodeSet)
        split PRP{..} cls p1 p2
          | n1 <- IM.size p1 -- XXX: O(n)
          , n2 <- (prpC2Size IM.! cls) - n1
          , let go x1 x2 m1 m2
                  | !new <- prpNext
                  , !prpNext <- prpNext + 1
                  , !prpN2C <- fmap (const new) x2`IM.intersection`prpN2C
                  , !prpC2Size <- IM.insert cls m1 prpC2Size
                  , !prpC2Size <- IM.insert new m2 prpC2Size
                  , !prpClass <- IM.insert cls x1 prpClass
                  , !prpClass <- IM.insert new x2 prpClass
                  = PRP{..}
          = case n1 <= n2 of
              True  | !out <- go p1 p2 n1 n2-> (out, p1)
              False | !out <- go p2 p1 n2 n1-> (out, p2)

-----------------------------------------------------------------------------

class (Monad m) => StateM m s | m -> s where
  get :: m s
  set :: s -> m ()
  gets :: (s -> a) -> m a
  modify :: (s -> s) -> m ()
  gets f = do s <- get; let {!a = f s}; return a
  modify f = do s <- get; let {!t = f s}; set t
class (Monad m) => ReaderM m r where
  ask :: m r
  asks :: (r -> a) -> m a
  asks f = do r <- ask; let {!a = f r}; return a
class (Monad m) => WriterM m w where
  tell :: w -> m ()
class (Monad m) => ContM m where
  callCC :: ((a -> m b) -> m a) -> m a
class (Monad m) => UniqM m where
  newUniqM :: m Int
  getUniqM :: m Int
  setUniqM :: Int -> m ()
  swapUniqM :: Int -> m Int
  newUniqM = do
    i <- getUniqM
    let !j = i + 1
    setUniqM j
    return i
  swapUniqM i = do
    j <- getUniqM
    setUniqM i
    return j
class (Monad m) => Uniq2M m where
  newUniq1M :: m Int
  getUniq1M :: m Int
  setUniq1M :: Int -> m ()
  swapUniq1M :: Int -> m Int
  newUniq2M :: m Int
  getUniq2M :: m Int
  setUniq2M :: Int -> m ()
  swapUniq2M :: Int -> m Int
  newUniq1M = do
    i <- getUniq1M
    let !j = i + 1
    setUniq1M j
    return i
  swapUniq1M i = do
    j <- getUniq1M
    setUniq1M i
    return j
  newUniq2M = do
    i <- getUniq2M
    let !j = i + 1
    setUniq2M j
    return i
  swapUniq2M i = do
    j <- getUniq2M
    setUniq2M i
    return j

newtype SU s a = SU {unSU :: forall o. (a -> Int -> s -> o) -> Int -> s -> o}
runSU :: SU s a -> Int -> s -> (a,(Int,s))
runSU (SU g) (i) = g (\a i s-> (a,(i,s))) i
evalSU :: SU s a -> Int -> s -> a
evalSU (SU g) (i) = g (\a _ _-> a) i
execSU :: SU s a -> Int -> s -> (Int,s)
execSU (SU g) (i) = g (\_ i s-> (i,s)) i
instance Functor (SU s) where
  fmap f (SU g) = SU (\k -> g (k . f))
instance Monad (SU s) where
  return a = SU (\k -> k a)
  SU g >>= f = SU (\k -> g (\a -> unSU (f a) k))
instance Applicative (SU s) where
  pure = return
  (<*>) = ap
instance StateM (SU s) s where
  get = SU (\k i s-> k s i s)
  gets f = SU (\k i s-> k (f s) i s)
  set s = SU (\k i _-> k () i s)
  modify f = SU (\k i s-> k () i (f s))
instance UniqM (SU s) where
  newUniqM = SU (\k i-> k (i) (i + 1))
  getUniqM = SU (\k i-> k (i) i)
  setUniqM (i) = SU (\k _ -> k () i)
  swapUniqM (j) = SU (\k i-> k (i) j)

newtype SU2 s a = SU2 {unSU2 :: forall o. (a -> Int -> Int -> s -> o) -> Int -> Int -> s -> o}
runSU2 :: SU2 s a -> Int -> Int -> s -> (a,(Int,Int,s))
evalSU2 :: SU2 s a -> Int -> Int -> s -> a
execSU2 :: SU2 s a -> Int -> Int -> s -> (Int,Int,s)
runSU2 (SU2 g) (i) (j) = g (\a i j s-> (a,(i,j,s))) i j
evalSU2 (SU2 g) (i) (j) = g (\a _ _ _-> a) i j
execSU2 (SU2 g) (i) (j) = g (\_ i j s-> (i,j,s)) i j
instance Functor (SU2 s) where
  fmap f (SU2 g) = SU2 (\k -> g (k . f))
instance Monad (SU2 s) where
  return a = SU2 (\k -> k a)
  SU2 g >>= f = SU2 (\k -> g (\a -> unSU2 (f a) k))
instance Applicative (SU2 s) where
  pure = return
  (<*>) = ap
instance StateM (SU2 s) s where
  get = SU2 (\k i j s-> k s i j s)
  gets f = SU2 (\k i j s-> k (f s) i j s)
  set s = SU2 (\k i j _-> k () i j s)
  modify f = SU2 (\k i j s-> k () i j (f s))
instance UniqM (SU2 s) where
  newUniqM = newUniq1M
  getUniqM = getUniq1M
  setUniqM = setUniq1M
  swapUniqM = swapUniq1M
instance Uniq2M (SU2 s) where
  newUniq1M = SU2 (\k i j-> k (i) (i + 1) j)
  getUniq1M = SU2 (\k i j-> k (i) i j)
  setUniq1M (i) = SU2 (\k _ j -> k () i j)
  swapUniq1M (i') = SU2 (\k i j-> k (i) i' j)
  newUniq2M = SU2 (\k i j-> k (j) i (j + 1))
  getUniq2M = SU2 (\k i j-> k (j) i j)
  setUniq2M (j) = SU2 (\k i _-> k () i j)
  swapUniq2M (j') = SU2 (\k i j-> k (j) i j')

-----------------------------------------------------------------------------
