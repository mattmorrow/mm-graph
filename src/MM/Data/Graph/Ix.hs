{-# OPTIONS -pgmP cpp -optP-w #-}
{-# LANGUAGE CPP #-}
#define __D deriving(Eq,Ord,Read,Show)
#define __D_BE deriving(Eq,Ord,Read,Show,Bounded,Enum)

module MM.Data.Graph.Ix (
) where


#if 0
   IxSet_,Partition,Cover,Graph,Graph_(..)

  ,idom_SimpleFast_TEST,idom_SimpleFast
  ,fromAdj,g0,g1

  ,isLegal,legalize,nodes,invert
  ,inducedSubgraph,quotientGraph
  ,CCs(..),CC(..),ccInit
  ,SCCs(..),SCC(..),sccInit
  ,DFN,DFSEdge(..),dfnInit,dfnClassifyEdge,dfnN2Pre,dfnN2Post,dfnPre2N,dfnPost2N,dfnPre,dfnPost,dfnPreOrder,dfnPostOrder,dfnRevPreOrder,dfnRevPostOrder
  ,NCA,ncaInit,nca
  ,DomTree,domTreeInit,domTreeIDom
  ,DomFront,domFrontInit,domFront
  ,DomFrontPlus,domFrontPlusInit,domFrontPlus
  ,PartRefine,partRefineInit,partRefine
) where

IMPORT_MM_DATA_IX
IMPORT_MM_DATA_INTMAPSET
IMPORT_MM_DATA_UF
IMPORT_MM_DATA_UTIL
IMPORT_MM_DATA_CLASSES
IMPORT_MM_DATA_EXTERNAL
import qualified MM.Data.Ix.Types as Ix(castIx,castIxArg,castIxArg2)
import qualified MM.Control.Monad.S.U2 as U2
import Unsafe.Coerce(unsafeCoerce)
import System.IO.Unsafe

-----------------------------------------------------------------------------

type Graph a = IxMap a (IxSet_ a)
type Tree a = Graph a
type Partition a b = (IxMap a (Ix b), IxMap b (IxSet_ a))
type Cover a b = (IxMap a (IxSet_ a), IxMap b (IxSet_ a))

data Graph_ a = Graph
  {
   graphSuccs :: IxMap a (IxSet_ a)
  ,graphPreds :: IxMap a (IxSet_ a)
  } __D

-- | XXX:FIXME:not here
type IxSet_ a = IxMap a ()

#if 1
g0 = fromAdj
  [(1,[2,3])
  ,(2,[3])
  ,(3,[4])
  ,(4,[3,5,6])
  ,(5,[7])
  ,(6,[7])
  ,(7,[4,8])
  ,(8,[3,9,10])
  ,(9,[1])
  ,(10,[7])]

g1 = fromAdj
  [(0,[1])
  ,(1,[2,3])
  ,(2,[7])
  ,(3,[4])
  ,(4,[5,6])
  ,(5,[7])
  ,(6,[4])
  ,(7,[])]
#endif

-----------------------------------------------------------------------------

-- | All graph algorithms ASSUME a "legal" graph. See @legalize@.
isLegal :: Graph a -> Bool
isLegal g = Ix.size (g `Ix.difference` nodes g) == 0

-- | Ensures every node is present in the domain of the map.
legalize :: Graph a -> Graph a
legalize g = g \/ fmap (const mempty) (nodes g)

nodes :: Graph a -> IxMap a ()
nodes g = Ix.foldWithKey go mempty g
  where go i is acc = Ix.insert i () (acc \/ is)

invert :: forall a. Graph a -> Graph a
invert g = Ix.foldWithKey go (fmap (const mempty) g) g
  where go :: Ix a -> IxSet_ a -> Graph a -> Graph a
        go i js acc
          | !is <- Ix.singleton i ()
          = Ix.foldWithKey (\j _ acc-> Ix.insertWith (\/) j is acc) acc js

fromAdj :: [(Ix a, [Ix a])] -> Graph a
fromAdj = fmap (\is-> fromList (zip is (repeat ()))) . fromList

-----------------------------------------------------------------------------

inducedSubgraph :: Graph a -> IxSet_ a -> Graph a
inducedSubgraph g ns = Ix.foldWithKey (\i is acc->
    let !js = is`Ix.intersection`ns
    in Ix.insert i js acc
  ) mempty (g`Ix.intersection`ns)

quotientGraph :: Graph a -> Partition a b -> Graph b
quotientGraph g _ = undefined

-----------------------------------------------------------------------------

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

-----------------------------------------------------------------------------

data DomTree a = DomTree
  {domTreeRoot :: !(Ix a)
  ,domTreeParent :: IxMap a (Ix a)
  ,domTreeChildren :: IxMap a (IxSet_ a)}
  __D
newtype DomFront a = DomFront
  {domFrontDF :: IxMap a (IxSet_ a)}
  __D
data DomFrontPlus a = DomFrontPlus
  {domFrontPlusDF :: DomFront a
  ,domFrontPlusDFPlus :: IxMap a (IxSet_ a)}
  __D

domTreeInit :: Graph a -> Ix a -> DomTree a
domTreeInit g root = undefined
domTreeIDom :: DomTree a -> Ix a -> Ix a
domTreeIDom DomTree{domTreeParent} i = domTreeParent Ix.! i

idom_SimpleFast_TEST :: Graph a -> Ix a -> IxMap a (Ix a)
idom_SimpleFast_TEST g root
  | dfn <- dfnInit g root
  , dfnpost <- dfnN2Post dfn
  , dfnpostinv <- dfnPost2N dfn
  , preds <- invert g
  = idom_SimpleFast dfnpost dfnpostinv preds root
idom_SimpleFast
  :: forall a.
     IxMap a Int    -- PostDfn
  -> IntMap (Ix a)  -- PostDfnInv
  -> Graph a        -- PREDECESSORS
  -> Ix a
  -> IxMap a (Ix a) -- idom
idom_SimpleFast dfn dfninv preds root = while (Ix.singleton root root)
  where rpo = drop 1 (reverse (IM.elems dfninv))
        while :: IxMap a (Ix a) -> IxMap a (Ix a)
        while idom
          | (changed,idom) <- foldl' go (False,idom) rpo
          = if changed then while idom else idom
        go :: (Bool, IxMap a (Ix a)) -> Ix a -> (Bool, IxMap a (Ix a))
        go acc@(changed,idom) i
          | ps <- (preds Ix.! i)`Ix.intersection`idom
          , not (Ix.null ps)
          , j <- Ix.minKeyWithDefault 0 ps
          , js <- Ix.delete j ps
          , let loop k _ newidom = intersect dfn idom k newidom
          , newidom <- Ix.foldWithKey loop j js
          , case Ix.lookup i idom of
              Just x-> x/=newidom
              Nothing-> True
          , !idom <- Ix.insert i newidom idom
          = (True,idom)
          | otherwise = acc
        intersect
          :: forall a.
             IxMap a Int -- PostDfn
          -> IxMap a (Ix a) -- parent
          -> Ix a -> Ix a -> Ix a
        intersect dfn parent i j = go i j
          where go :: Ix a -> Ix a -> Ix a
                go i j
                  | i==j = i
                  | i <- walk i j
                  , j <- walk j i
                  = go i j
                walk :: Ix a -> Ix a -> Ix a
                walk i j = loop (dfn Ix.! j) i
                  where loop !nj !i
                          | ni <- dfn Ix.! i
                          , ni < nj
                          = loop nj (parent Ix.! i)
                          | otherwise = i

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
domFrontInit :: DomTree a -> DomFront a
domFrontInit dt = undefined
domFront :: DomFront a -> Ix a -> IxSet_ a
domFront df i = undefined

domFrontPlusInit :: DomFront a -> DomFrontPlus a
domFrontPlusInit df = undefined
domFrontPlus :: DomFrontPlus a -> Ix a -> (IxSet_ a, DomFrontPlus a)
domFrontPlus dfp i = undefined

#if 0
NOTE:
Nodes a and b have the same control depencies iff a and b are cycle
equivalent in the strongly connected component formed by adding end->start
to the CFG.
#endif

-----------------------------------------------------------------------------

data PartRefine a = PartRefine
  {
  } __D

partRefineInit :: ()
partRefineInit = undefined

partRefine :: PartRefine a -> PartRefine a
partRefine p = undefined

-----------------------------------------------------------------------------

-- | Connected Components
data CCs a = CCs
  {ccsPartition :: Partition a (CC a)
  ,ccsComponents :: IxMap (CC a) (CC a)}
  __D
newtype CC a = CC
  {ccGraph :: Graph a
  } __D

-- XXX:figure out the Ix casts so no have to unsafeCoerce.
ccInit :: Graph a -> CCs a
ccInit g
  | uf <- singletons g
  , (# _,uf #) <- foldl2 go mempty uf (Ix.keys g)
  , (i2x, x2g) <- UF.quotient' uf
  , x2is <- (fmap . fmap) (const ()) x2g
  , ccsPartition <- unsafeCoerce (i2x, x2is)
  , ccsComponents <- unsafeCoerce (fmap CC x2g) --ugh,the fmap
  = CCs{..}
  where go seen uf i
          | i`Ix.member`seen
          = (# seen,uf #)
          | ss <- Ix.keys (g Ix.! i)
          , !seen <- Ix.insert i () seen
          , !uf <- foldl' (\uf j-> UF.unionWith_ Ix.union uf i j) uf ss
          = foldl2 go seen uf ss
        singletons :: Graph a -> UF a (Graph a)
        singletons = flip Ix.foldWithKey mempty
          (\i is acc-> UF.unsafeInsert acc i (Ix.singleton i is))

-----------------------------------------------------------------------------

-- | Strongly Connected Components
data SCCs a = SCCs
  {sccsPartition :: Partition a (SCC a)
  ,sccsComponents :: IxMap (SCC a) (SCC a)}
  __D
newtype SCC a = SCC
  {sccCyclicity :: Cyclicity
  } __D
data Cyclicity = Acyclic | Cyclic __D_BE

sccInit :: Graph a -> SCCs a
sccInit g = undefined

---- Data.Graph.SCC's interface
--scc :: Graph -> ([(Int, [Vertex])], Vertex -> Int)
--sccList :: Graph -> [SCC Vertex]
--sccListR :: Graph -> [SCC (Vertex, [Vertex])]
--sccGraph :: Graph -> [(SCC Int, Int, [Int])]
--stronglyConnComp :: Ord key => [(node, key, [key])] -> [SCC node]
--stronglyConnCompR :: Ord key => [(node, key, [key])] -> [SCC (node, key, [key])]

#if 0
data SccOps0 = SccOps0
  {sccMap_0   :: Graph a -> IxMap a Int
  ,sccMaps_0  :: Graph a -> (IxMap a Int, IntMap (IxSet_ a))
  --
  ,iscc_0     :: Graph a -> [[Ix a]]
  ,iscc2_0    :: Graph a -> [(Int, [Ix a])]
  ,iscc3_0    :: Graph a -> IntMap [Ix a]
  ,iscc4_0    :: Graph a -> IntMap (IxSet_ a)
  --
  ,scc_0      :: Graph a -> [SCC (Ix a) [Ix a]]
  ,scc2_0     :: Graph a -> [(Int, SCC (Ix a) [Ix a])]
  ,scc3_0     :: Graph a -> IntMap (SCC (Ix a) [Ix a])
  ,scc4_0     :: Graph a -> IntMap (SCC (Ix a) (IxSet_ a))}
#endif

#if 0
module MM.Algo.Graph.SCC.Kosaraju where
{
  -- ///////////////////////////////
  sccMap  :: Graph -> NodeMap Int
  -- ///////////////////////////////
  iscc    :: Graph -> [[Node]]
  iscc2   :: Graph -> [(Int, [Node])]
  itopo   :: Graph -> [Node]
  scc2    :: (Ord a) => [(a, [a])] -> [(Int, [a])]
  topo    :: (Ord a) => [(a, [a])] -> [a]
}
module MM.Algo.Graph.SCC.Tarjan where
{
  -- ///////////////////////////////
  tarjan_ :: Graph -> [[Node]]
  -- ///////////////////////////////
  tarjan  :: Graph -> [SCC Node [Node]]
}
#endif

-----------------------------------------------------------------------------

data DFN a = DFN
  {dfnN2Pre :: IxMap a Int
  ,dfnN2Post :: IxMap a Int
  ,dfnPre2N :: IntMap (Ix a)
  ,dfnPost2N :: IntMap (Ix a)}
  __D

data DFSEdge
  = TreeDFSEdge
  | ForwardDFSEdge
  | BackwardDFSEdge
  | CrossDFSEdge
  __D_BE

dfnPre :: DFN a -> Ix a -> Int
dfnPost :: DFN a -> Ix a -> Int
dfnPreOrder :: DFN a -> [Ix a]
dfnPostOrder :: DFN a -> [Ix a]
dfnRevPreOrder :: DFN a -> [Ix a]
dfnRevPostOrder :: DFN a -> [Ix a]
dfnPre DFN{dfnN2Pre} i = dfnN2Pre Ix.! i
dfnPost DFN{dfnN2Post} i = dfnN2Post Ix.! i
dfnPreOrder DFN{dfnPre2N} = IM.elems dfnPre2N
dfnPostOrder DFN{dfnPost2N} = IM.elems dfnPost2N
dfnRevPreOrder dfn = reverse (dfnPreOrder dfn)
dfnRevPostOrder dfn = reverse (dfnPostOrder dfn)

dfnClassifyEdge :: DFN a -> Ix a -> Ix a -> DFSEdge
dfnClassifyEdge DFN{..} i j
  | idn <- dfnN2Pre Ix.! i
  , jdn <- dfnN2Pre Ix.! j
  , icn <- dfnN2Post Ix.! i
  , jcn <- dfnN2Post Ix.! j
  , p1 <- idn < jdn
  , p2 <- icn < jcn
  = case (p1,p2) of
      (True,True)-> TreeDFSEdge
      (True,False)-> ForwardDFSEdge
      (False,True)-> BackwardDFSEdge
      (False,False)-> CrossDFSEdge

dfnInit :: Graph a -> Ix a -> DFN a
dfnInit g root
  | Dfs{..} <- dfs (root,g)
  , !dfnN2Pre <- dfsCallNum
  , !dfnN2Post <- dfsCompNum
  , !dfnPre2N <- Ix.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Pre
  , !dfnPost2N <- Ix.foldWithKey (\i n acc-> IM.insert n i acc) mempty dfnN2Post
  = DFN{..}
-- {{{
data Dfs a = Dfs
  {dfsSpanning  :: (Ix a, Graph a)
  ,dfsCallNum   :: IxMap a Int
  ,dfsCompNum   :: IxMap a Int} __D
dfs :: (Ix a, Graph a) -> Dfs a
dfs rg@(r,g)
  | DfsEnv{..}  <- execDfsM (dfsM r) (initDfsEnv rg)
  = Dfs
      (dfsEnvRoot,dfsEnvSpanning)
      (dfsEnvCallMap)
      (dfsEnvCompMap)
type DfsM t a = U2.S (DfsEnv t) a
data DfsEnv a = DfsEnv
  {dfsEnvRoot :: !(Ix a) -- RO
  ,dfsEnvGraph :: Graph a -- RO
  ,dfsEnvSpanning :: Graph a -- WO
  ,dfsEnvSeenNodes :: IxSet_ a -- RW
  ,dfsEnvCallMap :: IxMap a Int -- WO
  ,dfsEnvCompMap :: IxMap a Int} -- WO
dfsM :: Ix a -> DfsM a ()
dfsM v = do
  setCallM v
  addSeenM v
  vs <- succsM v
  mapM_ (go v) (Ix.keys vs)
  setCompM v
  return ()
  where go :: Ix a -> Ix a -> DfsM a ()
        go u v = do
          seen <- seenM v
          case seen of
            True-> return ()
            False-> do
              setCallM v
              addSeenM v
              addTreeEdgesM u (Ix.singleton v ())
              vs <- succsM v
              mapM_ (go v) (Ix.keys vs)
              setCompM v
              return ()
execDfsM :: DfsM t a -> DfsEnv t -> DfsEnv t
execDfsM m env | (_,_,env) <- U2.execS m 1 1 env = env
initDfsEnv :: (Ix a, Graph a) -> DfsEnv a
initDfsEnv (r,g) = DfsEnv
  {dfsEnvRoot = r
  ,dfsEnvGraph = g
  ,dfsEnvSpanning = mempty
  ,dfsEnvSeenNodes = mempty
  ,dfsEnvCallMap = mempty
  ,dfsEnvCompMap = mempty}
addTreeEdgesM :: Ix a -> IxSet_ a -> DfsM a ()
addTreeEdgesM v ws = do
  spant <- U2.gets dfsEnvSpanning
  U2.modify(\e->e{dfsEnvSpanning
    =Ix.insertWith Ix.union v ws spant})
seenM :: Ix a -> DfsM a Bool
seenM v = U2.gets ((v`Ix.member`) . dfsEnvSeenNodes)
succsM :: Ix a -> DfsM a (IxSet_ a)
succsM v = U2.gets ((Ix.! v) . dfsEnvGraph)
unseenM :: IxSet_ a -> DfsM a (IxSet_ a)
unseenM s = U2.gets
  ((s `Ix.difference`)
    . dfsEnvSeenNodes)
addSeenM :: Ix a -> DfsM a ()
addSeenM i = unionSeenM (Ix.singleton i ())
unionSeenM :: IxSet_ a -> DfsM a ()
unionSeenM s = do
  seen <- U2.gets dfsEnvSeenNodes
  U2.modify(\e->e{dfsEnvSeenNodes=seen`Ix.union`s})
nextCallM :: DfsM a Int
nextCallM = newUniq1M
nextCompM :: DfsM a Int
nextCompM = newUniq2M
setCallM :: Ix a -> DfsM a ()
setCallM v = do
  dn <- nextCallM
  dnm <- U2.gets dfsEnvCallMap
  U2.modify(\e->e{dfsEnvCallMap=Ix.insert v dn dnm})
setCompM :: Ix a -> DfsM a ()
setCompM v = do
  cn <- nextCompM
  cnm <- U2.gets dfsEnvCompMap
  U2.modify(\e->e{dfsEnvCompMap=Ix.insert v cn cnm})
-- }}}

-----------------------------------------------------------------------------

#if 0
data BFN a = BFN
  {bfnN2Pre :: IxMap a Int
  ,bfnN2Post :: IxMap a Int
  ,bfnPre2N :: IntMap (Ix a)
  ,bfnPost2N :: IntMap (Ix a)}
  __D

bfnInit :: Graph a -> Ix a -> BFN a
bfnPre :: BFN a -> Ix a -> Int
bfnPost :: BFN a -> Ix a -> Int
bfnPreOrder :: BFN a -> [Ix a]
bfnPostOrder :: BFN a -> [Ix a]
bfnRevPreOrder :: BFN a -> [Ix a]
bfnRevPostOrder :: BFN a -> [Ix a]
bfnPre BFN{bfnN2Pre} i = bfnN2Pre Ix.! i
bfnPost BFN{bfnN2Post} i = bfnN2Post Ix.! i
bfnPreOrder BFN{bfnPre2N} = IM.elems bfnPre2N
bfnPostOrder BFN{bfnPost2N} = IM.elems bfnPost2N
bfnRevPreOrder bfn = reverse (bfnPreOrder bfn)
bfnRevPostOrder bfn = reverse (bfnPostOrder bfn)

-- | XXX:IMPLEMENTME
bfnInit g root = undefined
#endif

-----------------------------------------------------------------------------

#if 0
-- | Compute the /Cyclomatic Complexity/
--  of each connected component of the input graph.
cyclomatic :: Graph -> [(Int, Graph)]
cyclomatic g
  | IM.null g = [(0,mempty)]
  | !gs <- cc g
  = fmap go gs
  where go g
          | p   <- 1 {-one component-}
          , n   <- length (nodes g)
          , e   <- length (edges g)
          , nr  <- IS.size (rootsG g)
          = case nr==0 {-wlog-} of
              True{-strongly conn-}
                | !b1 <- e - n + p
                {-first betti number-}
                -> (b1, g)
              False
                | nl  <- IS.size (leavesG g)
                  {-simulate:
                      1) Add a new node.
                      2) Add an edge from each
                         leaf to this new node.
                      3) For each root, add an
                         edge from this new node
                         to that root.-}
                , n   <- n + 1
                , e   <- e + nr + nl
                , !b1 <- e - n + p
                {-first betti number-}
                -> (b1, g)
-- | The /first Betti number/ of the input graph.
betti1 :: Graph -> Int
betti1 g
  | p <- length (cc g)
  , n <- length (nodes g)
  , e <- length (edges g)
  = e - n + p
#endif

-----------------------------------------------------------------------------
#endif

