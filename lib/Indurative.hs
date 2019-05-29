{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Indurative (Auth(..), Authenticate(..), hash, hashCons, nullHashes, replaced) where

import Control.Lens
import Control.Monad (join)
import Crypto.Hash (Digest, HashAlgorithm, hashlazy)
import Data.Bifunctor (Bifunctor(..))
import Data.Binary (Binary, encode)
import Data.Bits (Bits(..))
import Data.Bits.ByteString ()
import Data.ByteString (ByteString)
import Data.Proxy (Proxy(..))
import Data.List (find, foldl', sortBy)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import GHC.Generics (Generic)

import qualified Crypto.Hash     as H
import qualified Data.ByteArray  as BA
import qualified Data.ByteString as BS

-- Class definition
-- {{{

-- | A class for data structures with authenticated access semantics.
-- Ref. https://www.cs.umd.edu/~mwh/papers/gpads.pdf
class Authenticate t where
  -- | The type of the "digest" (as used in Miller et. al.)
  type HashFor  t :: *
  -- | The type of an access proof ("the set of digests needed to compute the root digest")
  type ProofFor t :: *
  -- | The return type of a query ('Maybe' if the query can fail, 'Identity' if it can't, etc.)
  type Access   t :: * -> *

  -- | Calculate the digest of some structure
  digest :: t -> HashFor t
  -- | Given an index into the structure, return the value there and a proof of its validity
  retrieve :: Index t -> t -> (Access t (IxValue t), ProofFor t)
  -- | Given the type of some structure (via 'Proxy'), an 'Index' into it, a digest of that
  -- structure, a proposed value at that index, and a proof of that value's validity, check whether
  -- the proof holds.
  verify :: Proxy t -> Index t -> HashFor t -> Access t (IxValue t) -> ProofFor t -> Bool

-- | Given the type of some structure (via 'Proxy'), an index into that it, two pairs of (value at
-- index, digest of the structure) and a proof claimed to hold for both, evaluate that it is doubly
-- valid. This is useful for authenticating writes, since when the prover asks to write a value to
-- some index, they recieve back a digest after that write. To validate that this is legitimate,
-- they can simply call @replaced Proxy ix (digest_old, read) (digest_new, wrote) prf@. If the proof
-- holds for the old value and their stored digest and also the written value and the proposed new
-- digest, they can safely update their digest. Ref. https://www.cs.umd.edu/~mwh/papers/gpads.pdf.
replaced :: Authenticate t
         => Proxy t
         -> Index t
         -> (HashFor t, Access t (IxValue t))
         -> (HashFor t, Access t (IxValue t))
         -> ProofFor t
         -> Bool
replaced t k old new p = let good x = uncurry (verify t k) x p in good old && good new

-- }}}
-- Hashing logic we export (because it's useful for instance creation)
-- {{{

-- | A replacement for the @hash@ function from "Crypto.Hash" that works for any 'Binary' type
hash :: (Binary v, HashAlgorithm a) => v -> Digest a
hash = hashlazy . encode

-- | Given two hashes, hash their concatenation
hashCons :: HashAlgorithm a => Digest a -> Digest a -> Digest a
hashCons x y = H.hash (BA.convert x <> BA.convert y :: BA.Bytes)

-- | Hashes of empty nodes in a sparse Merkle tree. Index corresponds to height (@head nullHashes@
-- is the hash of an empty node at the bottom layer, @nullHashes !! 256@ is the root of a completely
-- empty tree of depth 256).
nullHashes :: HashAlgorithm a => [Digest a]
nullHashes = iterate (join hashCons) $ hash EmptyNode

-- }}}
-- Misc. hashing utilities
-- {{{

-- The below are designed to work with sparse Merkle trees with nodes indexed by a ByteString.

-- Hash a key to a Merkle tree index
bsHash :: forall a x. (Binary x, HashAlgorithm a) => Proxy a -> x -> ByteString
bsHash = const $ BS.pack . BA.unpack . hash @_ @a

data EmptyNode = EmptyNode deriving (Binary, Generic)

-- Digest length of a given hash algorithm (in bits)
hLen :: forall a. HashAlgorithm a => Proxy a -> Int
hLen = const . (8 *) . BA.length $ head (nullHashes @a)

-- Merkle tree index 0x1, padded appropriately (necessary because of bits-bytestring bugs)
hOne :: HashAlgorithm a => Proxy a -> ByteString
hOne p = BS.pack $ replicate (hLen p `div` 8 - 1) 0 |> 1

-- Cons two hashes given the index of the former in the Merkle tree.
-- @debranch 0x0..1 x y := hashCons y x@, @debranch 0x..0 x y := hashCons x y@
debranch :: HashAlgorithm a => ByteString -> Digest a -> Digest a -> Digest a
debranch i = if testBit i 0 then flip hashCons else hashCons

-- }}}
-- Sparse Merkle tree logic
-- {{{

type SparseNode a = (ByteString, Digest a)
type SparsePath a = [(Int, Digest a)]

-- This takes a layer of non-empty nodes in a sparse Merkle tree plus the hash of an empty node and
-- returns the non-empty nodes on the next layer up. WARNING: it expects the list to be sorted (but
-- preserves sortedness)
up :: forall a. HashAlgorithm a => [SparseNode a] -> Digest a -> [SparseNode a]
-- If all notes are empty, the next layer is empty
up []                  _ = []
-- If there's only one non-empty node, there will only be one non-empty node on the next layer. The
-- index shifts right by one (half as many nodes) and we cons the hash with empty on the correct
-- side (if the index ends in one, cons(empty, full), ends in zero, cons(full, empty)).
up [(i, x)]            h = [(shiftR i 1, debranch i x h)]
-- If there's more than one non-empty node, we have to iterate through the list recursively. For
-- each pair of nodes in the list, we check if they're adjacent (indices differ by only last bit)
-- then if they are, cons them together and continue iterating through the list, and if not, bring
-- the first hash up a layer as in the previous case, then continue iterating through the list,
-- starting with the second hash.
-- NOTE: we should be able to just check if @setBit i 0 == j@, but the bits-bytestring instance
-- is broken there, and truncates the output to one @Char8@. Dunno why.
up ((i,x) : (j,y) : l) h = if i `xor` j == hOne (Proxy @a) then (shiftR i 1, hashCons x y) : up l h
                                                           else up [(i,x)] h ++ up ((j,y) : l) h

-- Given a base layer of non-empty sparse Markle tree nodes, calculate the root hash.
climb :: forall a. HashAlgorithm a => [SparseNode a] -> Digest a
-- If all the nodes are empty, root hash is just an empty hash at max height
climb [] = nullHashes !! hLen (Proxy @a)
-- If not all the nodes are empty, we work out the rest of the tree layer-by-layer by recursively
-- evaluating 'up'
climb l  = snd . head . foldl' up l $ take (hLen $ Proxy @a) nullHashes

-- Given a base layer of non-empty sparse Markle tree nodes and some node from that layer, create an
-- inclusion proof for that node. This proof consists of, for each node on the path from our node to
-- the root, the hash of the node below but on the "other side" of that node. Diagram follows:
--
--        [0]       0   - our node
--      /     \     x   - on the path from our node to the top
--     x       *    *   - included in our proof
--    / \     / \   .   - other node, there for completeness
--   *   x   .   .  [0] - root
--  / \ / \ / \ / \
--  . . 0 * . . . .
--
-- Also ref. comments for 'check'
--
-- For brevity, we omit all null hashes from this proof since they can be re-derived by the verifier
-- NOTE: This does not check that the provided node is in the provided layer.
zig :: forall a. HashAlgorithm a => [SparseNode a] -> SparseNode a -> SparsePath a
zig = go 0 where 
  go :: Int -> [SparseNode a] -> SparseNode a -> SparsePath a
  -- @go@ is like 'zig' but takes a height argument. If it's the tree height, we're done!
  go h l (i, x) = let nullHash = nullHashes !! h in if h == hLen (Proxy @a) then [] else
    -- We can step @go@ by increasing height by one, going up a layer, and shifting the address one,
    -- then calling it on the concatenation of our node and its neighbor. We just need to figure out
    -- what our neighbor is.
    let next = go (h + 1) (up l nullHash) . (shiftR i 1,) . debranch i x in
    -- If we aren't at the tree height, see if any non-empty nodes are next to our nodes.
    case find ((== xor (hOne $ Proxy @ a) i) . fst) l of
      -- If there aren't any, we're next to an empty node
      Nothing       ->            next nullHash
      -- If there are, we're next to that node, and should keep track of it in our proof.
      Just (_, res) -> (h, res) : next res

-- Given a root hash, a path up a Merkle tree (like that returned by 'zig'), and the node at which
-- this path started, check the validity of the proof by recursively hashing and concatenating
-- through it, then ensuring the final hash is the desired/saved root hash. Diagram follows:
--
--        [0]       0     - our node
--      /     \     x     - on the path from our node to the top
--     x       b    [a,b] - our proof
--    / \           .     - empty node, omitted from our proof
--   a   x          [0]   - root
--      / \        
--      0 .         check := cons(cons(a, cons(0, null hash)), b) == [0]
--
-- Also ref. comments for 'zig'
check :: forall a. HashAlgorithm a => Digest a -> SparseNode a -> SparsePath a -> Bool
check t = go 0 where
  -- As before, @go@ just keeps track of the height.
  -- If every hash in the proof is null, we just walk our node up an otherwise-empty tree.
  go n x      []           = let proof = snd . head . foldl' up [x] in
    t == proof (drop n $ take (hLen $ Proxy @a) nullHashes)
  -- If there are hashes in the proof, concatenate with null hashes til we're at the height where
  -- they start appearing, then concatenate with non-null hashes instead instead.
  go n (i, r) ((h,x) : hs) = go (n + 1) (shiftR i 1, debranch i r h') l' where
     (h', l') = if n == h then (x, hs) else (nullHashes !! n, (h,x) : hs)

-- Given some kind of 'FoldableWithIndex', return the base layer of a sparse Merkle tree with each
-- element at the Merkle tree index corresponding to the hash of its regular 'Index'.
baseLayer :: forall a k t v. (Binary k, Binary v, FoldableWithIndex k t, HashAlgorithm a)
          => t v -> [SparseNode a]
baseLayer = sortBy (comparing fst) . fmap (bimap (bsHash $ Proxy @a) hash) . itoList

-- Work out the root hash of some @FoldableWithIndex@ converted to a sparse Merkle tree
sparseHash :: (Binary k, Binary v, FoldableWithIndex k t, HashAlgorithm a) => t v -> Digest a
sparseHash = climb . baseLayer

-- Given an index into some @FoldableWithIndex@, return the value at that index (if defined) and an
-- [in/ex]clusion proof as appropriate.
sparseGet :: forall a k t v. (Binary k, Binary v, FoldableWithIndex k t, HashAlgorithm a)
          => k -> t v -> (Maybe v, SparsePath a)
sparseGet i l = let res = snd <$> ifind (\j _ -> hash @_ @a j == hash i) l in
  (res,) . zig (baseLayer l) . (bsHash (Proxy @a) i,) . fromMaybe (head nullHashes) $ hash <$> res

-- Given an index into some @FoldableWithIndex@, the root hash of its sparse Merkle tree
-- representation, a claimed value at that index, and a proof for the claim, check whether the
-- proof holds.
sparseCheck :: forall a k v. (Binary k, Binary v, HashAlgorithm a)
            => k -> Digest a -> Maybe v -> SparsePath a -> Bool
sparseCheck i h = check h . (bsHash (Proxy @a) i,) . maybe (head nullHashes) (hash @_ @a)

-- }}}
-- Machinery for DerivingVia
-- {{{

-- | This is designed so that if you'd like to have authenticated semantics for a @Map Int String@
-- you simply write @deriving Authenticate via Auth SHA3_256 (Map Int) String@ and get them. First
-- argument is the hash to use, second is the container, third is the value. Feels kinda magic,
-- doesn't it?
newtype Auth a t v = Auth (t v) deriving Functor
type instance Index   (Auth a t v) = Index (t v)
type instance IxValue (Auth a t v) = v

-- With this instance, we're able to derive instances for almost any indexed container! See
-- @test/Main.hs@ for examples from @containers@
instance (HashAlgorithm a, Binary (Index (t v)), Binary v, FoldableWithIndex (Index (t v)) t)
      => Authenticate (Auth a t v) where
  type HashFor  (Auth a t v) = Digest a
  type ProofFor (Auth a t v) = SparsePath a
  type Access   (Auth a t v) = Maybe

  retrieve k (Auth t) = sparseGet k t
  digest (Auth t) = sparseHash t
  verify _ = sparseCheck

-- }}}
