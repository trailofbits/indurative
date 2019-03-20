# Indurative

Indurative is a project to explore automatically deriving [authenticated](https://www.cs.umd.edu/~mwh/papers/gpads.pdf) versions of common data structures with `[DerivingVia](https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf)`. Right now, it works (somewhat inefficiently) for any `FoldableWithIndex` with serializable keys and values, and an ordering defined on keys keys. Eventually, it might do more interesting stuff.

## What are authenticated data structures?

Authenticated data structures are data structures that support efficient "delegation," wherein a _verifier_ gives some large data structure to a _prover_, keeping only a short digest. This digest allows the verifier to prove reads and writes it makes are valid, with proof size scaling logarithmically with data structure size. This allows for trustless (w.r.t. integrity, not confidentiality) delegation of data custody.

As a canonical example, consider the Merkle tree. In our setup above, the verifier retains just the top hash of the Merkle tree containing their data. Define a "path" as the nodes between a leaf of the Merkle tree and its root. To prove a read is valid, the prover attaches the value, and for each node on its path, the top hash of the tree on the other side (along with which side is which). The verifier can then iteratively hash and concatenate these values to calculate the root hash, and if it agrees with their saved digest, the read is valid.

In this setting, we can also verify writes. Simply perform a read, saving the previous value and proof, then perform the write and return the new top hash. The verifier verifies the old read, then checks that doing the same hashing and concatenation on the value written results in the new hash. As long as everything checks out, they update their saved digest to the new hash, and can continue as before. Forging proofs of either a read or write is as hard as hash collision.

It has long been a goal of researchers to allow for the "authentication" of regular, standard library, data structures. [Miller et. al.](http://www.cs.umd.edu/~mwh/papers/gpads.pdf) achieved this via a fork of the OCaml compiler that created a Merkle tree-like structure for many data types by considering them as a DAG with "leaves" containing primitive types, and sum and product types as "branches". Later, [Atkey](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html) achieved this as an OCaml library, which didn't require a fork of the compiler, but did require accessing data only in a monadic context, effectively as serialized JSON.

This work is an attempt to allow more natural semantics for accessing the data, while still avoiding the need for compiler modification. Right now, for any structure with a defined notion of indexing, it enables the compiler to derive of functions for authenticated reads, digest calculation, and proof verification in terms of just that structure and its indices. One trivial example is authenticating the stock `HashMap` type, so `retrieve @(HashMap String Int) :: String -> HashMap String Int -> (AtIndex String Int, MerklePath SHA3_256)`. This works via a GHC extension known as `DerivingVia`.

## What is `DerivingVia`

Haskell has a functionality known as `newtype`s, where a type can be "relabelled" while preserving memory equivalency (with no impact on runtime performance). Since Haskell implements polymorphism with typeclasses, which are instantiated on types, `newtype`s are a popular strategy for overloading one function on "the same" type. Consider the below code for clarification:

```
newtype Backwards a = Backwards a

instance Ord a => Ord (Backwards a) where
  compare (Backwards x) (Backwards y) = compare y x
```

Of course, if a programmer prefers not to write all the instances for their `newtype` by hand, it's trivial to derive them from the base type, since  as they're memory equivalent, it's just calling the same function as before. The only reason reason we require explicit derivation is to preserve type safety. As an example:

```
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

newtype Dollars = Dollars Int deriving Ord -- Just the Int instance
```

This past summer, GHC gained the ability to perform the same derivation in reverse! That is, one can define an instance on a `newtype`, then invoke that same instance on the base type. At a compiler level, this isn't particularly fancy (again, it's just linking an existing function), but for a programmer, it means the ability to ship "deriving strategies" as simple, zero-cost types! A trivial example follows:

```
{-# LANGUAGE DerivingVia #-}

data MyThing = MyThing String Int

newtype Left a = Left a

instance Eq (Left a) where
  x == y = False

instance Ord (Left a) where
  compare x y = LT

deriving via Left MyThing instance Eq MyThing
deriving via Left MyThing instance Ord MyThing
```

## Putting it all together

This code is a pretty simple combination of the above two ideas. We have a `newtype`, `Auth`, that functionally describes a strategy for authenticating an indexed data structure by mapping it to a Merkle tree in an index preserving way. This lets us derive authentication semantics for many stock data types, without requiring anything that would impede interoperability. Ideally, it should allow an authentication backed transparently compatible with data created and consumed by other libraries, without requiring so much as an explicit type conversion.
