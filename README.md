## Indurative

Indurative lets you easily build [authenticated](https://www.cs.umd.edu/~mwh/papers/gpads.pdf) data structures from many Haskell containers (take a look to [our blog post](https://blog.trailofbits.com/2019/06/17/leaves-of-hash/) about it!). You can delegate custody to a third party using an authenticated data structure, then cryptographically verify all reads and writes performed by that third party. Certificate and binary transparency are example use cases enabled by authenticated data structures that you can build with Indurative.

This is new, untested cryptographic code. Standard warnings apply.

## Using Authenticated Data Structures

Indurative can treat almost any indexed data structure as an authenticated data structure using its natural indexing scheme. You can take your existing Haskell code and add trustless third party data custody without any new data structures or cryptographic logic.

Authenticated data structures enable workflows like:

1. You have some large collection of data organized as some kind of key/value store.
2. You compute a short "digest" of this data (256 bits) then hand it off to a third party.
3. You can ask the third party to retrieve data in terms of the original indexing system. They reply with a value (if there is one at that index) and a proof. If they returned a value, the proof certifies that the value was in the original data structure at the index you specified. If no value was returned, the proof certifies that there was no value at the specified index.
4. Anyone with the "digest" can evaluate whether this proof holds, and if it does then you have a cryptographic guarantee of authenticity.
5. You can ask the third party to write data into the structure at some index. They can reply with a new digest as well as a proof. The proof certifies that the new digest is valid, and you should update your saved digest to it.

Effectively, you can delegate custody of a key-value store to a third party, then make reads and writes without trusting the 
third party for data integrity.

Merkle trees are the canonical example of an authenticated data structure. Merkle trees are designed to allow for easy inclusion proofs, verifiable using only the top hash. There are also [sparse Merkle trees](https://github.com/google/trillian/blob/master/docs/papers/RevocationTransparency.pdf) as invented by Laurie and Kasper, which support efficient exclusion proofs as well (and are used heavily by Indurative).

Indurative uses Haskell's [`DerivingVia`](https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf) language extension to derive authenticated semantics for any [`FoldableWithIndex`](https://hackage.haskell.org/package/lens-4.17.1/docs/Control-Lens-Indexed.html#t:FoldableWithIndex) with [`Binary`](https://hackage.haskell.org/package/binary-0.10.0.0/docs/Data-Binary.html#t:Binary) keys and values. It does this by hashing each index, then placing the value in the index corresponding to that hash of a sparse Merkle tree, then using that tree to compute digests and produce or verify access proofs.

### Example: Add binary transparency to a package manager with Indurative

You want to enable [binary transparency](https://wiki.mozilla.org/Security/Binary_Transparency) for a package server you're writing. Your package server has a `Map Name Binary` that it serves over http. Import Indurative and add the following code to gain the benefits of binary transparency:

On the server side:

```
deriving via SHA3_256 (Map Name) Binary instance Authenticate (Map Name Binary)

currentDigest :: Digest SHA3_256
currentDigest = digest myBigMapOfBinaries

authenticatedGet :: Name -> (Maybe Binary, ProofFor (Map Name Binary))
authenticatedGet name = retrieve name myBigMapOfBinaries

-- code to serve these functions below
```

On the client side:

```
deriving via SHA3_256 (Map Name) Binary instance Authenticate (Map Name Binary)

isBinaryLegit :: Name -> Binary -> ProofFor (Map Name Binary) -> Bool
isBinaryLegit name binary proof = check (Proxy :: Map Name Binary) name savedDigest (Just binary) proof

-- code to get digest from server and actually check downloads below
```

Your package manager now gains all the benefits of binary transparency without even writing ten lines of code! Not only that, but you can extend it slightly using `retrieved` and get revocation transparency. You didn't even have to use a different data structure.

## Start using Indurative

Use [stack](https://docs.haskellstack.org/en/stable/yaml_configuration/#packages) and add it as a github dependency. It'll be published on hackage soon.

## Learn more about Authenticated Data Structures

One of the best papers on the subject is [Authenticated Data Structures, Generically](https://www.cs.umd.edu/~mwh/papers/gpads.pdf) by Miller et. al. It gives an outline of what authenticated data structures are, the obstacles to using them, and one approach to offering generic authenticated semantics for data structure access. This paper was, in fact, the primary inspiration for Indurative.

Bob Atkey has also published an excellent blog adding on to their work, [Authenticated Data Structures as a Library, for Free!](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html). Edward Kmett has a [Haskell implementation](https://github.com/ekmett/auth) of some of their ideas.

I wanted to retain the "natural" semantics for data access from Miller's paper without forking a compiler (as Miller had to do), so Indurative uses an entirely new method. Indurative is built with [`DerivingVia`](https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf), a GHC language extension new since GHC 8.6. This avoids forking the compiler and writing our own operational semantics of data access (as in Atkey's work) by using GHC's powerful `newtype` system. The exact mechanics are outside the scope of this README, but that paper is highly recommended reading.
