# Indurative

Indurative is a project to explore automatically deriving [authenticated](https://www.cs.umd.edu/~mwh/papers/gpads.pdf) semantics for working with common data structures with [`DerivingVia`](https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf).
Right now, it works (somewhat inefficiently) for any `FoldableWithIndex` with `Binary` keys and values.

Note that this is new, untested cryptographic code, and you probably shouldn't rely on it right now.

## OK, but what does that mean.

Indurative allows you to treat almost any indexed data structure as an authenticated data structure using its natural indexing scheme.
This means that you can simply take your existing Haskell code and add trustless third party data custody without any new data structures or cryptographic logic (among other things).
Authenticated data structures enable approximately the following workflow:

  1. I have some large collection of data, organized as some kind of key/value store.

  2. I compute a short "digest" of this data (256 bits), then hand it off to a third party.

  3. I can ask this third party to retrieve data for me in terms of my original indexing system, which they reply to with a value (if there is one at that index) and a proof.
     If they returned a value, the proof certifies that the value was in my original data structure, at the index I specified.
     If no value was returned, the proof certifies that there was indeed no value at the specified index.

  4. Anyone with the "digest" can evaluate whether this proof holds, and if it does I have a cryptographic guarantee of authenticity.

  5. I can ask this third party to write data into this structure at some index, and they can reply to that with a new digest, as well as a proof.
     The proof certifies that the new digest is valid, and I should update my saved digest to it.

Effectively, I can delegate custody of a key value store to a third party, then make reads and writes without trusting them for data integrity.

One example of an authenticated data structure many readers may be familiar with is the Merkle tree.
Merkle trees are designed to allow for easy inclusion proofs, verifiable using only the top hash.
There are also [sparse Merkle trees](https://github.com/google/trillian/blob/master/docs/papers/RevocationTransparency.pdf) as invented by Laurie and Kasper, which support efficient _ex_clusion proofs as well (and are used heavily by Indurative).

## Can you show me an example?

I want to enable [binary transparency](https://wiki.mozilla.org/Security/Binary_Transparency) for a package server I'm writing.
Currently, the package server has a `Map Name Binary` that it essentially just serves over http.
To enable binary transparency, I simply import Indurative and write the following code:

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

And now my system gains all the benefits of binary transparency without even writing ten lines of code!
Not only that, but I can extend it slightly using `retrieved` and get revocation transparency in about as much work.
I didn't even have to use a different data structure.

## How can I start using this code?

Use [stack](https://docs.haskellstack.org/en/stable/yaml_configuration/#packages) and add it as a github dependency.
It'll be published on hackage soon.

## Where can I learn more about this?

One of the best papers on the subject is [Authenticated Data Structures, Generically](https://www.cs.umd.edu/~mwh/papers/gpads.pdf) by Miller et. al.
Reading that gives an outline of what authenticaed data structures are, the obstacles to using them, and one approach to offering generic authenticated semantics for data structure access.
That paper was, in fact, the primary inspiration for this work.
Bob Atkey has also published an excellent blog adding on to their work, [Authenticated Data Structures as a Library, for Free!](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html).
Edward Kmett has a [Haskell implementation](https://github.com/ekmett/auth) of some of the ideas therein.

However, I wanted to retain the "natural" semantics for data access from Miller's paper without forking a compiler (as Miller had to do), so Indurative uses an entirely new method.
Specifically, Indurative is built with [`DerivingVia`](https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf), a GHC language extension new since GHC 8.6.
This lets us avoid both forking the compiler and writing our own operational semantics of data access (as in Atkey's work) by using GHC's powerful `newtype` system.
The exact mechanics are outside the scope of this README, but that paper is highly recommended reading.
