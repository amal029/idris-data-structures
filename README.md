# Implementation of 2-3 trees in Idris.

* The implementation is based on 'C' code
  - The main issue is that many functions are not total!

* The implementation can be made much better,
  by splitting the 2-3 data type into 4 constructors:

  - Nil        : TwoThreeTree a
  - Leaf       : a -> TwoThreeTree a
  - TwoNodes   : a -> TwoThreeTree a -> TwoThreeTree a
  - ThreeNodes : a -> TwoThreeTree a -> TwoThreeTree a -> TwoThreeTree a -> TwoThreeTree a


* I might implement a new 2-3 tree using the above data-structure.

* See: http://pages.cs.wisc.edu/~vernon/cs367/notes/10.23TREE.html for
  deltails of the algorithm.