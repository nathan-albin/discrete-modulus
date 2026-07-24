import LeanModulus.Common.GraphicMatroid
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Restrict

/-!
Smoke test confirming the pinned `lean-modulus` dependency exposes the two
bridging facts the certificate verifier is built on: that a spanning tree of
a connected multigraph is exactly a base of its graphic matroid, and that a
spanning tree of a vertex block glues with a spanning tree of the contracted
remainder into a spanning tree of the whole graph.
-/

open scoped Matroid

#check @Multigraph.isSpanningTree_iff_isBase
#check @Multigraph.isBase_union_of_isBase_restrict_isBase_contract
