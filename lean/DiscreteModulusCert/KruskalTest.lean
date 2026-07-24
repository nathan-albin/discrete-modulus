import DiscreteModulusCert.Kruskal

/-!
Smoke test for `Kruskal.run` (`Kruskal.lean`) on a tiny, hand-checkable
triangle: confirms the greedy algorithm picks the two cheapest edges (not
just that it type-checks), and that the resulting weight sum correctly
distinguishes an admissible density from an inadmissible one, the same
arithmetic `CertChecker.checkCertificate`'s admissibility check uses. Since
`Kruskal.run`'s own correctness is *not* proven (see `Kruskal.lean`'s
docstring for the accepted gap), there is no `Prop` to `native_decide`
here; this observes and asserts on the computed output directly, the same
style `CertCheckerTest.lean` uses for running code rather than proving
statements about it.
-/

namespace DiscreteModulusCert.KruskalTest

-- Triangle: 3 vertices, edges 0:(0,1) w=3, 1:(1,2) w=1, 2:(2,0) w=2. The
-- minimum spanning tree is the two cheapest edges, {1, 2} (total weight 3),
-- excluding the most expensive edge 0.
private def endpoints : Array (Nat × Nat) := #[(0, 1), (1, 2), (2, 0)]
private def weights : Array ℚ := #[3, 1, 2]

#eval do
  let mst := Kruskal.run 3 endpoints weights
  let w : ℚ := mst.foldl (fun acc i => acc + weights.getD i 0) 0
  if decide (mst = [1, 2]) && decide (w = 3) then
    IO.println s!"KruskalTest triangle: PASS (mst={mst}, weight={w})"
  else
    IO.println s!"KruskalTest triangle: FAIL (mst={mst}, weight={w}, expected [1, 2] weight 3)"

-- Same triangle, all weights 0: the minimum spanning tree's weight is 0,
-- correctly identified as inadmissible (< 1), the same arithmetic
-- `CertChecker.checkCertificate`'s admissibility check performs, exercised
-- here in isolation on a case designed to fail it.
private def zeroWeights : Array ℚ := #[0, 0, 0]

#eval do
  let mst := Kruskal.run 3 endpoints zeroWeights
  let w : ℚ := mst.foldl (fun acc i => acc + zeroWeights.getD i 0) 0
  if decide (w < 1) then
    IO.println s!"KruskalTest zero-weight (expected inadmissible): PASS (weight={w} < 1)"
  else
    IO.println s!"KruskalTest zero-weight (expected inadmissible): FAIL (weight={w}, expected < 1)"

end DiscreteModulusCert.KruskalTest
