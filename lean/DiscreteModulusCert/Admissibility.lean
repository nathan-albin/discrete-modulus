import DiscreteModulusCert.Kruskal
import DiscreteModulusCert.Family

/-!
# The Kruskal-admissibility trust boundary, as a named axiom

`Certification_Plan.md` §3/§5.2 documents v1's one accepted soundness gap:
`Kruskal.run`'s output is trusted, not proven, to be a genuine minimum-weight
base of the graphic matroid. `CertChecker.lean` already *uses* that trust
(computing a density's admissibility via Kruskal's MST weight), but only as
an ordinary runtime `Bool` check -- nothing marks *where* the trust actually
enters the kernel-checked side. This file makes that boundary an explicit
Lean `axiom`, so it shows up by name under `#print axioms` for any
certificate whose `rho` isn't uniform (unlike `house`'s, `HouseCert.lean`'s
`houseCertificateOptimal` needed no such axiom at all -- see its own
docstring).

**No connectedness hypothesis.** `IsAdmissible`/`Pmf` (`Family.lean`) are
stated purely over an abstract `Matroid E`, with no reference to graph
connectivity. Kruskal's algorithm, exactly as coded in `Kruskal.lean` (sort
edges ascending by weight, greedily keep each that joins two still-separate
union-find components), is the general matroid-greedy algorithm for the
graphic matroid -- it produces a genuine minimum-weight *base* (a spanning
forest, one tree per component) whether or not the graph is connected. So
this axiom, unlike `HouseCert.lean`'s pattern, never needs to establish or
assume `G` is connected. -/

namespace DiscreteModulusCert

open scoped Matroid
open Multigraph

/-- The multigraph built from an explicit endpoints array -- the same
one-line construction `CertChecker.CheckedGraph.toMultigraph` uses,
defined standalone here (rather than importing `CertChecker`, which would
create an import cycle once `Soundness.lean` imports both this file and
`CertChecker`). -/
def mkMultigraph (n : Nat) (endpoints : Array (Fin n × Fin n)) :
    Multigraph (Fin n) (Fin endpoints.size) :=
  ⟨fun e => s(endpoints[e].1, endpoints[e].2)⟩

namespace Kruskal

/-- **v1's accepted, unverified admissibility oracle, as a named axiom.**
Bridges "Kruskal's computed minimum-spanning-forest weight is `≥ 1`"
directly to `IsAdmissible`, at exactly the granularity
`Certification_Plan.md`'s own wording asks for (bridging the computed
weight to admissibility, not decomposed further into "Kruskal computes a
genuine minimum base" plus a separate logical step) -- this is the one
place trust enters the kernel-checked side for a certificate whose `rho`
isn't uniform. `endpoints : Array (Fin n × Fin n)` matches
`CheckedGraph`'s own shape exactly, so applying this axiom at a
`CertChecker` call site only needs one small value-level bridging lemma
(`Soundness.lean`), not a graph rebuild. -/
axiom run_isAdmissible_of_weight_ge_one
    {n : Nat} (endpoints : Array (Fin n × Fin n)) (weight : Array ℚ)
    (hmin : 1 ≤ (Kruskal.run n (endpoints.map fun p => (p.1.val, p.2.val)) weight).foldl
      (fun acc i => acc + weight.getD i 0) 0) :
    IsAdmissible (mkMultigraph n endpoints).graphicMatroid
      (fun e : Fin endpoints.size => weight.getD e.val 0)

end Kruskal
end DiscreteModulusCert
