import DiscreteModulusCert.CertChecker

/-!
A standalone, compiled certificate verifier: `verify_cert <path/to/certificate.json>`.
Reads the file, parses it, and checks every invariant `CertChecker.lean`
implements (piece disjointness/coverage, every declared tree a genuine
forest and maximal within its piece, weights nonnegative and summing to
1, eta/rho matching pieces, admissibility of rho via Kruskal), printing
ACCEPTED or REJECTED with a reason. Unlike `#eval` (which runs under
Lean's bytecode interpreter), this is genuinely compiled native code --
the same computable `Decidable` instances, run at native speed.
-/

open DiscreteModulusCert.CertChecker

/-- The one non-standard trust assumption a passing certificate still
carries. Admissibility of `rho` is checked by running Kruskal's
algorithm to find a minimum-weight spanning tree and trusting its
output, rather than by a kernel-checked proof that the algorithm is
correct -- everything else a passing certificate asserts is fully
kernel-checked. Printed unconditionally alongside every ACCEPTED result
(not just noted in documentation), since it's a static fact regardless
of which certificate was checked. See `docs/certification/trust.md`
for the full trusted-computing-base ledger and the status of proving
Kruskal's algorithm correct. -/
def kruskalCaveat : String :=
  "  NOTE: admissibility of rho relies on an unverified Kruskal implementation \
(its output is trusted, not proven, to be a genuine minimum-weight spanning tree)."

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let s ← IO.FS.readFile path
    match checkCertificateJson s with
    | .ok () =>
      IO.println s!"{path}: ACCEPTED"
      IO.println kruskalCaveat
      return 0
    | .error e =>
      IO.println s!"{path}: REJECTED: {e}"
      return 1
  | _ =>
    IO.println "usage: verify_cert <certificate.json>"
    return 2
