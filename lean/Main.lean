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
carries -- kept visible in the verifier's own output (not just
`Certification_Plan.md`'s TCB ledger, §3), printed unconditionally
alongside every ACCEPTED result, since it's a static fact about v1
regardless of which certificate was checked. -/
def kruskalCaveat : String :=
  "  NOTE: admissibility of rho relies on an unverified Kruskal implementation \
(see Certification_Plan.md §3/§5.2 -- PR 6 is the tracked follow-up to prove it correct)."

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
