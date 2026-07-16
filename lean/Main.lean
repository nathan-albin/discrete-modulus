import DiscreteModulusCert.CertChecker

/-!
A standalone, compiled certificate verifier: `verify_cert <path/to/certificate.json>`.
Reads the file, parses it, and checks every invariant `CertChecker.lean`
implements (piece disjointness/coverage, every declared tree a genuine
forest and maximal within its piece, weights nonnegative and summing to
1), printing ACCEPTED or REJECTED with a reason. Unlike `#eval` (which
runs under Lean's bytecode interpreter), this is genuinely compiled native
code -- the same computable `Decidable` instances, run at native speed.
-/

open DiscreteModulusCert.CertChecker

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let s ← IO.FS.readFile path
    match checkCertificateJson s with
    | .ok () =>
      IO.println s!"{path}: ACCEPTED"
      return 0
    | .error e =>
      IO.println s!"{path}: REJECTED: {e}"
      return 1
  | _ =>
    IO.println "usage: verify_cert <certificate.json>"
    return 2
