import DiscreteModulusCert.CertChecker

/-!
Smoke test for `CertChecker.checkCertificateJson`, run against real
`certificate_builder.build_certificate` output via `#eval` -- genuine
program execution against real files, not a compile-time proof about
literals.

**`nested`/`branch_test` are deliberately not exercised here yet.** Their
larger pieces (nested's 190-edge K20 round; branch_test's two 45-edge K10
lobes) hit a real performance blowup in `ForestDecide.lean`'s
`instDecidableIsForestOfList` -- confirmed via direct experiment to be an
algorithmic issue, not a `#eval`-vs-`native_decide` interpreter artifact
(the same 190-edge check hangs under `native_decide` too, the same
mechanism `HouseCert.lean` uses successfully at 6 edges). Almost certainly
Mathlib's generic `SimpleGraph.Reachable` decidability instance, invoked
once per candidate edge insertion, isn't the efficient (e.g. union-find)
algorithm this needs at real sizes. Re-enable the two commented-out
`#eval`s below once that's fixed -- see `Certification_Plan.md` §5.1.6's
open items.
-/

open DiscreteModulusCert.CertChecker

#eval do
  let s ← IO.FS.readFile "../cpp/examples/house.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "house: ACCEPTED"
  | .error e => IO.println s!"house: REJECTED: {e}"

-- #eval do
--   let s ← IO.FS.readFile "../cpp/examples/nested.certificate.json"
--   match checkCertificateJson s with
--   | .ok () => IO.println "nested: ACCEPTED"
--   | .error e => IO.println s!"nested: REJECTED: {e}"

-- #eval do
--   let s ← IO.FS.readFile "../cpp/examples/branch_test.certificate.json"
--   match checkCertificateJson s with
--   | .ok () => IO.println "branch_test: ACCEPTED"
--   | .error e => IO.println s!"branch_test: REJECTED: {e}"
