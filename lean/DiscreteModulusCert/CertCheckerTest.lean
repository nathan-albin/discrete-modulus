import DiscreteModulusCert.CertChecker

/-!
Smoke test for `CertChecker.checkCertificateJson`, run against real
`certificate_builder.build_certificate` output via `#eval` -- genuine
program execution against real files, not a compile-time proof about
literals.

**`nested`'s exponential blowup is fixed, and its `#eval` is exercised
below like the other two.** `ForestDecide.lean`'s
`instDecidableIsForestOfList` used to hang indefinitely on `nested`'s
190-edge/20-vertex piece because Mathlib's `SimpleGraph.Reachable`
decidability instance is a genuinely exponential algorithm (enumerates
every walk, no visited-set pruning -- see `ForestDecide.lean`'s docstring).
That's been replaced with an incremental union-find over `Finset V`
partitions (`mergeStep`/`buildComponents`), reused as a components cache
across a piece's whole maximality check, and `nested` now *completes* and
reports `ACCEPTED`, verified directly with `lake exe verify_cert
../cpp/examples/nested.certificate.json` -- roughly 2.5 seconds, compiled.
Lean's interpreter (what `#eval` runs under, as opposed to `verify_cert`'s
genuinely compiled code) still carries real constant-factor overhead per
primitive operation, but `nested`'s `#eval` now finishes in ~8 seconds
(confirmed directly) rather than the 3+ minutes it used to take under the
old exponential instance -- comfortably within a smoke-test budget, so it's
re-enabled below alongside `house`/`branch_test`.
-/

open DiscreteModulusCert.CertChecker

#eval do
  let s ← IO.FS.readFile "../cpp/examples/house.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "house: ACCEPTED (rho-admissibility relies on unverified Kruskal, see Main.lean)"
  | .error e => IO.println s!"house: REJECTED: {e}"

#eval do
  let s ← IO.FS.readFile "../cpp/examples/nested.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "nested: ACCEPTED (rho-admissibility relies on unverified Kruskal, see Main.lean)"
  | .error e => IO.println s!"nested: REJECTED: {e}"

#eval do
  let s ← IO.FS.readFile "../cpp/examples/branch_test.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "branch_test: ACCEPTED (rho-admissibility relies on unverified Kruskal, see Main.lean)"
  | .error e => IO.println s!"branch_test: REJECTED: {e}"
