import DiscreteModulusCert.CertChecker

/-!
Smoke test for `CertChecker.checkCertificateJson`, run against real
`certificate_builder.build_certificate` output via `#eval` -- genuine
program execution against real files, not a compile-time proof about
literals.

**`nested`'s exponential blowup is fixed; its `#eval` stays commented out
anyway, for a different reason.** `ForestDecide.lean`'s
`instDecidableIsForestOfList` used to hang indefinitely on `nested`'s
190-edge/20-vertex piece because Mathlib's `SimpleGraph.Reachable`
decidability instance is a genuinely exponential algorithm (enumerates
every walk, no visited-set pruning -- see `ForestDecide.lean`'s docstring).
That's been replaced with a polynomial `Finset`-based BFS closure plus a
components cache reused across a piece's whole maximality check, and
`nested` (like `branch_test`, exercised below) now *completes* and reports
`ACCEPTED`, verified directly with `lake exe verify_cert
../cpp/examples/nested.certificate.json` -- roughly 45 seconds, compiled.
That's not exercised here as a `#eval`, though: Lean's interpreter (what
`#eval` runs under, as opposed to `verify_cert`'s genuinely compiled code)
carries a large constant-factor overhead per primitive operation, unrelated
to the algorithmic fix, and pushes `nested`'s `#eval` well past a
reasonable smoke-test budget (confirmed directly: still running after 3
minutes). `branch_test`'s two 45-edge pieces are small enough that this
doesn't bite -- its `#eval` below finishes in a couple of seconds.
-/

open DiscreteModulusCert.CertChecker

#eval do
  let s ← IO.FS.readFile "../cpp/examples/house.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "house: ACCEPTED"
  | .error e => IO.println s!"house: REJECTED: {e}"

-- Deliberately left as a `#eval` (not re-enabled) even though `nested`'s
-- exponential blowup itself is fixed -- see this file's own docstring.
-- #eval do
--   let s ← IO.FS.readFile "../cpp/examples/nested.certificate.json"
--   match checkCertificateJson s with
--   | .ok () => IO.println "nested: ACCEPTED"
--   | .error e => IO.println s!"nested: REJECTED: {e}"

#eval do
  let s ← IO.FS.readFile "../cpp/examples/branch_test.certificate.json"
  match checkCertificateJson s with
  | .ok () => IO.println "branch_test: ACCEPTED"
  | .error e => IO.println s!"branch_test: REJECTED: {e}"
