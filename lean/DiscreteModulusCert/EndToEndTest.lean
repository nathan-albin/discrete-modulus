import DiscreteModulusCert.Soundness
import Lean.Data.Json

/-!
# End-to-end test: certificate JSON on disk, parsed at compile time, proved optimal

Every earlier soundness result worked over an abstract,
universally-quantified `raw : RawCertificate` (`Soundness.lean`'s
`checkCertificate_sound`/`checkCertificate_optimal`), stopping short of
feeding a parsed certificate into `certificate_optimality` itself for a
file on disk. This file closes that gap.

`include_str` (Lean 4 core) embeds the contents of
`cpp/examples/house.certificate.json` and
`cpp/examples/nested.certificate.json` as string literals at elaboration
time: the same bytes `certificate_builder.py` wrote and `lake exe
verify_cert` reads at runtime, not a re-typed copy. Parsing that string
with the same `Lean.Data.Json`/`FromJson` machinery
(`CertChecker.RawCertificate`) and unwrapping the result (`Option.get`,
justified by `native_decide` rather than assumed) gives a concrete
`RawCertificate` term, with no dummy fallback value and no
hand-transcription. `native_decide` then runs `checkCertificate` against
that concrete term (compiled, the same mechanism `verify_cert` and
`ForestDecide.lean`'s maximality checks already rely on for `nested`'s
190-edge piece). This isn't for speed (`#eval` is fast enough here too,
see `CertCheckerTest.lean`'s own docstring); it's because `native_decide`
yields a kernel-checked *proof term*
(`houseCertRaw_accepted`/`nestedCertRaw_accepted` below), which `#eval`, a
runtime action that only runs and prints and produces no proof, cannot
provide. Feeding that acceptance proof into `checkCertificate_optimal`
(`Soundness.lean`) yields a kernel-checked term concluding that these
on-disk certificates are optimal: the actual end-to-end claim, not a proxy
for it.
-/

namespace DiscreteModulusCert
namespace CertChecker

open Lean

def houseJson : String := include_str "../../cpp/examples/house.certificate.json"
def nestedJson : String := include_str "../../cpp/examples/nested.certificate.json"

/-- Parses a certificate JSON string into `RawCertificate` via
`Lean.Data.Json.parse` + `deriving FromJson`: the same two-step process
`checkCertificateJson` runs at runtime, exposed here as its own step so
the intermediate `RawCertificate` can be named and fed to
`checkCertificate_optimal` directly. -/
def parseRawCertificate (s : String) : Except String RawCertificate := do
  let j ← Json.parse s
  fromJson? (α := RawCertificate) j

def houseRaw : Except String RawCertificate := parseRawCertificate houseJson
def nestedRaw : Except String RawCertificate := parseRawCertificate nestedJson

/-- The parsed `RawCertificate` for `house`, not a hand-written literal and
not a fallback value: `houseRaw` parses to `some _`, checked (not assumed)
by `native_decide`. -/
def houseCertRaw : RawCertificate := houseRaw.toOption.get (by native_decide)

def nestedCertRaw : RawCertificate := nestedRaw.toOption.get (by native_decide)

/-- `checkCertificate` accepts the on-disk `house` certificate, run via
`native_decide` (compiled), not assumed. -/
theorem houseCertRaw_accepted : checkCertificate houseCertRaw = Except.ok () := by native_decide

/-- Same, for the on-disk multi-round `nested` certificate (190-edge piece
included). This is what makes it a stronger test than `house` alone:
`nested` exercises the cross-round gluing and deflation machinery, not
just a single small piece. -/
theorem nestedCertRaw_accepted : checkCertificate nestedCertRaw = Except.ok () := by native_decide

/-- **The end-to-end claim for `house`**: the certificate JSON file, parsed
by the JSON parser and checked by the checker, is fed straight into
`certificate_optimality` (via `checkCertificate_optimal`), concluding that
`house`'s own declared `rho`/`eta` fields are simultaneously optimal, with
no hand-transcription anywhere in the chain. Note the conclusion names
`house`'s own graph/`eta`/`rho` fields explicitly (via the `Except.ok`
equations), unlike an earlier, weaker version of this claim that would
have looked identical for `house` and `nested` alike -- see
`docs/certification/theorem.md`. -/
theorem house_end_to_end_optimal :
    ∃ (cg : CheckedGraph), buildGraph houseCertRaw.graph = Except.ok cg ∧
      ∃ (declaredEta declaredRho : Array ℚ),
        parseRationalArray cg.endpoints.size houseCertRaw.eta "eta" = Except.ok declaredEta ∧
        parseRationalArray cg.endpoints.size houseCertRaw.rho "rho" = Except.ok declaredRho ∧
        ∃ (μ : Pmf cg.toMultigraph.graphicMatroid),
          (fun e : Fin cg.endpoints.size => declaredEta.getD e.val 0) = μ.marginal ∧
          (∀ ρ' : CertDensity (Fin cg.endpoints.size),
            IsAdmissible cg.toMultigraph.graphicMatroid ρ' →
              sqNorm (fun e : Fin cg.endpoints.size => declaredRho.getD e.val 0) ≤ sqNorm ρ') ∧
          (∀ μ' : Pmf cg.toMultigraph.graphicMatroid,
            sqNorm μ.marginal ≤ sqNorm μ'.marginal) :=
  checkCertificate_optimal houseCertRaw houseCertRaw_accepted

/-- Same, for `nested`: the multi-round trace, not just `house`'s single
round. -/
theorem nested_end_to_end_optimal :
    ∃ (cg : CheckedGraph), buildGraph nestedCertRaw.graph = Except.ok cg ∧
      ∃ (declaredEta declaredRho : Array ℚ),
        parseRationalArray cg.endpoints.size nestedCertRaw.eta "eta" = Except.ok declaredEta ∧
        parseRationalArray cg.endpoints.size nestedCertRaw.rho "rho" = Except.ok declaredRho ∧
        ∃ (μ : Pmf cg.toMultigraph.graphicMatroid),
          (fun e : Fin cg.endpoints.size => declaredEta.getD e.val 0) = μ.marginal ∧
          (∀ ρ' : CertDensity (Fin cg.endpoints.size),
            IsAdmissible cg.toMultigraph.graphicMatroid ρ' →
              sqNorm (fun e : Fin cg.endpoints.size => declaredRho.getD e.val 0) ≤ sqNorm ρ') ∧
          (∀ μ' : Pmf cg.toMultigraph.graphicMatroid,
            sqNorm μ.marginal ≤ sqNorm μ'.marginal) :=
  checkCertificate_optimal nestedCertRaw nestedCertRaw_accepted

end CertChecker
end DiscreteModulusCert
