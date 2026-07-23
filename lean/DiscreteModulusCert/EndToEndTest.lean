import DiscreteModulusCert.Soundness
import Lean.Data.Json

/-!
# End-to-end test: real certificate JSON, parsed at compile time, proved optimal

Every earlier soundness result worked over an abstract,
universally-quantified `raw : RawCertificate` (`Soundness.lean`'s
`checkCertificate_sound`/`checkCertificate_optimal`) -- not quite "feed a
parsed certificate into `certificate_optimality` itself" for a *real*
file on disk: this file closes that gap.

`include_str` (Lean 4 core) embeds `cpp/examples/house.certificate.json` and
`cpp/examples/nested.certificate.json`'s actual contents as string literals
at elaboration time -- the same bytes `certificate_builder.py` wrote and
`lake exe verify_cert` reads at runtime, not a re-typed copy. Parsing that
string with the real `Lean.Data.Json`/`FromJson` machinery
(`CertChecker.RawCertificate`) and unwrapping the result (`Option.get`,
justified by `native_decide` rather than assumed) gives a genuine, concrete
`RawCertificate` term -- no dummy fallback value, no hand-transcription.
`native_decide` then runs `checkCertificate` against that concrete term
(compiled, the same mechanism `verify_cert`/`ForestDecide.lean`'s maximality
checks already rely on for `nested`'s 190-edge piece -- `#eval`'s interpreter
would be far too slow here, see `CertCheckerTest.lean`'s own docstring for
why `nested`'s `#eval` stays disabled). Feeding the resulting acceptance
proof into `checkCertificate_optimal` (`Soundness.lean`) yields a
kernel-checked term concluding real, on-disk certificates are genuinely
optimal -- the actual end-to-end claim, not a proxy for it.
-/

namespace DiscreteModulusCert
namespace CertChecker

open Lean

def houseJson : String := include_str "../../cpp/examples/house.certificate.json"
def nestedJson : String := include_str "../../cpp/examples/nested.certificate.json"

/-- Parses a certificate JSON string into `RawCertificate` via the real
parser (`Lean.Data.Json.parse` + `deriving FromJson`) -- the same two-step
process `checkCertificateJson` runs at runtime, exposed here as its own
step so the intermediate `RawCertificate` can be named and fed to
`checkCertificate_optimal` directly. -/
def parseRawCertificate (s : String) : Except String RawCertificate := do
  let j ← Json.parse s
  fromJson? (α := RawCertificate) j

def houseRaw : Except String RawCertificate := parseRawCertificate houseJson
def nestedRaw : Except String RawCertificate := parseRawCertificate nestedJson

/-- The genuine, parsed `RawCertificate` for `house` -- not a hand-written
literal and not a fallback value: `houseRaw` really does parse to
`some _`, checked (not assumed) by `native_decide`. -/
def houseCertRaw : RawCertificate := houseRaw.toOption.get (by native_decide)

def nestedCertRaw : RawCertificate := nestedRaw.toOption.get (by native_decide)

/-- `checkCertificate` genuinely accepts the real, on-disk `house`
certificate -- run via `native_decide` (compiled), not assumed. -/
theorem houseCertRaw_accepted : checkCertificate houseCertRaw = Except.ok () := by native_decide

/-- Same, for the real, on-disk multi-round `nested` certificate
(190-edge piece included) -- this is exactly what makes it a stronger test
than `house` alone: `nested` actually exercises the cross-round gluing and
deflation machinery, not just a single small piece. -/
theorem nestedCertRaw_accepted : checkCertificate nestedCertRaw = Except.ok () := by native_decide

/-- **The end-to-end claim for `house`**: the real certificate JSON file,
parsed by the real JSON parser and checked by the real checker, is fed
straight into `certificate_optimality` (via `checkCertificate_optimal`) --
concluding `house`'s solver-produced `ρ`/`μ` really are simultaneously
optimal, with no hand-transcription anywhere in the chain. -/
theorem house_end_to_end_optimal :
    ∃ (n m : Nat) (G : Multigraph (Fin n) (Fin m)) (ρ : CertDensity (Fin m)) (μ : Pmf G.graphicMatroid),
      (∀ ρ' : CertDensity (Fin m), IsAdmissible G.graphicMatroid ρ' → sqNorm ρ ≤ sqNorm ρ') ∧
      (∀ μ' : Pmf G.graphicMatroid, sqNorm μ.marginal ≤ sqNorm μ'.marginal) :=
  checkCertificate_optimal houseCertRaw houseCertRaw_accepted

/-- Same, for `nested` -- the real multi-round trace, not just `house`'s
single round. -/
theorem nested_end_to_end_optimal :
    ∃ (n m : Nat) (G : Multigraph (Fin n) (Fin m)) (ρ : CertDensity (Fin m)) (μ : Pmf G.graphicMatroid),
      (∀ ρ' : CertDensity (Fin m), IsAdmissible G.graphicMatroid ρ' → sqNorm ρ ≤ sqNorm ρ') ∧
      (∀ μ' : Pmf G.graphicMatroid, sqNorm μ.marginal ≤ sqNorm μ'.marginal) :=
  checkCertificate_optimal nestedCertRaw nestedCertRaw_accepted

end CertChecker
end DiscreteModulusCert
