import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeSideScaleUnitAndItsUniversalFloor
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem

/-!
# The certificate below the first prime is a tautology

A reading that takes the same value on all data cannot certify anything beyond what holds
universally. That is obvious, and worth isolating as a lemma
(`resolutionLimit_eq_of_constant_reading`), because the field has readings which are constant in
regimes where one would not expect it.

The prime side has such a regime, and it is arithmetically determined. Every prime weight
whatsoever is Weil-positive on tests of aperture `3/10` (`weightAperturePositivity_threeTenths`,
from `SquareRootThreshold.weilFullFunctional_re_ge_of_support_le_threeTenths`), because no prime
enters the window: the first prime power sits at `log 2`. Hence the prime-side positivity reading at
any radius up to `3/10` is **constant** (`weightAperturePositivity_const_of_le_threeTenths`) and
therefore maximally uninformative for every invariant of a weight
(`resolutionLimit_eq_of_constant_weightAperturePositivity`).

So the universal floor of `ThePrimeSideScaleUnitAndItsUniversalFloor` is not merely a bound: inside
it the certificate is a tautology. A prime-side mechanism gains nothing at all until its radius
passes the first prime's window, and the arithmetic — the location of the smallest prime power —
fixes where that is. This is the prime-side companion of
`TheSignIsUninformativeAtEveryAperture`: a qualitative reading in a regime where it is constant
reads nothing, and the field's two faces each have such a regime.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

variable {D O : Type*}

/-! ### 1. Constant readings -/

/-- **A constant reading has the maximal limit for every invariant.** -/
theorem resolutionLimit_eq_of_constant_reading {I : D → ℝ} {r : D → O}
    (hconst : ∀ x y : D, r x = r y) {M : ℝ} (hub : ∀ x : D, I x ≤ M) {e : D} (hval : I e = M)
    (d : D) : resolutionLimit I r d = M :=
  resolutionLimit_eq_of_mem_shadow_of_max hub (hconst e d) hval

/-! ### 2. The prime-side regime -/

/-- **Below the first prime's window the certificate holds for every weight.** -/
theorem weightAperturePositivity_const_of_le_threeTenths {R : ℝ} (hR : R ≤ 3 / 10)
    (lam lam' : ℕ → ℝ) :
    weightAperturePositivity R lam = weightAperturePositivity R lam' :=
  propext (iff_of_true
    (weightAperturePositivity_mono hR (weightAperturePositivity_threeTenths lam))
    (weightAperturePositivity_mono hR (weightAperturePositivity_threeTenths lam')))

/-- **Hence it is maximally uninformative for every invariant of a weight.** -/
theorem resolutionLimit_eq_of_constant_weightAperturePositivity {R : ℝ} (hR : R ≤ 3 / 10)
    {I : (ℕ → ℝ) → ℝ} {M : ℝ} (hub : ∀ lam : ℕ → ℝ, I lam ≤ M) {e : ℕ → ℝ} (hval : I e = M)
    (lam : ℕ → ℝ) : resolutionLimit I (weightAperturePositivity R) lam = M :=
  resolutionLimit_eq_of_constant_reading
    (fun x y => weightAperturePositivity_const_of_le_threeTenths hR x y) hub hval lam

/-- **The prime-side tautology.** Inside the first prime's window the certificate is constant, so
it neither distinguishes any two weights nor certifies anything about any invariant; the
arithmetic — the position of the smallest prime power — is what fixes the regime. -/
theorem theCertificateBelowTheFirstPrimeIsATautology {R : ℝ} (hR : R ≤ 3 / 10) :
    (∀ lam lam' : ℕ → ℝ,
        weightAperturePositivity R lam = weightAperturePositivity R lam') ∧
      ∀ lam : ℕ → ℝ, weightFailureApertures lam ⊆ Ioi (3 / 10) :=
  ⟨fun lam lam' => weightAperturePositivity_const_of_le_threeTenths hR lam lam',
    weightFailureApertures_subset_Ioi_threeTenths⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
