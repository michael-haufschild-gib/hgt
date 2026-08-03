import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelope
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# The multiplier preserves every divisor in the critical strip

The multiplier is analytic and nonvanishing on the right half-plane, so on that region it is a
holomorphic unit.  Multiplying a meromorphic datum by a unit leaves

* the order (zero or pole multiplicity) unchanged, and
* the trailing Laurent coefficient — the top conormal class — multiplied by the nonzero value of the
  unit,

so it is nonzero exactly when it was.  Hence the enveloping map is faithful on divisors and on top
jets throughout the critical strip: it can neither create, cancel, nor move a zero or a pole there.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- On the right half-plane the multiplier has order zero. -/
theorem meromorphicOrderAt_gammaGaussianEnvelope {ρ : ℂ} (hρ : 0 < ρ.re) :
    meromorphicOrderAt gammaGaussianEnvelope ρ = 0 := by
  rw [(analyticAt_gammaGaussianEnvelope ρ).meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr (gammaGaussianEnvelope_ne_zero_of_re_pos hρ))]
  simp

/-- The trailing coefficient of the multiplier is its value. -/
theorem meromorphicTrailingCoeffAt_gammaGaussianEnvelope {ρ : ℂ} (hρ : 0 < ρ.re) :
    meromorphicTrailingCoeffAt gammaGaussianEnvelope ρ = gammaGaussianEnvelope ρ :=
  (analyticAt_gammaGaussianEnvelope ρ).meromorphicTrailingCoeffAt_of_ne_zero
    (gammaGaussianEnvelope_ne_zero_of_re_pos hρ)

/-- **Every divisor in the right half-plane is preserved.**  The order of the enveloped datum equals
the order of the datum. -/
theorem meromorphicOrderAt_envelope_mul {F : ℂ → ℂ} {ρ : ℂ} (hF : MeromorphicAt F ρ)
    (hρ : 0 < ρ.re) :
    meromorphicOrderAt (fun s => gammaGaussianEnvelope s * F s) ρ = meromorphicOrderAt F ρ := by
  have h := meromorphicOrderAt_mul (analyticAt_gammaGaussianEnvelope ρ).meromorphicAt hF
  rw [meromorphicOrderAt_gammaGaussianEnvelope hρ, zero_add] at h
  exact h

/-- **The top conormal class is preserved up to the nonzero value of the multiplier.** -/
theorem meromorphicTrailingCoeffAt_envelope_mul {F : ℂ → ℂ} {ρ : ℂ} (hF : MeromorphicAt F ρ)
    (hρ : 0 < ρ.re) :
    meromorphicTrailingCoeffAt (fun s => gammaGaussianEnvelope s * F s) ρ
      = gammaGaussianEnvelope ρ * meromorphicTrailingCoeffAt F ρ := by
  have h := MeromorphicAt.meromorphicTrailingCoeffAt_mul
    (analyticAt_gammaGaussianEnvelope ρ).meromorphicAt hF
  rw [meromorphicTrailingCoeffAt_gammaGaussianEnvelope hρ] at h
  exact h

/-- The enveloped datum has a nonzero top jet exactly when the datum does. -/
theorem meromorphicTrailingCoeffAt_envelope_mul_ne_zero_iff {F : ℂ → ℂ} {ρ : ℂ}
    (hF : MeromorphicAt F ρ) (hρ : 0 < ρ.re) :
    meromorphicTrailingCoeffAt (fun s => gammaGaussianEnvelope s * F s) ρ ≠ 0
      ↔ meromorphicTrailingCoeffAt F ρ ≠ 0 := by
  rw [meromorphicTrailingCoeffAt_envelope_mul hF hρ, ne_eq, mul_eq_zero]
  constructor
  · intro h hc
    exact h (Or.inr hc)
  · intro h hc
    rcases hc with hc | hc
    · exact gammaGaussianEnvelope_ne_zero_of_re_pos hρ hc
    · exact h hc

/-- The enveloped datum is a unit at `ρ` exactly when the datum is. -/
theorem meromorphicOrderAt_envelope_mul_eq_zero_iff {F : ℂ → ℂ} {ρ : ℂ} (hF : MeromorphicAt F ρ)
    (hρ : 0 < ρ.re) :
    meromorphicOrderAt (fun s => gammaGaussianEnvelope s * F s) ρ = 0
      ↔ meromorphicOrderAt F ρ = 0 := by
  rw [meromorphicOrderAt_envelope_mul hF hρ]

/-- The enveloped datum vanishes identically near `ρ` exactly when the datum does. -/
theorem meromorphicOrderAt_envelope_mul_eq_top_iff {F : ℂ → ℂ} {ρ : ℂ} (hF : MeromorphicAt F ρ)
    (hρ : 0 < ρ.re) :
    meromorphicOrderAt (fun s => gammaGaussianEnvelope s * F s) ρ = ⊤
      ↔ meromorphicOrderAt F ρ = ⊤ := by
  rw [meromorphicOrderAt_envelope_mul hF hρ]

/-- The enveloped datum is meromorphic wherever the datum is. -/
theorem meromorphicAt_envelope_mul {F : ℂ → ℂ} {ρ : ℂ} (hF : MeromorphicAt F ρ) :
    MeromorphicAt (fun s => gammaGaussianEnvelope s * F s) ρ :=
  (analyticAt_gammaGaussianEnvelope ρ).meromorphicAt.mul hF

/-! ## The surviving boundary pole -/

/-- **A simple pole on the critical line survives the envelope.**  This is the repair of the sharp
seed: the boundary datum is represented rather than discarded, since `1/2` lies in the region where
the multiplier is a unit. -/
theorem meromorphicOrderAt_envelope_mul_half {F : ℂ → ℂ} {n : WithTop ℤ}
    (hF : MeromorphicAt F (1 / 2)) (hn : meromorphicOrderAt F (1 / 2) = n) :
    meromorphicOrderAt (fun s => gammaGaussianEnvelope s * F s) (1 / 2) = n := by
  have hre : (0:ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  rw [meromorphicOrderAt_envelope_mul hF hre, hn]


end

end GaloisForLFunctions
