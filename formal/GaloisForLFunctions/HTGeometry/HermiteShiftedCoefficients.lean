import GaloisForLFunctions.HTGeometry.HermiteL2Expansion

/-!
# The Hermite coefficients under the shifted number operator

The shifted number operator is symmetric for the bilinear pairing, so moving one of its powers
across the pairing with a Hermite function multiplies the coefficient by the eigenvalue: the `j`-th
coefficient of `Kᵐf` is `(4π(j+1))ᵐ` times that of `f`.  Combined with the Cauchy–Schwarz bound on
the coefficients this says that the coefficient functional is bounded by the reciprocal eigenvalue
power times the `m`-th oscillator seminorm — arbitrarily strong decay, uniformly in the function.

Together with the value of the oscillator seminorms on the normalized Hermite functions this is
the pair of estimates that make the coefficient system nuclear.

* `hermiteCoeff_shiftedIterate` : **the coefficients of `Kᵐf`.**
* `norm_hermiteCoeff_shifted_le` : **`(4π(j+1))ᵐ|cⱼ(f)| ≤ Qₘ(f)`.**
* `shiftedSeminorm_hermiteUnit` : **`Qₖ(ĥⱼ) = (4π(j+1))ᵏ`.**
* `hermiteCoeffLM` : the coefficient functional, as a linear map.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Symmetry of the shifted number operator -/

theorem schwartzPair_shiftedNumberCLM (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (shiftedNumberCLM f) g = schwartzPair f (shiftedNumberCLM g) := by
  rw [shiftedNumberCLM_apply, shiftedNumberCLM_apply, schwartzPair_add_left,
    schwartzPair_add_right, schwartzPair_numberCLM, schwartzPair_smul_left,
    schwartzPair_smul_right]

theorem schwartzPair_shiftedNumberCLM_iterate (m : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair ((shiftedNumberCLM^[m]) f) g = schwartzPair f ((shiftedNumberCLM^[m]) g) := by
  induction m generalizing f g with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ m ih =>
    have h1 : ((shiftedNumberCLM^[m + 1]) f) = shiftedNumberCLM ((shiftedNumberCLM^[m]) f) :=
      Function.iterate_succ_apply' _ m f
    have h2 : ((shiftedNumberCLM^[m + 1]) g) = (shiftedNumberCLM^[m]) (shiftedNumberCLM g) :=
      Function.iterate_succ_apply _ m g
    rw [h1, h2, schwartzPair_shiftedNumberCLM, ih]

/-! ## The coefficients of an iterate -/

theorem hermiteCoeff_shiftedIterate (m j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    hermiteCoeff ((shiftedNumberCLM^[m]) f) j
      = ((4 * (π : ℂ) * (j + 1)) ^ m) * hermiteCoeff f j := by
  rw [hermiteCoeff, hermiteCoeff, schwartzPair_shiftedNumberCLM_iterate,
    shiftedNumberCLM_iterate_hermiteSchwartz, schwartzPair_smul_right]
  ring

theorem norm_hermiteCoeff_shifted_le (m j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (4 * π * ((j : ℝ) + 1)) ^ m * ‖hermiteCoeff f j‖ ≤ shiftedSeminorm m f := by
  have h := norm_hermiteCoeff_le ((shiftedNumberCLM^[m]) f) j
  rw [hermiteCoeff_shiftedIterate, norm_mul, norm_pow] at h
  have hval : ‖(4 * (π : ℂ) * ((j : ℂ) + 1))‖ = 4 * π * ((j : ℝ) + 1) := by
    have hcast : (4 * (π : ℂ) * ((j : ℂ) + 1)) = ((4 * π * ((j : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hval] at h
  rwa [shiftedSeminorm_apply]

/-! ## The oscillator seminorms of the normalized Hermite functions -/

theorem shiftedNumberCLM_iterate_hermiteUnit (m j : ℕ) :
    (shiftedNumberCLM^[m]) (hermiteUnit j) = ((4 * (π : ℂ) * (j + 1)) ^ m) • hermiteUnit j := by
  rw [hermiteUnit, shiftedNumberCLM_iterate_smul, shiftedNumberCLM_iterate_hermiteSchwartz,
    smul_comm]

theorem shiftedSeminorm_hermiteUnit (k j : ℕ) :
    shiftedSeminorm k (hermiteUnit j) = (4 * π * ((j : ℝ) + 1)) ^ k := by
  rw [shiftedSeminorm_apply]
  exact norm_toLp_hermiteUnit_shifted k j

/-! ## The coefficient functional -/

/-- The `j`-th Hermite coefficient, as a linear functional on the Schwartz space. -/
def hermiteCoeffLM (j : ℕ) : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun f := hermiteCoeff f j
  map_add' f g := by
    rw [hermiteCoeff, hermiteCoeff, hermiteCoeff, schwartzPair_add_left]
    ring
  map_smul' c f := by
    show hermiteCoeff (c • f) j = c * hermiteCoeff f j
    rw [hermiteCoeff, hermiteCoeff, schwartzPair_smul_left]
    ring

@[simp] theorem hermiteCoeffLM_apply (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    hermiteCoeffLM j f = hermiteCoeff f j := rfl

end GaloisForLFunctions

end
