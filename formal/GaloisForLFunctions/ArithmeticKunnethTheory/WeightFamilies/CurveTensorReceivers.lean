import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.TensorGrowth
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheWindowReceiversOfACurve

/-!
# From a fixed tensor growth rate to the curve windows

For a finite curve datum, a common exponential rate for all even powers of its
normalized traces is equivalent to purity and to positivity on the spectrum window.
The constants multiplying that rate may depend arbitrarily on the tensor degree.
The functional equation supplies the lower modulus bound once tensor amplification
has supplied the upper bound.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-- A common base rate across all even tensor degrees is precisely purity. -/
theorem curve_fixed_base_tensor_bound_iff (D : CurveDatum ι) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |D.trace n| ^ (2 * (k + 1)) ≤ C * B ^ n) ↔ ∀ i, ‖D.β i‖ = 1 := by
  have htrace (n : ℕ) : ‖∑ i, D.β i ^ n‖ = |D.trace n| := by
    change ‖D.powerSum n‖ = _
    rw [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
  have h := fixed_base_tensor_bound_iff D.β
  simp only [htrace] at h
  rw [h]
  refine ⟨fun hb i => ?_, fun hb i => (hb i).le⟩
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  have hi := hb i
  have hj := hb (D.fePerm i)
  have hlow := mul_le_mul_of_nonneg_right hj (norm_nonneg (D.β i))
  rw [hfe, one_mul] at hlow
  exact le_antisymm hi hlow

/-- The tensor growth criterion reproduces exactly the deciding window receiver. -/
theorem curve_tensor_bound_iff_spectrum_window (D : CurveDatum ι) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |D.trace n| ^ (2 * (k + 1)) ≤ C * B ^ n) ↔
      ∀ e : ℕ → ℝ, 0 ≤ D.toeplitz (range D.spectrum.card) e :=
  (curve_fixed_base_tensor_bound_iff D).trans D.unitary_iff_toeplitz_nonneg_on_spectrum_window

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
