import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCoupledEulerCorrectionPreservesThePolynomialLimit

/-!
# The coupled shifted Selberg form has its polynomial-profile limit

The exact Euler convolution identifies the literal Möbius–gcd form with
the corrected harmonic model. At the coupled shift the diagonal powers
cancel, so the full arithmetic form tends to the integral of `(P′−vP)²`.
-/

open Filter MeasureTheory Set Topology Polynomial
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The normalized Möbius–gcd form with independent gcd and coefficient shifts. -/
def shiftedSelbergProfileForm (P : ℝ → ℝ) (N : ℕ) (c v : ℝ) : ℝ :=
  Real.log N * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    shiftedSelbergOriginal (c / Real.log N) m n *
      (shiftedProfileWeight P N v m * shiftedProfileWeight P N v n))

/-- The literal arithmetic form equals its corrected harmonic model at every shift. -/
theorem shiftedSelbergProfileForm_eq_corrected (P : ℝ → ℝ) (N : ℕ) (c v : ℝ) :
    shiftedSelbergProfileForm P N c v =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        shiftedSelbergCorrectionCoeff (c / Real.log N) a b *
          shiftedProfileHarmonicRow P P N a b c v 0 := by
  unfold shiftedSelbergProfileForm
  rw [shiftedSelbergOriginal_weighted_eq_correction_harmonic_model]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
  have hb0 : 0 < b := (Finset.mem_Icc.mp hb).1
  rw [min_natDiv_eq_natDiv_max N a b ha0 hb0]
  unfold shiftedProfileHarmonicRow
  simp only [pow_zero, one_mul]
  rw [← mul_assoc, mul_comm (Real.log N), mul_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  rw [Real.rpow_def_of_pos hdR]
  have he : Real.log (d : ℝ) * (c / Real.log N) = c * (Real.log d / Real.log N) := by ring
  rw [he]

/-- The normalized shifted Möbius–gcd form at the coupled exponent. -/
def coupledShiftedSelbergForm (P : ℝ → ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  shiftedSelbergProfileForm P N (-2 * v) v

/-- The coupled arithmetic form is exactly the corrected coupled harmonic model. -/
theorem coupledShiftedSelbergForm_eq_corrected (P : ℝ → ℝ) (N : ℕ) (v : ℝ) :
    coupledShiftedSelbergForm P N v = correctedCoupledProfileSum P P N v 0 := by
  exact shiftedSelbergProfileForm_eq_corrected P N (-2 * v) v

/-- The full shifted Selberg polynomial form has the expected coupled limit,
including every convergent sequence of normalized shifts. -/
theorem tendsto_coupledShiftedSelbergForm (P : ℝ[X]) (hP0 : P.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun N : ℕ => coupledShiftedSelbergForm P.eval N (v N)) atTop
      (𝓝 (∫ t : ℝ in 0..1, (P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) ^ 2)) := by
  simpa only [coupledShiftedSelbergForm_eq_corrected, pow_zero, one_mul, pow_two] using
    tendsto_correctedCoupledProfileSum P P hP0 hP0 hv 0

end GaloisForLFunctions.MultiscaleMollifiedZetaField
