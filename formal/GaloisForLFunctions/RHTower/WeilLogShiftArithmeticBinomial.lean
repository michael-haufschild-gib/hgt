import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticMassComparison
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse
import Mathlib.Data.Nat.Choose.Sum

/-! Arithmetic nodal weights are signed binomial coefficients divided by a factorial. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilBinomialDual (r : ℕ) (i : Fin (r + 2)) : ℝ :=
  (-1 : ℝ) ^ ((r + 1) - (i : ℕ)) * ((r + 1).choose (i : ℕ) : ℝ)

theorem finiteWeilBinomialDual_abs (r : ℕ) (i : Fin (r + 2)) :
    |finiteWeilBinomialDual r i| = ((r + 1).choose (i : ℕ) : ℝ) := by
  rw [finiteWeilBinomialDual, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity)]

theorem finiteWeilBinomialDual_last (r : ℕ) :
    finiteWeilBinomialDual r (Fin.last (r + 1)) = 1 := by
  simp [finiteWeilBinomialDual]

theorem finiteWeilBinomialDual_norm (r : ℕ) :
    ‖finiteWeilBinomialDual r‖ = ((r + 1).choose ((r + 1) / 2) : ℝ) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs, finiteWeilBinomialDual_abs]
    exact_mod_cast Nat.choose_le_middle (i : ℕ) (r + 1)
  · let m : Fin (r + 2) := ⟨(r + 1) / 2, by omega⟩
    have hm := norm_le_pi_norm (finiteWeilBinomialDual r) m
    rw [Real.norm_eq_abs, finiteWeilBinomialDual_abs] at hm
    exact hm

theorem finiteWeilBinomialDual_norm_pos (r : ℕ) : 0 < ‖finiteWeilBinomialDual r‖ := by
  have h : 1 ≤ ‖finiteWeilBinomialDual r‖ := by
    simpa only [Real.norm_eq_abs, finiteWeilBinomialDual_last, abs_one] using
      norm_le_pi_norm (finiteWeilBinomialDual r) (Fin.last (r + 1))
  linarith only [h]

theorem finiteWeilBinomialDual_abs_mass (r : ℕ) :
    finiteWeilAbsMass (finiteWeilBinomialDual r) = (2 : ℝ) ^ (r + 1) := by
  unfold finiteWeilAbsMass
  simp only [finiteWeilBinomialDual_abs]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ)) (r + 2)]
  exact_mod_cast Nat.sum_range_choose (r + 1)

theorem finiteWeilBinomialDual_moment (r p : ℕ) (hp : p ≤ r) :
    ∑ i, finiteWeilBinomialDual r i * finiteWeilArithmeticNodes r i ^ p = 0 := by
  unfold finiteWeilBinomialDual finiteWeilArithmeticNodes
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ((-1 : ℝ) ^ ((r + 1) - i) * ((r + 1).choose i : ℝ)) * (i : ℝ) ^ p) (r + 2)]
  exact GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_zero
    (R := ℝ) (j := p) (n := r + 1) (by omega)

theorem finiteWeilBinomialDual_top_moment (r : ℕ) :
    (∑ i, finiteWeilBinomialDual r i * finiteWeilArithmeticNodes r i ^ (r + 1)) =
      ((r + 1).factorial : ℝ) := by
  unfold finiteWeilBinomialDual finiteWeilArithmeticNodes
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ((-1 : ℝ) ^ ((r + 1) - i) * ((r + 1).choose i : ℝ)) *
      (i : ℝ) ^ (r + 1)) (r + 2)]
  exact GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_factorial (R := ℝ) (n := r + 1)

/-- The top moment fixes the exact factorial scale of the raw arithmetic weights. -/
theorem finiteWeilArithmeticWeights_eq_binomial (r : ℕ) :
    finiteWeilMomentWeights (finiteWeilArithmeticNodes r) =
      ((r + 1).factorial : ℝ)⁻¹ • finiteWeilBinomialDual r := by
  have hF : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hs := finiteWeilMomentWeights_span (finiteWeilArithmeticNodes r)
    (finiteWeilArithmeticNodes_injective r) (finiteWeilBinomialDual r)
    (fun p hp => finiteWeilBinomialDual_moment r p (by omega))
  rw [finiteWeilBinomialDual_top_moment] at hs
  funext i
  have hi := congrFun hs i
  change finiteWeilBinomialDual r i =
    ((r + 1).factorial : ℝ) * finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i at hi
  change finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i =
    ((r + 1).factorial : ℝ)⁻¹ * finiteWeilBinomialDual r i
  rw [hi, ← mul_assoc, inv_mul_cancel₀ hF.ne', one_mul]

/-- Normalization cancels the factorial and retains the central binomial coefficient. -/
theorem finiteWeilArithmeticDual_eq_binomial (r : ℕ) :
    finiteWeilNormalizedMomentDual (finiteWeilArithmeticNodes r) =
      ((r + 1).choose ((r + 1) / 2) : ℝ)⁻¹ • finiteWeilBinomialDual r := by
  have hF : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hC : 0 < ((r + 1).choose ((r + 1) / 2) : ℝ) := by
    rw [← finiteWeilBinomialDual_norm]
    exact finiteWeilBinomialDual_norm_pos r
  have hscalar :
      (((r + 1).factorial : ℝ)⁻¹ * ((r + 1).choose ((r + 1) / 2) : ℝ))⁻¹ *
        ((r + 1).factorial : ℝ)⁻¹ = ((r + 1).choose ((r + 1) / 2) : ℝ)⁻¹ := by
    field_simp [hF.ne', hC.ne']
  simp only [finiteWeilNormalizedMomentDual, finiteWeilArithmeticWeights_eq_binomial,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hF), finiteWeilBinomialDual_norm,
    smul_smul, hscalar]

/-- Exact absolute mass of the normalized arithmetic-node moment annihilator. -/
theorem finiteWeilArithmeticMass_eq_binomial (r : ℕ) :
    finiteWeilArithmeticMass r =
      (2 : ℝ) ^ (r + 1) / ((r + 1).choose ((r + 1) / 2) : ℝ) := by
  have hC : 0 < ((r + 1).choose ((r + 1) / 2) : ℝ) := by
    rw [← finiteWeilBinomialDual_norm]
    exact finiteWeilBinomialDual_norm_pos r
  unfold finiteWeilArithmeticMass
  rw [finiteWeilArithmeticDual_eq_binomial]
  simp only [finiteWeilAbsMass, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hC), ← Finset.mul_sum]
  change ((r + 1).choose ((r + 1) / 2) : ℝ)⁻¹ * finiteWeilAbsMass (finiteWeilBinomialDual r) = _
  rw [finiteWeilBinomialDual_abs_mass, div_eq_mul_inv]
  ring

/-- The logarithmic mass now has an explicit central-binomial reference on both sides. -/
theorem finiteWeilCanonicalCluster_binomial_mass_comparison (r k : ℕ) :
    ((k + 2 : ℕ) : ℝ) ^ (r + 1) *
        ((2 : ℝ) ^ (r + 1) / ((r + 1).choose ((r + 1) / 2) : ℝ)) ≤
      ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ∧
    ((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤
      ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) *
        ((2 : ℝ) ^ (r + 1) / ((r + 1).choose ((r + 1) / 2) : ℝ)) := by
  simpa only [finiteWeilArithmeticMass_eq_binomial] using
    finiteWeilCanonicalCluster_arithmetic_mass_comparison r k

end RHTower
