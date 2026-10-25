import GaloisForLFunctions.BezoutValuationIncidence.UniformHarmonicVaughanGramsAtHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicLawsForVaughanSuperpositions

/-!
At half damping the harmonic Gram error controls every finite coefficient
superposition. Its bound is quadratic in the absolute coefficient sum; removing
the smooth coefficient gives a uniform finite energy bound.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The endpoint harmonic Gram law controls every real packet by its absolute coefficient sum. -/
theorem exists_uniform_pmPronicVaughanPacket_half_harmonic_energy_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, ∀ w : Fin 5 → ℝ,
      |pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T ^ 2 -
        (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V *
          (w 3 - w 2)) ^ 2 * (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1))| ≤
        C * (∑ i : Fin 5, |w i|) ^ 2 := by
  obtain ⟨C, hC, hG⟩ := exists_uniform_pmPronicVaughanCentredGram_half_harmonic_error_bound
  refine ⟨C, hC, fun U V T w => ?_⟩
  let k : ℝ := subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V
  let J : ℝ := ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1)
  let E : Fin 5 → Fin 5 → ℝ := fun i j =>
    pmPronicVaughanCentredGram (1 / 2) U V T i j -
      k ^ 2 * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j * J
  have hsmooth : (∑ i : Fin 5, ∑ j : Fin 5, w i * w j *
      (k ^ 2 * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j * J)) =
        (k * (w 3 - w 2)) ^ 2 * J := by
    rw [← sum_mul_pmPronicVaughanSmoothSigns w, mul_pow]
    simp only [pow_two, mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl fun j _ => by ring
  have heq : pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T ^ 2 -
      (k * (w 3 - w 2)) ^ 2 * J =
        ∑ i : Fin 5, ∑ j : Fin 5, w i * w j * E i j := by
    rw [sq_pronicNorm_pmPronicVaughanCentredPacket_eq_gram, ← hsmooth]
    simp only [E, mul_sub, sum_sub_distrib]
  change |pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T ^ 2 -
    (k * (w 3 - w 2)) ^ 2 * J| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |w i * w j * E i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |w i| * |w j| * C := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hG U V T i j)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      rw [pow_two]
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl fun j _ => by ring

/-- Annihilating the smooth coefficient gives one endpoint packet energy bound at every cutoff. -/
theorem exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_smooth_zero :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, ∀ w : Fin 5 → ℝ,
      subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V *
        (w 3 - w 2) = 0 →
      pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T ^ 2 ≤
        C * (∑ i : Fin 5, |w i|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmPronicVaughanPacket_half_harmonic_energy_error
  refine ⟨C, hC, fun U V T w hw => ?_⟩
  simpa only [hw, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero,
    abs_of_nonneg (sq_nonneg
      (pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T))] using hbound U V T w

/-- Equal convolution coefficients give a common endpoint energy bound for all cutoffs and horizons. -/
theorem exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_equal_convolution_coefficients :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, ∀ w : Fin 5 → ℝ, w 2 = w 3 →
      pronicNorm (pmPronicVaughanCentredPacket (1 / 2) U V w) T ^ 2 ≤
        C * (∑ i : Fin 5, |w i|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_smooth_zero
  exact ⟨C, hC, fun U V T w hw => hbound U V T w (by rw [hw, sub_self, mul_zero])⟩

#print axioms exists_uniform_pmPronicVaughanPacket_half_harmonic_energy_error
#print axioms exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_smooth_zero
#print axioms exists_uniform_pmPronicVaughanPacket_half_energy_bound_of_equal_convolution_coefficients
end GaloisForLFunctions.BezoutValuationIncidence
