import GaloisForLFunctions.BezoutValuationIncidence.ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits
import GaloisForLFunctions.HTGeometry.VanishingPositiveScalesRealizeHarmonicMasses
import GaloisForLFunctions.RHTower.FiniteMobiusHarmonicSumsNeverVanish

/-!
Squared nonzero Möbius harmonic products supply positive vanishing scales.
Choosing their horizons realizes every nonnegative endpoint harmonic mass and hence
every matrix on the exact Vaughan limit ray.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem vaughan_successor_cutoff_atTop :
    Tendsto (fun t : ℕ => t + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with t ht
  omega

/-- Every nonnegative harmonic mass is attained with both arithmetic cutoffs tending to infinity. -/
theorem exists_pmPronicVaughanHalfHarmonicMass_limit {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (t + 1) (t + 1) (H t)) atTop (𝓝 ℓ) := by
  by_cases hz : ℓ = 0
  · subst ℓ
    have hH : Tendsto (fun t : ℕ => (t + 1) * (t + 1)) atTop atTop := by
      apply tendsto_atTop.2
      intro N
      filter_upwards [eventually_ge_atTop N] with t ht
      simpa only [mul_one] using Nat.mul_le_mul (by omega : N ≤ t + 1) (by omega : 1 ≤ t + 1)
    exact ⟨fun t => (t + 1) * (t + 1), hH,
      tendsto_pmPronicVaughanHalfHarmonicMass_product (fun t => t + 1) (fun t => t + 1) hH⟩
  · have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ (Ne.symm hz)
    let k : ℕ → ℝ := fun t =>
      (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial (t + 1) * deningerHarmonicPartial (t + 1)) ^ 2
    have hk (t : ℕ) : 0 < k t := by
      have hc : subHalfZetaCoeff (1 / 2) ≠ 0 :=
        subHalfZetaCoeff_ne_zero (by norm_num) (by norm_num)
      have hH : deningerHarmonicPartial (t + 1) ≠ 0 := by
        rw [deningerHarmonicPartial_eq_sum_Icc]
        exact sum_moebius_div_ne_zero (by omega)
      exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero hc hH) hH)
    have hHarmonic : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
      simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
    have hk0 : Tendsto k atTop (𝓝 0) := by
      simpa only [k, Function.comp_def, mul_zero, zero_mul,
        zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (((hHarmonic.comp vaughan_successor_cutoff_atTop).const_mul (subHalfZetaCoeff (1 / 2))).mul
          (hHarmonic.comp vaughan_successor_cutoff_atTop)).pow 2
    obtain ⟨H, hH, hm⟩ := HTGeometry.exists_tendsto_scaled_shiftedHarmonicSum hk hk0 hℓpos
    refine ⟨H, hH, ?_⟩
    simpa only [pmPronicVaughanHalfHarmonicMass, k, HTGeometry.shiftedHarmonicSum] using hm

/-- Every point of the nonnegative endpoint limit ray is an actual moving Vaughan Gram limit. -/
theorem exists_pmPronicVaughanCentredGram_half_limit {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧ ∀ i j : Fin 5,
      Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (t + 1) (t + 1) (H t) i j)
        atTop (𝓝 (pmPronicVaughanHalfLimitRay ℓ i j)) := by
  obtain ⟨H, hH, hm⟩ := exists_pmPronicVaughanHalfHarmonicMass_limit hℓ
  exact ⟨H, hH, fun i j => tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass hH
    vaughan_successor_cutoff_atTop vaughan_successor_cutoff_atTop hm i j⟩

/-- The nonnegative ray is exactly the set of finite joint limits with both cutoffs and horizon divergent. -/
theorem pmPronicVaughanCentredGram_half_joint_limit_iff
    (L : Matrix (Fin 5) (Fin 5) ℝ) :
    (∃ H U V : ℕ → ℕ, Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧ Tendsto V atTop atTop ∧
      ∀ i j : Fin 5, Tendsto (fun t =>
        pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j) atTop (𝓝 (L i j))) ↔
      ∃ ℓ : ℝ, 0 ≤ ℓ ∧ L = pmPronicVaughanHalfLimitRay ℓ := by
  constructor
  · rintro ⟨H, U, V, hH, hU, hV, hL⟩
    obtain ⟨hℓ, _hm, heq⟩ := pmPronicVaughanCentredGram_half_limit_forces_harmonic_mass hH hU hV hL
    exact ⟨L 3 3, hℓ, heq⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain ⟨H, hH, hL⟩ := exists_pmPronicVaughanCentredGram_half_limit hℓ
    exact ⟨H, fun t => t + 1, fun t => t + 1, hH,
      vaughan_successor_cutoff_atTop, vaughan_successor_cutoff_atTop, hL⟩

#print axioms exists_pmPronicVaughanHalfHarmonicMass_limit
#print axioms exists_pmPronicVaughanCentredGram_half_limit
#print axioms pmPronicVaughanCentredGram_half_joint_limit_iff
end GaloisForLFunctions.BezoutValuationIncidence
