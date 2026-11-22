import GaloisForLFunctions.HTGeometry.AveragedRadiusSelection
import Mathlib.Analysis.MeanInequalities

/-! Select a radius with a lower bound on the product of distances to finitely many centres. -/

open Finset

namespace QH.PrimeProgressions.T2

/-- Averaging inverse square roots and applying AM–GM gives a radius with a large distance product. -/
theorem prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  by_cases he : s = ∅
  · subst s
    exact ⟨c, by simpa using hr.le, by simp⟩
  obtain ⟨x, hx, hsep, hsum⟩ :=
    GaloisForLFunctions.HTGeometry.exists_mem_Icc_sum_rpow_le s (fun j => t j - (c - 3 * r))
      (show 0 < 4 * r by positivity)
  let ρ := c - 3 * r + x
  have hρ : |ρ - c| ≤ r := abs_le.mpr
    ⟨by dsimp only [ρ]; linarith only [hx.1], by dsimp only [ρ]; linarith only [hx.2]⟩
  refine ⟨ρ, hρ, ?_⟩
  have ht (j : ι) : |x - (t j - (c - 3 * r))| = |ρ - t j| := by
    congr 1
    dsimp only [ρ]
    ring
  let u (j : ι) := (Real.sqrt |ρ - t j|)⁻¹
  let A := 3 * Real.sqrt (2 * r) / (2 * r)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hu (j : ι) (hj : j ∈ s) : 0 ≤ u j := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hpsum : ∑ j ∈ s, u j ≤ s.card * A := by
    simp_rw [ht, Real.rpow_neg (abs_nonneg _) (1 / 2), ← Real.sqrt_eq_rpow] at hsum
    rw [show 4 * r / 2 = 2 * r by ring] at hsum
    exact hsum
  have hc : (0 : ℝ) < s.card := Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr he))
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => 1) u (fun _ _ => zero_le_one)
    (by simpa only [sum_const, nsmul_eq_mul, mul_one] using hc) hu
  simp only [Real.rpow_one, sum_const, nsmul_eq_mul, mul_one, one_mul] at hgm
  have hmean : (∑ j ∈ s, u j) / s.card ≤ A := (div_le_iff₀ hc).2 (by
    rw [mul_comm A]
    exact hpsum)
  have hp0 : 0 ≤ ∏ j ∈ s, u j := prod_nonneg hu
  have hp : (∏ j ∈ s, u j) ≤ A ^ s.card := by
    calc
      _ = ((∏ j ∈ s, u j) ^ ((s.card : ℝ)⁻¹)) ^ s.card := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hp0 _) (hgm.trans hmean) _
  have hu2 : (∏ j ∈ s, u j) ^ 2 = (∏ j ∈ s, |ρ - t j|)⁻¹ := by
    rw [← Finset.prod_pow]
    simp only [u, inv_pow, Real.sq_sqrt (abs_nonneg _), Finset.prod_inv_distrib]
  have hA2 : A ^ 2 = 9 / (2 * r) := by
    dsimp only [A]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hr.ne'] <;> ring
  have hp2 := pow_le_pow_left₀ hp0 hp 2
  rw [hu2, ← pow_mul, Nat.mul_comm s.card 2, pow_mul, hA2] at hp2
  have hpPos : 0 < ∏ j ∈ s, |ρ - t j| := prod_pos fun j hj => abs_pos.mpr fun hz =>
    hsep j hj (by dsimp only [ρ] at hz; linarith only [hz])
  have hrecip : ((9 / (2 * r)) ^ s.card)⁻¹ ≤ ∏ j ∈ s, |ρ - t j| :=
    (inv_le_comm₀ (by positivity) hpPos).2 hp2
  rw [← inv_pow, inv_div] at hrecip
  have hbase : r / 25 ≤ 2 * r / 9 := by linarith only [hr]
  exact (pow_le_pow_left₀ (by positivity) hbase _).trans hrecip

end QH.PrimeProgressions.T2
