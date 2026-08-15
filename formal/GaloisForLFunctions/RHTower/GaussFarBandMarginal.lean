import GaloisForLFunctions.RHTower.GaussCubicTripleDominatingKernel

/-!
# Far-band vanishing from a summable coordinate marginal

A product-index kernel whose marginal in one integer coordinate decays with exponent `s > 1`
remains negligible after multiplication by the standard Gauss far-band ratio `I / |I+j|`.
-/

namespace RHTower

open Filter Topology GaloisForLFunctions
open scoped ENNReal

noncomputable section

theorem tendsto_tsum_prod_farBand_of_marginal
    {β : Type*} (W : ℤ → β → ℝ)
    {C D s : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hs : 1 < s)
    (hmarginal : ∀ j : ℤ,
      (∑' b : β, ENNReal.ofReal (W j b)) ≤
        ENNReal.ofReal (C / (1 + (j.natAbs : ℝ)) ^ s)) :
    Tendsto (fun I : ℕ => ∑' jb : ℤ × β,
      if I < 2 * jb.1.natAbs ∧ ((I : ℤ) + jb.1).natAbs ≠ 0 then
        ENNReal.ofReal (W jb.1 jb.2 *
          (D * (I : ℝ) / (((I : ℤ) + jb.1).natAbs : ℝ))) else 0)
      atTop (nhds 0) := by
  have hsqueeze : ∀ {f g : ℕ → ℝ≥0∞}, (∀ I, f I ≤ g I) →
      Tendsto g atTop (nhds 0) → Tendsto f atTop (nhds 0) := by
    intro f g hle hg
    rw [ENNReal.tendsto_nhds_zero] at hg ⊢
    intro ε hε
    filter_upwards [hg ε hε] with I hI
    exact (hle I).trans hI
  refine hsqueeze (g := fun I : ℕ => ∑' j : ℤ,
    if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
      ENNReal.ofReal ((C * D) * (I : ℝ) /
        ((1 + (j.natAbs : ℝ)) ^ s * (((I : ℤ) + j).natAbs : ℝ))) else 0) ?_
    (tendsto_tsum_farBandPower_zero (mul_nonneg hC hD) hs)
  intro I
  rw [ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hP : I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0
  · simp only [if_pos hP]
    set q : ℝ := D * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) with hq
    have hqnn : 0 ≤ q := by rw [hq]; positivity
    have hterm : ∀ b : β,
        ENNReal.ofReal (W j b * q) = ENNReal.ofReal q * ENNReal.ofReal (W j b) := by
      intro b
      rw [mul_comm, ← ENNReal.ofReal_mul hqnn]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine (mul_le_mul' le_rfl (hmarginal j)).trans_eq ?_
    rw [← ENNReal.ofReal_mul hqnn]
    congr 1
    rw [hq]
    have hden1 : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ s :=
      Real.rpow_pos_of_pos (by positivity) _
    have hden2 : (0 : ℝ) < (((I : ℤ) + j).natAbs : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr (by
        intro hz
        apply hP.2
        rw [hz, Int.natAbs_zero])
    field_simp
  · simp only [if_neg hP, tsum_zero]
    exact le_rfl

end

end RHTower
