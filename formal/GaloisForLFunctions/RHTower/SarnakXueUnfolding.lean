import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

/-!
# Unfolding a ball integral against a fundamental domain

For a countable group `G` acting by measure-preserving maps with fundamental domain `F`, a `G`-invariant
`u ≥ 0` and a measurable set `B`, the automorphic kernel `K(x) = Σ_g 1_B(g⁻¹x)` gives
`∫_B u = ∫_F K u` and `∫_F K² = Σ_g μ(B ∩ gB)`; Cauchy–Schwarz then yields
`(∫_B u)² ≤ (Σ_g μ(B ∩ gB)) ∫_F u²` (`lintegral_set_sq_le`). This is the pretrace inequality in the form
used for multiplicity bounds.
-/

namespace GaloisForLFunctions.RHTower.SarnakXueUnfolding

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued functions. -/
theorem lintegral_mul_sq_le {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {G : Type*} [Group G] [MulAction G α] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
  [Countable G]

/-- **Unfolded Cauchy–Schwarz.** For a fundamental domain `F` of a countable group `G` acting by
measure-preserving maps, a `G`-invariant `u ≥ 0` and a measurable set `B`,
`(∫_B u)² ≤ (Σ_g μ(B ∩ g•B)) · ∫_F u²`. -/
theorem lintegral_set_sq_le {F B : Set α} (hF : IsFundamentalDomain G F μ) (hB : MeasurableSet B)
    {u : α → ℝ≥0∞} (hu : Measurable u) (hinv : ∀ (g : G) x, u (g • x) = u x) :
    (∫⁻ x in B, u x ∂μ) ^ 2 ≤ (∑' g : G, μ (B ∩ g • B)) * ∫⁻ x in F, u x ^ 2 ∂μ := by
  classical
  set K : α → ℝ≥0∞ := fun x => ∑' g : G, B.indicator 1 (g⁻¹ • x)
  have hKm : Measurable K := by
    apply Measurable.tsum
    intro g
    exact (measurable_one.indicator hB).comp (measurable_const_smul g⁻¹)
  have hKinv : ∀ (h : G) x, K (h • x) = K x := by
    intro h x
    simp only [K]
    rw [← (Equiv.mulLeft h).tsum_eq]
    apply tsum_congr
    intro g
    simp only [Equiv.coe_mulLeft, mul_inv_rev, mul_smul, inv_smul_smul]
  -- unfold `∫_B u`
  have h1 : ∫⁻ x in B, u x ∂μ = ∫⁻ x in F, K x * u x ∂μ := by
    rw [← lintegral_indicator hB, hF.lintegral_eq_tsum' (B.indicator u)]
    rw [← lintegral_tsum (f := fun g x => B.indicator u (g⁻¹ • x))
      (fun g => ((hu.indicator hB).comp (measurable_const_smul g⁻¹)).aemeasurable)]
    congr 1
    funext x
    simp only [K, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    simp only [indicator, Pi.one_apply, hinv]
    split_ifs <;> simp
  -- unfold `∫_F K²`
  have h2 : ∫⁻ x in F, K x ^ 2 ∂μ = ∑' g : G, μ (B ∩ g • B) := by
    have e : ∀ x, K x ^ 2 = ∑' g : G, B.indicator 1 (g⁻¹ • x) * K x := by
      intro x; rw [ENNReal.tsum_mul_right, sq]
    simp_rw [e]
    rw [lintegral_tsum (f := fun g x => B.indicator 1 (g⁻¹ • x) * K x)
      (fun g => (((measurable_one.indicator hB).comp (measurable_const_smul g⁻¹)).mul
      hKm).aemeasurable)]
    -- each term: `∫_F 1_B(g⁻¹x) K(x) = ∫_{g•F} 1_B K`
    have hterm : ∀ g : G, ∫⁻ x in F, B.indicator 1 (g⁻¹ • x) * K x ∂μ =
        ∫⁻ x in F, (fun y => B.indicator 1 y * K y) (g⁻¹ • x) ∂μ := by
      intro g
      apply lintegral_congr
      intro x
      simp only [hKinv]
    simp_rw [hterm]
    rw [← hF.lintegral_eq_tsum' (fun y => B.indicator 1 y * K y)]
    -- `∫ 1_B K = Σ_g μ(B ∩ g•B)`
    simp only [K]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum (f := fun g x => B.indicator 1 x * B.indicator 1 (g⁻¹ • x))
      (fun g => ((measurable_one.indicator hB).mul
      ((measurable_one.indicator hB).comp (measurable_const_smul g⁻¹))).aemeasurable)]
    apply tsum_congr
    intro g
    rw [← lintegral_indicator_one (hB.inter (hB.const_smul g))]
    apply lintegral_congr
    intro x
    simp only [indicator, Pi.one_apply, mem_inter_iff, mem_smul_set_iff_inv_smul_mem]
    split_ifs <;> simp_all
  rw [h1, ← h2]
  exact lintegral_mul_sq_le hKm.aemeasurable hu.aemeasurable

end GaloisForLFunctions.RHTower.SarnakXueUnfolding
