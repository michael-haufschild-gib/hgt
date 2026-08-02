import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceSpace

/-!
# The co-Poisson sum has a constant aperture head

If the seed vanishes below the aperture then every term of the co-Poisson sum vanishes on the
aperture head: for `|t| < b` and `n ≥ 1` the argument `|t|/n` is again below `b`.  The whole sum is
therefore empty there and the co-Poisson value reduces to its correction term, which is a constant.

This is the mechanism behind Burnol's landing statement, and it settles the first of the two
defining Sonine conditions for every seed supported above the aperture, with no analytic hypothesis
beyond the support condition.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem burnolCoPoissonRightSum_term_eq_zero {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} (ht : |t| < b) (n : ℕ) :
    g (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
  by_contra hne
  have hmem : |t| / ((n + 1 : ℕ) : ℝ) ∈ Icc b b⁻¹ :=
    hsupp (Function.mem_support.mpr hne)
  have hle : |t| / ((n + 1 : ℕ) : ℝ) ≤ |t| := by
    refine div_le_self (abs_nonneg t) ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  have := hmem.1
  linarith

/-- **The co-Poisson head is empty below the aperture.**  For a seed supported above `b` the sum
part of the co-Poisson value vanishes on the aperture head. -/
theorem burnolCoPoissonRightSum_eq_const {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) {t : ℝ} (ht : |t| < b) :
    burnolCoPoissonRightSum g t = -∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹) := by
  have hzero : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) = 0 := by
    intro n
    rw [burnolCoPoissonRightSum_term_eq_zero hsupp ht n, mul_zero]
  rw [burnolCoPoissonRightSum, tsum_congr hzero, tsum_zero, zero_sub]

/-- **Constant aperture head of the co-Poisson sum.**  A seed supported above the aperture makes the
co-Poisson sum almost everywhere constant on the aperture head, so the first defining Sonine
condition holds unconditionally. -/
theorem soninHeadConstant_burnolCoPoissonRightSum {b : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    SoninHeadConstant b (burnolCoPoissonRightSum g) := by
  refine ⟨-∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹), ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  refine burnolCoPoissonRightSum_eq_const hsupp ?_
  rw [abs_of_pos ht.1]
  exact ht.2

/-- The same statement for the seed of an inhabited co-Poisson source. -/
theorem soninHeadConstant_burnolCoPoissonSource_seed {b : ℝ} (g : BurnolCoPoissonSource b) :
    SoninHeadConstant b (burnolCoPoissonRightSum g.seed) :=
  soninHeadConstant_burnolCoPoissonRightSum g.seed_support

end RHTower
