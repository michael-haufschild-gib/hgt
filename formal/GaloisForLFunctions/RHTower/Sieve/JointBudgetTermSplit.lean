import GaloisForLFunctions.RHTower.Sieve.AffineMajorantFromHeight

/-!
# The Gallagher terms at a low expiry height

`Sieve/BudgetTermSplit.spectral_terms_le` packages Gallagher's dyadic split for an expiry height
`T₀` equal to the index range `B₀`.  The §4 arrangement cannot supply a bound at that height — the
cancellation threshold of `(35)` would have to be a *square root* of the block rather than a
polylogarithmic saving — but it does not need to: the expiry height only has to exceed the Gallagher
cut `B₀/h` by a factor tending to infinity.

This module records the two arithmetic facts that make that work: the affine majorant with the mean
value theorem's constant converted into slope at the expiry height, and the resulting bound on the
three Gallagher terms.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- **The affine majorant at a free expiry height.**  Above `T₀` the mean value theorem's constant
term is at most `(M/T₀)·T`, so it can be carried in the slope. -/
theorem affineMajorant_of_bound_at' {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) {M : ℕ}
    (hsM : ∀ n ∈ s, n ≤ M) {Wc T₀ β₀ : ℝ} (hW : 1 ≤ Wc) (hT0 : 0 < T₀) :
    (∫ w in Set.Icc (-T₀) T₀, ‖logPoly a s w‖ ^ 2) ≤ β₀ →
    ∀ T : ℝ, Wc ≤ T →
      (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ 2)
        ≤ ((5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((M : ℝ) / T₀))
            * ∑ n ∈ s, ‖a n‖ ^ 2) * T + β₀ := by
  intro hbound T hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hW hT
  have hT0' : (0 : ℝ) ≤ T := by linarith
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hβ0 : (0 : ℝ) ≤ β₀ := by
    refine le_trans ?_ hbound
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => ?_
    positivity
  have hslope0 : (0 : ℝ)
      ≤ ((5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((M : ℝ) / T₀)) * ∑ n ∈ s, ‖a n‖ ^ 2) * T := by
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((M : ℝ) / T₀) := by
      have : (0 : ℝ) ≤ (M : ℝ) / T₀ := div_nonneg hM0 hT0.le
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith
    exact mul_nonneg (mul_nonneg h1 hE0) hT0'
  rcases le_total T T₀ with hle | hge
  · have hmono := integral_normSq_logPoly_mono a s hle
    linarith [hmono, hbound, hslope0]
  · have hmvt := integral_Icc_normSq_logPoly_le_energy a hs0 hsM hT1
    have hMT : (M : ℝ) ≤ ((M : ℝ) / T₀) * T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
      nlinarith [hM0, hge, hT0]
    have hstep : (5 * Real.pi / 2 * T + 5 * Real.exp 1 / 2 * (M : ℝ))
        ≤ (5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((M : ℝ) / T₀)) * T := by
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith [hMT, he]
    have hmul := mul_le_mul_of_nonneg_right hstep hE0
    linarith [hmvt, hmul, hβ0]

/-- **The three Gallagher terms, at a cut `Wc` with `δ·Wc ≤ 1`.**  Both surviving quantities are
the affine majorant's slope over the cut and its constant over the cut squared. -/
theorem joint_spectral_terms_le {Wc α β₀ δ : ℝ} (hWc : 0 < Wc) (hδ : 0 ≤ δ)
    (hδle : δ * Wc ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β₀) :
    2 * δ ^ 2 * (α * Wc + β₀)
        + (4 * α / (Real.pi ^ 2 * Wc) + 4 * β₀ / (3 * Real.pi ^ 2 * Wc ^ 2))
      ≤ 3 * α / Wc + 3 * β₀ / Wc ^ 2 := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hp9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [hpi3]
  set t : ℝ := 1 / Wc with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have hWt : Wc * t = 1 := by rw [ht]; field_simp
  have hδt : δ ≤ t := by
    rw [ht, le_div_iff₀ hWc]
    linarith [hδle]
  have e1 : 3 * α / Wc = 3 * (α * t) := by rw [ht]; ring
  have e2 : 3 * β₀ / Wc ^ 2 = 3 * (β₀ * t ^ 2) := by
    rw [ht, div_pow]
    field_simp
  have e3 : 4 * α / (Real.pi ^ 2 * Wc) = 4 * α * t / Real.pi ^ 2 := by
    rw [ht]
    field_simp
  have e4 : 4 * β₀ / (3 * Real.pi ^ 2 * Wc ^ 2) = 4 * β₀ * t ^ 2 / (3 * Real.pi ^ 2) := by
    rw [ht, div_pow]
    field_simp
  rw [e1, e2, e3, e4]
  have hδ2 : δ ^ 2 ≤ t ^ 2 := by nlinarith [hδ, hδt, ht0]
  have hone : 2 * δ ^ 2 * (α * Wc + β₀) ≤ 2 * α * t + 2 * β₀ * t ^ 2 := by
    have hnn : (0 : ℝ) ≤ α * Wc + β₀ := by positivity
    have hstep : 2 * δ ^ 2 * (α * Wc + β₀) ≤ 2 * t ^ 2 * (α * Wc + β₀) := by nlinarith [hδ2, hnn]
    have hval : 2 * t ^ 2 * (α * Wc + β₀) = 2 * α * (Wc * t) * t + 2 * β₀ * t ^ 2 := by ring
    rw [hval, hWt] at hstep
    linarith [hstep]
  have hthree : 4 * α * t / Real.pi ^ 2 ≤ 4 * α * t / 9 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hp9
  have hfour : 4 * β₀ * t ^ 2 / (3 * Real.pi ^ 2) ≤ 4 * β₀ * t ^ 2 / 27 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith [hp9])
  have hat : (0 : ℝ) ≤ α * t := mul_nonneg hα ht0.le
  have hbt : (0 : ℝ) ≤ β₀ * t ^ 2 := by positivity
  linarith [hone, hthree, hfour, hat, hbt]

end

end RHTower.Sieve
