import GaloisForLFunctions.RHTower.PrimeMultWindowCoefficientBound

/-!
# Chebyshev's inequality for the fixed-length window

The second moment of `ψ(x+y) − ψ(x) − y` on `[X, 2X]`, supplied by
`integral_sq_fixedIncr_psi_bound`, controls the measure of the set where that quantity is large.
This is the last step of Guth–Maynard's Corollary 1.4 in the fixed-length normalisation: the
exceptional set is small as soon as the second moment is.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory intervalIntegral

noncomputable section

/-- **Chebyshev's inequality on an interval.**  The measure of the set where `|f|` exceeds `r` is at
most the second moment of `f` divided by `r²`. -/
theorem volume_lt_abs_le_integral_sq {f : ℝ → ℝ} {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hf : IntervalIntegrable (fun x => (f x) ^ 2) volume a b) :
    (volume {x : ℝ | x ∈ Set.Icc a b ∧ r < |f x|}).toReal
      ≤ (∫ x in a..b, (f x) ^ 2) / r ^ 2 := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hsub : {x : ℝ | x ∈ Set.Icc a b ∧ r < |f x|}
      ⊆ {x : ℝ | r ^ 2 ≤ (f x) ^ 2} ∩ Set.Icc a b := by
    rintro x ⟨hx, hlt⟩
    refine ⟨?_, hx⟩
    have h1 : r ^ 2 ≤ |f x| ^ 2 := by nlinarith [abs_nonneg (f x)]
    rwa [sq_abs] at h1
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] fun x => (f x) ^ 2 := by
    filter_upwards with x
    exact sq_nonneg _
  have hgint : Integrable (fun x => (f x) ^ 2) (volume.restrict (Set.Icc a b)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf
    exact hf
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hg0 hgint (r ^ 2)
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Icc] at hmarkov
  have hint_eq : ∫ x, (f x) ^ 2 ∂(volume.restrict (Set.Icc a b)) = ∫ x in a..b, (f x) ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [hint_eq] at hmarkov
  have hfin : (volume ({x : ℝ | r ^ 2 ≤ (f x) ^ 2} ∩ Set.Icc a b)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmono : (volume {x : ℝ | x ∈ Set.Icc a b ∧ r < |f x|}).toReal
      ≤ (volume ({x : ℝ | r ^ 2 ≤ (f x) ^ 2} ∩ Set.Icc a b)).toReal :=
    ENNReal.toReal_mono hfin (measure_mono hsub)
  refine hmono.trans ?_
  rw [le_div_iff₀ hr2]
  linarith [hmarkov]

/-- **The exceptional set for a window of fixed length.**  If the second moment of
`ψ(x+y) − ψ(x) − y` on `[X, 2X]` is at most `S`, then the set of `x` in that range where the
discrepancy exceeds `r` has measure at most `S / r²`. -/
theorem volume_fixedIncr_psi_gt_le {X y r S : ℝ} (hX : 0 < X) (hy : 0 ≤ y) (hr : 0 < r)
    (hS : ∫ x in X..(2 * X), (fixedIncr Chebyshev.psi y x) ^ 2 ≤ S) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ r < |Chebyshev.psi (x + y) - Chebyshev.psi x - y|}).toReal ≤ S / r ^ 2 := by
  have hX2 : X ≤ 2 * X := by linarith
  have hf : IntervalIntegrable (fun x => (fixedIncr Chebyshev.psi y x) ^ 2) volume X (2 * X) :=
    intervalIntegrable_sq_fixedIncr_psi hy hX.le hX2
  have hset : {x : ℝ | x ∈ Set.Icc X (2 * X)
      ∧ r < |Chebyshev.psi (x + y) - Chebyshev.psi x - y|}
      = {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ r < |fixedIncr Chebyshev.psi y x|} := rfl
  rw [hset]
  refine (volume_lt_abs_le_integral_sq hX2 hr hf).trans ?_
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  exact div_le_div_of_nonneg_right hS hr2.le |>.trans_eq rfl

end

end RHTower
