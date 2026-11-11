import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ThePositiveCalibratedBlocksSurviveSplineSmoothing
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-!
# Spline weights and local counts of calibrated blocks

The squared cubic-spline transform makes each coefficient at ordinate at least `Γ/2`
smaller than `65536 exp(4)/Γ⁸`. Index separation gives at most `1+k/Γ`
ordinates in a unit interval. These are the mass and local-count bounds
needed to assemble the blocks into a tempered configuration.
-/

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.SquareRootThreshold Zeta23

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The squared cubic-spline coefficient has an explicit inverse-eighth-power bound. -/
theorem norm_calibrated_spline_coefficient_le {Γ : ℝ} (hΓ : 0 < Γ)
    {w : ℂ} (hw : |w.re| ≤ 1 / 2) (him : Γ / 2 ≤ w.im) :
    ‖sincC (-I * w) ^ 8‖ ≤ 65536 * Real.exp 4 / Γ ^ 8 := by
  have hwim : |(-I * w).im| ≤ 1 / 2 := by
    simpa only [Complex.mul_im, Complex.neg_re, Complex.I_re, neg_zero, zero_mul,
      Complex.neg_im, Complex.I_im, neg_one_mul, zero_add, abs_neg] using hw
  have hy : Γ / 2 ≤ ‖-I * w‖ := by
    have hh := Complex.abs_re_le_norm (-I * w)
    have he : (-I * w).re = w.im := by simp
    rw [he, abs_of_pos (by linarith only [hΓ, him] : 0 < w.im)] at hh
    exact him.trans hh
  have hh := norm_paperFT_boxSpline_le' 7 hwim (by positivity : 0 ≤ Γ / 2) hy
  rw [paperFT_boxSpline_eq] at hh
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hh
  have hden : Γ ^ 8 ≤ 256 * (1 + Γ / 2) ^ 8 := by
    have hp := pow_le_pow_left₀ hΓ.le (show Γ ≤ 2 * (1 + Γ / 2) by linarith) 8
    norm_num only [mul_pow] at hp
    exact hp
  have hden0 : 0 < (1 + Γ / 2) ^ 8 := by positivity
  have hΓ4 : 0 < Γ ^ 8 := by positivity
  have hmul := (le_div_iff₀ hden0).mp hh
  apply (le_div_iff₀ hΓ4).mpr
  calc
    _ ≤ ‖sincC (-I * w) ^ 8‖ * (256 * (1 + Γ / 2) ^ 8) :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = 256 * (‖sincC (-I * w) ^ 8‖ * (1 + Γ / 2) ^ 8) := by ring
    _ ≤ 256 * (256 * Real.exp 4) := mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = _ := by ring

/-- Twice the coefficient mass controls the real trace of a finite block. -/
def splineBlockWeight {ι : Type*} [Fintype ι] (w : ι → ℂ) : ℝ :=
  2 * ∑ j, ‖sincC (-I * w j) ^ 8‖

theorem splineBlockWeight_nonneg {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    0 ≤ splineBlockWeight w := by unfold splineBlockWeight; positivity

/-- A whole finite block obeys its coefficient mass times its maximal exponential growth. -/
theorem abs_two_re_splineExponentialBlock_le {ι : Type*} [Fintype ι]
    (w : ι → ℂ) {D t : ℝ} (ht : 0 ≤ t) (hw : ∀ j, (w j).re ≤ D) :
    |2 * (splineExponentialBlock w t).re| ≤ splineBlockWeight w * Real.exp (D * t) := by
  classical
  have hnorm : ‖splineExponentialBlock w t‖ ≤
      (∑ j, ‖sincC (-I * w j) ^ 8‖) * Real.exp (D * t) := by
    unfold splineExponentialBlock
    calc
      _ ≤ ∑ j, ‖sincC (-I * w j) ^ 8 * Complex.exp (w j * (t : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖sincC (-I * w j) ^ 8‖ * Real.exp (D * t) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_exp]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          using mul_le_mul_of_nonneg_right (hw j) ht
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := (Complex.abs_re_le_norm (splineExponentialBlock w t)).trans hnorm
  unfold splineBlockWeight
  nlinarith only [hh]

/-- High-frequency strip blocks have small total spline weight. -/
theorem splineBlockWeight_le {ι : Type*} [Fintype ι] {Γ : ℝ} (hΓ : 0 < Γ)
    (w : ι → ℂ) (hw : ∀ j, |(w j).re| ≤ 1 / 2) (him : ∀ j, Γ / 2 ≤ (w j).im) :
    splineBlockWeight w ≤ 131072 * Real.exp 4 * Fintype.card ι / Γ ^ 8 := by
  classical
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    norm_calibrated_spline_coefficient_le hΓ (hw j) (him j))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold splineBlockWeight
  calc
    _ ≤ 2 * ((Fintype.card ι : ℝ) * (65536 * Real.exp 4 / Γ ^ 8)) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Index-separated ordinates are distinct. -/
theorem ordinate_injective_of_index_separated {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {z : Fin (k + 1) → ℂ}
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |(z i).im - (z j).im|) :
    Function.Injective (fun i => (z i).im) := by
  intro i j he
  by_contra hij
  have hh := hsep i j
  rw [he, sub_self, abs_zero] at hh
  have hi := mul_le_mul_of_nonneg_right (one_le_abs_fin_index_sub hij) hδ.le
  linarith only [hh, hi, hδ]

/-- A unit window contains at most one plus the reciprocal spacing many ordinates. -/
theorem card_calibrated_ordinate_window_le {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin (k + 1) → ℂ)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |(z i).im - (z j).im|)
    (t : ℝ) :
    ((Finset.univ.filter (fun i => t < (z i).im ∧ (z i).im ≤ t + 1)).card : ℝ) ≤ 1 / δ + 1 := by
  classical
  let S := Finset.univ.filter (fun i => t < (z i).im ∧ (z i).im ≤ t + 1)
  let F := S.image (fun i => (z i).im)
  have hinj := ordinate_injective_of_index_separated hδ hsep
  have hcard : F.card = S.card := Finset.card_image_iff.mpr hinj.injOn
  have hh := card_le_of_separated_of_subset_Icc hδ (show t ≤ t + 1 by linarith) F
    (by
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hij : i ≠ j := fun he => hab (congrArg (fun i => (z i).im) he)
      have hbase : δ ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (one_le_abs_fin_index_sub hij) hδ.le
      exact hbase.trans (hsep i j))
    (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hh := (Finset.mem_filter.mp hi).2
      exact ⟨hh.1.le, hh.2⟩)
  rw [hcard] at hh
  simpa only [add_sub_cancel_left] using hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
