import GaloisForLFunctions.HTGeometry.SmoothWeightMellin
import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion for the smooth cutoff

The cutoff is recovered from its Mellin transform by the vertical integral

`w(x) = (1/2π) ∫ x^{-(σ+iy)} W(σ+iy) dy`

on every line `Re s = σ > 0`.

The only nontrivial hypothesis of the inversion theorem is absolute convergence of the vertical
integral, and that is exactly what the second-order integration-by-parts bound supplies: on the
line `Re s = σ` the identity `‖s‖ ‖s+1‖ ‖W(s)‖ ≤ C` gives `‖W(σ+iy)‖ ≤ C/(σ²+y²)`, which is
integrable.
-/

open MeasureTheory Complex Set Filter Asymptotics
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- The cutoff, viewed as a complex-valued function, is continuous. -/
theorem continuous_smoothWeight_ofReal (N H : ℝ) :
    Continuous (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (smoothWeight_contDiff N H (n := 0)).continuous

/-- The cutoff vanishes near infinity, so it is `O(x^{-a})` there for every `a`. -/
theorem isBigO_atTop_smoothWeight {N H : ℝ} (hH : 0 < H) (a : ℝ) :
    (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  have hzero : (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (N + H)] with x hx
    rw [smoothWeight_eq_zero hH hx]
    simp
  exact hzero.trans_isBigO (isBigO_zero _ _)

/-- The cutoff is bounded, so it is `O(1)` at the origin. -/
theorem isBigO_zero_smoothWeight (N H : ℝ) :
    (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  refine isBigO_of_le _ fun x => ?_
  rw [neg_zero, Real.rpow_zero, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (smoothWeight_nonneg N H x)]
  exact smoothWeight_le_one N H x

/-- The Mellin transform of the cutoff is holomorphic on `Re s > 0`. -/
theorem differentiableAt_mellin_smoothWeight {N H : ℝ} (hH : 0 < H) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((continuous_smoothWeight_ofReal N H).locallyIntegrable.locallyIntegrableOn _)
    (isBigO_atTop_smoothWeight hH _) (by linarith) (isBigO_zero_smoothWeight N H) hs

/-- The Mellin transform of the cutoff is continuous along every line `Re s = σ > 0`. -/
theorem continuous_mellin_smoothWeight_line {N H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ) :
    Continuous
      (fun y : ℝ => mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((σ : ℂ) + (y : ℝ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
  have hd := differentiableAt_mellin_smoothWeight (N := N) hH
    (s := (σ : ℂ) + (y : ℝ) * I) (by rw [hre]; exact hσ)
  exact hd.continuousAt.comp (f := fun y : ℝ => (σ : ℂ) + (y : ℝ) * I)
    (Continuous.continuousAt (by fun_prop))

/-- **Quadratic decay along a vertical line.**  On `Re s = σ > 0` the transform is bounded by a
constant times `(1 + y²)⁻¹`; this is the second-order integration-by-parts bound rewritten in terms
of the real and imaginary parts. -/
theorem exists_bound_mellin_smoothWeight_line {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ}
    (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖
        ≤ C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_mellin_smoothWeight hN hH 1 σ
  set m : ℝ := min (σ ^ 2) 1 with hm
  have hm0 : 0 < m := by
    rw [hm]
    exact lt_min (by positivity) one_pos
  refine ⟨C / m, by positivity, fun y => ?_⟩
  set s : ℂ := (σ : ℂ) + (y : ℝ) * I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = y := by rw [hsdef]; simp
  have h := hbound s (by rw [hsre]; exact hσ) (by rw [hsre])
  rw [Finset.prod_range_one] at h
  simp only [Nat.cast_zero, add_zero] at h
  rw [mellin_smoothWeight_eq (N := N) (H := H) s]
  set W : ℝ := ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  -- `‖s‖ ≤ ‖s+1‖`, so `‖s‖ ‖s+1‖ ≥ ‖s‖² = σ² + y²`
  have hns : ‖s‖ ^ 2 = σ ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]; ring
  have hns1 : ‖s + 1‖ ^ 2 = (σ + 1) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, hsre, hsim]
    simp
    ring
  have hle : ‖s‖ ≤ ‖s + 1‖ := by
    nlinarith [norm_nonneg s, norm_nonneg (s + 1), hns, hns1, hσ]
  have hsq : σ ^ 2 + y ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    nlinarith [norm_nonneg s, hns, hle]
  have hXP : (σ ^ 2 + y ^ 2) * W ≤ C := by
    nlinarith [hW0, hsq, h, norm_nonneg s, norm_nonneg (s + 1)]
  have hkey : m * (1 + y ^ 2) ≤ σ ^ 2 + y ^ 2 := by
    have h1 : m ≤ σ ^ 2 := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg y]
  have hy1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hmain : W * (1 + y ^ 2) ≤ C / m := by
    rw [le_div_iff₀ hm0]
    calc W * (1 + y ^ 2) * m = W * (m * (1 + y ^ 2)) := by ring
      _ ≤ W * (σ ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_left hkey hW0
      _ ≤ C := by nlinarith [hXP]
  calc W = W * (1 + y ^ 2) * (1 + y ^ 2)⁻¹ := by field_simp
    _ ≤ C / m * (1 + y ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hmain (by positivity)

/-- **The vertical integral converges absolutely** on every line `Re s = σ > 0`. -/
theorem verticalIntegrable_mellin_smoothWeight {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ}
    (hσ : 0 < σ) :
    VerticalIntegrable (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) σ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_mellin_smoothWeight_line hN hH hσ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (continuous_mellin_smoothWeight_line hH hσ).aestronglyMeasurable ?_
  filter_upwards with y using hbound y

/-- **Mellin inversion for the cutoff.**  The cutoff is recovered from its Mellin transform by the
vertical integral on any line `Re s = σ > 0`. -/
theorem mellinInv_mellin_smoothWeight {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin (fun y : ℝ => ((smoothWeight N H y : ℝ) : ℂ))) x
      = ((smoothWeight N H x : ℝ) : ℂ) := by
  refine mellinInv_mellin_eq σ _ hx ?_ (verticalIntegrable_mellin_smoothWeight hN hH hσ)
    ((continuous_smoothWeight_ofReal N H).continuousAt)
  have hconv := integrableOn_mellin_smoothWeight (N := N) (H := H) hN.le hH
    (s := (σ : ℂ)) (by simpa using hσ)
  simpa [MellinConvergent, smul_eq_mul] using hconv

/-- **Uniform decay on horizontal segments.**  On the strip `0 < Re s ≤ σmax` the transform decays
faster than any power of `|Im s|`, uniformly in the real part: every factor `‖s+1+i‖` is at least
`|Im s|`, so the `j`-th integration-by-parts bound gives `|Im s|^{j+1} ‖W(s)‖ ≤ C`. -/
theorem exists_bound_mellin_smoothWeight_horizontal {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight hN hH j σmax
  refine ⟨C, hC, fun s hs hsmax => ?_⟩
  have h := hbd s hs hsmax
  rw [← mellin_smoothWeight_eq (N := N) (H := H) s] at h
  set X : ℝ := ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hprod : |s.im| ^ j ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    have hconst : |s.im| ^ j = ∏ _i ∈ Finset.range j, |s.im| := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hconst]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
    have him' : (s + 1 + (i : ℂ)).im = s.im := by simp
    calc |s.im| = |(s + 1 + (i : ℂ)).im| := by rw [him']
      _ ≤ ‖s + 1 + (i : ℂ)‖ := Complex.abs_im_le_norm _
  calc |s.im| ^ (j + 1) * X = (|s.im| * |s.im| ^ j) * X := by rw [pow_succ]; ring
    _ ≤ (‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) * X := by
        refine mul_le_mul_of_nonneg_right ?_ hX0
        exact mul_le_mul him hprod (by positivity) (norm_nonneg s)
    _ ≤ C := h

/-- **Arbitrarily fast polynomial decay along a vertical line.**  For every `m` the transform is
`O((1+y²)^{-m})` on the line `Re s = σ > 0`.  Taking `j = 2m` in the integration-by-parts bound and
using `‖s+1+i‖ ≥ ‖s‖` turns that bound into `‖s‖^{2m+1} ‖W(s)‖ ≤ C`, and `‖s‖² = σ²+y²` dominates
`min(σ²,1)(1+y²)`. -/
theorem exists_bound_mellin_smoothWeight_line_pow {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ}
    (hσ : 0 < σ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖
        ≤ C * ((1 + y ^ 2) ^ m)⁻¹ := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight hN hH (2 * m) σ
  set mm : ℝ := (min (σ ^ 2) 1) ^ m with hmm
  have hmin0 : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (by positivity) one_pos
  have hmm0 : (0 : ℝ) < mm := by rw [hmm]; positivity
  refine ⟨C / (σ * mm), by positivity, fun y => ?_⟩
  set s : ℂ := (σ : ℂ) + (y : ℝ) * I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = y := by rw [hsdef]; simp
  have h := hbd s (by rw [hsre]; exact hσ) (by rw [hsre])
  rw [mellin_smoothWeight_eq (N := N) (H := H) s]
  set A : ℝ := ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hnorm2 : ‖s‖ ^ 2 = σ ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]; ring
  have hσle : σ ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rwa [hsre, abs_of_pos hσ] at this
  have hprod : ‖s‖ ^ (2 * m) ≤ ∏ i ∈ Finset.range (2 * m), ‖s + 1 + (i : ℂ)‖ := by
    have hconst : ‖s‖ ^ (2 * m) = ∏ _i ∈ Finset.range (2 * m), ‖s‖ := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hconst]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    have hre : (s + 1 + (i : ℂ)).re = σ + 1 + (i : ℝ) := by
      simp [Complex.add_re, hsre]
    have him : (s + 1 + (i : ℂ)).im = y := by simp [hsim]
    have hsq : ‖s + 1 + (i : ℂ)‖ ^ 2 = (σ + 1 + (i : ℝ)) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    nlinarith [norm_nonneg s, norm_nonneg (s + 1 + (i : ℂ)), hnorm2, hsq,
      Nat.cast_nonneg (α := ℝ) i, hσ]
  set P : ℝ := ‖s‖ ^ (2 * m) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set Q : ℝ := (1 + y ^ 2) ^ m with hQ
  have hQ0 : (0 : ℝ) < Q := by rw [hQ]; positivity
  have hbase : min (σ ^ 2) 1 * (1 + y ^ 2) ≤ ‖s‖ ^ 2 := by
    have h1 : min (σ ^ 2) 1 ≤ σ ^ 2 := min_le_left _ _
    have h2 : min (σ ^ 2) 1 ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg y, hnorm2]
  have hmQ : mm * Q ≤ P := by
    rw [hmm, hQ, hP, ← mul_pow, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase m
  have hstep : (σ * mm * Q) * A ≤ C := by
    calc (σ * mm * Q) * A = (σ * (mm * Q)) * A := by ring
      _ ≤ (‖s‖ * P) * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA0
          exact mul_le_mul hσle hmQ (by positivity) (norm_nonneg s)
      _ ≤ C := by
          refine le_trans (mul_le_mul_of_nonneg_right ?_ hA0) h
          exact mul_le_mul_of_nonneg_left hprod (norm_nonneg s)
  have hAle : A ≤ C / (σ * mm * Q) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hstep]
  calc A ≤ C / (σ * mm * Q) := hAle
    _ = C / (σ * mm) * Q⁻¹ := by
        field_simp

end GaloisForLFunctions.HTGeometry
