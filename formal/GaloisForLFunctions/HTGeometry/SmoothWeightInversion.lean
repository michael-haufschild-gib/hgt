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

end GaloisForLFunctions.HTGeometry
