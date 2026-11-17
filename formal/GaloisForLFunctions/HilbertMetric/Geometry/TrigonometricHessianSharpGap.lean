import GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessianSeed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact spectral gap of the periodic Hessian

Completing two squares sharpens the nonvanishing mechanism of the
Ando–Umehara seed: its squared eigenvalue gap has minimum `127/256`.
The minimizing sine squares have sum one and squared sum `193/256`.
Explicit inverse-trigonometric coordinates attain the minimum.
-/

namespace GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessian
open Real
noncomputable section

/-- The trace-free Hessian norm admits an exact sum-of-squares certificate. -/
theorem squared_gap_decomposition (x y : ℝ) :
    anisotropy x y ^ 2 + shear x y ^ 2 =
      127 / 256 + 2 * (sin x ^ 2 + sin y ^ 2 - 1) ^ 2 +
        256 * (sin x ^ 4 + sin y ^ 4 - 193 / 256) ^ 2 := by
  have hx : cos x ^ 2 = 1 - sin x ^ 2 := by linarith only [sin_sq_add_cos_sq x]
  have hy : cos y ^ 2 = 1 - sin y ^ 2 := by linarith only [sin_sq_add_cos_sq y]
  have hs : shear x y ^ 2 = 4 * (cos x ^ 2 * cos y ^ 2) := by unfold shear; ring
  rw [hs, hx, hy]
  unfold anisotropy
  ring

/-- The exact global lower bound, proved without a minimizing-point assumption. -/
theorem squared_gap_sharp_lower_bound (x y : ℝ) :
    (127 / 256 : ℝ) ≤ anisotropy x y ^ 2 + shear x y ^ 2 := by
  rw [squared_gap_decomposition]
  nlinarith only [sq_nonneg (sin x ^ 2 + sin y ^ 2 - 1),
    sq_nonneg (sin x ^ 4 + sin y ^ 4 - 193 / 256)]

/-- Equality is determined by two elementary symmetric conditions on sine squares. -/
theorem squared_gap_minimizer_iff (x y : ℝ) :
    anisotropy x y ^ 2 + shear x y ^ 2 = 127 / 256 ↔
      sin x ^ 2 + sin y ^ 2 = 1 ∧ sin x ^ 4 + sin y ^ 4 = 193 / 256 := by
  rw [squared_gap_decomposition]
  constructor
  · intro h
    have hs : (sin x ^ 2 + sin y ^ 2 - 1) ^ 2 = 0 := by
      nlinarith only [h, sq_nonneg (sin x ^ 4 + sin y ^ 4 - 193 / 256),
        sq_nonneg (sin x ^ 2 + sin y ^ 2 - 1)]
    have hr : (sin x ^ 4 + sin y ^ 4 - 193 / 256) ^ 2 = 0 := by
      nlinarith only [h, sq_nonneg (sin x ^ 2 + sin y ^ 2 - 1),
        sq_nonneg (sin x ^ 4 + sin y ^ 4 - 193 / 256)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hs), sub_eq_zero.mp (sq_eq_zero_iff.mp hr)⟩
  · rintro ⟨hs, hr⟩
    rw [hs, hr]
    ring

private theorem sin_sq_arcsin_sqrt {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    sin (arcsin (sqrt u)) ^ 2 = u := by
  rw [sin_arcsin (by linarith only [sqrt_nonneg u]) (sqrt_le_one.mpr hu1), sq_sqrt hu]

/-- An explicit point realizing the least possible squared eigenvalue gap. -/
theorem squared_gap_attained :
    ∃ x y : ℝ, anisotropy x y ^ 2 + shear x y ^ 2 = 127 / 256 := by
  let r : ℝ := sqrt (65 / 128)
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hr1 : r ≤ 1 := sqrt_le_one.mpr (by norm_num)
  have hrsq : r ^ 2 = 65 / 128 := sq_sqrt (by norm_num)
  let u := (1 + r) / 2
  let v := (1 - r) / 2
  have hu0 : 0 ≤ u := by dsimp [u]; linarith only [hr0]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith only [hr1]
  have hv0 : 0 ≤ v := by dsimp [v]; linarith only [hr1]
  have hv1 : v ≤ 1 := by dsimp [v]; linarith only [hr0]
  refine ⟨arcsin (sqrt u), arcsin (sqrt v), (squared_gap_minimizer_iff _ _).mpr ?_⟩
  have hx := sin_sq_arcsin_sqrt hu0 hu1
  have hy := sin_sq_arcsin_sqrt hv0 hv1
  constructor
  · rw [hx, hy]
    dsimp [u, v]
    ring
  · have hx4 : sin (arcsin (sqrt u)) ^ 4 = u ^ 2 := by nlinarith only [hx]
    have hy4 : sin (arcsin (sqrt v)) ^ 4 = v ^ 2 := by nlinarith only [hy]
    rw [hx4, hy4]
    dsimp [u, v]
    nlinarith only [hrsq]

/-- No larger uniform constant can bound this Hessian's squared gap below. -/
theorem squared_gap_uniform_bound_iff (c : ℝ) :
    (∀ x y, c ≤ anisotropy x y ^ 2 + shear x y ^ 2) ↔ c ≤ 127 / 256 := by
  constructor
  · intro hc
    obtain ⟨x, y, hxy⟩ := squared_gap_attained
    simpa only [hxy] using hc x y
  · intro hc x y
    exact hc.trans (squared_gap_sharp_lower_bound x y)

/-- The sharp seed constant gives a quantitative perturbation margin. -/
theorem perturbed_gap_sharp_lower_bound (x y u v : ℝ) :
    (127 / 512 : ℝ) - (u ^ 2 + v ^ 2) ≤
      (anisotropy x y + u) ^ 2 + (shear x y + v) ^ 2 := by
  nlinarith only [squared_gap_sharp_lower_bound x y,
    sq_nonneg (anisotropy x y + 2 * u), sq_nonneg (shear x y + 2 * v)]

#print axioms squared_gap_decomposition
#print axioms squared_gap_minimizer_iff
#print axioms squared_gap_attained
#print axioms squared_gap_uniform_bound_iff
#print axioms perturbed_gap_sharp_lower_bound
end
end GaloisForLFunctions.HilbertMetric.Geometry.TrigonometricHessian
