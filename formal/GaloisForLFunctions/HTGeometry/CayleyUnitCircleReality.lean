import GaloisForLFunctions.CayleySchur

/-!
# Cayley unit-circle reality bridge

The Cayley transform `(z-i)/(z+i)` lies on the unit circle exactly when `z` is real.  This is the
pointwise terminal bridge needed to turn a unit-circle root theorem, such as paraorthogonal OPUC
root location, into a real-root theorem on the line.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- Complex Cayley transform from the real line to the multiplicative unit circle. -/
noncomputable def lineCayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- Exact reality criterion: the Cayley image has norm one precisely on the real axis. -/
theorem norm_lineCayley_eq_one_iff_im_eq_zero (z : ℂ) :
    ‖lineCayley z‖ = 1 ↔ z.im = 0 := by
  constructor
  · intro hnorm
    have hden : z + I ≠ 0 := by
      intro hzero
      have hc : lineCayley z = 0 := by simp [lineCayley, hzero]
      rw [hc, norm_zero] at hnorm
      norm_num at hnorm
    have heq : ‖z - I‖ = ‖z + I‖ := by
      rw [lineCayley, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)] at hnorm
      exact hnorm
    have hsq : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 :=
      congrArg (fun x : ℝ => x ^ 2) heq
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im] at hsq
    nlinarith
  · intro him
    have hden : z + I ≠ 0 := by
      intro hzero
      have hzeroim := congrArg Complex.im hzero
      simp only [Complex.add_im, Complex.I_im, Complex.zero_im, him] at hzeroim
      norm_num at hzeroim
    have hsq : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.I_re, Complex.I_im, him]
      ring
    have heq : ‖z - I‖ = ‖z + I‖ := by
      nlinarith [norm_nonneg (z - I), norm_nonneg (z + I)]
    rw [lineCayley, norm_div, heq, div_self (norm_ne_zero_iff.mpr hden)]

/-- Set-valued form of the same reality criterion. -/
theorem lineCayley_mem_unitCircle_iff_real (z : ℂ) :
    lineCayley z ∈ Metric.sphere (0 : ℂ) 1 ↔ z.im = 0 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_lineCayley_eq_one_iff_im_eq_zero]

end GaloisForLFunctions.HTGeometry
