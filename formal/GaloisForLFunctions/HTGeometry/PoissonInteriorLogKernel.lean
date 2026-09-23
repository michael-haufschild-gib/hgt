import Mathlib

/-!
# The Poisson average of a logarithmic pole inside the disc

Mathlib computes the Poisson average of `log ‖· − ρ‖` over the circle of radius `R` for `ρ` on
that circle.  For the Poisson–Jensen formula one needs the same average for `ρ` anywhere in the
closed disc, where the answer acquires the Blaschke correction

`(R² − conj(ρ − c)(z − c)) / R`,

a function which is analytic and nowhere zero on a neighbourhood of the closed disc and whose
modulus on the boundary circle is exactly `‖z − ρ‖`.  Its logarithm is therefore the harmonic
majorant of `log ‖· − ρ‖`, and the Poisson formula for harmonic functions evaluates the average.
-/

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real InnerProductSpace

/-- The Blaschke-type harmonic majorant attached to an interior point. -/
noncomputable def innerLogKernel (c ρ : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (ρ - c) * (z - c)) / (R : ℂ)

theorem innerLogKernel_ne_zero {c ρ z : ℂ} {R : ℝ} (hR : 0 < R)
    (h : ‖ρ - c‖ * ‖z - c‖ < R ^ (2 : ℕ)) :
    innerLogKernel c ρ R z ≠ 0 := by
  unfold innerLogKernel
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  refine div_ne_zero (fun hzero => ?_) hRne
  have hEq : ((R : ℂ)) ^ (2 : ℕ) = (starRingEnd ℂ) (ρ - c) * (z - c) := by linear_combination hzero
  have hnorm : ‖((R : ℂ)) ^ (2 : ℕ)‖ = ‖(starRingEnd ℂ) (ρ - c)‖ * ‖z - c‖ := by
    rw [hEq, norm_mul]
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, RCLike.norm_conj] at hnorm
  linarith

theorem norm_innerLogKernel_sphere {c ρ : ℂ} {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ sphere c R) :
    ‖innerLogKernel c ρ R z‖ = ‖z - ρ‖ := by
  have hzc : ‖z - c‖ = R := by
    rw [mem_sphere_iff_norm] at hz
    exact hz
  have hsq : (z - c) * (starRingEnd ℂ) (z - c) = ((R : ℂ)) ^ (2 : ℕ) := by
    have hns : Complex.normSq (z - c) = R ^ (2 : ℕ) := by
      rw [Complex.normSq_eq_norm_sq, hzc]
    rw [Complex.mul_conj, hns]
    push_cast
    ring
  have hfac : (R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (ρ - c) * (z - c)
      = (z - c) * (starRingEnd ℂ) (z - ρ) := by
    have hexp : (starRingEnd ℂ) (z - ρ)
        = (starRingEnd ℂ) (z - c) - (starRingEnd ℂ) (ρ - c) := by
      rw [← map_sub]
      congr 1
      ring
    rw [hexp]
    linear_combination -hsq
  rw [innerLogKernel, hfac, norm_div, norm_mul, RCLike.norm_conj, hzc, Complex.norm_real,
    Real.norm_of_nonneg hR.le]
  field_simp

/-- **Poisson formula for an interior logarithmic pole.**  The Poisson average of
`log ‖· − ρ‖` over the circle, for `ρ` inside the disc, is the value of the Blaschke-corrected
harmonic majorant. -/
theorem circleAverage_re_herglotzRieszKernel_mul_log_of_mem_ball
    {ρ w c : ℂ} {R : ℝ} (hρ : ρ ∈ ball c R) (hw : w ∈ ball c R) :
    Real.circleAverage ((Complex.re ∘ herglotzRieszKernel c w) •
        (fun z => Real.log ‖z - ρ‖)) c R
      = Real.log ‖innerLogKernel c ρ R w‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hρnorm : ‖ρ - c‖ < R := by
    rw [mem_ball_iff_norm] at hρ
    exact hρ
  have hharm : HarmonicOnNhd (fun z => Real.log ‖innerLogKernel c ρ R z‖) (closedBall c R) := by
    intro x hx
    refine AnalyticAt.harmonicAt_log_norm ?_ ?_
    · unfold innerLogKernel
      fun_prop
    · refine innerLogKernel_ne_zero hR ?_
      have hxc : ‖x - c‖ ≤ R := by
        rw [mem_closedBall_iff_norm] at hx
        exact hx
      nlinarith [norm_nonneg (ρ - c), norm_nonneg (x - c)]
  have hval := HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul hharm hw
  rw [← hval]
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hR] at hz
  simp only [Pi.smul_apply', Function.comp_apply, smul_eq_mul]
  rw [norm_innerLogKernel_sphere hR hz]

end GaloisForLFunctions.HTGeometry.PoissonJensen

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real InnerProductSpace

theorem norm_innerLogKernel_of_mem_sphere {c ρ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ : ρ ∈ sphere c R) :
    ‖innerLogKernel c ρ R w‖ = ‖w - ρ‖ := by
  have hρc : ‖ρ - c‖ = R := by
    rw [mem_sphere_iff_norm] at hρ
    exact hρ
  have hsq : (ρ - c) * (starRingEnd ℂ) (ρ - c) = ((R : ℂ)) ^ (2 : ℕ) := by
    have hns : Complex.normSq (ρ - c) = R ^ (2 : ℕ) := by
      rw [Complex.normSq_eq_norm_sq, hρc]
    rw [Complex.mul_conj, hns]
    push_cast
    ring
  have hfac : (R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) (ρ - c) * (w - c)
      = (starRingEnd ℂ) (ρ - c) * (ρ - w) := by
    linear_combination -hsq
  rw [innerLogKernel, hfac, norm_div, norm_mul, RCLike.norm_conj, hρc, Complex.norm_real,
    Real.norm_of_nonneg hR.le, norm_sub_rev ρ w]
  field_simp

/-- **Poisson formula for a logarithmic pole anywhere in the closed disc.**  For every `ρ` in the
closed disc the Poisson average of `log ‖· − ρ‖` is the logarithm of the Blaschke-corrected
kernel. -/
theorem circleAverage_re_herglotzRieszKernel_mul_log_of_mem_closedBall
    {ρ w c : ℂ} {R : ℝ} (hρ : ρ ∈ closedBall c R) (hw : w ∈ ball c R) :
    Real.circleAverage ((Complex.re ∘ herglotzRieszKernel c w) •
        (fun z => Real.log ‖z - ρ‖)) c R
      = Real.log ‖innerLogKernel c ρ R w‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rcases lt_or_eq_of_le (mem_closedBall_iff_norm.mp hρ) with hlt | heq
  · exact circleAverage_re_herglotzRieszKernel_mul_log_of_mem_ball
      (mem_ball_iff_norm.mpr hlt) hw
  · have hsph : ρ ∈ sphere c R := mem_sphere_iff_norm.mpr heq
    rw [norm_innerLogKernel_of_mem_sphere hR hsph]
    have := circleAverage_re_herglotzRieszKernel_mul_log (w := w) (ρ := ρ) (c := c) (R := R)
      hsph hw
    rw [← this]
    apply Real.circleAverage_congr_sphere
    intro z _
    rfl

end GaloisForLFunctions.HTGeometry.PoissonJensen
