import Mathlib

/-!
# Circle moments of functions analytic on the closed unit disk

The **circle moment** of a function `g : ℂ → ℂ` at integer index `j` is
`∫₀^{2π} (e^{iθ})^j g(e^{iθ}) dθ`, written here with the unit circle map
`circleMap 0 1 θ = e^{iθ}`.

For a function `g` analytic on the open unit disk and continuous on the closed
disk (`DiffContOnCl ℂ g (ball 0 1)`) two facts hold, and they are the common
analytic substrate of the F.&M. Riesz theorem, Szegő's theorem, and the
Bernstein–Szegő orthogonality relations:

* `circleMoment_succ_eq_zero` — the **positive-index moments vanish**
  (Cauchy's theorem: `∮ zᵐ g dz = 0`);
* `circleMoment_zero` — the **zeroth moment equals `2π·g(0)`**
  (the mean value property / Cauchy's integral formula at the centre).

Together they say that the boundary values of an analytic function have a
one-sided (nonnegative-frequency) Fourier spectrum whose constant term
reproduces the value at the origin.
-/

open Complex MeasureTheory intervalIntegral
open scoped Real

namespace ValueDistribution.CircleMoments

/-- The unit circle point `e^{iθ}` is never zero. -/
lemma circleMap_unit_ne_zero (θ : ℝ) : circleMap 0 1 θ ≠ 0 :=
  circleMap_ne_center (R := (1 : ℝ)) (c := (0 : ℂ)) one_ne_zero

/-- The circle moment `∫₀^{2π} (e^{iθ})^j g(e^{iθ}) dθ`. -/
noncomputable def circleMoment (g : ℂ → ℂ) (j : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 1 θ) ^ j * g (circleMap 0 1 θ)

/-- The contour integral `∮ zᵐ g dz` equals `I` times the `(m+1)`-st circle moment. -/
lemma circleIntegral_pow_mul_eq (g : ℂ → ℂ) (m : ℕ) :
    (∮ z in C(0, 1), (fun z => z ^ m * g z) z) = Complex.I * circleMoment g (m + 1) := by
  rw [circleIntegral, circleMoment, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [deriv_circleMap]
  have hzne : circleMap 0 1 θ ≠ 0 := circleMap_unit_ne_zero θ
  simp only [smul_eq_mul]
  rw [zpow_add_one₀ hzne, zpow_natCast]
  ring

/-- **Positive-index circle moments of an analytic function vanish.**  This is Cauchy's
theorem: the boundary spectrum of a function analytic on the closed disk is one-sided. -/
theorem circleMoment_succ_eq_zero (g : ℂ → ℂ) (hg : DiffContOnCl ℂ g (Metric.ball 0 1))
    (m : ℕ) : circleMoment g (m + 1) = 0 := by
  have hpm : DiffContOnCl ℂ (fun z => z ^ m * g z) (Metric.ball 0 1) :=
    ⟨DifferentiableOn.mul (by fun_prop) hg.differentiableOn,
      (Continuous.continuousOn (by fun_prop)).mul hg.continuousOn⟩
  have hcauchy : (∮ z in C(0, 1), (fun z => z ^ m * g z) z) = 0 :=
    hpm.circleIntegral_eq_zero (by norm_num)
  rw [circleIntegral_pow_mul_eq] at hcauchy
  simpa [Complex.I_ne_zero] using hcauchy

/-- **The zeroth circle moment reproduces `2π` times the value at the origin.**  This is the
mean value property / Cauchy's integral formula at the centre of the disk. -/
theorem circleMoment_zero (g : ℂ → ℂ) (hg : DiffContOnCl ℂ g (Metric.ball 0 1)) :
    circleMoment g 0 = 2 * Real.pi * g 0 := by
  have hcf : (∮ z in C(0, 1), (z - 0)⁻¹ • g z) = (2 * ↑Real.pi * Complex.I) • g 0 :=
    hg.circleIntegral_sub_inv_smul (by simp)
  have hred : (∮ z in C(0, 1), (z - 0)⁻¹ • g z) = Complex.I * circleMoment g 0 := by
    rw [circleIntegral, circleMoment, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [deriv_circleMap]
    have hzne : circleMap 0 1 θ ≠ 0 := circleMap_unit_ne_zero θ
    simp only [smul_eq_mul, sub_zero, zpow_zero, one_mul]
    calc circleMap 0 1 θ * Complex.I * ((circleMap 0 1 θ)⁻¹ * g (circleMap 0 1 θ))
        = Complex.I * (circleMap 0 1 θ * (circleMap 0 1 θ)⁻¹) * g (circleMap 0 1 θ) := by ring
      _ = Complex.I * 1 * g (circleMap 0 1 θ) := by rw [mul_inv_cancel₀ hzne]
      _ = Complex.I * g (circleMap 0 1 θ) := by ring
  rw [hred, smul_eq_mul] at hcf
  have hI : Complex.I * circleMoment g 0 = Complex.I * (2 * ↑Real.pi * g 0) := by
    rw [hcf]; ring
  exact mul_left_cancel₀ Complex.I_ne_zero hI

end ValueDistribution.CircleMoments
