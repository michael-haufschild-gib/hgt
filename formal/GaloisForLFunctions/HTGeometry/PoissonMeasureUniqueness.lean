import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection

/-!
# Uniqueness and comparison of Poisson measures on the disc

A finite measure on angles is determined, as a measure on the circle `ℝ/2πℤ`, by its Poisson integral
on the unit disc (`map_mk_eq_of_poissonIntegral_eq`).  Consequently, a pointwise inequality between
Poisson integrals with harmonic difference is an inequality between the measures
(`map_mk_le_of_poissonIntegral_le`).

The moments come from the Poisson formula for harmonic functions continuous up to the circle
(`integral_poissonIntegral_mul_harmonic`).  Against `h(e^{iφ})` the Poisson integral at radius `r`
integrates to `2π ∫ h(r e^{iθ}) dν`, by symmetry of the kernel in the two angles
(`poissonKernel_circleMap_symm`).  With `h = Re z^k`, `Im z^k` this gives the moments
`∫ e^{ikθ} dν` (`integral_exp_mul_eq_of_poissonIntegral_eq`).

Existence of the representing measure for a nonnegative harmonic function is
`exists_poissonRepresentation`.  Uniqueness and comparison let one read off the support of a
Herglotz measure from a sandwich `0 ≤ Re A ≤ Re B`.
-/

open Complex MeasureTheory Metric Real InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `‖e^{iθ} - r e^{iφ}‖ = ‖e^{iφ} - r e^{iθ}‖`. -/
theorem norm_circleMap_one_sub_circleMap_symm (r φ θ : ℝ) :
    ‖circleMap 0 1 θ - circleMap 0 r φ‖ = ‖circleMap 0 1 φ - circleMap 0 r θ‖ := by
  simp only [circleMap, zero_add, ofReal_one, one_mul]
  have h : cexp (θ * I) - r * cexp (φ * I) =
      cexp ((θ + φ : ℝ) * I) * (starRingEnd ℂ) (cexp (φ * I) - r * cexp (θ * I)) := by
    rw [map_sub, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_sub, ← Complex.exp_add, ← mul_assoc, mul_comm (cexp _) (r : ℂ), mul_assoc,
      ← Complex.exp_add]
    push_cast
    ring_nf
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]

/-- The unit-circle Poisson kernel is symmetric in the two angles. -/
theorem poissonKernel_circleMap_symm (r φ θ : ℝ) :
    poissonKernel 0 (circleMap 0 r φ) (circleMap 0 1 θ) =
      poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 φ) := by
  simp only [poissonKernel_def, sub_zero, norm_circleMap_zero]
  rw [norm_circleMap_one_sub_circleMap_symm]

theorem continuous_poissonKernel_circleMap_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Continuous fun p : ℝ × ℝ => poissonKernel 0 (circleMap 0 r p.1) (circleMap 0 1 p.2) := by
  simp only [poissonKernel_def, sub_zero, norm_circleMap_zero]
  refine continuous_const.div ((((continuous_circleMap 0 1).comp continuous_snd).sub
    ((continuous_circleMap 0 r).comp continuous_fst)).norm.pow 2) fun p => ?_
  have h1 := one_sub_norm_le_norm_circleMap_sub (circleMap 0 r p.1) p.2
  rw [norm_circleMap_zero, abs_of_nonneg hr0] at h1
  exact ne_of_gt (pow_pos (lt_of_lt_of_le (by linarith) h1) 2)

/-- **Moments of a Poisson measure.**  If `h` is harmonic on a neighbourhood of the closed unit disc,
continuous, and bounded by `M` on the unit circle, then for a finite measure `ν` on angles and `0 ≤ r < 1`,
`∫₀^{2π} P[ν](r e^{iφ}) h(e^{iφ}) dφ = 2π ∫ h(r e^{iθ}) dν(θ)`.

Swap the integrals, use the symmetry of the kernel in the two angles, and apply the Poisson
formula for `h` at the point `r e^{iθ}`. -/
theorem integral_poissonIntegral_mul_harmonic {ν : Measure ℝ} [IsFiniteMeasure ν] {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h (closedBall 0 1)) (hc : Continuous h) {M : ℝ}
    (hM : ∀ φ : ℝ, |h (circleMap 0 1 φ)| ≤ M) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ∫ φ in Set.Ioc 0 (2 * π), (∫ θ, poissonKernel 0 (circleMap 0 r φ) (circleMap 0 1 θ) ∂ν) *
        h (circleMap 0 1 φ) =
      2 * π * ∫ θ, h (circleMap 0 r θ) ∂ν := by
  set F : ℝ → ℝ → ℝ := fun φ θ =>
    poissonKernel 0 (circleMap 0 r φ) (circleMap 0 1 θ) * h (circleMap 0 1 φ) with hF
  have hK : ∀ φ θ : ℝ, 0 ≤ poissonKernel 0 (circleMap 0 r φ) (circleMap 0 1 θ) ∧
      poissonKernel 0 (circleMap 0 r φ) (circleMap 0 1 θ) ≤ (1 - r ^ 2) / (1 - r) ^ 2 := by
    intro φ θ
    have hn : ‖circleMap 0 r φ‖ = r := by rw [norm_circleMap_zero, abs_of_nonneg hr0]
    have hw : ‖circleMap 0 r φ‖ < 1 := by rw [hn]; exact hr
    refine ⟨poissonKernel_circleMap_one_nonneg hw θ, ?_⟩
    have := poissonKernel_circleMap_one_le hw θ
    rwa [hn] at this
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Set.Ioc 0 (2 * π))).prod ν) := by
    refine Integrable.of_bound ?_ ((1 - r ^ 2) / (1 - r) ^ 2 * M) (Filter.Eventually.of_forall
      fun p => ?_)
    · exact ((continuous_poissonKernel_circleMap_two hr0 hr).mul
        (hc.comp ((continuous_circleMap 0 1).comp continuous_fst))).aestronglyMeasurable
    · obtain ⟨h0, h1⟩ := hK p.1 p.2
      simp only [Function.uncurry, hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      exact mul_le_mul h1 (hM p.1) (abs_nonneg _) (le_trans h0 h1)
  have hswap := integral_integral_swap hint
  have hleft : ∫ φ in Set.Ioc 0 (2 * π), (∫ θ, poissonKernel 0 (circleMap 0 r φ)
      (circleMap 0 1 θ) ∂ν) * h (circleMap 0 1 φ) =
      ∫ φ in Set.Ioc 0 (2 * π), ∫ θ, F φ θ ∂ν := by
    refine setIntegral_congr_fun measurableSet_Ioc fun φ _ => ?_
    simp only [hF]
    rw [integral_mul_const]
  have hright : ∀ θ : ℝ, ∫ φ in Set.Ioc 0 (2 * π), F φ θ = 2 * π * h (circleMap 0 r θ) := by
    intro θ
    have hw : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
      exact hr
    have havg := hh.circleAverage_poissonKernel_smul hw
    rw [Real.circleAverage, intervalIntegral.integral_of_le (by positivity), smul_eq_mul] at havg
    have hsymm : ∫ φ in Set.Ioc 0 (2 * π), F φ θ =
        ∫ φ in Set.Ioc 0 (2 * π), (poissonKernel 0 (circleMap 0 r θ) • h) (circleMap 0 1 φ) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun φ _ => ?_
      simp only [hF, smul_eq_mul, Pi.mul_apply]
      rw [poissonKernel_circleMap_symm]
    rw [hsymm]
    have hπ : (2 * π)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    field_simp at havg
    linarith [havg]
  rw [hleft, hswap]
  simp_rw [hright]
  rw [integral_const_mul]

theorem harmonicOnNhd_re_pow (k : ℕ) : HarmonicOnNhd (fun z : ℂ => (z ^ k).re) (closedBall 0 1) :=
  fun _ _ => (analyticAt_id.pow k).harmonicAt_re

theorem harmonicOnNhd_im_pow (k : ℕ) : HarmonicOnNhd (fun z : ℂ => (z ^ k).im) (closedBall 0 1) :=
  fun _ _ => (analyticAt_id.pow k).harmonicAt_im

theorem circleMap_zero_pow (r θ : ℝ) (k : ℕ) :
    circleMap 0 r θ ^ k = (r : ℂ) ^ k * cexp (k * θ * I) := by
  simp only [circleMap, zero_add]
  rw [mul_pow, ← Complex.exp_nat_mul]
  ring_nf

/-- Equal Poisson integrals give equal moments `∫ e^{ikθ} dν` for `k ∈ ℕ`. -/
theorem integral_exp_mul_eq_of_poissonIntegral_eq {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂]
    (h : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν₁ =
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν₂) (k : ℕ) :
    ∫ θ, cexp (k * θ * I) ∂ν₁ = ∫ θ, cexp (k * θ * I) ∂ν₂ := by
  have hw : ∀ φ : ℝ, circleMap 0 (1 / 2) φ ∈ ball (0 : ℂ) 1 := by
    intro φ
    rw [mem_ball, dist_zero_right, norm_circleMap_zero]
    norm_num
  have hbd : ∀ (g : ℂ → ℝ), (∀ z : ℂ, |g z| ≤ ‖z ^ k‖) → ∀ φ : ℝ, |g (circleMap 0 1 φ)| ≤ 1 := by
    intro g hg φ
    refine (hg _).trans ?_
    rw [norm_pow, norm_circleMap_zero]
    simp
  have hre : ∀ z : ℂ, |(z ^ k).re| ≤ ‖z ^ k‖ := fun z => Complex.abs_re_le_norm _
  have him : ∀ z : ℂ, |(z ^ k).im| ≤ ‖z ^ k‖ := fun z => Complex.abs_im_le_norm _
  have key : ∀ (g : ℂ → ℝ), HarmonicOnNhd g (closedBall 0 1) → Continuous g →
      (∀ z : ℂ, |g z| ≤ ‖z ^ k‖) →
      ∫ θ, g (circleMap 0 (1 / 2) θ) ∂ν₁ = ∫ θ, g (circleMap 0 (1 / 2) θ) ∂ν₂ := by
    intro g hg hgc hgb
    have h1 := integral_poissonIntegral_mul_harmonic (ν := ν₁) hg hgc (hbd g hgb)
      (r := 1 / 2) (by norm_num) (by norm_num)
    have h2 := integral_poissonIntegral_mul_harmonic (ν := ν₂) hg hgc (hbd g hgb)
      (r := 1 / 2) (by norm_num) (by norm_num)
    have heq : ∫ φ in Set.Ioc 0 (2 * π), (∫ θ, poissonKernel 0 (circleMap 0 (1 / 2) φ)
        (circleMap 0 1 θ) ∂ν₁) * g (circleMap 0 1 φ) =
        ∫ φ in Set.Ioc 0 (2 * π), (∫ θ, poissonKernel 0 (circleMap 0 (1 / 2) φ)
        (circleMap 0 1 θ) ∂ν₂) * g (circleMap 0 1 φ) :=
      setIntegral_congr_fun measurableSet_Ioc fun φ _ => by rw [h _ (hw φ)]
    rw [h1, h2] at heq
    have hπ : (2 * π) ≠ 0 := by positivity
    exact mul_left_cancel₀ hπ heq
  have hR := key (fun z => (z ^ k).re) (harmonicOnNhd_re_pow k) (by fun_prop) hre
  have hI := key (fun z => (z ^ k).im) (harmonicOnNhd_im_pow k) (by fun_prop) him
  have hint : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable (fun θ : ℝ => cexp (k * θ * I)) μ := by
    intro μ _
    refine Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [show (k : ℂ) * θ * I = ((k * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hscale : ∀ θ : ℝ, circleMap 0 (1 / 2) θ ^ k = ((1 / 2 : ℝ) : ℂ) ^ k * cexp (k * θ * I) :=
    fun θ => circleMap_zero_pow _ _ _
  simp only [hscale] at hR hI
  apply Complex.ext
  · rw [show (∫ θ, cexp (k * θ * I) ∂ν₁).re = ∫ θ, (cexp (k * θ * I)).re ∂ν₁ from
      (integral_re (hint ν₁)).symm, show (∫ θ, cexp (k * θ * I) ∂ν₂).re =
      ∫ θ, (cexp (k * θ * I)).re ∂ν₂ from (integral_re (hint ν₂)).symm]
    have hc : (((1 / 2 : ℝ) : ℂ) ^ k).im = 0 := by norm_cast
    have e : ∀ θ : ℝ, (((1 / 2 : ℝ) : ℂ) ^ k * cexp (k * θ * I)).re =
        (1 / 2 : ℝ) ^ k * (cexp (k * θ * I)).re := by
      intro θ
      rw [Complex.mul_re, hc, zero_mul, sub_zero]
      norm_cast
    simp only [e] at hR
    rw [integral_const_mul, integral_const_mul] at hR
    exact mul_left_cancel₀ (by positivity) hR
  · rw [show (∫ θ, cexp (k * θ * I) ∂ν₁).im = ∫ θ, (cexp (k * θ * I)).im ∂ν₁ from
      (integral_im (hint ν₁)).symm, show (∫ θ, cexp (k * θ * I) ∂ν₂).im =
      ∫ θ, (cexp (k * θ * I)).im ∂ν₂ from (integral_im (hint ν₂)).symm]
    have hc : (((1 / 2 : ℝ) : ℂ) ^ k).im = 0 := by norm_cast
    have e : ∀ θ : ℝ, (((1 / 2 : ℝ) : ℂ) ^ k * cexp (k * θ * I)).im =
        (1 / 2 : ℝ) ^ k * (cexp (k * θ * I)).im := by
      intro θ
      rw [Complex.mul_im, hc, zero_mul, add_zero]
      norm_cast
    simp only [e] at hI
    rw [integral_const_mul, integral_const_mul] at hI
    exact mul_left_cancel₀ (by positivity) hI

local instance poissonCirclePositive : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- **Uniqueness of the Poisson measure.**  Two finite measures on angles with the same Poisson
integral on the unit disc have the same image on the circle `ℝ/2πℤ`.  Their moments `∫ e^{ikθ}`
agree for `k ≥ 0` by the moment identity, for `k < 0` by conjugation, and a finite measure on the
circle is determined by its Fourier coefficients. -/
theorem map_mk_eq_of_poissonIntegral_eq {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂]
    (h : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν₁ =
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν₂) :
    ν₁.map (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) =
      ν₂.map (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) := by
  refine addCircle_measure_eq_of_fourier_integral_eq _ _ fun n => ?_
  have hmeas : AEMeasurable (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) ν₁ :=
    AddCircle.measurable_mk'.aemeasurable
  have hmeas₂ : AEMeasurable (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) ν₂ :=
    AddCircle.measurable_mk'.aemeasurable
  rw [integral_map hmeas (fourier n).continuous.aestronglyMeasurable,
    integral_map hmeas₂ (fourier n).continuous.aestronglyMeasurable]
  have hf : ∀ θ : ℝ, fourier n ((θ : ℝ) : AddCircle (2 * π)) = cexp (n * θ * I) := by
    intro θ
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  simp only [hf]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast integral_exp_mul_eq_of_poissonIntegral_eq h k
  · have hc : ∀ θ : ℝ, cexp (((-(k : ℤ) : ℤ) : ℂ) * θ * I) =
        (starRingEnd ℂ) (cexp (k * θ * I)) := by
      intro θ
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast]
      push_cast
      ring
    simp only [hc]
    rw [integral_conj, integral_conj, integral_exp_mul_eq_of_poissonIntegral_eq h k]

/-- **Comparison of Poisson measures.**  If `P[μ] ≤ P[ν]` on the unit disc and the difference is
harmonic, then `μ ≤ ν` on the circle.  The difference is the Poisson integral of a positive
measure `ρ`, and uniqueness gives `μ + ρ = ν`. -/
theorem map_mk_le_of_poissonIntegral_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hharm : HarmonicOnNhd (fun w => (∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν) -
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂μ) (ball 0 1))
    (hle : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂μ ≤
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν) :
    μ.map (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) ≤
      ν.map (QuotientAddGroup.mk : ℝ → AddCircle (2 * π)) := by
  obtain ⟨ρ, hρfin, hρ⟩ := exists_poissonRepresentation hharm fun w hw => sub_nonneg.mpr (hle w hw)
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (w : ℂ), w ∈ ball (0 : ℂ) 1 →
      Integrable (fun θ => poissonKernel 0 w (circleMap 0 1 θ)) m := by
    intro m _ w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    exact Integrable.of_bound (continuous_poissonKernel_circleMap hw').aestronglyMeasurable
      ((1 - ‖w‖ ^ 2) / (1 - ‖w‖) ^ 2) (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (poissonKernel_circleMap_one_nonneg hw' θ)]
        exact poissonKernel_circleMap_one_le hw' θ)
  have hsum : ∀ w ∈ ball (0 : ℂ) 1, ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂(μ + ρ) =
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν := by
    intro w hw
    rw [integral_add_measure (hint μ w hw) (hint ρ w hw), hρ w hw]
    ring
  have heq := map_mk_eq_of_poissonIntegral_eq hsum
  rw [← heq, Measure.map_add _ _ AddCircle.measurable_mk']
  exact Measure.le_add_right le_rfl

end GaloisForLFunctions.HTGeometry
