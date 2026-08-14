import GaloisForLFunctions.RHTower.PoissonAbelUniformBound
import GaloisForLFunctions.RHTower.PoissonMuntzRadialSource
import GaloisForLFunctions.HTGeometry.FiniteRegularityWienerFamily

/-!
# The Abel limit commutes with the radial primitive

The Abel-regularized radial sum converges pointwise to the radial source, and — by Poisson-kernel
positivity — the family is bounded uniformly in the Abel radius.  On a compact range of apertures
that bound is a constant, so dominated convergence moves the Abel limit through the growing
half-line primitive.

This is the interchange the transport of the primitive bound needs: any bound on the
Abel-regularized primitives, uniform in the radius, descends to the radial source itself.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral Filter Topology
open scoped FourierTransform

namespace RHTower

/-- The Fourier integral is bounded by the source's total mass. -/
theorem norm_fourier_le_integral_norm {g : ℝ → ℂ} (w : ℝ) :
    ‖𝓕 g w‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) • g x‖ = ‖g x‖
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The Abel sum is continuous in the aperture. -/
theorem continuous_poissonMuntzAbelSum_aperture {f : ℝ → ℝ} (hf : Integrable f)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous fun b : ℝ => poissonMuntzAbelSum f b r := by
  have hgi : Integrable (fun x : ℝ => (f x : ℂ)) := hf.ofReal
  have hFc : Continuous (𝓕 (fun x : ℝ => (f x : ℂ))) :=
    GaloisForLFunctions.HTGeometry.continuous_fourier_of_integrable hgi
  set C : ℝ := ∫ x : ℝ, ‖(f x : ℂ)‖ with hC
  have hCnn : (0 : ℝ) ≤ C := integral_nonneg fun x => norm_nonneg _
  refine continuous_tsum (u := fun n : ℕ => r ^ (n + 1) * C) ?_ ?_ ?_
  · intro n
    exact continuous_const.mul (hFc.comp (continuous_id.mul continuous_const))
  · have hgeo : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    refine (hgeo.mul_left (r * C)).congr fun n => ?_
    rw [pow_succ]
    ring
  · intro n b
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral_norm _) (by positivity)

/-- A compactly supported even source vanishes past a nonnegative radius, in absolute value. -/
theorem exists_vanishing_radius_abs {f : ℝ → ℝ} (heven : Function.Even f)
    (hcompact : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ, L < |y| → f y = 0 := by
  obtain ⟨L, hL0, hL⟩ := exists_vanishing_radius hcompact
  refine ⟨L, hL0, fun y hy => ?_⟩
  by_cases hy0 : 0 ≤ y
  · exact hL y (by rwa [abs_of_nonneg hy0] at hy)
  · have hy0' : y < 0 := not_le.mp hy0
    have hneg : L < -y := by rwa [abs_of_neg hy0'] at hy
    rw [← heven y]
    exact hL (-y) hneg

/-- **The interchange.**  The primitive of the Abel-regularized radial sum converges to the
primitive of the radial source. -/
theorem tendsto_intervalIntegral_sqrt_mul_poissonMuntzAbelSum
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f) (hcompact : HasCompactSupport f)
    {Cf : ℝ} (hbnd : ∀ y : ℝ, |f y| ≤ Cf) (hmean : ∫ x : ℝ, f x = 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hleb : ∀ b : ℝ, 0 < b → Tendsto (fun s : ℝ => (∫ u in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f b u - poissonMuntzAngularDatum f b 0| +
          |poissonMuntzAngularDatum f b (-u) - poissonMuntzAngularDatum f b 0|) / s)
      (𝓝[>] 0) (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun r : ℝ => ∫ s in (0 : ℝ)..t, Real.exp (s / 2) *
        ((Real.sqrt (lam * Real.exp s) : ℂ) *
          poissonMuntzAbelSum f (lam * Real.exp s) r).re)
      (𝓝[<] 1)
      (𝓝 (HTGeometry.halfLineExpPrimitive
        (HTGeometry.radialFullLogSource f lam) t)) := by
  obtain ⟨L, hL0, hvan⟩ := exists_vanishing_radius_abs heven hcompact
  have hCf : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hbnd 0)
  set D : ℝ := Real.exp (t / 2) *
    ((2 * (lam * Real.exp t) * L + 1) * Cf / (2 * Real.sqrt lam)) with hD
  have hDnn : (0 : ℝ) ≤ D := by
    have h1 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have h2 : (0 : ℝ) ≤ 2 * (lam * Real.exp t) * L + 1 := by positivity
    rw [hD]
    positivity
  have hev0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (0 : ℝ) < r :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num))
    have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := eventually_mem_nhdsWithin
    filter_upwards [h1, h2] with r hr1 hr2
    exact ⟨hr1.le, hr2⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => D) ?_ ?_ ?_ ?_
  · filter_upwards [hev0] with r hr
    refine Continuous.aestronglyMeasurable ?_
    refine (Real.continuous_exp.comp (continuous_id.div_const 2)).mul ?_
    refine Complex.continuous_re.comp ?_
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_const.mul Real.continuous_exp))
    · exact (continuous_poissonMuntzAbelSum_aperture hf hr.1 hr.2).comp
        (continuous_const.mul Real.continuous_exp)
  · filter_upwards [hev0] with r hr
    filter_upwards with s hs
    have hs0 : (0 : ℝ) ≤ s := by
      rw [Set.uIoc_of_le ht] at hs
      exact le_of_lt hs.1
    have hst : s ≤ t := by
      rw [Set.uIoc_of_le ht] at hs
      exact hs.2
    have ha : (0 : ℝ) < lam * Real.exp s := by positivity
    have hbase := norm_sqrt_mul_poissonMuntzAbelSum_le_of_bounded (L := L) (Cf := Cf)
      hf heven ha hL0 hvan hbnd hmean hr.1 hr.2
    have hre : |((Real.sqrt (lam * Real.exp s) : ℂ) *
        poissonMuntzAbelSum f (lam * Real.exp s) r).re|
        ≤ (2 * (lam * Real.exp s) * L + 1) * Cf / (2 * Real.sqrt (lam * Real.exp s)) :=
      le_trans (Complex.abs_re_le_norm _) hbase
    have hmono1 : (2 * (lam * Real.exp s) * L + 1) ≤ (2 * (lam * Real.exp t) * L + 1) := by
      have hexp : Real.exp s ≤ Real.exp t := Real.exp_le_exp.mpr hst
      have h1 : lam * Real.exp s ≤ lam * Real.exp t := mul_le_mul_of_nonneg_left hexp hlam.le
      have h2 : lam * Real.exp s * L ≤ lam * Real.exp t * L :=
        mul_le_mul_of_nonneg_right h1 hL0
      linarith
    have hmono2 : Real.sqrt lam ≤ Real.sqrt (lam * Real.exp s) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [Real.one_le_exp hs0, hlam.le]
    have hsl : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hquot : (2 * (lam * Real.exp s) * L + 1) * Cf / (2 * Real.sqrt (lam * Real.exp s))
        ≤ (2 * (lam * Real.exp t) * L + 1) * Cf / (2 * Real.sqrt lam) := by
      have hposnum : (0 : ℝ) ≤ 2 * (lam * Real.exp s) * L + 1 := by
        nlinarith [hL0, hlam.le, (Real.exp_pos s).le]
      have h3 : (0 : ℝ) ≤ (2 * (lam * Real.exp s) * L + 1) * Cf :=
        mul_nonneg hposnum hCf
      have h1 : (2 * (lam * Real.exp s) * L + 1) * Cf
          ≤ (2 * (lam * Real.exp t) * L + 1) * Cf := mul_le_mul_of_nonneg_right hmono1 hCf
      have h2 : 2 * Real.sqrt lam ≤ 2 * Real.sqrt (lam * Real.exp s) := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1, h2, h3, hsl.le]
    have hexps : Real.exp (s / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, hD]
    exact mul_le_mul hexps (le_trans hre hquot) (abs_nonneg _) (Real.exp_pos _).le
  · exact intervalIntegrable_const
  · filter_upwards with s _
    have ha : (0 : ℝ) < lam * Real.exp s := by positivity
    have hpt := tendsto_sqrt_mul_poissonMuntzAbelSum_eq_radialFullLogSource
      hf heven hcompact hlam hmean (hleb (lam * Real.exp s) ha)
    have hre := (Complex.continuous_re.tendsto _).comp hpt
    simp only [Function.comp_def, Complex.ofReal_re] at hre
    exact hre.const_mul (Real.exp (s / 2))

end RHTower
