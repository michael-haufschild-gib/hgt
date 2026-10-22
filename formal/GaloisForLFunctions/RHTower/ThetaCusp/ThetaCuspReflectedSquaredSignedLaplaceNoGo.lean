import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSquaredAtomicLaplaceNoGo
import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace
import GaloisForLFunctions.RHTower.LaplaceTransformMomentDerivative
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# No finite signed Laplace law for the reflected theta square profile

The atomic obstruction extends to arbitrary continuous signed carriers.  A finite measure on the
nonnegative half-line has a bounded complex Laplace transform on the closed right half-plane,
holomorphic in its interior.  Phragmen--Lindelof rigidity says that a superexponentially decaying
difference of two such transforms vanishes identically.  Laplace uniqueness then identifies the
two measures.

The reflected completed-theta product, viewed in squared displacement, decays faster than every
exponential but is strictly positive at the origin.  It therefore cannot be the Laplace transform
of any finite signed measure, with no discreteness, support-onset, or noncancellation assumption.
-/

open MeasureTheory Set Filter Topology Asymptotics Complex Bornology

namespace RHTower

noncomputable section

/-- Full complex Laplace transform of a finite measure. -/
def finiteComplexLaplace (tau : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ r : ℝ, Complex.exp (-z * (r : ℂ)) ∂tau

theorem integrable_finiteComplexLaplace_kernel
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (fun r : ℝ => Complex.exp (-z * (r : ℂ))) tau := by
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
  filter_upwards [hae] with r hr
  rw [GaloisForLFunctions.RHTower.norm_cexp_neg_mul]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hz hr])

/-- A finite half-line Laplace transform is bounded by total mass on the closed right half-plane. -/
theorem norm_finiteComplexLaplace_le
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖finiteComplexLaplace tau z‖ ≤ (tau Set.univ).toReal := by
  calc
    ‖finiteComplexLaplace tau z‖ ≤ 1 * tau.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
      filter_upwards [hae] with r hr
      rw [GaloisForLFunctions.RHTower.norm_cexp_neg_mul]
      exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hz hr])
    _ = (tau Set.univ).toReal := by rw [one_mul, measureReal_def]

/-- Boundary continuity of a finite half-line Laplace transform. -/
theorem continuousOn_finiteComplexLaplace_closedRightHalfPlane
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    ContinuousOn (finiteComplexLaplace tau) {z : ℂ | 0 ≤ z.re} := by
  intro z hz
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  unfold finiteComplexLaplace
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
  · filter_upwards with w
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with w hw
    filter_upwards [hae] with r hr
    rw [GaloisForLFunctions.RHTower.norm_cexp_neg_mul]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hw hr])
  · filter_upwards with r
    have hcont : Continuous (fun w : ℂ => Complex.exp (-w * (r : ℂ))) := by fun_prop
    exact (hcont.tendsto z).mono_left inf_le_left

/-- Interior holomorphy of a finite half-line Laplace transform. -/
theorem differentiableOn_finiteComplexLaplace_openRightHalfPlane
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    DifferentiableOn ℂ (finiteComplexLaplace tau) {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  set epsilon : ℝ := z.re / 2 with hepsilon
  have hepsilon0 : 0 < epsilon := by rw [hepsilon]; linarith
  have hlow : 0 < z.re - epsilon := by rw [hepsilon]; linarith
  have hbound : Integrable (fun _r : ℝ => (z.re - epsilon)⁻¹) tau := integrable_const _
  have hmeasF : ∀ᶠ x : ℂ in nhds z,
      AEStronglyMeasurable (fun r : ℝ => Complex.exp (-x * (r : ℂ))) tau := by
    filter_upwards with x
    fun_prop
  have hInt : Integrable (fun r : ℝ => Complex.exp (-z * (r : ℂ))) tau :=
    integrable_finiteComplexLaplace_kernel tau htau hz.le
  have hmeasF' : AEStronglyMeasurable
      (fun r : ℝ => -((r : ℂ) * Complex.exp (-z * (r : ℂ)))) tau := by
    fun_prop
  have hae : ∀ᵐ r ∂tau, r ∈ Ici (0 : ℝ) := ae_iff.mpr htau
  have hdom : ∀ᵐ (r : ℝ) ∂tau, ∀ x ∈ Metric.ball z epsilon,
      ‖-((r : ℂ) * Complex.exp (-x * (r : ℂ)))‖ ≤ (z.re - epsilon)⁻¹ := by
    filter_upwards [hae] with r hr x hx
    have hxre : z.re - epsilon < x.re := by
      have h1 : |x.re - z.re| ≤ ‖x - z‖ := by
        simpa using Complex.abs_re_le_norm (x - z)
      have h2 : ‖x - z‖ < epsilon := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hx
      have h3 : |x.re - z.re| < epsilon := lt_of_le_of_lt h1 h2
      linarith [abs_lt.mp h3 |>.1]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
      GaloisForLFunctions.RHTower.norm_cexp_neg_mul]
    have hsplit : r * Real.exp (-x.re * r) ≤
        r * Real.exp (-(z.re - epsilon) * r) := by
      gcongr
    exact hsplit.trans (GaloisForLFunctions.RHTower.mul_exp_neg_le hlow)
  have hderiv : ∀ᵐ (r : ℝ) ∂tau, ∀ x ∈ Metric.ball z epsilon,
      HasDerivAt (fun y : ℂ => Complex.exp (-y * (r : ℂ)))
        (-((r : ℂ) * Complex.exp (-x * (r : ℂ)))) x := by
    filter_upwards with r x _
    have h1 : HasDerivAt (fun y : ℂ => -y * (r : ℂ)) (-(r : ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℂ => (-(r : ℂ)) * y) ((-(r : ℂ)) * 1) x :=
        (hasDerivAt_id x).const_mul (-(r : ℂ))
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have h2 := h1.cexp
    refine h2.congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (r : ℝ) => Complex.exp (-x * (r : ℂ)))
    (F' := fun (x : ℂ) (r : ℝ) => -((r : ℂ) * Complex.exp (-x * (r : ℂ))))
    (bound := fun _r : ℝ => (z.re - epsilon)⁻¹)
    (Metric.ball_mem_nhds z hepsilon0) hmeasF hInt hmeasF' hdom hbound hderiv
  change DifferentiableWithinAt ℂ
    (fun x : ℂ => ∫ r : ℝ, Complex.exp (-x * (r : ℂ)) ∂tau)
    {z : ℂ | 0 < z.re} z
  exact hmain.2.differentiableAt.differentiableWithinAt

/-- A finite half-line Laplace transform is holomorphic inside and continuous on the boundary. -/
theorem diffContOnCl_finiteComplexLaplace
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    DiffContOnCl ℂ (finiteComplexLaplace tau) {z : ℂ | 0 < z.re} := by
  constructor
  · exact differentiableOn_finiteComplexLaplace_openRightHalfPlane tau htau
  · simpa only [closure_setOf_lt_re] using
      continuousOn_finiteComplexLaplace_closedRightHalfPlane tau htau

/-- A finite half-line Laplace transform has order-zero growth in the right half-plane. -/
theorem finiteComplexLaplace_rightHalfPlane_growth
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    ∃ c < (2 : ℝ), ∃ B,
      finiteComplexLaplace tau =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
  refine ⟨0, by norm_num, 0, ?_⟩
  rw [isBigO_iff]
  refine ⟨(tau Set.univ).toReal, ?_⟩
  refine eventually_inf_principal.2 <| Eventually.of_forall fun z hz => ?_
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact norm_finiteComplexLaplace_le tau htau hz.le

/-- A finite half-line Laplace transform is uniformly bounded on the imaginary axis. -/
theorem finiteComplexLaplace_imaginaryAxis_bounded
    (tau : Measure ℝ) [IsFiniteMeasure tau]
    (htau : tau (Ici (0 : ℝ))ᶜ = 0) :
    ∃ C, ∀ x : ℝ, ‖finiteComplexLaplace tau (x * Complex.I)‖ ≤ C := by
  refine ⟨(tau Set.univ).toReal, fun x => ?_⟩
  apply norm_finiteComplexLaplace_le tau htau
  simp

/-- A complex finite Laplace transform restricts to the real Bochner transform on the real ray. -/
theorem finiteComplexLaplace_ofReal
    (tau : Measure ℝ) (x : ℝ) :
    finiteComplexLaplace tau (x : ℂ) =
      (∫ r : ℝ, Real.exp (-x * r) ∂tau : ℂ) := by
  unfold finiteComplexLaplace
  apply integral_congr_ae
  filter_upwards with r
  have harg : -(x : ℂ) * (r : ℂ) = ((-x * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.ofReal_exp]

/-- **Signed Laplace rigidity.** A superexponentially cancelling difference of two finite
half-line Laplace transforms forces equality of the measures. -/
theorem finiteMeasures_eq_of_superexponential_laplace_difference
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu (Ici (0 : ℝ))ᶜ = 0) (hnu : nu (Ici (0 : ℝ))ᶜ = 0)
    (hdecay : SuperpolynomialDecay atTop Real.exp fun x : ℝ =>
      ‖finiteComplexLaplace mu (x : ℂ) - finiteComplexLaplace nu (x : ℂ)‖) :
    mu = nu := by
  have heq : EqOn (finiteComplexLaplace mu) (finiteComplexLaplace nu)
      {z : ℂ | 0 ≤ z.re} :=
    PhragmenLindelof.eqOn_right_half_plane_of_superexponential_decay
      (diffContOnCl_finiteComplexLaplace mu hmu)
      (diffContOnCl_finiteComplexLaplace nu hnu)
      (finiteComplexLaplace_rightHalfPlane_growth mu hmu)
      (finiteComplexLaplace_rightHalfPlane_growth nu hnu)
      hdecay
      (finiteComplexLaplace_imaginaryAxis_bounded mu hmu)
      (finiteComplexLaplace_imaginaryAxis_bounded nu hnu)
  apply GaloisForLFunctions.HTGeometry.measure_eq_of_laplace_eq hmu hnu
  intro x hx
  have hxmem : ((x : ℂ)).re ≥ 0 := by simpa using hx.le
  have hcx := heq hxmem
  rw [finiteComplexLaplace_ofReal, finiteComplexLaplace_ofReal] at hcx
  exact_mod_cast hcx

/-- No finite signed measure on the nonnegative half-line represents the reflected theta square
profile as a fixed Laplace transform. -/
theorem not_exists_finiteSignedLaplaceRepresentation_thetaCuspReflectedSquaredProduct
    (u : ℝ) :
    ¬ ∃ mu nu : Measure ℝ,
      IsFiniteMeasure mu ∧ IsFiniteMeasure nu ∧
      mu (Ici (0 : ℝ))ᶜ = 0 ∧ nu (Ici (0 : ℝ))ᶜ = 0 ∧
      ∀ x : ℝ, 0 ≤ x →
        (thetaCuspReflectedSourceProduct u (Real.sqrt x) : ℂ) =
          finiteComplexLaplace mu (x : ℂ) - finiteComplexLaplace nu (x : ℂ) := by
  rintro ⟨mu, nu, hmuFin, hnuFin, hmu, hnu, hrep⟩
  letI : IsFiniteMeasure mu := hmuFin
  letI : IsFiniteMeasure nu := hnuFin
  have hproduct_pos (x : ℝ) :
      0 < thetaCuspReflectedSourceProduct u (Real.sqrt x) := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hdecay : SuperpolynomialDecay atTop Real.exp fun x : ℝ =>
      ‖finiteComplexLaplace mu (x : ℂ) - finiteComplexLaplace nu (x : ℂ)‖ := by
    intro n
    have htheta := tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero
      u (a := (n : ℝ)) (by positivity)
    apply htheta.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← hrep x hx, norm_real, Real.norm_eq_abs, abs_of_pos (hproduct_pos x)]
    rw [← Real.exp_nat_mul]
  have hmunu := finiteMeasures_eq_of_superexponential_laplace_difference
    mu nu hmu hnu hdecay
  have hzero := hrep 0 le_rfl
  rw [hmunu, sub_self] at hzero
  have hne : (thetaCuspReflectedSourceProduct u 0 : ℂ) ≠ 0 := by
    exact_mod_cast (show 0 < thetaCuspReflectedSourceProduct u 0 by
      unfold thetaCuspReflectedSourceProduct
      exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)).ne'
  apply hne
  simpa using hzero

end

end RHTower
