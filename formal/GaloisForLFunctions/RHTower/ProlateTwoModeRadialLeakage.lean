import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination
import GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum
import GaloisForLFunctions.RHTower.ProlateCanonicalSeparationLimit
import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay
import GaloisForLFunctions.RHTower.RadialLeakageWeakConvergenceTransfer
import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# The constrained two-mode radial leakage law

A constrained source built from two prolate modes has exterior radial density
`(α P₀ + β P₁)²`, where `P₀`, `P₁` are the two endpoint-normalized radial profiles at the common
bandwidth and `α`, `β` are the mixing coefficients after normalizing by the dominant mode's exterior
leakage.  Each `Pₘ²` is the single-mode exterior density, whose tail masses converge to
`arcsin(1/b)/π`; the coefficient of the subordinate mode carries the ratio of the two leakages and
tends to zero.

Cauchy--Schwarz therefore removes the subordinate mode together with its cross term, and the tail
mass of the combination converges to `β₀²` times the single-mode value.  With the constrained
Connes--Consani--Moscovici seed weights the surviving squared coefficient is exactly `8/11`, so the
tail mass converges to `(8/(11π)) arcsin(1/b)`, the tail of the arcsine leakage measure.
-/

noncomputable section

open Filter MeasureTheory Set

open scoped Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-! ## Integrability of a single exterior density -/

/-- The exact exterior density of an endpoint-normalized radial profile is integrable on every
strict exterior tail beyond the Dunster crossing radius: it is dominated there by a fixed multiple
of the integrable profile weight. -/
theorem integrableOn_Ioi_radialProlateDensity
    {s c b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hb : 1 < b)
    (hcrossb : dunsterEndpointCrossing c ≤ b)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    IntegrableOn (radialProlateDensity c R) (Ioi b) := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous (radialProlateDensity c R) := by
    unfold radialProlateDensity
    fun_prop
  have hdom : IntegrableOn
      (fun x : ℝ => radialProlateDensityEnvelopeConstant * profileWeight s x) (Ioi b) :=
    (integrableOn_profileWeight hs0 hs1 hb).const_mul radialProlateDensityEnvelopeConstant
  refine Integrable.mono' hdom
    (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hnn : 0 ≤ radialProlateDensity c R x := by
    unfold radialProlateDensity
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact radialProlateDensity_le_profileWeight hs0 hs1 hc hR1 hR hDR hode (hcrossb.trans hx.le)

/-- Every canonical signed radial mode has an integrable exterior density on every strict exterior
tail, for all large apertures. -/
theorem eventually_integrableOn_Ioi_signedModeRadialDensity (n : ℕ) {b : ℝ} (hb : 1 < b) :
    ∀ᶠ a : ℝ in atTop, IntegrableOn
      (radialProlateDensity (signedModeRadialBandwidth a) (signedModeRadialData a n).R)
      (Ioi b) := by
  have hsHalf : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ 1 / 2 :=
    ((tendsto_signedModeRadialData_s_zero n).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hc5 : ∀ᶠ a : ℝ in atTop, 5 ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one
    tendsto_signedModeRadialBandwidth_atTop
  have hcrossb : ∀ᶠ a : ℝ in atTop,
      dunsterEndpointCrossing (signedModeRadialBandwidth a) ≤ b :=
    (hcross.eventually (eventually_lt_nhds hb)).mono fun _ h => h.le
  filter_upwards [eventually_signedModeRadialData_s_nonneg n, hsHalf, hc5, hcrossb,
    eventually_signedModeRadialData_R_one n,
    eventually_signedModeRadialData_hasDerivAt n,
    eventually_signedModeRadialData_hasSecondDerivAt n,
    eventually_signedModeRadialData_ode n] with
      a hs0 hs1 hc hcrossa hR1 hR hDR hode
  exact integrableOn_Ioi_radialProlateDensity hs0 hs1 hc hb hcrossa hR1 hR hDR hode

/-- The rescaled radial profile is continuous, hence measurable on every exterior tail. -/
theorem aestronglyMeasurable_signedModeRadialRescaledProfile (n : ℕ) (b : ℝ) :
    ∀ᶠ a : ℝ in atTop, AEStronglyMeasurable
      (radialProlateRescaledProfile (signedModeRadialBandwidth a) (signedModeRadialData a n).R)
      (volume.restrict (Ioi b)) := by
  filter_upwards [eventually_signedModeRadialData_hasDerivAt n] with a hR
  have hRc : Continuous (signedModeRadialData a n).R :=
    continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous
      (radialProlateRescaledProfile (signedModeRadialBandwidth a) (signedModeRadialData a n).R) := by
    unfold radialProlateRescaledProfile
    fun_prop
  exact hcont.aestronglyMeasurable

/-- The square of the rescaled profile is literally the exterior density. -/
theorem signedModeRadialRescaledProfile_sq (a : ℝ) (n : ℕ) (x : ℝ) :
    radialProlateRescaledProfile (signedModeRadialBandwidth a) (signedModeRadialData a n).R x ^ 2
      = radialProlateDensity (signedModeRadialBandwidth a) (signedModeRadialData a n).R x := by
  refine radialProlateRescaledProfile_sq_eq_density ?_
  unfold signedModeRadialBandwidth
  positivity

/-- Unconditional single-mode exterior tail mass in rescaled-profile form. -/
theorem tendsto_integral_Ioi_signedModeRadialRescaledProfile_sq (n : ℕ) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
        radialProlateRescaledProfile (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x ^ 2)
      atTop (𝓝 (Real.arcsin (1 / b) / Real.pi)) := by
  have h := tendsto_integral_Ioi_signedModeRadialDensity_unconditional n hb
  rw [_root_.RHTower.integral_Ioi_radialLeakageDensity hb.le] at h
  refine h.congr fun a => ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  exact (signedModeRadialRescaledProfile_sq a n x).symm

/-! ## The two-mode exterior density -/

/-- Exterior radial profile of a two-mode constrained source: the subordinate mode enters with
coefficient `α`, the dominant one with coefficient `β`. -/
def twoModeRadialProfile (α β c : ℝ) (R₀ R₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  α * radialProlateRescaledProfile c R₀ x + β * radialProlateRescaledProfile c R₁ x

/-- Exterior radial density of a two-mode constrained source. -/
def twoModeRadialDensity (α β c : ℝ) (R₀ R₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  twoModeRadialProfile α β c R₀ R₁ x ^ 2

theorem twoModeRadialDensity_nonneg (α β c : ℝ) (R₀ R₁ : ℝ → ℝ) (x : ℝ) :
    0 ≤ twoModeRadialDensity α β c R₀ R₁ x :=
  sq_nonneg _

/-- **The two-mode radial leakage law.**  A subordinate mode whose mixing coefficient tends to zero
contributes nothing to the exterior tail mass, neither directly nor through its cross term with the
dominant mode; the tail mass converges to the square of the limiting dominant coefficient times the
single-mode arcsine tail. -/
theorem tendsto_integral_Ioi_twoModeRadialDensity
    (n₀ n₁ : ℕ) {b : ℝ} (hb : 1 < b) {α β : ℝ → ℝ} {β₀ : ℝ}
    (hα : Tendsto α atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 β₀)) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
        twoModeRadialDensity (α a) (β a) (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x)
      atTop (𝓝 (β₀ ^ 2 * (Real.arcsin (1 / b) / Real.pi))) := by
  have hsq : ∀ (n : ℕ), ∀ᶠ a : ℝ in atTop,
      Integrable (fun x : ℝ =>
        radialProlateRescaledProfile (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x ^ 2) (volume.restrict (Ioi b)) := by
    intro n
    filter_upwards [eventually_integrableOn_Ioi_signedModeRadialDensity n hb] with a h
    refine h.congr ?_
    filter_upwards with x
    exact (signedModeRadialRescaledProfile_sq a n x).symm
  have hmain := GaloisForLFunctions.HTGeometry.tendsto_integral_sq_two_mode
    (μ := volume.restrict (Ioi b))
    (f := fun a : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₁).R)
    (g := fun a : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R)
    (b := β) (c := α)
    (A := Real.arcsin (1 / b) / Real.pi) (B := Real.arcsin (1 / b) / Real.pi)
    (b₀ := β₀)
    (aestronglyMeasurable_signedModeRadialRescaledProfile n₁ b)
    (aestronglyMeasurable_signedModeRadialRescaledProfile n₀ b)
    (hsq n₁) (hsq n₀)
    (tendsto_integral_Ioi_signedModeRadialRescaledProfile_sq n₁ hb)
    (tendsto_integral_Ioi_signedModeRadialRescaledProfile_sq n₀ hb)
    hβ hα
  refine hmain.congr fun a => ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  unfold twoModeRadialDensity twoModeRadialProfile
  ring

/-! ## Uniform exterior mass on the full ray -/

/-- The exterior density of a canonical signed mode is integrable on the whole exterior ray, with a
total exterior mass bounded independently of the aperture: the endpoint collar costs `O(c⁻¹)` and
everything beyond the Dunster crossing radius is dominated by the arcsine envelope. -/
theorem exists_bound_integral_Ioi_one_signedModeRadialDensity (n : ℕ) :
    ∃ M : ℝ, ∀ᶠ a : ℝ in atTop,
      IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R) (Ioi 1) ∧
      (∫ x in Ioi (1 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x) ≤ M := by
  refine ⟨9 / 40 + 4 * radialProlateDensityEnvelopeConstant * (radialAngle 2 / Real.pi)
    + 2 * radialProlateDensityEnvelopeConstant, ?_⟩
  have hsHalf : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ 1 / 2 :=
    ((tendsto_signedModeRadialData_s_zero n).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hc5 : ∀ᶠ a : ℝ in atTop, 5 ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one
    tendsto_signedModeRadialBandwidth_atTop
  have hcross2 : ∀ᶠ a : ℝ in atTop,
      dunsterEndpointCrossing (signedModeRadialBandwidth a) ≤ 2 :=
    (hcross.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))).mono fun _ h => h.le
  filter_upwards [eventually_signedModeRadialData_s_nonneg n, hsHalf, hc5, hcross2,
    eventually_signedModeRadialData_R_one n,
    eventually_signedModeRadialData_hasDerivAt n,
    eventually_signedModeRadialData_hasSecondDerivAt n,
    eventually_signedModeRadialData_ode n] with
      a hs0 hs1 hc hcrossa hR1 hR hDR hode
  set K := radialProlateDensityEnvelopeConstant with hKdef
  have hK0 : (0 : ℝ) ≤ K := radialProlateDensityEnvelopeConstant_nonneg
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := lt_of_lt_of_le (by norm_num) hc
  have hRc : Continuous (signedModeRadialData a n).R :=
    continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous (radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R) := by
    unfold radialProlateDensity
    fun_prop
  have hIoc : IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R) (Ioc (1 : ℝ) 2) := hcont.integrableOn_Ioc
  have hIoi2 : IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R) (Ioi 2) :=
    integrableOn_Ioi_radialProlateDensity hs0 hs1 hc (by norm_num) hcrossa hR1 hR hDR hode
  have hunion : Ioc (1 : ℝ) 2 ∪ Ioi 2 = Ioi 1 :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hInt : IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R) (Ioi 1) := by
    rw [← hunion]
    exact hIoc.union hIoi2
  refine ⟨hInt, ?_⟩
  have hsplit : (∫ x in Ioi (1 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x)
      = (∫ x in Ioc (1 : ℝ) 2, radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x)
        + ∫ x in Ioi (2 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x := by
    rw [← hunion]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi2
  have hcollar : (∫ x in Ioc (1 : ℝ) 2, radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R x) ≤ 9 / 40 + 4 * K * (radialAngle 2 / Real.pi) := by
    have h := integral_radialProlateDensity_endpoint_le hs0 hs1 hc
      (by norm_num : (1 : ℝ) < 2) hcrossa hR1 hR hDR hode
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)] at h
    have hbd : 9 / (8 * signedModeRadialBandwidth a) ≤ 9 / 40 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 40)]
      nlinarith
    linarith
  have htail : (∫ x in Ioi (2 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R x) ≤ 2 * K := by
    have hdom : IntegrableOn
        (fun x : ℝ => K * profileWeight (signedModeRadialData a n).s x) (Ioi 2) :=
      (integrableOn_profileWeight hs0 hs1 (by norm_num)).const_mul K
    have hmono : (∫ x in Ioi (2 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x)
        ≤ ∫ x in Ioi (2 : ℝ), K * profileWeight (signedModeRadialData a n).s x := by
      refine integral_mono_ae hIoi2 hdom ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact radialProlateDensity_le_profileWeight hs0 hs1 hc hR1 hR hDR hode
        (hcrossa.trans hx.le)
    have hconst : (∫ x in Ioi (2 : ℝ), K * profileWeight (signedModeRadialData a n).s x)
        = K * ∫ x in Ioi (2 : ℝ), profileWeight (signedModeRadialData a n).s x :=
      integral_const_mul _ _
    have hweight : (∫ x in Ioi (2 : ℝ), profileWeight (signedModeRadialData a n).s x) ≤ 2 :=
      integral_Ioi_profileWeight_le_two hs0 hs1 (by norm_num)
    have := mul_le_mul_of_nonneg_left hweight hK0
    rw [hconst] at hmono
    linarith
  rw [hsplit]
  linarith

/-- Every fixed dilation of a canonical signed radial profile is a uniformly square-bounded family
on the exterior ray. -/
theorem sqBoundedFamily_signedModeRadialDilatedProfile (n : ℕ) {j M : ℝ} (hj : 1 ≤ j)
    (hM : ∀ᶠ a : ℝ in atTop,
      IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R) (Ioi 1) ∧
      (∫ x in Ioi (1 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x) ≤ M) :
    GaloisForLFunctions.HTGeometry.SqBoundedFamily (volume.restrict (Ioi (1 : ℝ))) atTop M
      (fun a x => radialProlateRescaledProfile (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R (j * x)) := by
  have hj0 : (0 : ℝ) < j := lt_of_lt_of_le zero_lt_one hj
  filter_upwards [hM, eventually_signedModeRadialData_hasDerivAt n] with a ⟨hInt, hle⟩ hR
  have hRc : Continuous (signedModeRadialData a n).R :=
    continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous (fun x : ℝ =>
      radialProlateRescaledProfile (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R (j * x)) := by
    unfold radialProlateRescaledProfile
    fun_prop
  have hsub : Ioi (j * 1) ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi (by simpa using hj)
  have hdil : IntegrableOn (fun x : ℝ =>
      radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R (j * x)) (Ioi 1) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 1 hj0).mpr (hInt.mono_set hsub)
  have hsqeq : (fun x : ℝ =>
      radialProlateRescaledProfile (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R (j * x) ^ 2)
      = fun x : ℝ => radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R (j * x) := by
    funext x
    exact signedModeRadialRescaledProfile_sq a n (j * x)
  refine ⟨hcont.aestronglyMeasurable, ?_, ?_⟩
  · rw [hsqeq]
    exact hdil
  · rw [hsqeq]
    have hscale := integral_comp_mul_left_Ioi
      (radialProlateDensity (signedModeRadialBandwidth a) (signedModeRadialData a n).R) 1 hj0
    have hnn : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
        0 ≤ radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x := by
      filter_upwards with x
      unfold radialProlateDensity signedModeRadialBandwidth
      positivity
    have hmono : (∫ x in Ioi (j * 1), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x)
        ≤ ∫ x in Ioi (1 : ℝ), radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x :=
      setIntegral_mono_set hInt hnn (Eventually.of_forall hsub)
    have hnn2 : (0 : ℝ) ≤ ∫ x in Ioi (j * 1), radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x := by
      refine setIntegral_nonneg measurableSet_Ioi fun x _ => ?_
      unfold radialProlateDensity signedModeRadialBandwidth
      positivity
    have hjinv : j⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hj0]
      exact hj
    rw [hscale, smul_eq_mul]
    calc j⁻¹ * ∫ x in Ioi (j * 1), radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x
        ≤ 1 * ∫ x in Ioi (j * 1), radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x := mul_le_mul_of_nonneg_right hjinv hnn2
      _ = ∫ x in Ioi (j * 1), radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n).R x := one_mul _
      _ ≤ M := hmono.trans hle

/-! ## Uniform inverse-square decay of the diagonal -/

/-- Jordan's inequality in inverse form: `arcsin` lies below its chord on `[0,1]`. -/
theorem arcsin_le_pi_div_two_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.arcsin u ≤ Real.pi / 2 * u := by
  have harc0 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr h0
  have harc1 : Real.arcsin u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
  have hjordan := Real.mul_le_sin harc0 harc1
  rw [Real.sin_arcsin (by linarith : (-1 : ℝ) ≤ u) h1] at hjordan
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := hpi.ne'
  have h := mul_le_mul_of_nonneg_left hjordan (by positivity : (0:ℝ) ≤ Real.pi / 2)
  rw [show Real.pi / 2 * (2 / Real.pi * Real.arcsin u) = Real.arcsin u from by
    field_simp] at h
  exact h

/-- The limiting profile density has inverse-linear tail mass. -/
theorem integral_Ioi_profileDensity_le {k : ℝ} (hk : 1 ≤ k) :
    (∫ x in Ioi k, profileDensity x) ≤ 1 / (2 * k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hval : (∫ x in Ioi k, profileDensity x) = Real.arcsin (1 / k) / Real.pi := by
    rw [integral_Ioi_profileDensity_eq hk, radialAngle_eq_pi_div_two_sub_arcsin hk]
    field_simp
    ring
  have hinv0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hinv1 : 1 / k ≤ 1 := by
    rw [div_le_one hk0]
    exact hk
  have harc := arcsin_le_pi_div_two_mul hinv0 hinv1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [hval, div_le_div_iff₀ hpi (by positivity : (0:ℝ) < 2 * k)]
  have : Real.pi / 2 * (1 / k) * (2 * k) = Real.pi := by field_simp
  nlinarith [harc, hk0]

/-- Uniform inverse-linear exterior tail mass of a single canonical signed mode, simultaneously for
every dilation beyond the second: the Dunster crossing radius passes below `2` once and for all. -/
theorem eventually_integral_Ioi_signedModeRadialDensity_le (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℝ, 2 ≤ k →
      IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R) (Ioi k) ∧
      (∫ x in Ioi k, radialProlateDensity (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R x)
        ≤ 2 * radialProlateDensityEnvelopeConstant / k := by
  have hsHalf : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ 1 / 2 :=
    ((tendsto_signedModeRadialData_s_zero n).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hc5 : ∀ᶠ a : ℝ in atTop, 5 ≤ signedModeRadialBandwidth a :=
    tendsto_signedModeRadialBandwidth_atTop.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one
    tendsto_signedModeRadialBandwidth_atTop
  have hcrossk : ∀ᶠ a : ℝ in atTop,
      dunsterEndpointCrossing (signedModeRadialBandwidth a) ≤ 2 :=
    (hcross.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))).mono fun _ h => h.le
  filter_upwards [eventually_signedModeRadialData_s_nonneg n, hsHalf, hc5, hcrossk,
    eventually_signedModeRadialData_R_one n,
    eventually_signedModeRadialData_hasDerivAt n,
    eventually_signedModeRadialData_hasSecondDerivAt n,
    eventually_signedModeRadialData_ode n] with
      a hs0 hs1 hc hcross2 hR1 hR hDR hode
  intro k hk
  have hk1 : (1 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hcrossa : dunsterEndpointCrossing (signedModeRadialBandwidth a) ≤ k := hcross2.trans hk
  have hK0 : (0 : ℝ) ≤ radialProlateDensityEnvelopeConstant :=
    radialProlateDensityEnvelopeConstant_nonneg
  have hInt : IntegrableOn (radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R) (Ioi k) :=
    integrableOn_Ioi_radialProlateDensity hs0 hs1 hc hk1 hcrossa hR1 hR hDR hode
  have hdom : IntegrableOn
      (fun x : ℝ => 4 * radialProlateDensityEnvelopeConstant * profileDensity x) (Ioi k) :=
    (integrableOn_profileDensity.mono_set (Ioi_subset_Ioi hk1.le)).const_mul
      (4 * radialProlateDensityEnvelopeConstant)
  have hmono : (∫ x in Ioi k, radialProlateDensity (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R x)
      ≤ ∫ x in Ioi k, 4 * radialProlateDensityEnvelopeConstant * profileDensity x := by
    refine integral_mono_ae hInt hdom ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxk : k ≤ x := hx.le
    have hdens := radialProlateDensity_le_profileWeight hs0 hs1 hc hR1 hR hDR hode
      (hcrossa.trans hxk)
    have hweight := profileWeight_le_four_mul_profileDensity hs0 hs1 (hk1.trans hx)
    nlinarith [hdens, hweight, hK0]
  have hconst : (∫ x in Ioi k, 4 * radialProlateDensityEnvelopeConstant * profileDensity x)
      = 4 * radialProlateDensityEnvelopeConstant * ∫ x in Ioi k, profileDensity x :=
    integral_const_mul _ _
  have htail : (∫ x in Ioi k, profileDensity x) ≤ 1 / (2 * k) :=
    integral_Ioi_profileDensity_le hk1.le
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  have hfin : 4 * radialProlateDensityEnvelopeConstant * (∫ x in Ioi k, profileDensity x)
      ≤ 2 * radialProlateDensityEnvelopeConstant / k := by
    have h := mul_le_mul_of_nonneg_left htail
      (by positivity : (0:ℝ) ≤ 4 * radialProlateDensityEnvelopeConstant)
    calc 4 * radialProlateDensityEnvelopeConstant * (∫ x in Ioi k, profileDensity x)
        ≤ 4 * radialProlateDensityEnvelopeConstant * (1 / (2 * k)) := h
      _ = 2 * radialProlateDensityEnvelopeConstant / k := by field_simp; ring
  rw [hconst] at hmono
  exact ⟨hInt, by linarith⟩

/-! ## Radial dilation Gram entries of the two-mode source -/

/-- Exterior dilation Gram entry of the constrained two-mode source. -/
def twoModeRadialGramEntry (a : ℝ) (n₀ n₁ : ℕ) (α β j k : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ),
    twoModeRadialProfile α β (signedModeRadialBandwidth a)
        (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R (j * x) *
      twoModeRadialProfile α β (signedModeRadialBandwidth a)
        (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R (k * x)

/-- A diagonal two-mode Gram entry is the reciprocal-dilation multiple of one density tail. -/
theorem twoModeRadialGramEntry_diag_eq (a : ℝ) (n₀ n₁ : ℕ) (α β : ℝ) {k : ℝ} (hk : 0 < k) :
    twoModeRadialGramEntry a n₀ n₁ α β k k
      = k⁻¹ * ∫ x in Ioi k, twoModeRadialDensity α β (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x := by
  have hpoint : (fun x : ℝ =>
      twoModeRadialProfile α β (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R (k * x) *
        twoModeRadialProfile α β (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R (k * x))
      = fun x : ℝ => twoModeRadialDensity α β (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R (k * x) := by
    funext x
    rw [twoModeRadialDensity, sq]
  rw [twoModeRadialGramEntry, hpoint, integral_comp_mul_left_Ioi _ 1 hk, mul_one, smul_eq_mul]

/-- **The two-mode radial dilation spectrum.**  Every diagonal Gram entry of the constrained
two-mode source converges to the `1/k`-scaled arcsine tail, weighted by the square of the limiting
dominant coefficient. -/
theorem tendsto_twoModeRadialGramEntry_diag
    (n₀ n₁ : ℕ) {k : ℝ} (hk : 1 < k) {α β : ℝ → ℝ} {β₀ : ℝ}
    (hα : Tendsto α atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 β₀)) :
    Tendsto (fun a : ℝ => twoModeRadialGramEntry a n₀ n₁ (α a) (β a) k k) atTop
      (𝓝 (β₀ ^ 2 * (Real.arcsin (1 / k) / (Real.pi * k)))) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have h := (tendsto_integral_Ioi_twoModeRadialDensity n₀ n₁ hk hα hβ).const_mul k⁻¹
  have hval : k⁻¹ * (β₀ ^ 2 * (Real.arcsin (1 / k) / Real.pi))
      = β₀ ^ 2 * (Real.arcsin (1 / k) / (Real.pi * k)) := by
    field_simp
  rw [hval] at h
  refine h.congr fun a => ?_
  exact (twoModeRadialGramEntry_diag_eq a n₀ n₁ (α a) (β a) hk0).symm

/-- **Every fixed off-diagonal two-mode Gram entry vanishes.**  The dominant-dominant block already
cancels; the three blocks involving the subordinate mode stay bounded by Cauchy--Schwarz and are
removed by the subordinate coefficient. -/
theorem tendsto_twoModeRadialGramEntry_of_ne
    (n₀ n₁ : ℕ) {j k : ℝ} (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k)
    {α β : ℝ → ℝ} {β₀ : ℝ}
    (hα : Tendsto α atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 β₀)) :
    Tendsto (fun a : ℝ => twoModeRadialGramEntry a n₀ n₁ (α a) (β a) j k) atTop (𝓝 0) := by
  obtain ⟨M₀, hM₀⟩ := exists_bound_integral_Ioi_one_signedModeRadialDensity n₀
  obtain ⟨M₁, hM₁⟩ := exists_bound_integral_Ioi_one_signedModeRadialDensity n₁
  set M := max M₀ M₁ with hMdef
  have hb₀j := (sqBoundedFamily_signedModeRadialDilatedProfile n₀ hj hM₀).mono
    (le_max_left M₀ M₁)
  have hb₁j := (sqBoundedFamily_signedModeRadialDilatedProfile n₁ hj hM₁).mono
    (le_max_right M₀ M₁)
  have hb₀k := (sqBoundedFamily_signedModeRadialDilatedProfile n₀ hk hM₀).mono
    (le_max_left M₀ M₁)
  have hb₁k := (sqBoundedFamily_signedModeRadialDilatedProfile n₁ hk hM₁).mono
    (le_max_right M₀ M₁)
  have hcross : Tendsto (fun a : ℝ => ∫ x in Ioi (1 : ℝ),
      radialProlateRescaledProfile (signedModeRadialBandwidth a)
          (signedModeRadialData a n₁).R (j * x) *
        radialProlateRescaledProfile (signedModeRadialBandwidth a)
          (signedModeRadialData a n₁).R (k * x)) atTop (𝓝 0) :=
    tendsto_signedModeRadialGramEntry_of_ne n₁ hj hk hjk
  have hmain := GaloisForLFunctions.HTGeometry.tendsto_integral_mul_two_mode
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (u₀ := fun a : ℝ => fun x : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R (j * x))
    (u₁ := fun a : ℝ => fun x : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₁).R (j * x))
    (v₀ := fun a : ℝ => fun x : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R (k * x))
    (v₁ := fun a : ℝ => fun x : ℝ => radialProlateRescaledProfile (signedModeRadialBandwidth a)
      (signedModeRadialData a n₁).R (k * x))
    (α := α) (β := β) (β₀ := β₀)
    hb₀j hb₁j hb₀k hb₁k hcross hα hβ
  refine hmain.congr fun a => ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  unfold twoModeRadialProfile
  ring

/-- **Uniform inverse-square decay of the two-mode diagonal Gram entries.**  Beyond the second
dilation the constrained diagonal is dominated by `C/k²`, simultaneously for every dilation and
uniformly in the aperture. -/
theorem eventually_twoModeRadialGramEntry_diag_le
    (n₀ n₁ : ℕ) (α β : ℝ → ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℝ, 2 ≤ k →
      twoModeRadialGramEntry a n₀ n₁ (α a) (β a) k k
        ≤ 4 * radialProlateDensityEnvelopeConstant * (α a ^ 2 + β a ^ 2) / k ^ 2 := by
  filter_upwards [eventually_integral_Ioi_signedModeRadialDensity_le n₀,
    eventually_integral_Ioi_signedModeRadialDensity_le n₁] with a h₀ h₁
  intro k hk
  have hk1 : (1 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  obtain ⟨hI₀, hb₀⟩ := h₀ k hk
  obtain ⟨hI₁, hb₁⟩ := h₁ k hk
  set K := radialProlateDensityEnvelopeConstant with hKdef
  have hK0 : (0 : ℝ) ≤ K := radialProlateDensityEnvelopeConstant_nonneg
  have hdom : IntegrableOn (fun x : ℝ =>
      2 * α a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R x
        + 2 * β a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₁).R x) (Ioi k) :=
    (hI₀.const_mul (2 * α a ^ 2)).add (hI₁.const_mul (2 * β a ^ 2))
  have hle : (∫ x in Ioi k, twoModeRadialDensity (α a) (β a) (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x)
      ≤ ∫ x in Ioi k,
          (2 * α a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
              (signedModeRadialData a n₀).R x
            + 2 * β a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
              (signedModeRadialData a n₁).R x) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
      twoModeRadialDensity_nonneg _ _ _ _ _ x) hdom ?_
    filter_upwards with x
    have h₀ := signedModeRadialRescaledProfile_sq a n₀ x
    have h₁ := signedModeRadialRescaledProfile_sq a n₁ x
    unfold twoModeRadialDensity twoModeRadialProfile
    rw [← h₀, ← h₁]
    nlinarith [sq_nonneg (α a * radialProlateRescaledProfile (signedModeRadialBandwidth a)
        (signedModeRadialData a n₀).R x
      - β a * radialProlateRescaledProfile (signedModeRadialBandwidth a)
        (signedModeRadialData a n₁).R x)]
  have hsplit : (∫ x in Ioi k,
      (2 * α a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R x
        + 2 * β a ^ 2 * radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₁).R x))
      = 2 * α a ^ 2 * (∫ x in Ioi k, radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R x)
        + 2 * β a ^ 2 * ∫ x in Ioi k, radialProlateDensity (signedModeRadialBandwidth a)
          (signedModeRadialData a n₁).R x := by
    rw [integral_add (hI₀.const_mul (2 * α a ^ 2)) (hI₁.const_mul (2 * β a ^ 2)),
      integral_const_mul, integral_const_mul]
  have hbound : (∫ x in Ioi k, twoModeRadialDensity (α a) (β a) (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x)
      ≤ 4 * K * (α a ^ 2 + β a ^ 2) / k := by
    rw [hsplit] at hle
    have h₀ := mul_le_mul_of_nonneg_left hb₀ (by positivity : (0:ℝ) ≤ 2 * α a ^ 2)
    have h₁ := mul_le_mul_of_nonneg_left hb₁ (by positivity : (0:ℝ) ≤ 2 * β a ^ 2)
    have hid : 2 * α a ^ 2 * (2 * K / k) + 2 * β a ^ 2 * (2 * K / k)
        = 4 * K * (α a ^ 2 + β a ^ 2) / k := by field_simp; ring
    linarith [hle, h₀, h₁, hid.ge, hid.le]
  rw [twoModeRadialGramEntry_diag_eq a n₀ n₁ (α a) (β a) hk0]
  have hnn : (0 : ℝ) ≤ ∫ x in Ioi k, twoModeRadialDensity (α a) (β a) (signedModeRadialBandwidth a)
      (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => twoModeRadialDensity_nonneg _ _ _ _ _ x
  have hstep := mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ k⁻¹)
  have hid2 : k⁻¹ * (4 * K * (α a ^ 2 + β a ^ 2) / k)
      = 4 * K * (α a ^ 2 + β a ^ 2) / k ^ 2 := by
    field_simp
  linarith [hstep, hid2.ge, hid2.le]

/-- Diagonal two-mode Gram entries are nonnegative. -/
theorem twoModeRadialGramEntry_diag_nonneg (a : ℝ) (n₀ n₁ : ℕ) (α β : ℝ) {k : ℝ} (hk : 0 < k) :
    0 ≤ twoModeRadialGramEntry a n₀ n₁ α β k k := by
  rw [twoModeRadialGramEntry_diag_eq a n₀ n₁ α β hk]
  refine mul_nonneg (by positivity) ?_
  exact setIntegral_nonneg measurableSet_Ioi fun x _ => twoModeRadialDensity_nonneg _ _ _ _ _ x

/-- The divisor-weighted diagonal majorant is summable. -/
theorem summable_log_shift_div_sq :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_weighted_rowMajorant
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    positivity
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hx
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    nlinarith

/-- **The divisor-weighted diagonal series limit.**  Weights trapped between zero and `log k`, and
stabilizing at every fixed dilation, may be summed against the uniformly `C/k²`-dominated diagonal:
the limit is the weighted arcsine spectrum. -/
theorem tendsto_tsum_weighted_twoModeRadialGramEntry_diag
    (n₀ n₁ : ℕ) {α β : ℝ → ℝ} {β₀ : ℝ}
    (hα : Tendsto α atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 β₀))
    {w : ℝ → ℕ → ℝ}
    (hw0 : ∀ a k, 0 ≤ w a k) (hwle : ∀ a k, w a k ≤ Real.log ((k : ℝ) + 2))
    (hwev : ∀ k, ∀ᶠ a : ℝ in atTop, w a k = Real.log ((k : ℝ) + 2)) :
    Tendsto (fun a : ℝ => ∑' k : ℕ,
        w a k * twoModeRadialGramEntry a n₀ n₁ (α a) (β a) ((k : ℝ) + 2) ((k : ℝ) + 2))
      atTop (𝓝 (∑' k : ℕ, Real.log ((k : ℝ) + 2) *
        (β₀ ^ 2 * (Real.arcsin (1 / ((k : ℝ) + 2)) / (Real.pi * ((k : ℝ) + 2)))))) := by
  set K := radialProlateDensityEnvelopeConstant with hKdef
  have hK0 : (0 : ℝ) ≤ K := radialProlateDensityEnvelopeConstant_nonneg
  set B : ℝ := 1 + (|β₀| + 1) ^ 2 with hBdef
  have hB0 : (0 : ℝ) ≤ B := by positivity
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k : ℕ => 4 * K * B * (Real.log ((k : ℝ) + 2) / ((k : ℝ) + 2) ^ 2))
    (summable_log_shift_div_sq.mul_left (4 * K * B)) ?_ ?_
  · intro k
    have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hG := tendsto_twoModeRadialGramEntry_diag n₀ n₁ hk2 hα hβ
    have hwk : Tendsto (fun a : ℝ => w a k) atTop (𝓝 (Real.log ((k : ℝ) + 2))) :=
      Tendsto.congr' ((hwev k).mono fun a h => h.symm) tendsto_const_nhds
    exact hwk.mul hG
  · have hαsmall : ∀ᶠ a : ℝ in atTop, |α a| ≤ 1 := by
      have habs : Tendsto (fun a : ℝ => |α a|) atTop (𝓝 0) := by
        have h := hα.abs
        simpa using h
      exact (habs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))).mono
        fun a h => le_of_lt h
    have hβsmall : ∀ᶠ a : ℝ in atTop, |β a| ≤ |β₀| + 1 := by
      have habs : Tendsto (fun a : ℝ => |β a|) atTop (𝓝 |β₀|) := hβ.abs
      exact (habs.eventually (eventually_lt_nhds (by linarith : |β₀| < |β₀| + 1))).mono
        fun a h => le_of_lt h
    filter_upwards [eventually_twoModeRadialGramEntry_diag_le n₀ n₁ α β, hαsmall, hβsmall] with
      a hdiag hαa hβa
    intro k
    have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
    have hGnn : 0 ≤ twoModeRadialGramEntry a n₀ n₁ (α a) (β a) ((k : ℝ) + 2) ((k : ℝ) + 2) :=
      twoModeRadialGramEntry_diag_nonneg a n₀ n₁ (α a) (β a) hk0
    have hGle := hdiag ((k : ℝ) + 2) hk2
    have hcoef : α a ^ 2 + β a ^ 2 ≤ B := by
      have h1 : α a ^ 2 ≤ 1 := by nlinarith [abs_nonneg (α a), sq_abs (α a)]
      have h2 : β a ^ 2 ≤ (|β₀| + 1) ^ 2 := by
        nlinarith [abs_nonneg (β a), sq_abs (β a), abs_nonneg β₀]
      simpa [hBdef] using add_le_add h1 h2
    have hlognn : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hstep : twoModeRadialGramEntry a n₀ n₁ (α a) (β a) ((k : ℝ) + 2) ((k : ℝ) + 2)
        ≤ 4 * K * B / ((k : ℝ) + 2) ^ 2 := by
      refine hGle.trans ?_
      have hnum : 4 * K * (α a ^ 2 + β a ^ 2) ≤ 4 * K * B :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      exact div_le_div_of_nonneg_right hnum (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 a k) hGnn)]
    calc w a k * twoModeRadialGramEntry a n₀ n₁ (α a) (β a) ((k : ℝ) + 2) ((k : ℝ) + 2)
        ≤ Real.log ((k : ℝ) + 2) * (4 * K * B / ((k : ℝ) + 2) ^ 2) :=
          mul_le_mul (hwle a k) hstep hGnn hlognn
      _ = 4 * K * B * (Real.log ((k : ℝ) + 2) / ((k : ℝ) + 2) ^ 2) := by ring

/-! ## The constrained CCM source -/

/-- Constrained seed weight of the subordinate mode. -/
def ccmSeedZero : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)

/-- Constrained seed weight of the dominant mode. -/
def ccmSeedFour : ℝ := Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)

theorem ccmSeedZero_pos : 0 < ccmSeedZero := Real.rpow_pos_of_pos (by norm_num) _

theorem ccmSeedFour_pos : 0 < ccmSeedFour := by
  unfold ccmSeedFour
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- Normalizing constant of the constrained two-mode source. -/
def ccmSeedNorm : ℝ := Real.sqrt (ccmSeedZero ^ 2 + ccmSeedFour ^ 2)

theorem ccmSeedNorm_pos : 0 < ccmSeedNorm := by
  refine Real.sqrt_pos.mpr ?_
  have := ccmSeedZero_pos
  have := ccmSeedFour_pos
  positivity

/-- Mixing coefficient of the dominant mode: its square is the constrained ground-state weight. -/
def ccmDominantCoeff : ℝ := -(ccmSeedZero / ccmSeedNorm)

/-- **The constrained ground-state weight `8/11`.** -/
theorem ccmDominantCoeff_sq : ccmDominantCoeff ^ 2 = 8 / 11 := by
  have hz := ccmSeedZero_pos
  have hf := ccmSeedFour_pos
  have hden : (0 : ℝ) < ccmSeedZero ^ 2 + ccmSeedFour ^ 2 := by positivity
  have hnorm : ccmSeedNorm ^ 2 = ccmSeedZero ^ 2 + ccmSeedFour ^ 2 :=
    Real.sq_sqrt hden.le
  have hne : ccmSeedNorm ≠ 0 := ccmSeedNorm_pos.ne'
  unfold ccmDominantCoeff
  rw [neg_pow, div_pow, hnorm]
  simpa [ccmSeedZero, ccmSeedFour] using GaloisForLFunctions.ccm_groundState_weight_eq

/-- Mixing coefficient of the subordinate mode: the seed weight times the square root of the
exterior leakage ratio of the two modes. -/
def ccmSubordinateCoeff (A₀ A₁ : ℝ) (a : ℝ) : ℝ :=
  ccmSeedFour * Real.sqrt (fuchsRate A₀ 0 a / fuchsRate A₁ 4 a) / ccmSeedNorm

/-- **The subordinate mixing coefficient vanishes.**  The Fuchs ladder separates the two exterior
leakages by four powers of the aperture, so the subordinate mode enters the normalized source with
an amplitude of order `λ⁻⁴`. -/
theorem tendsto_ccmSubordinateCoeff_zero {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    Tendsto (ccmSubordinateCoeff A₀ A₁) atTop (𝓝 0) := by
  have hratio : Tendsto (fun a : ℝ => fuchsRate A₀ 0 a / fuchsRate A₁ 4 a) atTop (𝓝 0) := by
    have h := fuchsRate_div_tendsto_zero (A := A₁) (A' := A₀) hA₁ hA₀ 0
      (k := 4) (by norm_num)
    simpa using h
  have hsqrt : Tendsto (fun a : ℝ =>
      Real.sqrt (fuchsRate A₀ 0 a / fuchsRate A₁ 4 a)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hratio
    rw [Real.sqrt_zero] at h
    exact h
  have h := (hsqrt.const_mul ccmSeedFour).div_const ccmSeedNorm
  rw [mul_zero, zero_div] at h
  exact h

/-- **The constrained two-mode radial leakage law.**  For the constrained Connes--Consani--Moscovici
source built from the canonical modes `n₀` and `n₁` with the Fuchs ladder separating their exterior
leakages, the normalized exterior radial mass beyond every radius `b > 1` converges to the
corresponding tail of the arcsine leakage measure `(8/(11π)) dx/(x√(x²−1))`. -/
theorem tendsto_integral_Ioi_ccmTwoModeRadialDensity
    (n₀ n₁ : ℕ) {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
        twoModeRadialDensity (ccmSubordinateCoeff A₀ A₁ a) ccmDominantCoeff
          (signedModeRadialBandwidth a)
          (signedModeRadialData a n₀).R (signedModeRadialData a n₁).R x)
      atTop (𝓝 (∫ x in Ioi b, nuInfinityDensity x)) := by
  have h := tendsto_integral_Ioi_twoModeRadialDensity n₀ n₁ hb
    (tendsto_ccmSubordinateCoeff_zero hA₀ hA₁)
    (tendsto_const_nhds (x := ccmDominantCoeff) (f := (atTop : Filter ℝ)))
  rw [ccmDominantCoeff_sq] at h
  have heq : (8 : ℝ) / 11 * (Real.arcsin (1 / b) / Real.pi)
      = 8 / (11 * Real.pi) * Real.arcsin (1 / b) := by
    field_simp
  rw [integral_Ioi_nuInfinityDensity hb.le, ← heq]
  exact h


/-- **The constrained arcsine dilation spectrum.**  Every diagonal Gram entry of the constrained
two-mode source converges to `(8/(11 π k)) arcsin(1/k)`. -/
theorem tendsto_ccmTwoModeRadialGramEntry_diag
    (n₀ n₁ : ℕ) {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) {k : ℝ} (hk : 1 < k) :
    Tendsto (fun a : ℝ => twoModeRadialGramEntry a n₀ n₁
        (ccmSubordinateCoeff A₀ A₁ a) ccmDominantCoeff k k) atTop
      (𝓝 (8 / (11 * Real.pi * k) * Real.arcsin (1 / k))) := by
  have hk0 : k ≠ 0 := (lt_trans zero_lt_one hk).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := tendsto_twoModeRadialGramEntry_diag n₀ n₁ hk
    (tendsto_ccmSubordinateCoeff_zero hA₀ hA₁)
    (tendsto_const_nhds (x := ccmDominantCoeff) (f := (atTop : Filter ℝ)))
  rw [ccmDominantCoeff_sq] at h
  have heq : (8 : ℝ) / 11 * (Real.arcsin (1 / k) / (Real.pi * k))
      = 8 / (11 * Real.pi * k) * Real.arcsin (1 / k) := by
    field_simp
  rwa [heq] at h

/-- **Every fixed off-diagonal constrained Gram entry vanishes.**  The constrained radial dilation
Gram matrix is therefore asymptotically diagonal. -/
theorem tendsto_ccmTwoModeRadialGramEntry_of_ne
    (n₀ n₁ : ℕ) {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    {j k : ℝ} (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k) :
    Tendsto (fun a : ℝ => twoModeRadialGramEntry a n₀ n₁
        (ccmSubordinateCoeff A₀ A₁ a) ccmDominantCoeff j k) atTop (𝓝 0) :=
  tendsto_twoModeRadialGramEntry_of_ne n₀ n₁ hj hk hjk
    (tendsto_ccmSubordinateCoeff_zero hA₀ hA₁)
    (tendsto_const_nhds (x := ccmDominantCoeff) (f := (atTop : Filter ℝ)))


/-- **The constrained diagonal von Mangoldt charge.**  Twice the divisor-weighted diagonal Gram
series converges to the arithmetic trace `∑ κ_k`, hence to the negative of the constrained prolate
prime constant.  The weights only have to be trapped between `0` and `log k` and to stabilize at
every fixed dilation, which is exactly what a truncated divisor weight does. -/
theorem tendsto_two_mul_tsum_weighted_ccmTwoModeRadialGramEntry_diag
    (n₀ n₁ : ℕ) {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    {w : ℝ → ℕ → ℝ}
    (hw0 : ∀ a k, 0 ≤ w a k) (hwle : ∀ a k, w a k ≤ Real.log ((k : ℝ) + 2))
    (hwev : ∀ k, ∀ᶠ a : ℝ in atTop, w a k = Real.log ((k : ℝ) + 2)) :
    Tendsto (fun a : ℝ => 2 * ∑' k : ℕ,
        w a k * twoModeRadialGramEntry a n₀ n₁ (ccmSubordinateCoeff A₀ A₁ a) ccmDominantCoeff
          ((k : ℝ) + 2) ((k : ℝ) + 2))
      atTop (𝓝 (-GaloisForLFunctions.constrainedProlatePrimeConstant)) := by
  have h := tendsto_tsum_weighted_twoModeRadialGramEntry_diag n₀ n₁
    (tendsto_ccmSubordinateCoeff_zero hA₀ hA₁)
    (tendsto_const_nhds (x := ccmDominantCoeff) (f := (atTop : Filter ℝ))) hw0 hwle hwev
  rw [ccmDominantCoeff_sq] at h
  have hterm : ∀ k : ℕ, 2 * (Real.log ((k : ℝ) + 2) *
      ((8 : ℝ) / 11 * (Real.arcsin (1 / ((k : ℝ) + 2)) / (Real.pi * ((k : ℝ) + 2)))))
      = GaloisForLFunctions.constrainedProlateArithmeticEigenvalue k := by
    intro k
    rw [GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_eq]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have h2 := h.const_mul 2
  have hval : 2 * ∑' k : ℕ, Real.log ((k : ℝ) + 2) *
      ((8 : ℝ) / 11 * (Real.arcsin (1 / ((k : ℝ) + 2)) / (Real.pi * ((k : ℝ) + 2))))
      = -GaloisForLFunctions.constrainedProlatePrimeConstant := by
    rw [← tsum_mul_left, tsum_congr hterm,
      GaloisForLFunctions.tsum_constrainedProlateArithmeticEigenvalue]
  rwa [hval] at h2

end RHTower

end
