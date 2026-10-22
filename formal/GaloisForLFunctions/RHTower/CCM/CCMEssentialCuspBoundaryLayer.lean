import GaloisForLFunctions.RHTower.CCM.CCMMeromorphicCuspBoundaryNoGo
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-
# Essential periodic cusps and the CCM four-unit boundary layer

The meromorphic period-charge obstruction is sharp.  This file constructs an
entire `2π`-periodic map into an infinite-dimensional `L²` space whose thermal
boundary density is exactly four.  Its descended cusp is therefore
nonmeromorphic.  The exact energy law also proves that all normalized energy
concentrates at the endpoint: every interval separated from zero carries
asymptotically zero thermal density.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section

namespace RHTower

def ccmEssentialBoundaryLayer (u t : ℝ) : ℝ :=
  2 * Real.sqrt 2 * Real.exp (-t / u)

def ccmEssentialBoundaryLayerEnergy (u : ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1, ccmEssentialBoundaryLayer u t ^ 2

theorem integral_exp_neg_two_div
    {u a b : ℝ} (hu : u ≠ 0) :
    (∫ t in a..b, Real.exp (-2 * t / u)) =
      u / 2 * (Real.exp (-2 * a / u) - Real.exp (-2 * b / u)) := by
  let F : ℝ → ℝ := fun t => -(u / 2) * Real.exp (-2 * t / u)
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.exp (-2 * t / u)) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ => -2 * x / u) (-2 / u) t := by
      simpa only [id_eq, mul_one] using!
        ((hasDerivAt_id t).const_mul (-2 : ℝ)).div_const u
    have hexp := hlin.exp
    have hraw := hexp.const_mul (-(u / 2))
    have hraw' := hraw.congr_deriv
      (g' := Real.exp (-2 * t / u)) (by
        field_simp [hu])
    simpa only [F, Function.comp_apply] using! hraw'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hderiv t)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-2 * t / u))).intervalIntegrable a b)]
  dsimp [F]
  ring

theorem ccmEssentialBoundaryLayerEnergy_eq
    {u : ℝ} (hu : 0 < u) :
    ccmEssentialBoundaryLayerEnergy u =
      4 * u * (1 - Real.exp (-2 / u)) := by
  rw [ccmEssentialBoundaryLayerEnergy,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [ccmEssentialBoundaryLayer]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfun :
      (fun t : ℝ => (2 * Real.sqrt 2 * Real.exp (-t / u)) ^ 2) =
        fun t : ℝ => 8 * Real.exp (-2 * t / u) := by
    funext t
    rw [mul_pow, mul_pow, hsq]
    have hexp : Real.exp (-t / u) ^ 2 = Real.exp (-2 * t / u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_exp_neg_two_div hu.ne']
  simp
  ring

theorem tendsto_exp_neg_two_div_nhdsGT_zero :
    Tendsto (fun u : ℝ => Real.exp (-2 / u)) (𝓝[>] 0) (nhds 0) := by
  have htop : Tendsto (fun u : ℝ => u⁻¹ * 2) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_pos zero_lt_two tendsto_const_nhds
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
  convert he using 1
  funext u
  congr 1
  ring

theorem ccmEssentialBoundaryLayer_fourUnitDensity :
    Tendsto
      (fun u : ℝ =>
        ccmEssentialBoundaryLayerEnergy u / (1 - Real.exp (-u)))
      (𝓝[>] 0) (nhds 4) := by
  have henergy :
      (fun u : ℝ =>
        ccmEssentialBoundaryLayerEnergy u / (1 - Real.exp (-u))) =ᶠ[𝓝[>] 0]
      (fun u : ℝ =>
        4 * (u / (1 - Real.exp (-u))) *
          (1 - Real.exp (-2 / u))) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [ccmEssentialBoundaryLayerEnergy_eq hu]
    ring
  have htail :
      Tendsto (fun u : ℝ => 1 - Real.exp (-2 / u)) (𝓝[>] 0) (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_exp_neg_two_div_nhdsGT_zero
  have hraw :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (4 : ℝ)) (𝓝[>] 0) (nhds 4)).mul
      HTGeometry.tendsto_id_div_one_sub_exp_neg_nhdsGT_zero).mul htail
  have h : Tendsto
      (fun u : ℝ => 4 * (u / (1 - Real.exp (-u))) *
        (1 - Real.exp (-2 / u)))
      (𝓝[>] 0) (nhds 4) := by
    simpa using hraw
  exact h.congr' henergy.symm

def ccmEssentialBoundaryLayerTailEnergy (δ u : ℝ) : ℝ :=
  ∫ t in Set.Ioc δ 1, ccmEssentialBoundaryLayer u t ^ 2

theorem ccmEssentialBoundaryLayerTailEnergy_eq
    {δ u : ℝ} (hδ : δ ≤ 1) (hu : 0 < u) :
    ccmEssentialBoundaryLayerTailEnergy δ u =
      4 * u * (Real.exp (-2 * δ / u) - Real.exp (-2 / u)) := by
  rw [ccmEssentialBoundaryLayerTailEnergy,
    ← intervalIntegral.integral_of_le hδ]
  simp_rw [ccmEssentialBoundaryLayer]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfun :
      (fun t : ℝ => (2 * Real.sqrt 2 * Real.exp (-t / u)) ^ 2) =
        fun t : ℝ => 8 * Real.exp (-2 * t / u) := by
    funext t
    rw [mul_pow, mul_pow, hsq]
    have hexp : Real.exp (-t / u) ^ 2 =
        Real.exp (-2 * t / u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_exp_neg_two_div hu.ne']
  ring_nf

theorem tendsto_exp_neg_two_mul_div_nhdsGT_zero
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun u : ℝ => Real.exp (-2 * δ / u))
      (𝓝[>] 0) (nhds 0) := by
  have htop : Tendsto (fun u : ℝ => u⁻¹ * (2 * δ))
      (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_pos
      (mul_pos zero_lt_two hδ) tendsto_const_nhds
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
  convert he using 1
  funext u
  congr 1
  ring

/-- Every interval separated from the endpoint carries asymptotically zero
thermal density: the four units concentrate in a boundary layer at `t = 0`. -/
theorem ccmEssentialBoundaryLayer_tailDensity_zero
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto
      (fun u : ℝ =>
        ccmEssentialBoundaryLayerTailEnergy δ u /
          (1 - Real.exp (-u)))
      (𝓝[>] 0) (nhds 0) := by
  have htail :
      Tendsto
        (fun u : ℝ =>
          Real.exp (-2 * δ / u) - Real.exp (-2 / u))
        (𝓝[>] 0) (nhds 0) := by
    simpa using
      (tendsto_exp_neg_two_mul_div_nhdsGT_zero hδ0).sub
        tendsto_exp_neg_two_div_nhdsGT_zero
  have hraw :=
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (4 : ℝ)) (𝓝[>] 0) (nhds 4)).mul
        HTGeometry.tendsto_id_div_one_sub_exp_neg_nhdsGT_zero).mul
      htail
  have hformula :
      (fun u : ℝ =>
        ccmEssentialBoundaryLayerTailEnergy δ u /
          (1 - Real.exp (-u))) =ᶠ[𝓝[>] 0]
      (fun u : ℝ =>
        4 * (u / (1 - Real.exp (-u))) *
          (Real.exp (-2 * δ / u) - Real.exp (-2 / u))) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [ccmEssentialBoundaryLayerTailEnergy_eq hδ1 hu]
    ring
  have hraw0 : Tendsto
      (fun u : ℝ =>
        4 * (u / (1 - Real.exp (-u))) *
          (Real.exp (-2 * δ / u) - Real.exp (-2 / u)))
      (𝓝[>] 0) (nhds 0) := by
    simpa using hraw
  exact hraw0.congr' hformula.symm

/-! ## An actual entire periodic Hilbert cusp -/

def ccmCuspMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

noncomputable instance : IsFiniteMeasure ccmCuspMeasure := by
  rw [ccmCuspMeasure]
  infer_instance

noncomputable def ccmUnitClampBCF : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => ((max (0 : ℝ) (min t 1) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp
      (continuous_const.max (continuous_id.min continuous_const)))
    1 (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_right _ _))

@[simp] theorem ccmUnitClampBCF_apply (t : ℝ) :
    ccmUnitClampBCF t = ((max (0 : ℝ) (min t 1) : ℝ) : ℂ) := rfl

noncomputable def ccmEssentialLogCuspBCF (z : ℂ) : ℝ →ᵇ ℂ :=
  ((2 * Real.sqrt 2 : ℝ) : ℂ) •
    NormedSpace.exp
      (-(Complex.exp (-Complex.I * z)) • ccmUnitClampBCF)

noncomputable def ccmEssentialLogCusp (z : ℂ) :
    Lp ℂ 2 ccmCuspMeasure :=
  BoundedContinuousFunction.toLp 2 ccmCuspMeasure ℂ
    (ccmEssentialLogCuspBCF z)

theorem analyticAt_ccmEssentialLogCuspBCF (z : ℂ) :
    AnalyticAt ℂ ccmEssentialLogCuspBCF z := by
  unfold ccmEssentialLogCuspBCF
  change AnalyticAt ℂ
    ((fun _ : ℂ => ((2 * Real.sqrt 2 : ℝ) : ℂ)) •
      (fun w : ℂ => NormedSpace.exp
        (-(Complex.exp (-Complex.I * w)) • ccmUnitClampBCF))) z
  apply AnalyticAt.smul analyticAt_const
  apply (NormedSpace.exp_analytic _).comp
  have hexp : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp (-Complex.I * w)) z := by
    have hlin : AnalyticAt ℂ
        (fun w : ℂ => -Complex.I * w) z :=
      analyticAt_const.mul analyticAt_id
    exact hlin.cexp'
  exact hexp.neg.smul analyticAt_const

theorem analyticAt_ccmEssentialLogCusp (z : ℂ) :
    AnalyticAt ℂ ccmEssentialLogCusp z := by
  change AnalyticAt ℂ
    ((BoundedContinuousFunction.toLp 2 ccmCuspMeasure ℂ) ∘
      ccmEssentialLogCuspBCF) z
  exact ((BoundedContinuousFunction.toLp 2 ccmCuspMeasure ℂ).analyticAt
    (ccmEssentialLogCuspBCF z)).comp
      (analyticAt_ccmEssentialLogCuspBCF z)

theorem analyticOnNhd_ccmEssentialLogCusp :
    AnalyticOnNhd ℂ ccmEssentialLogCusp Set.univ :=
  fun z _hz => analyticAt_ccmEssentialLogCusp z

def bcfEvalRingHom (t : ℝ) : (ℝ →ᵇ ℂ) →+* ℂ where
  toFun f := f t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_bcfEvalRingHom (t : ℝ) :
    Continuous (bcfEvalRingHom t) :=
  (BoundedContinuousFunction.lipschitz_eval_const t).continuous

theorem ccmEssentialLogCuspBCF_apply (z : ℂ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ccmEssentialLogCuspBCF z t =
      ((2 * Real.sqrt 2 : ℝ) : ℂ) *
        Complex.exp (-(t : ℂ) * Complex.exp (-Complex.I * z)) := by
  rw [ccmEssentialLogCuspBCF]
  change ((2 * Real.sqrt 2 : ℝ) : ℂ) *
      (bcfEvalRingHom t) (NormedSpace.exp
        (-(Complex.exp (-Complex.I * z)) • ccmUnitClampBCF)) = _
  rw [NormedSpace.map_exp (bcfEvalRingHom t)
    (continuous_bcfEvalRingHom t)]
  congr 1
  rw [Complex.exp_eq_exp_ℂ]
  change NormedSpace.exp
      ((bcfEvalRingHom t)
        (-(NormedSpace.exp (-Complex.I * z)) • ccmUnitClampBCF)) =
    NormedSpace.exp (-(t : ℂ) * NormedSpace.exp (-Complex.I * z))
  congr 1
  change -(NormedSpace.exp (-Complex.I * z)) * ccmUnitClampBCF t =
    -(t : ℂ) * NormedSpace.exp (-Complex.I * z)
  rw [ccmUnitClampBCF_apply]
  rw [max_eq_right (le_min ht0 zero_le_one),
    min_eq_left ht1]
  ring

theorem ccmEssentialLogCusp_periodic :
    Function.Periodic ccmEssentialLogCusp (2 * Real.pi) := by
  intro z
  have hturn :
      Complex.exp (-Complex.I * (z + 2 * Real.pi)) =
        Complex.exp (-Complex.I * z) := by
    rw [show -Complex.I * (z + 2 * Real.pi) =
        -Complex.I * z + -(2 * Real.pi * Complex.I) by ring,
      Complex.exp_add]
    have hone : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (1 : ℤ) using 1
      norm_num
    rw [Complex.exp_neg, hone]
    simp
  unfold ccmEssentialLogCusp
  congr 1
  simp only [ccmEssentialLogCuspBCF, hturn]

theorem norm_ccmEssentialLogCuspBCF_imaginary
    (y : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖ccmEssentialLogCuspBCF (Complex.I * y) t‖ =
      ccmEssentialBoundaryLayer (Real.exp (-y)) t := by
  rw [ccmEssentialLogCuspBCF_apply _ ht0 ht1,
    Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)),
    Complex.norm_exp]
  have hinner :
      Complex.exp (-Complex.I * (Complex.I * (y : ℂ))) =
        (Real.exp y : ℂ) := by
    rw [show -Complex.I * (Complex.I * (y : ℂ)) = (y : ℂ) by
      rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
      simp,
      Complex.ofReal_exp]
  rw [hinner]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [ccmEssentialBoundaryLayer]
  congr 2
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

theorem norm_ccmEssentialLogCusp_imaginary_sq (y : ℝ) :
    ‖ccmEssentialLogCusp (Complex.I * y)‖ ^ 2 =
      ccmEssentialBoundaryLayerEnergy (Real.exp (-y)) := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq,
    ccmEssentialBoundaryLayerEnergy]
  apply integral_congr_ae
  filter_upwards
    [BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞)) ccmCuspMeasure ℂ
      (ccmEssentialLogCuspBCF (Complex.I * y)),
     ae_restrict_mem measurableSet_Ioc] with t hcoe ht
  change ‖ccmEssentialLogCusp (Complex.I * y) t‖ ^ 2 =
    ccmEssentialBoundaryLayer (Real.exp (-y)) t ^ 2
  rw [show ccmEssentialLogCusp (Complex.I * y) t =
      ccmEssentialLogCuspBCF (Complex.I * y) t by
        exact hcoe]
  rw [norm_ccmEssentialLogCuspBCF_imaginary y ht.1.le ht.2]

theorem ccmEssentialLogCusp_fourUnitDensity :
    Tendsto
      (HTGeometry.logarithmicCuspBoundaryDensity
        ccmEssentialLogCusp)
      atTop (nhds 4) := by
  have hexp : Tendsto (fun y : ℝ => Real.exp (-y))
      atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall fun y => Real.exp_pos (-y)⟩
  have hlimit := ccmEssentialBoundaryLayer_fourUnitDensity.comp hexp
  convert hlimit using 1
  funext y
  rw [HTGeometry.logarithmicCuspBoundaryDensity,
    show (y : ℂ) * Complex.I = Complex.I * y by ring,
    norm_ccmEssentialLogCusp_imaginary_sq]
  rfl

theorem ccmEssentialLogCusp_descended_not_meromorphic :
    ¬ MeromorphicAt
      (HTGeometry.normedPeriodicCuspFunction
        (2 * Real.pi) ccmEssentialLogCusp) 0 := by
  intro hmero
  have hperiod : Function.Periodic ccmEssentialLogCusp
      (((2 * Real.pi : ℝ) : ℂ)) := by
    convert ccmEssentialLogCusp_periodic using 1
    norm_num
  exact
    (ccmFourUnit_not_two_pi_periodic_meromorphic_logarithmicCuspBoundary
      hperiod hmero)
      ccmEssentialLogCusp_fourUnitDensity

/-- **Sharpness of the meromorphic CCM cusp exclusion.**  The surviving
infinite-dimensional essential category is nonempty: an entire one-loop
logarithmic cusp has four-unit density, while its punctured-disk descent is
necessarily nonmeromorphic. -/
theorem exists_entire_twoPi_periodic_fourUnit_essential_Hilbert_cusp :
    ∃ f : ℂ → Lp ℂ 2 ccmCuspMeasure,
      AnalyticOnNhd ℂ f Set.univ ∧
      Function.Periodic f (2 * Real.pi) ∧
      Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f)
        atTop (nhds 4) ∧
      ¬ MeromorphicAt
        (HTGeometry.normedPeriodicCuspFunction (2 * Real.pi) f) 0 := by
  exact ⟨ccmEssentialLogCusp,
    analyticOnNhd_ccmEssentialLogCusp,
    ccmEssentialLogCusp_periodic,
    ccmEssentialLogCusp_fourUnitDensity,
    ccmEssentialLogCusp_descended_not_meromorphic⟩

end RHTower
