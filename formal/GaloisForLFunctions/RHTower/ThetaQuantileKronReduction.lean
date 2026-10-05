import GaloisForLFunctions.RHTower.ThetaQuantileScoreProjection
import GaloisForLFunctions.RHTower.ThetaQuantileChargedPort

/-!
# Kron reduction of the theta one-port: the universal clock port

Short the positive metric `M_h` over the constant mode: with `h₀ = ∫₀¹ h > 0`, `b = P h` and

`G = T − (b ⊗ b)/h₀`,   `γ(f) = ∫₀¹ i V f = i ∫₀¹ (1/2 − t) f(t) dt`,

the quadratic form of `G` on `H₀` is the weighted variance `∫ h|f|² − |∫ h f|²/h₀`, strictly
positive but not bounded below, and the full identity `M_h B = iV` gives

`T D = A − b β`,   `⟨b, D f⟩ + h₀ β(f) = γ(f)`,   `G D = A − (b/h₀) γ`.                (8)

In Fourier coordinates `b_n = −a_|n|`, `γ(e_n) = −1/(2πn)`, so
`(G D)_(m,n) = 1_{m=n}/(2πn) − a_|m|/(2πn h₀)` (9).  The clock functional stays singular in the
`G`-energy; a nonreal eigenmode must have `γ(f) ≠ 0`; every divisor eigenmode satisfies the
boundary-work law (10); and for the normalized root primitive `g = V f`,
`⟨f, G f⟩ = |z|²(E − |I|²/h₀)` (11), which turns (10) into the root-energy law `Re I = (Im z) E`.
-/

namespace RHTower

open MeasureTheory Filter Topology Set HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The shorted metric and the clock functional -/

/-- The profile mass `h₀ = ∫₀¹ h`. -/
def thetaProfileMass : ℝ := metricEnergy constMode

theorem thetaProfileMass_eq : thetaProfileMass = ∫ t, metricReal t ∂unitIntervalMeasure := by
  rw [thetaProfileMass, metricEnergy]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_unitFourierBasis 0] with t ht
  rw [show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, ht, fourierMode_zero, norm_one, one_pow, mul_one]

theorem thetaProfileMass_pos : 0 < thetaProfileMass :=
  metricEnergy_pos (unitFourierBasis.orthonormal.ne_zero 0)

theorem thetaProfileMass_ne_zero : (thetaProfileMass : ℂ) ≠ 0 := by exact_mod_cast thetaProfileMass_pos.ne'

theorem inner_constMode_thetaMetricOperator_constMode :
    ⟪constMode, thetaMetricOperator constMode⟫_ℂ = (thetaProfileMass : ℂ) := by
  rw [inner_thetaMetricOperator, thetaProfileMass, metricEnergy]

/-- `⟨h, f⟩ = ⟨b, f⟩` on `H₀`. -/
theorem inner_thetaMetricOperator_constMode {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪thetaMetricOperator constMode, f⟫_ℂ = ⟪onePortOutputVector, f⟫_ℂ := by
  rw [onePortOutputVector, inner_meanZeroProj_left, meanZeroProj_eq_self hf]

/-- The shorted (Kron-reduced) metric `G = T − (b ⊗ b)/h₀`. -/
def kronMetric : ThetaL2 →L[ℂ] ThetaL2 :=
  onePortMetric - ((thetaProfileMass : ℂ)⁻¹) • (innerSL ℂ onePortOutputVector).smulRight onePortOutputVector

theorem kronMetric_apply (f : ThetaL2) :
    kronMetric f = onePortMetric f - ((thetaProfileMass : ℂ)⁻¹ * ⟪onePortOutputVector, f⟫_ℂ) • onePortOutputVector := by
  simp [kronMetric, innerSL_apply_apply, smul_smul]

/-- The universal clock `γ(f) = i ⟨1, V f⟩ = ∫₀¹ i V f`. -/
def clockInput : ThetaL2 →L[ℂ] ℂ := Complex.I • (innerSL ℂ constMode ∘L pinnedVolterraCLM)

theorem clockInput_apply (f : ThetaL2) :
    clockInput f = Complex.I * ⟪constMode, pinnedVolterraCLM f⟫_ℂ := by
  simp [clockInput, innerSL_apply_apply]

theorem pinnedVolterraCLM_constMode : pinnedVolterraCLM constMode = 0 := by
  apply Lp.ext
  filter_upwards [pinnedVolterra_coeFn constMode, Lp.coeFn_zero ℂ 2 unitIntervalMeasure,
    ae_mem_Icc_unitInterval] with t h1 h2 h3
  change (pinnedVolterra constMode : ℝ → ℂ) t = _
  rw [h1, h2, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl,
    pinnedVolterraFun_unitFourierBasis_zero h3]
  rfl

theorem inner_pinnedCoordinate (f : ThetaL2) : ⟪pinnedCoordinate, f⟫_ℂ = pinnedFirstMoment f := by
  rw [inner_lp_eq, pinnedFirstMoment]
  refine integral_congr_ae ?_
  filter_upwards [pinnedCoordinate_coeFn] with t ht
  rw [ht, Complex.conj_ofReal]

/-- `⟨1, V f⟩ = ∫₀¹ (1/2 − t) f(t) dt` (the reverse pinned primitive of `1` is `1/2 − t`). -/
theorem inner_constMode_pinnedVolterraCLM (f : ThetaL2) :
    ⟪constMode, pinnedVolterraCLM f⟫_ℂ = (1 / 2 : ℂ) * pinnedMean f - pinnedFirstMoment f := by
  have hadj : pinnedVolterraCLM.adjoint = pinnedBoundaryCLM - pinnedVolterraCLM := by
    rw [← adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM, add_sub_cancel_right]
  rw [← ContinuousLinearMap.adjoint_inner_left, hadj, sub_apply, pinnedVolterraCLM_constMode,
    sub_zero, constMode_eq_pinnedOne, pinnedBoundaryCLM_pinnedOne, inner_sub_left, inner_smul_left,
    inner_pinnedCoordinate, ← constMode_eq_pinnedOne, inner_constMode_eq_pinnedMean,
    show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by rw [map_div₀, map_one, map_ofNat]]

/-- **The clock functional** `γ(f) = i ∫₀¹ (1/2 − t) f(t) dt`. -/
theorem clockInput_eq_integral (f : ThetaL2) :
    clockInput f = Complex.I * ∫ t, ((1 / 2 - t : ℝ) : ℂ) * f t ∂unitIntervalMeasure := by
  rw [clockInput_apply, inner_constMode_pinnedVolterraCLM, pinnedMean, pinnedFirstMoment, ← integral_const_mul,
    ← integral_sub ((integrable_coe f).const_mul _) (integrable_coordinate_mul f)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  push_cast
  ring

/-! ## The exact Kron identities (8) -/

theorem thetaQuotientOperator_mem_meanZeroSpace (f : ThetaL2) : thetaQuotientOperator f ∈ meanZeroSpace := by
  rw [thetaQuotientOperator_apply]; exact meanZeroProj_mem _

/-- **(8), constant row**: `⟨b, D f⟩ + h₀ β(f) = γ(f)` on `H₀`. -/
theorem inner_onePortOutputVector_thetaQuotientOperator (f : ThetaL2) :
    ⟪onePortOutputVector, thetaQuotientOperator f⟫_ℂ + (thetaProfileMass : ℂ) * onePortInput f = clockInput f := by
  have h1 : ⟪constMode, thetaMetricOperator (thetaKernelOperator f)⟫_ℂ = clockInput f := by
    rw [thetaMetricOperator_thetaKernelOperator, inner_smul_right, clockInput_apply]
  have hB : thetaKernelOperator f = thetaQuotientOperator f + onePortInput f • constMode := by
    rw [thetaQuotientOperator_apply, meanZeroProj_thetaKernelOperator, sub_add_cancel]
  rw [← h1, ← thetaMetricOperator_inner, hB, inner_add_right, inner_smul_right,
    inner_thetaMetricOperator_constMode (thetaQuotientOperator_mem_meanZeroSpace f),
    ← inner_conj_symm (thetaMetricOperator constMode) constMode,
    inner_constMode_thetaMetricOperator_constMode, Complex.conj_ofReal]
  ring

/-- **(8), shorted form**: `G D f = A f − (γ(f)/h₀) b` on `H₀`. -/
theorem kronMetric_thetaQuotientOperator {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    kronMetric (thetaQuotientOperator f) =
      onePortPrimitive f - ((thetaProfileMass : ℂ)⁻¹ * clockInput f) • onePortOutputVector := by
  rw [kronMetric_apply, onePortMetric_thetaQuotientOperator hf,
    ← inner_onePortOutputVector_thetaQuotientOperator f]
  have hM := thetaProfileMass_ne_zero
  rw [sub_sub, ← add_smul]
  congr 2
  field_simp
  ring

/-! ## The weighted variance -/

/-- `⟨f, G f⟩ = ∫ h|f|² − |∫ h f|²/h₀` on `H₀`. -/
theorem inner_kronMetric {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪f, kronMetric f⟫_ℂ =
      ((metricEnergy f - ‖⟪onePortOutputVector, f⟫_ℂ‖ ^ 2 / thetaProfileMass : ℝ) : ℂ) := by
  rw [kronMetric_apply, inner_sub_right, inner_onePortMetric_of_mem hf, inner_smul_right,
    ← inner_conj_symm f onePortOutputVector, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem inner_onePortOutputVector_eq_integral {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪onePortOutputVector, f⟫_ℂ = ∫ t, (metricReal t : ℂ) * f t ∂unitIntervalMeasure := by
  rw [← inner_thetaMetricOperator_constMode hf, thetaMetricOperator_inner, inner_lp_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_unitFourierBasis 0, coeFn_thetaMetricOperator f] with t h1 h2
  rw [show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h1, fourierMode_zero, map_one, one_mul, h2,
    metricSymbol_eq_norm]

/-- **The weighted variance** `⟨f, G f⟩ = ∫ h|f|² − |∫ h f|²/h₀`. -/
theorem inner_kronMetric_eq_variance {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪f, kronMetric f⟫_ℂ = (((∫ t, metricReal t * ‖f t‖ ^ 2 ∂unitIntervalMeasure) -
      ‖∫ t, (metricReal t : ℂ) * f t ∂unitIntervalMeasure‖ ^ 2 /
        ∫ t, metricReal t ∂unitIntervalMeasure : ℝ) : ℂ) := by
  rw [inner_kronMetric hf, inner_onePortOutputVector_eq_integral hf, ← thetaProfileMass_eq]
  rfl

/-- The variance is the metric energy of the centred vector `f − (⟨b,f⟩/h₀) 1`. -/
theorem inner_kronMetric_eq_metricEnergy {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪f, kronMetric f⟫_ℂ =
      (metricEnergy (f - ((thetaProfileMass : ℂ)⁻¹ * ⟪onePortOutputVector, f⟫_ℂ) • constMode) : ℂ) := by
  set c : ℂ := (thetaProfileMass : ℂ)⁻¹ * ⟪onePortOutputVector, f⟫_ℂ
  have hE : ∀ g : ThetaL2, (metricEnergy g : ℂ) = ⟪g, thetaMetricOperator g⟫_ℂ := fun g => by
    rw [inner_thetaMetricOperator, metricEnergy]
  have h1 : ⟪constMode, thetaMetricOperator f⟫_ℂ = ⟪onePortOutputVector, f⟫_ℂ := by
    rw [← thetaMetricOperator_inner, inner_thetaMetricOperator_constMode hf]
  have h2 : ⟪f, thetaMetricOperator constMode⟫_ℂ = (starRingEnd ℂ) ⟪onePortOutputVector, f⟫_ℂ := by
    rw [← inner_conj_symm, inner_thetaMetricOperator_constMode hf]
  rw [hE, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, ← hE, h1, h2, inner_constMode_thetaMetricOperator_constMode,
    inner_kronMetric hf]
  have hM := thetaProfileMass_ne_zero
  simp only [c, map_mul, map_inv₀, Complex.conj_ofReal]
  have hn : (‖⟪onePortOutputVector, f⟫_ℂ‖ ^ 2 : ℂ) =
      ⟪onePortOutputVector, f⟫_ℂ * (starRingEnd ℂ) ⟪onePortOutputVector, f⟫_ℂ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  push_cast
  rw [hn]
  field_simp
  ring

theorem im_inner_kronMetric {f : ThetaL2} (hf : f ∈ meanZeroSpace) : (⟪f, kronMetric f⟫_ℂ).im = 0 := by
  rw [inner_kronMetric hf, Complex.ofReal_im]

theorem re_inner_kronMetric_le {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    (⟪f, kronMetric f⟫_ℂ).re ≤ metricEnergy f := by
  rw [inner_kronMetric hf, Complex.ofReal_re]
  have := thetaProfileMass_pos
  have : 0 ≤ ‖⟪onePortOutputVector, f⟫_ℂ‖ ^ 2 / thetaProfileMass := by positivity
  linarith

/-- **Strict positivity of the shorted metric on `H₀`.** -/
theorem re_inner_kronMetric_pos {f : ThetaL2} (hf : f ∈ meanZeroSpace) (hne : f ≠ 0) :
    0 < (⟪f, kronMetric f⟫_ℂ).re := by
  rw [inner_kronMetric_eq_metricEnergy hf, Complex.ofReal_re]
  refine metricEnergy_pos fun h0 => hne ?_
  set c : ℂ := (thetaProfileMass : ℂ)⁻¹ * ⟪onePortOutputVector, f⟫_ℂ
  have hfc : f = c • constMode := sub_eq_zero.1 h0
  have hc : c = 0 := by
    have := (mem_meanZeroSpace_iff f).1 hf
    rw [hfc, inner_smul_right, inner_constMode_self, mul_one] at this
    exact this
  rw [hfc, hc, zero_smul]

/-! ## Fourier coordinates and (9) -/

theorem pinnedVolterraCLM_unitFourierBasis {n : ℤ} (hn : n ≠ 0) :
    pinnedVolterraCLM (unitFourierBasis n) =
      (2 * Real.pi * Complex.I * n : ℂ)⁻¹ • (unitFourierBasis n - constMode) := by
  apply Lp.ext
  filter_upwards [pinnedVolterra_coeFn (unitFourierBasis n),
    Lp.coeFn_smul ((2 * Real.pi * Complex.I * n : ℂ)⁻¹) (unitFourierBasis n - constMode),
    Lp.coeFn_sub (unitFourierBasis n) constMode, coeFn_unitFourierBasis n, coeFn_unitFourierBasis 0,
    ae_mem_Icc_unitInterval] with t h1 h2 h3 h4 h5 h6
  change (pinnedVolterra (unitFourierBasis n) : ℝ → ℂ) t = _
  rw [h1, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h5,
    fourierMode_zero, pinnedVolterraFun_unitFourierBasis hn h6, smul_eq_mul, div_eq_inv_mul]

/-- **`γ(e_n) = −1/(2πn)`.** -/
theorem clockInput_unitFourierBasis {n : ℤ} (hn : n ≠ 0) :
    clockInput (unitFourierBasis n) = -((1 / (2 * Real.pi * n) : ℝ) : ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [clockInput_apply, pinnedVolterraCLM_unitFourierBasis hn, inner_smul_right, inner_sub_right,
    show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, inner_unitFourierBasis, inner_unitFourierBasis,
    if_neg (Ne.symm hn), if_pos rfl]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem profileCoeff_natAbs (h : ℝ → ℝ) (n : ℤ) : profileCoeff h (n.natAbs : ℤ) = profileCoeff h n := by
  rcases Int.natAbs_eq n with hn | hn
  · rw [← hn]
  · conv_rhs => rw [hn]
    rw [profileCoeff_neg]

/-- **`b_n = −a_|n|`.** -/
theorem inner_unitFourierBasis_onePortOutputVector {n : ℤ} (hn : n ≠ 0) :
    ⟪unitFourierBasis n, onePortOutputVector⟫_ℂ = -(thetaConductance n.natAbs : ℂ) := by
  rw [onePortOutputVector, ← inner_meanZeroProj_left, meanZeroProj_unitFourierBasis hn, inner_lp_eq]
  have hae : (fun t => (starRingEnd ℂ) ((unitFourierBasis n : ℝ → ℂ) t) *
      (thetaMetricOperator constMode : ℝ → ℂ) t) =ᵐ[unitIntervalMeasure]
      fun t => ((thetaQuantileProfile t * Real.cos (2 * Real.pi * n * t) : ℝ) : ℂ) -
        Complex.I * ((thetaQuantileProfile t * Real.sin (2 * Real.pi * n * t) : ℝ) : ℂ) := by
    filter_upwards [coeFn_unitFourierBasis n, coeFn_profileVector] with t h1 h2
    rw [h1, h2, conj_fourierMode, fourierMode_eq_cos_add_sin, show 2 * Real.pi * ((-n : ℤ) : ℝ) * t =
      -(2 * Real.pi * n * t) by push_cast; ring, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hI : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn (fun t => thetaQuantileProfile t * g t) (Ioo 0 1) :=
    fun g hg => ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      (isJumpProfile_thetaNetworkProfile.intervalIntegrable_mul hg)).congr_fun
        (fun t ht => by simp only [thetaNetworkProfile_of_mem ht]) measurableSet_Ioo
  have hS : ∀ g : ℝ → ℝ, ∫ t in Ioo (0 : ℝ) 1, thetaQuantileProfile t * g t =
      ∫ t in (0 : ℝ)..1, thetaNetworkProfile t * g t := fun g => by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp only [thetaNetworkProfile_of_mem ht]
  rw [integral_congr_ae hae, unitIntervalMeasure_eq,
    integral_sub (hI _ (by fun_prop : Continuous fun t : ℝ => Real.cos (2 * Real.pi * n * t))).ofReal
      ((hI _ (by fun_prop : Continuous fun t : ℝ => Real.sin (2 * Real.pi * n * t))).ofReal.const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, hS, hS,
    isJumpProfile_thetaNetworkProfile.integral_mul_sin_eq_zero, Complex.ofReal_zero, mul_zero, sub_zero]
  rw [show (∫ t in (0 : ℝ)..1, thetaNetworkProfile t * Real.cos (2 * Real.pi * n * t)) =
    profileCoeff thetaNetworkProfile n from rfl, ← profileCoeff_natAbs, thetaConductance, jumpConductance,
    Complex.ofReal_neg, neg_neg]

/-- `⟨e_m, A e_n⟩ = 1_{m=n}/(2πn)`. -/
theorem inner_unitFourierBasis_onePortPrimitive {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪unitFourierBasis m, onePortPrimitive (unitFourierBasis n)⟫_ℂ =
      (((if m = n then 1 else 0) / (2 * Real.pi * n) : ℝ) : ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [onePortPrimitive, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, meanZeroProj_unitFourierBasis hn, inner_smul_right,
    ← inner_meanZeroProj_left, meanZeroProj_unitFourierBasis hm, pinnedVolterraCLM_unitFourierBasis hn,
    inner_smul_right, inner_sub_right, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl,
    inner_unitFourierBasis, inner_unitFourierBasis m 0, if_neg hm, sub_zero]
  by_cases hmn : m = n
  · rw [if_pos hmn, if_pos hmn]
    push_cast
    field_simp
  · rw [if_neg hmn, if_neg hmn]
    simp

/-- **(9) The shorted Schur-complement matrix**:
`(G D)_(m,n) = 1_{m=n}/(2πn) − a_|m|/(2πn h₀)` for `m, n ≠ 0`. -/
theorem inner_unitFourierBasis_kronMetric_thetaQuotientOperator {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪unitFourierBasis m, kronMetric (thetaQuotientOperator (unitFourierBasis n))⟫_ℂ =
      (((if m = n then 1 else 0) / (2 * Real.pi * n) -
        thetaConductance m.natAbs / (2 * Real.pi * n * thetaProfileMass) : ℝ) : ℂ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hM := thetaProfileMass_pos.ne'
  rw [kronMetric_thetaQuotientOperator (unitFourierBasis_mem_meanZeroSpace hn), inner_sub_right,
    inner_smul_right, inner_unitFourierBasis_onePortPrimitive hm hn, clockInput_unitFourierBasis hn,
    inner_unitFourierBasis_onePortOutputVector hm]
  push_cast
  field_simp

/-! ## Reality of neutral clock modes and the boundary-work law (10) -/

theorem im_inner_onePortPrimitive (f : ThetaL2) : (⟪f, onePortPrimitive f⟫_ℂ).im = 0 := by
  have h1 : ⟪onePortPrimitive f, f⟫_ℂ = ⟪f, onePortPrimitive f⟫_ℂ :=
    isSelfAdjoint_onePortPrimitive.isSymmetric f f
  rw [← inner_conj_symm] at h1
  exact Complex.conj_eq_iff_im.1 h1

/-- **A nonreal eigenmode must load the clock**: if `D f = μ f`, `f ∈ H₀ \ {0}` and `γ(f) = 0`, then
`μ` is real. -/
theorem im_eq_zero_of_clockInput_eq_zero {f : ThetaL2} {μ : ℂ} (hf : f ∈ meanZeroSpace) (hne : f ≠ 0)
    (hD : thetaQuotientOperator f = μ • f) (hγ : clockInput f = 0) : μ.im = 0 := by
  have h := congrArg (fun g => ⟪f, g⟫_ℂ) (kronMetric_thetaQuotientOperator hf)
  rw [hD, map_smul, inner_smul_right, hγ, mul_zero, zero_smul, sub_zero] at h
  have him := congrArg Complex.im h
  rw [Complex.mul_im, im_inner_kronMetric hf, mul_zero, zero_add, im_inner_onePortPrimitive] at him
  exact (mul_eq_zero.1 him).resolve_right (re_inner_kronMetric_pos hf hne).ne'

/-- **(10) The boundary-work law**: for a divisor eigenmode `D f = −z⁻¹ f` on `H₀`,
`(Im z/|z|²) ⟨f, G f⟩ = −(1/h₀) Im(γ(f) ⟨f, b⟩)`. -/
theorem boundaryWork_law {f : ThetaL2} {z : ℂ} (hf : f ∈ meanZeroSpace)
    (hD : thetaQuotientOperator f = (-z⁻¹) • f) :
    z.im / Complex.normSq z * (⟪f, kronMetric f⟫_ℂ).re =
      -(thetaProfileMass⁻¹ * (clockInput f * ⟪f, onePortOutputVector⟫_ℂ).im) := by
  have h := congrArg (fun g => ⟪f, g⟫_ℂ) (kronMetric_thetaQuotientOperator hf)
  rw [hD, map_smul, inner_smul_right, inner_sub_right, inner_smul_right] at h
  have him := congrArg Complex.im h
  rw [Complex.mul_im, im_inner_kronMetric hf, mul_zero, zero_add, Complex.sub_im, im_inner_onePortPrimitive,
    zero_sub, mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul, Complex.neg_im, Complex.inv_im] at him
  rw [← him]
  ring

/-! ## The normalized root primitive and (11) -/

/-- The root integral `I = ∫₀¹ V f = ⟨1, V f⟩`. -/
def rootIntegral (f : ThetaL2) : ℂ := ⟪constMode, pinnedVolterraCLM f⟫_ℂ

/-- The root energy `E = ∫₀¹ q |V f|²`. -/
def rootEnergy (f : ThetaL2) : ℝ :=
  ∫ t, thetaQuantileSpeed t * ‖pinnedVolterraFun f t‖ ^ 2 ∂unitIntervalMeasure

theorem rootIntegral_eq_integral (f : ThetaL2) :
    rootIntegral f = ∫ t, pinnedVolterraFun f t ∂unitIntervalMeasure := by
  rw [rootIntegral, inner_constMode_eq_pinnedMean, pinnedMean]
  exact integral_congr_ae (pinnedVolterra_coeFn f)

/-- `γ(f) = i I`. -/
theorem clockInput_eq_rootIntegral (f : ThetaL2) : clockInput f = Complex.I * rootIntegral f :=
  clockInput_apply f

theorem metricReal_mul_thetaQuantileSpeed (t : ℝ) : metricReal t * thetaQuantileSpeed t = 1 := by
  rw [metricReal, norm_metricSymbol, thetaQuantileSpeed_eq]
  have hk : thetaSource.k (thetaSource.quantileFun t) ≠ 0 := (thetaSource.pos_k _).ne'
  have hM := thetaSource.mass_pos.ne'
  change thetaSource.k (thetaSource.quantileFun t) / thetaSource.mass *
    (thetaSource.mass / thetaSource.k (thetaSource.quantileFun t)) = 1
  field_simp

section RootMode

variable {f : ThetaL2} {z : ℂ} (hf : f ∈ meanZeroSpace) (hz : z ≠ 0)
  (hD : thetaQuotientOperator f = (-z⁻¹) • f) (hβ : onePortInput f = -z⁻¹)
include hf hz hD hβ

omit hf in
/-- **(11b)** `∫ h g' = ⟨b, f⟩ = −h₀ − i z I`. -/
theorem inner_onePortOutputVector_root :
    ⟪onePortOutputVector, f⟫_ℂ = -(thetaProfileMass : ℂ) - Complex.I * z * rootIntegral f := by
  have h := inner_onePortOutputVector_thetaQuotientOperator f
  rw [hD, inner_smul_right, hβ, clockInput_eq_rootIntegral] at h
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  linear_combination (-z) * h - (⟪onePortOutputVector, f⟫_ℂ + (thetaProfileMass : ℂ)) * hzinv

omit hf in
/-- **The root equation** `g' + 1 = −i z q g` with `g = V f`, `g' = f`. -/
theorem root_ode_ae :
    ∀ᵐ t ∂unitIntervalMeasure, f t = -1 - Complex.I * z * (thetaQuantileSpeed t : ℂ) * pinnedVolterraFun f t := by
  have hB : thetaKernelOperator f = (-z⁻¹) • f + (-z⁻¹) • constMode := by
    have h := meanZeroProj_thetaKernelOperator f
    rw [← thetaQuotientOperator_apply, hD, hβ] at h
    rw [h, sub_add_cancel]
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  filter_upwards [thetaKernelOperator_ae f, Lp.coeFn_add ((-z⁻¹) • f) ((-z⁻¹) • constMode),
    Lp.coeFn_smul (-z⁻¹) f, Lp.coeFn_smul (-z⁻¹) constMode, coeFn_unitFourierBasis 0] with t h1 h2 h3 h4 h5
  rw [hB, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply,
    show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h5, fourierMode_zero, smul_eq_mul, smul_eq_mul] at h1
  linear_combination (-z) * h1 - (f t + 1) * hzinv

omit hf in
theorem integrable_rootEnergy :
    Integrable (fun t => thetaQuantileSpeed t * ‖pinnedVolterraFun f t‖ ^ 2) unitIntervalMeasure := by
  have hI := (integrable_metric_mul_norm_sq (f + constMode)).const_mul (‖z‖ ^ 2)⁻¹
  refine hI.congr ?_
  filter_upwards [root_ode_ae hz hD hβ, Lp.coeFn_add f constMode, coeFn_unitFourierBasis 0] with t h1 h2 h3
  rw [h2, Pi.add_apply, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h3, fourierMode_zero, h1,
    show (-1 - Complex.I * z * (thetaQuantileSpeed t : ℂ) * pinnedVolterraFun f t + 1 : ℂ) =
      -(Complex.I * z * (thetaQuantileSpeed t : ℂ) * pinnedVolterraFun f t) by ring,
    norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaQuantileSpeed_pos t)]
  have hhq := metricReal_mul_thetaQuantileSpeed t
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  simp only [metricReal] at hhq
  field_simp
  linear_combination (thetaQuantileSpeed t * ‖pinnedVolterraFun f t‖ ^ 2) * hhq

omit hf in
/-- **The root energy identity** `∫ h|g'|² = h₀ + 2 Re(i z I) + |z|² E`. -/
theorem metricEnergy_root :
    metricEnergy f = thetaProfileMass + 2 * (Complex.I * z * rootIntegral f).re + ‖z‖ ^ 2 * rootEnergy f := by
  have hg : Integrable (pinnedVolterraFun f) unitIntervalMeasure :=
    (memLp_pinnedVolterraFun f).integrable one_le_two
  have hpt : (fun t => ‖metricSymbol thetaSource t‖ * ‖f t‖ ^ 2) =ᵐ[unitIntervalMeasure]
      fun t => metricReal t + 2 * (Complex.I * z * pinnedVolterraFun f t).re +
        ‖z‖ ^ 2 * (thetaQuantileSpeed t * ‖pinnedVolterraFun f t‖ ^ 2) := by
    filter_upwards [root_ode_ae hz hD hβ] with t h1
    rw [h1]
    have hhq := metricReal_mul_thetaQuantileSpeed t
    set w := Complex.I * z * pinnedVolterraFun f t
    have hw : ‖w‖ ^ 2 = ‖z‖ ^ 2 * ‖pinnedVolterraFun f t‖ ^ 2 := by
      simp only [w, norm_mul, Complex.norm_I, one_mul]; ring
    have hrw : (-1 - Complex.I * z * (thetaQuantileSpeed t : ℂ) * pinnedVolterraFun f t : ℂ) =
        -(1 + (thetaQuantileSpeed t : ℂ) * w) := by simp only [w]; ring
    rw [hrw, norm_neg, Complex.sq_norm, Complex.normSq_apply]
    rw [Complex.sq_norm, Complex.normSq_apply] at hw
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul] at hw ⊢
    change metricReal t * _ = _
    linear_combination (2 * w.re + thetaQuantileSpeed t * (w.re * w.re + w.im * w.im)) * hhq +
      thetaQuantileSpeed t * hw
  have hm : Integrable metricReal unitIntervalMeasure :=
    (integrable_const metricBound).mono' (measurable_metricSymbol thetaSource).norm.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (metricReal_nonneg t)]; exact metricReal_le t)
  have hre : Integrable (fun t => (Complex.I * z * pinnedVolterraFun f t).re) unitIntervalMeasure :=
    (hg.const_mul (Complex.I * z)).re
  have hI3 : Integrable (fun t => ‖z‖ ^ 2 * (thetaQuantileSpeed t * ‖pinnedVolterraFun f t‖ ^ 2))
      unitIntervalMeasure := (integrable_rootEnergy hz hD hβ).const_mul _
  have hI2 : Integrable (fun t => 2 * (Complex.I * z * pinnedVolterraFun f t).re) unitIntervalMeasure :=
    hre.const_mul 2
  have hI12 : Integrable (fun t => metricReal t + 2 * (Complex.I * z * pinnedVolterraFun f t).re)
      unitIntervalMeasure := hm.add hI2
  have hre_int : ∫ t, (Complex.I * z * pinnedVolterraFun f t).re ∂unitIntervalMeasure =
      (Complex.I * z * rootIntegral f).re := by
    have h := integral_re (hg.const_mul (Complex.I * z))
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul, ← rootIntegral_eq_integral]
  rw [metricEnergy, integral_congr_ae hpt, integral_add hI12 hI3, integral_add hm hI2,
    integral_const_mul, integral_const_mul, ← thetaProfileMass_eq, hre_int]
  rfl

/-- **(11)** `⟨g', G g'⟩ = |z|² (E − |I|²/h₀)`. -/
theorem re_inner_kronMetric_root :
    (⟪f, kronMetric f⟫_ℂ).re = ‖z‖ ^ 2 * (rootEnergy f - ‖rootIntegral f‖ ^ 2 / thetaProfileMass) := by
  rw [inner_kronMetric hf, Complex.ofReal_re, metricEnergy_root hz hD hβ,
    inner_onePortOutputVector_root hz hD hβ]
  set w := Complex.I * z * rootIntegral f
  have hw : ‖w‖ ^ 2 = ‖z‖ ^ 2 * ‖rootIntegral f‖ ^ 2 := by
    simp only [w, norm_mul, Complex.norm_I, one_mul]; ring
  have hn : ‖-(thetaProfileMass : ℂ) - w‖ ^ 2 = thetaProfileMass ^ 2 + 2 * thetaProfileMass * w.re + ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hn, hw]
  have hM := thetaProfileMass_pos.ne'
  field_simp
  ring

/-- **The root-energy law** `Re I(z) = (Im z) E(z)`, recovered from (10) and (11). -/
theorem rootIntegral_re : (rootIntegral f).re = z.im * rootEnergy f := by
  have hbw := boundaryWork_law hf hD
  rw [re_inner_kronMetric_root hf hz hD hβ, clockInput_eq_rootIntegral,
    ← inner_conj_symm f onePortOutputVector, inner_onePortOutputVector_root hz hD hβ] at hbw
  set R := rootIntegral f
  have him : (Complex.I * R * (starRingEnd ℂ) (-(thetaProfileMass : ℂ) - Complex.I * z * R)).im =
      -thetaProfileMass * R.re + z.im * ‖R‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [map_sub, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im, Complex.mul_re,
      Complex.sub_im, Complex.sub_re, Complex.neg_im, Complex.neg_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have key : z.im / Complex.normSq z * (‖z‖ ^ 2 * (rootEnergy f - ‖R‖ ^ 2 / thetaProfileMass)) =
      z.im * (rootEnergy f - ‖R‖ ^ 2 / thetaProfileMass) := by
    rw [Complex.normSq_eq_norm_sq]; field_simp
  rw [key, him] at hbw
  have hM := thetaProfileMass_pos.ne'
  have h2 : -(thetaProfileMass⁻¹ * (-thetaProfileMass * R.re + z.im * ‖R‖ ^ 2)) = R.re - z.im * ‖R‖ ^ 2 / thetaProfileMass := by
    field_simp; ring
  rw [h2] at hbw
  linear_combination -hbw

end RootMode

/-! ## The actual Xi divisor -/

/-- **(10) at every Xi zero**, for the normalized charged mode `f_z`. -/
theorem boundaryWork_law_portEigenmode {z : ℂ} (hz : XiC z = 0) :
    z.im / Complex.normSq z * (⟪portEigenmode z, kronMetric (portEigenmode z)⟫_ℂ).re =
      -(thetaProfileMass⁻¹ * (clockInput (portEigenmode z) * ⟪portEigenmode z, onePortOutputVector⟫_ℂ).im) :=
  boundaryWork_law (portEigenmode_mem hz) (thetaQuotientOperator_portEigenmode hz)

/-- **(11) at every Xi zero.** -/
theorem re_inner_kronMetric_portEigenmode {z : ℂ} (hz : XiC z = 0) :
    (⟪portEigenmode z, kronMetric (portEigenmode z)⟫_ℂ).re =
      ‖z‖ ^ 2 * (rootEnergy (portEigenmode z) - ‖rootIntegral (portEigenmode z)‖ ^ 2 / thetaProfileMass) :=
  re_inner_kronMetric_root (portEigenmode_mem hz) (XiC_eq_zero_ne_zero hz)
    (thetaQuotientOperator_portEigenmode hz) (onePortInput_portEigenmode hz)

/-- **The root-energy law at every Xi zero**: `Re I(z) = (Im z) E(z)`. -/
theorem rootIntegral_re_portEigenmode {z : ℂ} (hz : XiC z = 0) :
    (rootIntegral (portEigenmode z)).re = z.im * rootEnergy (portEigenmode z) :=
  rootIntegral_re (portEigenmode_mem hz) (XiC_eq_zero_ne_zero hz)
    (thetaQuotientOperator_portEigenmode hz) (onePortInput_portEigenmode hz)

/-- A nonreal Xi zero loads the clock: `Im z ≠ 0 ⇒ γ(f_z) ≠ 0`. -/
theorem clockInput_portEigenmode_ne_zero {z : ℂ} (hz : XiC z = 0) (him : z.im ≠ 0) :
    clockInput (portEigenmode z) ≠ 0 := by
  intro h0
  have h := im_eq_zero_of_clockInput_eq_zero (portEigenmode_mem hz) (portEigenmode_ne_zero hz)
    (thetaQuotientOperator_portEigenmode hz) h0
  have hz0 := XiC_eq_zero_ne_zero hz
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at h
  exact him ((div_eq_zero_iff.1 h).resolve_right (Complex.normSq_pos.2 hz0).ne')

/-! ## The shorted metric is not bounded below -/

theorem norm_sq_eq_integral_unitInterval (g : ThetaL2) :
    ‖g‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 ∂unitIntervalMeasure := by
  have h1 : (inner ℂ g g : ℂ) = ∫ t, (inner ℂ (g t) (g t) : ℂ) ∂unitIntervalMeasure := L2.inner_def g g
  have h2 : ∀ w : ℂ, (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [h2] at h1
  rw [integral_complex_ofReal] at h1
  rw [@norm_sq_eq_re_inner ℂ, h1]
  rfl

theorem metricReal_eq_thetaQuantileProfile (t : ℝ) : metricReal t = thetaQuantileProfile t := by
  rw [metricReal, norm_metricSymbol, thetaQuantileProfile_eq]
  rfl

theorem unitIntervalMeasure_real_Ioo {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    unitIntervalMeasure.real (Ioo a b) = b - a := by
  rw [unitIntervalMeasure_eq, measureReal_restrict_apply measurableSet_Ioo, Ioo_inter_Ioo, max_eq_left ha,
    min_eq_left hb, Real.volume_real_Ioo_of_le hab]

theorem inner_indicatorConstLp_constMode {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hμ : unitIntervalMeasure (Ioo a b) ≠ ⊤) :
    ⟪(indicatorConstLp 2 measurableSet_Ioo hμ (1 : ℂ) : ThetaL2), constMode⟫_ℂ = ((b - a : ℝ) : ℂ) := by
  rw [L2.inner_indicatorConstLp_one]
  have hae : ∀ᵐ x ∂unitIntervalMeasure, x ∈ Ioo a b → (constMode : ThetaL2) x = (1 : ℂ) := by
    filter_upwards [coeFn_unitFourierBasis 0] with x hx _
    rw [show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, hx, fourierMode_zero]
  rw [setIntegral_congr_ae measurableSet_Ioo hae, setIntegral_const, unitIntervalMeasure_real_Ioo ha hb hab,
    Complex.real_smul, mul_one]

/-- **The shorted metric is not bounded below on `H₀`.** -/
theorem not_kronMetric_boundedBelow :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ f ∈ meanZeroSpace, c * ‖f‖ ^ 2 ≤ (⟪f, kronMetric f⟫_ℂ).re := by
  rintro ⟨c, hc, hbd⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (tendsto_thetaQuantileProfile_nhdsGT_zero (Iio_mem_nhds (half_pos hc)))
  set ε : ℝ := min u (1 / 4)
  have hε0 : 0 < ε := lt_min hu (by norm_num)
  have hεu : ε ≤ u := min_le_left _ _
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  have hA : ∀ t ∈ Ioo 0 ε, metricReal t < c / 2 := fun t ht => by
    rw [metricReal_eq_thetaQuantileProfile]; exact hsub ⟨ht.1, lt_of_lt_of_le ht.2 hεu⟩
  have hB : ∀ t ∈ Ioo (1 - ε) 1, metricReal t < c / 2 := fun t ht => by
    have h1 : 1 - t ∈ Ioo 0 ε := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    rw [← metricReal_one_sub ht01]; exact hA _ h1
  have hμA : unitIntervalMeasure (Ioo 0 ε) ≠ ⊤ := measure_ne_top _ _
  have hμB : unitIntervalMeasure (Ioo (1 - ε) 1) ≠ ⊤ := measure_ne_top _ _
  set fA : ThetaL2 := indicatorConstLp 2 measurableSet_Ioo hμA (1 : ℂ)
  set fB : ThetaL2 := indicatorConstLp 2 measurableSet_Ioo hμB (1 : ℂ)
  set f : ThetaL2 := fA - fB
  have hdisj : ∀ t, t ∈ Ioo 0 ε → t ∉ Ioo (1 - ε) 1 := fun t ht ht' => by linarith [ht.2, ht'.1]
  have hAc := inner_indicatorConstLp_constMode le_rfl (by linarith) hε0.le hμA
  have hBc := inner_indicatorConstLp_constMode (by linarith) le_rfl (by linarith) hμB
  have hf0 : f ∈ meanZeroSpace := by
    rw [mem_meanZeroSpace_iff, inner_sub_right, ← inner_conj_symm constMode fA, ← inner_conj_symm constMode fB,
      hAc, hBc]
    simp
  have hae : ∀ᵐ t ∂unitIntervalMeasure,
      f t = (Ioo 0 ε).indicator (fun _ => (1 : ℂ)) t - (Ioo (1 - ε) 1).indicator (fun _ => (1 : ℂ)) t := by
    filter_upwards [Lp.coeFn_sub fA fB, indicatorConstLp_coeFn (hs := measurableSet_Ioo) (hμs := hμA) (c := (1 : ℂ)),
      indicatorConstLp_coeFn (hs := measurableSet_Ioo) (hμs := hμB) (c := (1 : ℂ))] with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hfne : f ≠ 0 := by
    intro h0
    have hin : ⟪fA, f⟫_ℂ = ((ε - 0 : ℝ) : ℂ) := by
      rw [L2.inner_indicatorConstLp_one]
      have hae' : ∀ᵐ x ∂unitIntervalMeasure, x ∈ Ioo 0 ε → (f : ℝ → ℂ) x = (1 : ℂ) := by
        filter_upwards [hae] with x hx hxA
        rw [hx, indicator_of_mem hxA, indicator_of_notMem (hdisj x hxA), sub_zero]
      rw [setIntegral_congr_ae measurableSet_Ioo hae', setIntegral_const,
        unitIntervalMeasure_real_Ioo le_rfl (by linarith) hε0.le, Complex.real_smul, mul_one]
    rw [h0, inner_zero_right] at hin
    have : ((ε - 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hε0).ne'
    exact this hin.symm
  have hnorm : Integrable (fun t => ‖f t‖ ^ 2) unitIntervalMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have henergy : metricEnergy f ≤ c / 2 * ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral_unitInterval, ← integral_const_mul]
    refine integral_mono_ae (integrable_metric_mul_norm_sq f) (hnorm.const_mul _) ?_
    filter_upwards [hae] with t ht
    have hn0 := sq_nonneg ‖f t‖
    by_cases tA : t ∈ Ioo 0 ε
    · exact mul_le_mul_of_nonneg_right (hA t tA).le hn0
    by_cases tB : t ∈ Ioo (1 - ε) 1
    · exact mul_le_mul_of_nonneg_right (hB t tB).le hn0
    · rw [ht, indicator_of_notMem tA, indicator_of_notMem tB, sub_zero, norm_zero]
      simp
  have h1 := hbd f hf0
  have h2 := re_inner_kronMetric_le hf0
  have hpos : 0 < ‖f‖ ^ 2 := by have := norm_pos_iff.2 hfne; positivity
  nlinarith

/-! ## The clock stays singular in the shorted energy -/

/-- The flat clock test field `(1/2 − F(x)) 1_{|x| ≤ L}`. -/
def clockTestField (L x : ℝ) : ℂ := if |x| ≤ L then ((1 / 2 - thetaSource.cdfFun x : ℝ) : ℂ) else 0

theorem abs_half_sub_cdfFun_le (x : ℝ) : |1 / 2 - thetaSource.cdfFun x| ≤ 1 / 2 := by
  have h := thetaSource.cdfFun_mem_Ioo x
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

theorem isFlatTest_clockTestField (L : ℝ) : IsFlatTest (clockTestField L) where
  measurable := Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (Complex.continuous_ofReal.comp (continuous_const.sub thetaSource.continuous_cdfFun)).measurable
    measurable_const
  bounded := ⟨1 / 2, fun x => by
    unfold clockTestField
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_half_sub_cdfFun_le x
    · simp⟩
  compact := ⟨L, fun x hx => if_neg (not_le.2 hx)⟩

theorem clockTestField_neg (L x : ℝ) : clockTestField L (-x) = -clockTestField L x := by
  simp only [clockTestField, abs_neg]
  split_ifs
  · rw [cdfFun_thetaSource_neg]; push_cast; ring
  · simp

theorem integral_clockTestField (L : ℝ) : ∫ x, clockTestField L x = 0 := by
  have h := integral_neg_eq_self (fun x => clockTestField L x) volume
  simp only [clockTestField_neg, integral_neg] at h
  have h2 : (2 : ℂ) * ∫ x, clockTestField L x = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem integrable_norm_sq_clockTestField (L : ℝ) : Integrable fun x => ‖clockTestField L x‖ ^ 2 := by
  have hI : Integrable ((Icc (-L) L).indicator fun _ : ℝ => (1 / 4 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))
  refine hI.mono' ((isFlatTest_clockTestField L).measurable.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold clockTestField
  split_ifs with hx
  · rw [indicator_of_mem (show x ∈ Icc (-L) L from abs_le.1 hx), Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have := abs_half_sub_cdfFun_le x
    rw [abs_le] at this
    nlinarith [this.1, this.2]
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact indicator_nonneg (fun _ _ => by norm_num) x

/-- `γ(f_L) = i ∫ |u_L|²` for the pull-back `f_L` of the clock test field. -/
theorem clockInput_preFlat_clockTestField (L : ℝ) :
    clockInput (preFlat (isFlatTest_clockTestField L)) =
      Complex.I * ((∫ x, ‖clockTestField L x‖ ^ 2 : ℝ) : ℂ) := by
  set hu := isFlatTest_clockTestField L
  rw [clockInput_eq_integral, integral_unitInterval_eq_cdf (g := fun t => ((1 / 2 - t : ℝ) : ℂ) *
      (preFlat hu : ThetaL2) t)
    (((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _))]
  congr 1
  rw [← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [flatField_preFlat hu] with x hx
  have hfx : (thetaSource.normalized x : ℂ) * (preFlat hu : ThetaL2) (thetaSource.cdfFun x) = clockTestField L x := hx
  rw [Complex.real_smul, ← mul_assoc, mul_comm (thetaSource.normalized x : ℂ), mul_assoc, hfx]
  unfold clockTestField
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; push_cast; ring
  · simp

theorem cdfFun_thetaSource_zero : thetaSource.cdfFun 0 = 1 / 2 := by
  have h := cdfFun_thetaSource_neg 0
  rw [neg_zero] at h
  linarith

/-- **The clock functional is unbounded in the shorted energy**: no `C` gives
`|γ(f)| ≤ C ⟨f, G f⟩^{1/2}` on `H₀`. -/
theorem not_clockInput_bounded :
    ¬ ∃ C : ℝ, ∀ f ∈ meanZeroSpace, ‖clockInput f‖ ≤ C * Real.sqrt (⟪f, kronMetric f⟫_ℂ).re := by
  rintro ⟨C, hC⟩
  set κ : ℝ := (thetaSource.cdfFun 1 - 1 / 2) ^ 2
  have hF1 : 1 / 2 < thetaSource.cdfFun 1 := by
    rw [← cdfFun_thetaSource_zero]; exact thetaSource.strictMono_cdfFun one_pos
  have hκ : 0 < κ := by
    have : 0 < thetaSource.cdfFun 1 - 1 / 2 := by linarith
    positivity
  set L : ℝ := C ^ 2 / κ + 2
  have hL : 1 ≤ L := by
    have : 0 ≤ C ^ 2 / κ := by positivity
    linarith
  set hu := isFlatTest_clockTestField L
  set f := preFlat hu
  have hf : f ∈ meanZeroSpace := preFlat_mem_meanZeroSpace hu (integral_clockTestField L)
  set E : ℝ := ∫ x, ‖clockTestField L x‖ ^ 2
  have hγ : ‖clockInput f‖ = E := by
    rw [clockInput_preFlat_clockTestField, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  have hG : (⟪f, kronMetric f⟫_ℂ).re ≤ E := (re_inner_kronMetric_le hf).trans (metricEnergy_preFlat hu).le
  have hE : κ * (L - 1) ≤ E := by
    have h1 : ∫ x in Icc 1 L, κ ≤ ∫ x in Icc 1 L, ‖clockTestField L x‖ ^ 2 := by
      refine setIntegral_mono_on (integrableOn_const (by simp) (by simp))
        (integrable_norm_sq_clockTestField L).integrableOn measurableSet_Icc fun x hx => ?_
      have hxL : |x| ≤ L := by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2
      have hFx : thetaSource.cdfFun 1 ≤ thetaSource.cdfFun x := thetaSource.strictMono_cdfFun.monotone hx.1
      simp only [clockTestField, if_pos hxL, Complex.norm_real, Real.norm_eq_abs, sq_abs, κ]
      nlinarith
    have h2 : ∫ x in Icc 1 L, ‖clockTestField L x‖ ^ 2 ≤ E :=
      setIntegral_le_integral (integrable_norm_sq_clockTestField L) (Eventually.of_forall fun _ => sq_nonneg _)
    rw [setIntegral_const, Real.volume_real_Icc_of_le hL, smul_eq_mul] at h1
    linarith
  have hEpos : 0 < E := by
    have : 0 < κ * (L - 1) := by
      have : 0 < L - 1 := by
        have : 0 ≤ C ^ 2 / κ := by positivity
        simp only [L]; linarith
      positivity
    linarith
  have h1 := hC f hf
  rw [hγ] at h1
  have hs : Real.sqrt (⟪f, kronMetric f⟫_ℂ).re ≤ Real.sqrt E := Real.sqrt_le_sqrt hG
  have hsE := Real.sq_sqrt hEpos.le
  have hs0 := Real.sqrt_nonneg E
  have hsr := Real.sqrt_nonneg (⟪f, kronMetric f⟫_ℂ).re
  have hCE : E ≤ C ^ 2 := by
    rcases le_or_gt 0 C with hC0 | hC0
    · have h3 : E ≤ C * Real.sqrt E := h1.trans (mul_le_mul_of_nonneg_left hs hC0)
      have h4 : Real.sqrt E ≤ C := by
        by_contra hcon
        have hcon := not_le.1 hcon
        have hsp : 0 < Real.sqrt E := Real.sqrt_pos.2 hEpos
        nlinarith
      nlinarith
    · nlinarith
  have hκL : κ * (L - 1) = C ^ 2 + κ := by simp only [L]; field_simp; ring
  linarith

end

end RHTower
