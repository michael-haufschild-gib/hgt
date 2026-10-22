import GaloisForLFunctions.HTGeometry.PrimePairWallLanding
import GaloisForLFunctions.RHTower.ThetaCarrierPolarizationFisher
import GaloisForLFunctions.RHTower.MobiusThetaNativeMeyerAdmission
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.ThetaSourceGlobalStrictLogConvexity
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape

/-!
# The Cayley–theta record flatness mismatch

Two conservative contrast colligations carry the same observability law but different endpoint
orders.

* **Prime gauge.**  On `L²((-1, 1), μ_H)` with `dμ_H = (105/16) v²(1 - v²)² dv`, the multipliers
  `S_H = v`, `E_H = √(1 - v²)` and the unit state `Ω_H = 1` form the cyclic spectral model of the
  Hodge collision colligation: `μ_H` is the spectral law of `(S, Ω_H)` on the exponential clock
  pair, and `‖S_Hⁿ Ω_H‖² = m_n = 105/((2n+3)(2n+5)(2n+7))`.
* **Theta gauge.**  For the positive even theta source `k` and every real `a`, the balanced tilt
  `dν_a = Z_a⁻¹ cosh(ax) k(x) dx` carries `S_a = tanh(ax)`, `E_a = sech(ax)`, `Ω_a = 1`; for `|a| ≤
1`
  it is the balanced law of the literal theta tilts.

**(A)** Both satisfy `∑_{n<N} ‖E Sⁿ f‖² + ‖Sᴺ f‖² = ‖f‖²`, `Sᴺ → 0` strongly, and the full-history
observability maps are isometries; theta reflection makes `S_a` odd and `E_a` even.
**(B)** The prime spectral law has cubic endpoint mass `μ_H(|v| > 1 - ε)/ε³ → 35/2`, while every
theta contrast law is flat: `σ_a(|v| > 1 - ε) ≤ C_{a,N} εᴺ`.
**(C)** `nᴷ q_n(a) → 0` for every `K`, while `n³ m_n → 105/8`.
**(D)** Hence no state-preserving isometric intertwiner `U S_H = S_a U`, `U Ω_H = Ω_a` exists, even
on the cyclic orbit, and the two spectral laws differ.
-/

open MeasureTheory Filter Topology Set ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance factOneLeTwoFlatness : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-! ## Multiplier colligations -/

section Generic

variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

/-- **Complementary multipliers.**  `φ² + ψ² = 1` a.e. gives `M_φ* M_φ + M_ψ* M_ψ = 1`. -/
theorem multiplier_colligation {φ ψ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1)
    (hψ : Measurable ψ) (hc : ∀ z, |ψ z| ≤ 1) (h : ∀ᵐ z ∂ν, φ z ^ 2 + ψ z ^ 2 = 1) :
    adjoint (contractionMul ν hφ hb) ∘L contractionMul ν hφ hb
      + adjoint (contractionMul ν hψ hc) ∘L contractionMul ν hψ hc
        = ContinuousLinearMap.id ℂ _ := by
  rw [adjoint_contractionMul, adjoint_contractionMul]
  ext1 f
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (contractionMul ν hφ hb (contractionMul ν hφ hb f))
    (contractionMul ν hψ hc (contractionMul ν hψ hc f)),
    contractionMul_coeFn ν hφ hb (contractionMul ν hφ hb f), contractionMul_coeFn ν hφ hb f,
    contractionMul_coeFn ν hψ hc (contractionMul ν hψ hc f), contractionMul_coeFn ν hψ hc f, h]
    with z h1 h2 h3 h4 h5 h6
  rw [add_apply, comp_apply, comp_apply, id_apply, h1, Pi.add_apply, h2, h3, h4, h5]
  have hsum : (φ z : ℂ) * ((φ z : ℂ) * (f : α → ℂ) z) + (ψ z : ℂ) * ((ψ z : ℂ) * (f : α → ℂ) z)
      = ((φ z ^ 2 + ψ z ^ 2 : ℝ) : ℂ) * (f : α → ℂ) z := by
    push_cast
    ring
  rw [hsum, h6]
  simp

variable [IsFiniteMeasure ν]

/-- The unit state `Ω = 1` of `L²(ν)`. -/
def unitState : Lp ℂ 2 ν := (memLp_const (1 : ℂ)).toLp _

theorem unitState_coeFn : (unitState ν : α → ℂ) =ᵐ[ν] fun _ => 1 :=
  (memLp_const (1 : ℂ)).coeFn_toLp

/-- **Survival moments of the unit state.**  `‖M_φⁿ 1‖² = ∫ (φ²)ⁿ dν`. -/
theorem norm_contractionMul_pow_unitState_sq {φ : α → ℝ} (hφ : Measurable φ)
    (hb : ∀ z, |φ z| ≤ 1) (n : ℕ) :
    ‖(contractionMul ν hφ hb ^ n) (unitState ν)‖ ^ 2 = ∫ z, (φ z ^ 2) ^ n ∂ν := by
  rw [contractionMul_pow, norm_sq_Lp_two_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [contractionMul_coeFn ν (hφ.pow_const n) (abs_pow_le_one' hb n) (unitState ν),
    unitState_coeFn ν] with z h1 h2
  rw [h1, h2, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← pow_mul, ← pow_mul,
    mul_comm n 2]

end Generic

/-! ## The prime spectral colligation -/

section Prime

/-- The Hodge spectral density `(105/16) v²(1 - v²)²`. -/
def hodgeSpectralDensity (v : ℝ) : ℝ := 105 / 16 * (v ^ 2 * (1 - v ^ 2) ^ 2)

theorem hodgeSpectralDensity_nonneg (v : ℝ) : 0 ≤ hodgeSpectralDensity v := by
  unfold hodgeSpectralDensity
  positivity

theorem measurable_hodgeSpectralDensity : Measurable hodgeSpectralDensity := by
  unfold hodgeSpectralDensity
  fun_prop

/-- The Hodge spectral law `μ_H` on `(-1, 1)`. -/
def hodgeSpectralLaw : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity fun v => ENNReal.ofReal (hodgeSpectralDensity v)

theorem integral_hodgeSpectralLaw (f : ℝ → ℝ) :
    ∫ v, f v ∂hodgeSpectralLaw = ∫ v in Ioo (-1 : ℝ) 1, hodgeSpectralDensity v * f v := by
  rw [hodgeSpectralLaw, integral_withDensity_eq_integral_toReal_smul
    measurable_hodgeSpectralDensity.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hodgeSpectralDensity_nonneg v)]

theorem hodgeSpectralDensity_eq (v : ℝ) :
    hodgeSpectralDensity v = 1 / 2 * hodgeCollisionAmplitude v ^ 2 := by
  rw [hodgeSpectralDensity, hodgeCollisionAmplitude_sq]
  ring

/-- **The spectral law of the Hodge collision state.**  For bounded measurable `F`,
`∬ F(δ) Ω_H² dμ dμ = ∫ F dμ_H`: `μ_H` is the spectral law of `(S, Ω_H)`. -/
theorem integral_hodgeCollision_sq_mul_contrast {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ v ∈ Ioo (-1 : ℝ) 1, |F v| ≤ C) :
    ∫ z, hodgeCollisionAmplitude (cayleyContrast z.1 z.2) ^ 2 * F (cayleyContrast z.1 z.2)
        ∂expPairLaw
      = ∫ v, F v ∂hodgeSpectralLaw := by
  have hφ : Measurable fun v => hodgeCollisionAmplitude v ^ 2 * F v := by
    unfold hodgeCollisionAmplitude
    fun_prop
  have hbound : ∀ v ∈ Ioo (-1 : ℝ) 1, |hodgeCollisionAmplitude v ^ 2 * F v| ≤ 105 / 8 * C :=
    fun v hv => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hodgeCollisionAmplitude_sq_le hv) (hC v hv) (abs_nonneg _) (by norm_num)
  rw [integral_cayleyContrast_prod hφ hbound, integral_hodgeSpectralLaw, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  rw [hodgeSpectralDensity_eq]
  ring

instance isProbabilityMeasure_hodgeSpectralLaw : IsProbabilityMeasure hodgeSpectralLaw := by
  constructor
  have hint : IntegrableOn hodgeSpectralDensity (Ioo (-1) 1) :=
    (by unfold hodgeSpectralDensity; fun_prop : Continuous hodgeSpectralDensity).integrableOn_Icc
      |>.mono_set Ioo_subset_Icc_self
  have h := integral_hodgeCollision_sq_mul_contrast (F := fun _ => (1 : ℝ)) measurable_const
    (C := 1) (fun _ _ => by norm_num)
  simp only [mul_one] at h
  rw [integral_hodgeCollision_sq, integral_hodgeSpectralLaw] at h
  simp only [mul_one] at h
  rw [hodgeSpectralLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun v => hodgeSpectralDensity_nonneg v), ← h, ENNReal.ofReal_one]

/-- The unit clamp `max (-1) (min v 1)`, equal to `v` on `[-1, 1]`. -/
def unitClamp (v : ℝ) : ℝ := max (-1) (min v 1)

theorem measurable_unitClamp : Measurable unitClamp := by
  unfold unitClamp
  fun_prop

theorem abs_unitClamp_le_one (v : ℝ) : |unitClamp v| ≤ 1 := by
  unfold unitClamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem unitClamp_of_mem {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) : unitClamp v = v := by
  rw [unitClamp, min_eq_left hv.2.le, max_eq_right hv.1.le]

theorem ae_mem_hodgeSpectralLaw : ∀ᵐ v ∂hodgeSpectralLaw, v ∈ Ioo (-1 : ℝ) 1 := by
  rw [hodgeSpectralLaw]
  exact (ae_withDensity_iff (measurable_hodgeSpectralDensity.ennreal_ofReal)).mpr
    (ae_restrict_mem measurableSet_Ioo |>.mono fun v hv _ => hv)

/-- The prime survival operator `S_H f = v f`. -/
def hodgeSpectralSurvival : Lp ℂ 2 hodgeSpectralLaw →L[ℂ] Lp ℂ 2 hodgeSpectralLaw :=
  contractionMul hodgeSpectralLaw measurable_unitClamp abs_unitClamp_le_one

theorem abs_sqrt_one_sub_sq_le_one (v : ℝ) : |Real.sqrt (1 - v ^ 2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  linarith [sq_nonneg v]

/-- The prime exit operator `E_H f = √(1 - v²) f`. -/
def hodgeSpectralExit : Lp ℂ 2 hodgeSpectralLaw →L[ℂ] Lp ℂ 2 hodgeSpectralLaw :=
  contractionMul hodgeSpectralLaw ((measurable_const.sub (measurable_unitClamp.pow_const 2)).sqrt)
    fun v => abs_sqrt_one_sub_sq_le_one (unitClamp v)

theorem unitClamp_sq_le_one (v : ℝ) : unitClamp v ^ 2 ≤ 1 := by
  have h := abs_unitClamp_le_one v
  nlinarith [abs_nonneg (unitClamp v), sq_abs (unitClamp v)]

/-- `S_H* S_H + E_H* E_H = 1`. -/
theorem hodgeSpectral_colligation :
    adjoint hodgeSpectralSurvival ∘L hodgeSpectralSurvival
      + adjoint hodgeSpectralExit ∘L hodgeSpectralExit = ContinuousLinearMap.id ℂ _ :=
  multiplier_colligation _ _ _ _ _ (Eventually.of_forall fun v => by
    simp only [Pi.sub_apply]
    rw [Real.sq_sqrt (by linarith [unitClamp_sq_le_one v])]
    ring)

/-- `S_Hᴺ → 0` strongly. -/
theorem hodgeSpectral_stable (f : Lp ℂ 2 hodgeSpectralLaw) :
    Tendsto (fun N => (hodgeSpectralSurvival ^ N) f) atTop (𝓝 0) :=
  tendsto_contractionMul_pow_apply _ _ _ (ae_mem_hodgeSpectralLaw.mono fun v hv => by
    rw [unitClamp_of_mem hv]
    exact abs_lt.mpr hv) f

/-- The prime record state `Ω_H = 1`. -/
abbrev hodgeSpectralState : Lp ℂ 2 hodgeSpectralLaw := unitState hodgeSpectralLaw

/-- **(CTRFM.1).**  `‖S_Hⁿ Ω_H‖² = m_n`, the survival moments of the Hodge collision state. -/
theorem norm_hodgeSpectralSurvival_pow_sq (n : ℕ) :
    ‖(hodgeSpectralSurvival ^ n) hodgeSpectralState‖ ^ 2 = PrimeHodgeHistory.m n := by
  rw [hodgeSpectralSurvival, norm_contractionMul_pow_unitState_sq,
    ← norm_survival_pow_hodgeCollisionState_sq n, norm_collisionSurvival_pow_state_sq,
    collisionMass_expPair]
  have h1 : ∫ v, (unitClamp v ^ 2) ^ n ∂hodgeSpectralLaw = ∫ v, (v ^ 2) ^ n ∂hodgeSpectralLaw :=
    integral_congr_ae (ae_mem_hodgeSpectralLaw.mono fun v hv => by
      simp only
      rw [unitClamp_of_mem hv])
  rw [h1, ← integral_hodgeCollision_sq_mul_contrast (F := fun v => (v ^ 2) ^ n)
    ((measurable_id.pow_const 2).pow_const n) (C := 1) (fun v hv => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (sq_nonneg _) (by nlinarith [hv.1, hv.2])), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pairContrast_ae_eq] with z hz
  rw [collisionProfile_sq_eq, hz]
  ring

end Prime

/-! ## The theta colligation -/

section Theta

theorem exp_mul_abs_le_cosh_sum (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-(c * x)) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-(c * x))]
  · rw [abs_of_nonpos hx, show c * -x = -(c * x) by ring]
    linarith [Real.exp_pos (c * x)]

theorem integrable_exp_mul_theta (c : ℝ) :
    Integrable fun x => Real.exp (c * x) * thetaCuspFullSource x :=
  HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource c

/-- `e^{c|x|} cosh(ax) k(x)` is integrable for all real `c, a`. -/
theorem integrable_exp_abs_cosh_theta (c a : ℝ) :
    Integrable fun x => Real.exp (c * |x|) * Real.cosh (a * x) * thetaCuspFullSource x := by
  have hsum : Integrable fun x =>
      (Real.exp ((c + a) * x) * thetaCuspFullSource x + Real.exp ((c - a) * x) *
        thetaCuspFullSource x + Real.exp ((a - c) * x) * thetaCuspFullSource x +
          Real.exp (-(c + a) * x) * thetaCuspFullSource x) / 2 :=
    ((((integrable_exp_mul_theta _).add (integrable_exp_mul_theta _)).add
      (integrable_exp_mul_theta _)).add (integrable_exp_mul_theta _)).div_const 2
  refine hsum.mono' ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (c * |x|) * Real.cosh (a * x)).mul continuous_thetaCuspFullSource).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hk := (thetaCuspFullSource_pos_all x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.cosh_eq]
  have h1 := exp_mul_abs_le_cosh_sum c x
  have e1 : Real.exp ((c + a) * x) = Real.exp (c * x) * Real.exp (a * x) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((c - a) * x) = Real.exp (c * x) * Real.exp (-(a * x)) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp ((a - c) * x) = Real.exp (-(c * x)) * Real.exp (a * x) := by
    rw [← Real.exp_add]; ring_nf
  have e4 : Real.exp (-(c + a) * x) = Real.exp (-(c * x)) * Real.exp (-(a * x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2, e3, e4]
  have hA : 0 ≤ (Real.exp (a * x) + Real.exp (-(a * x))) / 2 := by positivity
  calc Real.exp (c * |x|) * ((Real.exp (a * x) + Real.exp (-(a * x))) / 2) * thetaCuspFullSource x
      ≤ (Real.exp (c * x) + Real.exp (-(c * x))) * ((Real.exp (a * x) + Real.exp (-(a * x))) / 2)
          * thetaCuspFullSource x := by gcongr
    _ = _ := by ring

theorem integrable_cosh_theta (a : ℝ) :
    Integrable fun x => Real.cosh (a * x) * thetaCuspFullSource x := by
  simpa using integrable_exp_abs_cosh_theta 0 a

/-- The balance mass `Z_a = ∫ cosh(ax) k(x) dx`. -/
def thetaBalanceMass (a : ℝ) : ℝ := ∫ x, Real.cosh (a * x) * thetaCuspFullSource x

theorem thetaBalanceMass_eq (a : ℝ) : thetaBalanceMass a = thetaTiltMoment a 0 := by
  have hneg : ∫ x, Real.exp (-a * x) * thetaCuspFullSource x
      = ∫ x, Real.exp (a * x) * thetaCuspFullSource x := by
    have h := thetaTiltMoment_zero_neg a
    simpa [thetaTiltMoment] using h
  rw [thetaBalanceMass, thetaTiltMoment]
  have hpt : (fun x => Real.cosh (a * x) * thetaCuspFullSource x)
      = fun x => (Real.exp (a * x) * thetaCuspFullSource x
          + Real.exp (-a * x) * thetaCuspFullSource x) / 2 := by
    funext x
    rw [Real.cosh_eq, neg_mul]
    ring
  rw [hpt, integral_div, integral_add (integrable_exp_mul_theta a) (integrable_exp_mul_theta (-a)),
    hneg]
  simp only [pow_zero, one_mul]
  ring

/-- **(CTRFM.4).**  `0 < Z_a < ∞`. -/
theorem thetaBalanceMass_pos (a : ℝ) : 0 < thetaBalanceMass a := by
  rw [thetaBalanceMass_eq]
  exact thetaTiltMoment_zero_pos_global a

/-- The balanced density `Z_a⁻¹ cosh(ax) k(x)`. -/
def thetaBalanceDensity (a x : ℝ) : ℝ :=
  Real.cosh (a * x) * thetaCuspFullSource x / thetaBalanceMass a

theorem thetaBalanceDensity_nonneg (a x : ℝ) : 0 ≤ thetaBalanceDensity a x :=
  div_nonneg (mul_nonneg (Real.cosh_pos _).le (thetaCuspFullSource_pos_all x).le)
    (thetaBalanceMass_pos a).le

theorem measurable_thetaBalanceDensity (a : ℝ) : Measurable (thetaBalanceDensity a) := by
  unfold thetaBalanceDensity
  exact ((by fun_prop : Continuous fun x : ℝ => Real.cosh (a * x)).mul
    continuous_thetaCuspFullSource).measurable.div_const _

/-- **(CTRFM.4).**  The balanced theta law `dν_a = Z_a⁻¹ cosh(ax) k(x) dx`. -/
def thetaBalanceLaw (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (thetaBalanceDensity a x)

theorem integral_thetaBalanceLaw (a : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂thetaBalanceLaw a = ∫ x, thetaBalanceDensity a x * f x := by
  rw [thetaBalanceLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_thetaBalanceDensity a).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (thetaBalanceDensity_nonneg a x)]

theorem integrable_thetaBalanceDensity (a : ℝ) : Integrable (thetaBalanceDensity a) :=
  (integrable_cosh_theta a).div_const _

theorem integral_thetaBalanceDensity (a : ℝ) : ∫ x, thetaBalanceDensity a x = 1 := by
  simp only [thetaBalanceDensity]
  rw [integral_div, ← thetaBalanceMass, div_self (thetaBalanceMass_pos a).ne']

instance isProbabilityMeasure_thetaBalanceLaw (a : ℝ) :
    IsProbabilityMeasure (thetaBalanceLaw a) := by
  constructor
  rw [thetaBalanceLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_thetaBalanceDensity a)
      (Eventually.of_forall fun x => thetaBalanceDensity_nonneg a x),
    integral_thetaBalanceDensity, ENNReal.ofReal_one]

/-- **(CTRFM.4).**  For `|a| ≤ 1`, `ν_a` is the balanced law of the literal theta tilts `±a`. -/
theorem thetaBalanceLaw_eq_balancedLaw {a : ℝ} (ha : |a| ≤ 1) :
    thetaBalanceLaw a = balancedLaw (thetaTiltProb a) (thetaTiltProb (-a)) := by
  have hna : |(-a)| ≤ 1 := by rwa [abs_neg]
  have hM := thetaTiltMoment_zero_pos a ha
  have hmeas : ∀ b : ℝ, Measurable fun x : ℝ =>
      ENNReal.ofReal (Real.exp (b * x) * thetaCuspFullSource x / thetaTiltMoment b 0) := fun b =>
    ((((by fun_prop : Continuous fun x : ℝ => Real.exp (b * x)).mul
      continuous_thetaCuspFullSource).measurable).div_const _).ennreal_ofReal
  rw [balancedLaw, thetaTiltProb_eq_withDensity ha, thetaTiltProb_eq_withDensity hna,
    ← withDensity_add_left (hmeas a), ← withDensity_smul _ ((hmeas a).add (hmeas (-a))),
    thetaBalanceLaw]
  congr 1
  funext x
  have hk := (thetaCuspFullSource_pos_all x).le
  rw [Pi.smul_apply, Pi.add_apply, thetaTiltMoment_zero_neg,
    ← ENNReal.ofReal_add (by positivity) (by positivity), smul_eq_mul,
    show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div],
    ← ENNReal.ofReal_mul (by norm_num), thetaBalanceDensity, thetaBalanceMass_eq, Real.cosh_eq]
  congr 1
  rw [neg_mul]
  field_simp

theorem continuous_tanh_real : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

theorem measurable_tanh_mul (a : ℝ) : Measurable fun x : ℝ => Real.tanh (a * x) :=
  (continuous_tanh_real.comp (continuous_const.mul continuous_id)).measurable

theorem abs_tanh_lt_one (t : ℝ) : |Real.tanh t| < 1 :=
  abs_lt.mpr ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩

theorem abs_cosh_inv_le_one (t : ℝ) : |(Real.cosh t)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.mpr (Real.cosh_pos t))]
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh t)

/-- The theta survival operator `S_a f = tanh(ax) f`. -/
def thetaSurvival (a : ℝ) : Lp ℂ 2 (thetaBalanceLaw a) →L[ℂ] Lp ℂ 2 (thetaBalanceLaw a) :=
  contractionMul (thetaBalanceLaw a) (φ := fun x => Real.tanh (a * x))
    (measurable_tanh_mul a) fun _ => (abs_tanh_lt_one _).le

/-- The theta exit operator `E_a f = sech(ax) f`. -/
def thetaExit (a : ℝ) : Lp ℂ 2 (thetaBalanceLaw a) →L[ℂ] Lp ℂ 2 (thetaBalanceLaw a) :=
  contractionMul (thetaBalanceLaw a) (φ := fun x => (Real.cosh (a * x))⁻¹)
    (by fun_prop) fun _ => abs_cosh_inv_le_one _

theorem tanh_sq_add_cosh_inv_sq (t : ℝ) : Real.tanh t ^ 2 + (Real.cosh t)⁻¹ ^ 2 = 1 := by
  have hc := (Real.cosh_pos t).ne'
  have := Real.cosh_sq t
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, inv_pow]
  field_simp
  linarith

/-- **Theorem CTRFM-A (theta gauge).**  `S_a* S_a + E_a* E_a = 1`. -/
theorem theta_colligation (a : ℝ) :
    adjoint (thetaSurvival a) ∘L thetaSurvival a + adjoint (thetaExit a) ∘L thetaExit a
      = ContinuousLinearMap.id ℂ _ :=
  multiplier_colligation _ _ _ _ _ (Eventually.of_forall fun _ => tanh_sq_add_cosh_inv_sq _)

/-- **Theorem CTRFM-A (theta gauge).**  `S_aᴺ → 0` strongly. -/
theorem theta_stable (a : ℝ) (f : Lp ℂ 2 (thetaBalanceLaw a)) :
    Tendsto (fun N => (thetaSurvival a ^ N) f) atTop (𝓝 0) :=
  tendsto_contractionMul_pow_apply _ _ _ (Eventually.of_forall fun _ => abs_tanh_lt_one _) f

/-- The theta record state `Ω_a = 1`. -/
abbrev thetaState (a : ℝ) : Lp ℂ 2 (thetaBalanceLaw a) := unitState (thetaBalanceLaw a)

/-- **(CTRFM.10).**  The theta survival moments `q_n(a) = ∫ tanh(ax)²ⁿ dν_a`. -/
def thetaSurvivalMoment (a : ℝ) (n : ℕ) : ℝ := ∫ x, (Real.tanh (a * x) ^ 2) ^ n ∂thetaBalanceLaw a

theorem norm_thetaSurvival_pow_sq (a : ℝ) (n : ℕ) :
    ‖(thetaSurvival a ^ n) (thetaState a)‖ ^ 2 = thetaSurvivalMoment a n :=
  norm_contractionMul_pow_unitState_sq _ _ _ n

end Theta

/-! ## Reflection parity -/

section Reflection

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {σ : α → α}
  (hσ : MeasurePreserving σ ν ν)

include hσ in
theorem reflection_coeFn_of_ae {f : Lp ℂ 2 ν} {F : α → ℂ} (h : (f : α → ℂ) =ᵐ[ν] F) :
    (compL2 hσ f : α → ℂ) =ᵐ[ν] F ∘ σ :=
  (compL2_coeFn hσ f).trans (h.comp_tendsto hσ.quasiMeasurePreserving.tendsto_ae)

/-- For an involution `σ`, `J M_φ J = M_{φ ∘ σ}` with `J f = f ∘ σ`. -/
theorem reflection_conj_contractionMul (hinv : ∀ z, σ (σ z) = z) {φ : α → ℝ}
    (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) :
    compL2 hσ ∘L contractionMul ν hφ hb ∘L compL2 hσ
      = contractionMul ν (hφ.comp hσ.measurable) (fun z => hb (σ z)) := by
  ext1 f
  refine Lp.ext ?_
  have h1 := reflection_coeFn_of_ae hσ (contractionMul_coeFn ν hφ hb (compL2 hσ f))
  have h2 : (fun z => (φ z : ℂ) * ((compL2 hσ f : Lp ℂ 2 ν) : α → ℂ) z) ∘ σ
      =ᵐ[ν] fun z => (φ (σ z) : ℂ) * (f : α → ℂ) z := by
    filter_upwards [reflection_coeFn_of_ae hσ (f := f) (F := (f : α → ℂ)) EventuallyEq.rfl
      |>.comp_tendsto hσ.quasiMeasurePreserving.tendsto_ae] with z hz
    simp only [Function.comp_apply] at hz ⊢
    rw [hz, hinv]
  filter_upwards [h1, h2, contractionMul_coeFn ν (hφ.comp hσ.measurable) (fun z => hb (σ z)) f]
    with z hz1 hz2 hz3
  rw [comp_apply, comp_apply, hz1, hz2, hz3]
  rfl

omit hσ in
theorem contractionMul_neg_symbol {φ : α → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) :
    contractionMul ν hφ.neg (fun z => by rw [Pi.neg_apply, abs_neg]; exact hb z)
      = -contractionMul ν hφ hb := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [contractionMul_coeFn ν hφ.neg
      (fun z => by rw [Pi.neg_apply, abs_neg]; exact hb z) f,
    contractionMul_coeFn ν hφ hb f, Lp.coeFn_neg (contractionMul ν hφ hb f)] with z h1 h2 h3
  rw [neg_apply, h1, h3]
  simp only [Pi.neg_apply]
  rw [h2]
  push_cast
  ring

end Reflection

section ThetaReflection

theorem thetaBalanceDensity_neg (a x : ℝ) :
    thetaBalanceDensity a (-x) = thetaBalanceDensity a x := by
  rw [thetaBalanceDensity, thetaBalanceDensity, mul_neg, Real.cosh_neg, thetaCuspFullSource_neg]

/-- The theta law is reflection symmetric. -/
theorem measurePreserving_neg_thetaBalanceLaw (a : ℝ) :
    MeasurePreserving (fun x : ℝ => -x) (thetaBalanceLaw a) (thetaBalanceLaw a) :=
  ⟨measurable_neg, by
    rw [thetaBalanceLaw, map_neg_withDensity]
    simp_rw [thetaBalanceDensity_neg]⟩

/-- The theta reflection `J f(x) = f(-x)`. -/
def thetaReflection (a : ℝ) : Lp ℂ 2 (thetaBalanceLaw a) →L[ℂ] Lp ℂ 2 (thetaBalanceLaw a) :=
  compL2 (measurePreserving_neg_thetaBalanceLaw a)

/-- **Theorem CTRFM-A, parity.**  `J S_a J = -S_a`. -/
theorem thetaReflection_conj_survival (a : ℝ) :
    thetaReflection a ∘L thetaSurvival a ∘L thetaReflection a = -thetaSurvival a := by
  rw [thetaReflection, thetaSurvival, reflection_conj_contractionMul _ (fun x => neg_neg x),
    ← contractionMul_neg_symbol]
  exact contractionMul_congr _ _ _ _ _ (Eventually.of_forall fun x => by
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [mul_neg, Real.tanh_neg])

/-- **Theorem CTRFM-A, parity.**  `J E_a J = E_a`. -/
theorem thetaReflection_conj_exit (a : ℝ) :
    thetaReflection a ∘L thetaExit a ∘L thetaReflection a = thetaExit a := by
  rw [thetaReflection, thetaExit, reflection_conj_contractionMul _ (fun x => neg_neg x)]
  exact contractionMul_congr _ _ _ _ _ (Eventually.of_forall fun x => by
    simp only [Function.comp_apply]
    rw [mul_neg, Real.cosh_neg])

/-- The theta exit vectors `e_n = E_a S_aⁿ Ω_a`. -/
def thetaExitVector (a : ℝ) (n : ℕ) : Lp ℂ 2 (thetaBalanceLaw a) :=
  thetaExit a ((thetaSurvival a ^ n) (thetaState a))

theorem thetaExitVector_coeFn (a : ℝ) (n : ℕ) :
    (thetaExitVector a n : ℝ → ℂ) =ᵐ[thetaBalanceLaw a]
      fun x => (((Real.cosh (a * x))⁻¹ * Real.tanh (a * x) ^ n : ℝ) : ℂ) := by
  have hS : (((thetaSurvival a ^ n) (thetaState a) : Lp ℂ 2 (thetaBalanceLaw a)) : ℝ → ℂ)
      =ᵐ[thetaBalanceLaw a] fun x => ((Real.tanh (a * x) ^ n : ℝ) : ℂ) * 1 := by
    rw [thetaSurvival, contractionMul_pow]
    filter_upwards [contractionMul_coeFn _ ((measurable_tanh_mul a).pow_const n)
      (abs_pow_le_one' (fun _ => (abs_tanh_lt_one _).le) n) (thetaState a),
      unitState_coeFn (thetaBalanceLaw a)] with x h1 h2
    rw [h1, h2]
  filter_upwards [contractionMul_coeFn (thetaBalanceLaw a) (φ := fun x => (Real.cosh (a * x))⁻¹)
    (by fun_prop) (fun _ => abs_cosh_inv_le_one _) ((thetaSurvival a ^ n) (thetaState a)), hS]
    with x h1 h2
  rw [thetaExitVector, thetaExit, h1, h2]
  push_cast
  ring

/-- **Theorem CTRFM-A, parity.**  `J Ω_a = Ω_a` and `J e_n = (-1)ⁿ e_n`. -/
theorem thetaReflection_state_and_exit (a : ℝ) :
    thetaReflection a (thetaState a) = thetaState a ∧
      ∀ n, thetaReflection a (thetaExitVector a n) = ((-1 : ℂ) ^ n) • thetaExitVector a n := by
  refine ⟨?_, fun n => ?_⟩
  · refine Lp.ext ?_
    filter_upwards [reflection_coeFn_of_ae (measurePreserving_neg_thetaBalanceLaw a)
      (unitState_coeFn (thetaBalanceLaw a)), unitState_coeFn (thetaBalanceLaw a)] with x h1 h2
    rw [thetaReflection, h1, h2]
    rfl
  · refine Lp.ext ?_
    filter_upwards [reflection_coeFn_of_ae (measurePreserving_neg_thetaBalanceLaw a)
      (thetaExitVector_coeFn a n), Lp.coeFn_smul ((-1 : ℂ) ^ n) (thetaExitVector a n),
      thetaExitVector_coeFn a n] with x h1 h2 h3
    rw [thetaReflection, h1, h2, Pi.smul_apply, h3, Function.comp_apply, smul_eq_mul, mul_neg,
      Real.cosh_neg, Real.tanh_neg]
    push_cast
    rw [neg_pow]
    ring

end ThetaReflection

/-! ## Theorem B: finite-order versus flat endpoints -/

section Endpoint

/-- **(CTRFM.7), exact form.**  `μ_H(|v| > 1 - ε) = (105/8) ε³ (4/3 - 3ε + 13ε²/5 - ε³ + ε⁴/7)`. -/
theorem hodgeSpectralLaw_endpoint {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    hodgeSpectralLaw.real {v : ℝ | 1 - ε < |v|}
      = 105 / 8 * ε ^ 3 * (4 / 3 - 3 * ε + 13 / 5 * ε ^ 2 - ε ^ 3 + ε ^ 4 / 7) := by
  have hA : MeasurableSet {v : ℝ | 1 - ε < |v|} := measurableSet_lt measurable_const measurable_abs
  have hcont : Continuous hodgeSpectralDensity := by
    unfold hodgeSpectralDensity
    fun_prop
  rw [← integral_indicator_one hA, integral_hodgeSpectralLaw]
  have hi : IntegrableOn (fun v => hodgeSpectralDensity v * {v : ℝ | 1 - ε < |v|}.indicator 1 v)
      (Ioo (-1) 1) := by
    refine (integrable_const (105 / 16 : ℝ)).mono'
      ((hcont.measurable.mul (measurable_one.indicator hA)).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun v hv => ?_)
    have h1 : v ^ 2 * (1 - v ^ 2) ^ 2 ≤ 1 := by
      have h2 : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
      have : (1 - v ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
      nlinarith [sq_nonneg v]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hodgeSpectralDensity_nonneg v)]
    refine (mul_le_of_le_one_right (hodgeSpectralDensity_nonneg v) ?_).trans ?_
    · by_cases hmem : v ∈ {v : ℝ | 1 - ε < |v|} <;> simp [hmem]
    · rw [hodgeSpectralDensity]
      linarith
  rw [integral_Ioo_of_even hi fun v => by
    simp only [Set.indicator, Set.mem_setOf_eq, abs_neg, Pi.one_apply]
    rw [hodgeSpectralDensity, hodgeSpectralDensity, neg_sq]]
  have hset : ∫ v in Ioo (0 : ℝ) 1, hodgeSpectralDensity v * {v : ℝ | 1 - ε < |v|}.indicator 1 v
      = ∫ v in Ioo (1 - ε) 1, hodgeSpectralDensity v := by
    rw [setIntegral_congr_fun measurableSet_Ioo (g := (Ioi (1 - ε)).indicator hodgeSpectralDensity)
      fun v hv => by
        have hv0 : 0 < v := hv.1
        by_cases h : 1 - ε < v
        · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | 1 - ε < |v|} by
            show 1 - ε < |v|; rw [abs_of_pos hv0]; exact h),
            Set.indicator_of_mem (show v ∈ Ioi (1 - ε) from h), Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | 1 - ε < |v|} by
            show ¬(1 - ε < |v|); rw [abs_of_pos hv0]; exact h),
            Set.indicator_of_notMem (show v ∉ Ioi (1 - ε) from h), mul_zero],
      setIntegral_indicator measurableSet_Ioi]
    have hI : Ioo (0 : ℝ) 1 ∩ Ioi (1 - ε) = Ioo (1 - ε) 1 := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [hI]
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v => 105 / 16 * (v ^ 3 / 3 - 2 * v ^ 5 / 5 + v ^ 7 / 7))
      (fun v _ => by
        have h := ((((hasDerivAt_pow 3 v).div_const 3).sub
          (((hasDerivAt_pow 5 v).const_mul 2).div_const 5)).add
            ((hasDerivAt_pow 7 v).div_const 7)).const_mul (105 / 16 : ℝ)
        refine h.congr_deriv ?_
        rw [hodgeSpectralDensity]
        push_cast
        ring)
      (hcont.intervalIntegrable _ _)]
  ring

/-- **(CTRFM.7).**  `μ_H(|v| > 1 - ε)/ε³ → 35/2` as `ε → 0⁺`. -/
theorem tendsto_hodgeSpectralLaw_endpoint :
    Tendsto (fun ε => hodgeSpectralLaw.real {v : ℝ | 1 - ε < |v|} / ε ^ 3) (𝓝[>] 0)
      (𝓝 (35 / 2)) := by
  have hpoly : Tendsto (fun ε : ℝ => 105 / 8 * (4 / 3 - 3 * ε + 13 / 5 * ε ^ 2 - ε ^ 3 + ε ^ 4 / 7))
      (𝓝[>] 0) (𝓝 (35 / 2)) := by
    have h : Continuous fun ε : ℝ =>
        105 / 8 * (4 / 3 - 3 * ε + 13 / 5 * ε ^ 2 - ε ^ 3 + ε ^ 4 / 7) := by
      fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    convert this using 2
    norm_num
  refine hpoly.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hne : ε ≠ 0 := hε.1.ne'
  rw [hodgeSpectralLaw_endpoint hε.1 hε.2.le]
  field_simp

theorem abs_tanh_eq (t : ℝ) : |Real.tanh t| = Real.tanh |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.cosh_pos t).le
  · rw [abs_of_nonpos ht, abs_of_nonpos, Real.tanh_neg]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr ht) (Real.cosh_pos t).le

/-- Near the contrast boundary the clock is far out: `|tanh t| > 1 - ε` forces `e^{-2|t|} < ε`. -/
theorem exp_neg_two_abs_lt_of_tanh {t ε : ℝ} (hε : ε < 1) (h : 1 - ε < |Real.tanh t|) :
    Real.exp (-(2 * |t|)) < ε := by
  rw [abs_tanh_eq, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq] at h
  set u := Real.exp (-|t|) with hu_def
  have hu : 0 < u := Real.exp_pos _
  have hE : Real.exp |t| = u⁻¹ := by rw [hu_def, Real.exp_neg, inv_inv]
  rw [hE] at h
  have hkey : (u⁻¹ - u) / 2 / ((u⁻¹ + u) / 2) = (1 - u ^ 2) / (1 + u ^ 2) := by
    field_simp
  rw [hkey, lt_div_iff₀ (by positivity)] at h
  have hsq : Real.exp (-(2 * |t|)) = u ^ 2 := by
    rw [hu_def, ← Real.exp_nat_mul]
    ring_nf
  rw [hsq]
  nlinarith [sq_nonneg u]

/-- The theta contrast law `σ_a = tanh(a·)_* ν_a`. -/
def thetaContrastLaw (a : ℝ) : Measure ℝ :=
  Measure.map (fun x => Real.tanh (a * x)) (thetaBalanceLaw a)

/-- The exponential moment constant `C_{a,N} = ∫ e^{2N|a||x|} dν_a`. -/
def thetaEndpointConstant (a : ℝ) (N : ℕ) : ℝ :=
  ∫ x, Real.exp (2 * N * |a| * |x|) ∂thetaBalanceLaw a

theorem integrable_exp_abs_thetaBalanceLaw (a c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|)) (thetaBalanceLaw a) := by
  rw [thetaBalanceLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_thetaBalanceDensity a).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine ((integrable_exp_abs_cosh_theta c a).div_const (thetaBalanceMass a)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (thetaBalanceDensity_nonneg a x), thetaBalanceDensity]
  ring

/-- Chebyshev's endpoint bound `ν_a(|tanh(ax)| > 1 - ε) ≤ C_{a,N} εᴺ`. -/
theorem thetaBalanceLaw_real_endpoint_le (a : ℝ) (N : ℕ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    (thetaBalanceLaw a).real {x : ℝ | 1 - ε < |Real.tanh (a * x)|}
      ≤ thetaEndpointConstant a N * ε ^ N := by
  have hA : MeasurableSet {x : ℝ | 1 - ε < |Real.tanh (a * x)|} :=
    measurableSet_lt measurable_const (measurable_tanh_mul a).abs
  rw [← integral_indicator_one hA, thetaEndpointConstant, ← integral_mul_const]
  refine integral_mono ((integrable_const 1).indicator hA)
    ((integrable_exp_abs_thetaBalanceLaw a _).mul_const _) fun x => ?_
  by_cases hx : x ∈ {x : ℝ | 1 - ε < |Real.tanh (a * x)|}
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    have h := exp_neg_two_abs_lt_of_tanh hε.2 hx
    rw [abs_mul] at h
    have hpow : Real.exp (-(2 * (|a| * |x|))) ^ N ≤ ε ^ N :=
      pow_le_pow_left₀ (Real.exp_pos _).le h.le N
    rw [← Real.exp_nat_mul] at hpow
    have h1 : Real.exp (2 * N * |a| * |x|) * Real.exp (N * -(2 * (|a| * |x|))) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    nlinarith [Real.exp_pos (2 * N * |a| * |x|), Real.exp_pos (N * -(2 * (|a| * |x|)))]
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hε.1.le N)

/-- **(CTRFM.8).**  Every theta contrast law is flat at the boundary: `σ_a(|v| > 1 - ε) ≤ C εᴺ`. -/
theorem thetaContrastLaw_endpoint_le (a : ℝ) (N : ℕ) :
    ∃ C, ∀ ε ∈ Ioo (0 : ℝ) 1, (thetaContrastLaw a).real {v : ℝ | 1 - ε < |v|} ≤ C * ε ^ N := by
  refine ⟨thetaEndpointConstant a N, fun ε hε => ?_⟩
  have hA : MeasurableSet {v : ℝ | 1 - ε < |v|} := measurableSet_lt measurable_const measurable_abs
  rw [thetaContrastLaw, measureReal_def, Measure.map_apply (measurable_tanh_mul a) hA,
    ← measureReal_def]
  exact thetaBalanceLaw_real_endpoint_le a N hε

/-- **(CTRFM.8), centre.**  At `a = 0` the contrast law charges no endpoint neighbourhood. -/
theorem thetaContrastLaw_zero_endpoint {ε : ℝ} (hε : ε < 1) :
    (thetaContrastLaw 0).real {v : ℝ | 1 - ε < |v|} = 0 := by
  have hA : MeasurableSet {v : ℝ | 1 - ε < |v|} := measurableSet_lt measurable_const measurable_abs
  rw [thetaContrastLaw, measureReal_def, Measure.map_apply (measurable_tanh_mul 0) hA]
  have hempty : (fun x : ℝ => Real.tanh (0 * x)) ⁻¹' {v : ℝ | 1 - ε < |v|} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, zero_mul, Real.tanh_zero, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    linarith
  rw [hempty, measure_empty, ENNReal.toReal_zero]

end Endpoint

/-! ## Theorem C and Corollary D -/

section Moments

theorem tanh_sq_pow_le_one (t : ℝ) (n : ℕ) : (Real.tanh t ^ 2) ^ n ≤ 1 := by
  have h1 := abs_tanh_lt_one t
  have h2 := sq_abs (Real.tanh t)
  have h3 := abs_nonneg (Real.tanh t)
  exact pow_le_one₀ (sq_nonneg _) (by nlinarith)

theorem thetaSurvivalMoment_nonneg (a : ℝ) (n : ℕ) : 0 ≤ thetaSurvivalMoment a n :=
  integral_nonneg fun _ => by positivity

/-- `q_n(a) ≤ (1 - ε)²ⁿ + C_{a,N} εᴺ`. -/
theorem thetaSurvivalMoment_le (a : ℝ) (n N : ℕ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    thetaSurvivalMoment a n ≤ (1 - ε) ^ (2 * n) + thetaEndpointConstant a N * ε ^ N := by
  have hA : MeasurableSet {x : ℝ | 1 - ε < |Real.tanh (a * x)|} :=
    measurableSet_lt measurable_const (measurable_tanh_mul a).abs
  have hint1 : Integrable (fun x => (Real.tanh (a * x) ^ 2) ^ n) (thetaBalanceLaw a) :=
    (integrable_const 1).mono'
      (((measurable_tanh_mul a).pow_const 2).pow_const n).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact tanh_sq_pow_le_one _ n)
  have hint2 : Integrable (fun x => (1 - ε) ^ (2 * n)
      + {x : ℝ | 1 - ε < |Real.tanh (a * x)|}.indicator 1 x) (thetaBalanceLaw a) :=
    (integrable_const _).add ((integrable_const 1).indicator hA)
  have hmono : thetaSurvivalMoment a n ≤ ∫ x, ((1 - ε) ^ (2 * n)
      + {x : ℝ | 1 - ε < |Real.tanh (a * x)|}.indicator 1 x) ∂thetaBalanceLaw a := by
    refine integral_mono hint1 hint2 fun x => ?_
    by_cases hx : x ∈ {x : ℝ | 1 - ε < |Real.tanh (a * x)|}
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      have := tanh_sq_pow_le_one (a * x) n
      have : 0 ≤ (1 - ε) ^ (2 * n) := pow_nonneg (by linarith [hε.2]) _
      linarith
    · rw [Set.indicator_of_notMem hx, add_zero, pow_mul]
      have hx' : |Real.tanh (a * x)| ≤ 1 - ε := not_lt.mp hx
      refine pow_le_pow_left₀ (sq_nonneg _) ?_ n
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx' 2
  rw [integral_add (integrable_const _) ((integrable_const 1).indicator hA), integral_const,
    probReal_univ, one_smul, integral_indicator_one hA] at hmono
  linarith [thetaBalanceLaw_real_endpoint_le a N hε]

/-- **(CTRFM.11).**  The theta record is superpolynomially small: `nᴷ q_n(a) → 0`. -/
theorem tendsto_pow_mul_thetaSurvivalMoment (a : ℝ) (K : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ K * thetaSurvivalMoment a n) atTop (𝓝 0) := by
  set C := thetaEndpointConstant a (2 * K + 2)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.sqrt n ^ (2 * K) * Real.exp (-Real.sqrt n)) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * K)).comp hsqrt
  have h2 : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hup := h1.add h2
  rw [zero_add] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg n) K)
      (thetaSurvivalMoment_nonneg a n)) ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hε : (Real.sqrt n)⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hs, inv_lt_one_of_one_lt₀ hs1⟩
  have hq := thetaSurvivalMoment_le a n (2 * K + 2) hε
  have hexp : (1 - (Real.sqrt n)⁻¹) ^ (2 * n) ≤ Real.exp (-(2 * Real.sqrt n)) := by
    have hb : 0 ≤ 1 - (Real.sqrt n)⁻¹ := by linarith [hε.2]
    calc (1 - (Real.sqrt n)⁻¹) ^ (2 * n) ≤ Real.exp (-(Real.sqrt n)⁻¹) ^ (2 * n) :=
          pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp (-(Real.sqrt n)⁻¹)]) _
      _ = Real.exp (-(2 * Real.sqrt n)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          rw [show (2 : ℝ) * n * -(Real.sqrt n)⁻¹ = -(2 * (n / Real.sqrt n)) by ring,
            Real.div_sqrt]
  have hpow : (Real.sqrt n)⁻¹ ^ (2 * K + 2) = ((n : ℝ) ^ (K + 1))⁻¹ := by
    rw [inv_pow, show 2 * K + 2 = 2 * (K + 1) by ring, pow_mul, hs2]
  have hnK : (n : ℝ) ^ K = Real.sqrt n ^ (2 * K) := by rw [pow_mul, hs2]
  have hC0 : 0 ≤ C := integral_nonneg fun _ => (Real.exp_pos _).le
  have hnpos : (0 : ℝ) < n := by linarith
  calc (n : ℝ) ^ K * thetaSurvivalMoment a n
      ≤ (n : ℝ) ^ K * (Real.exp (-(2 * Real.sqrt n)) + C * ((n : ℝ) ^ (K + 1))⁻¹) := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_left (hq.trans (by linarith)) (pow_nonneg hnpos.le K)
    _ ≤ Real.sqrt n ^ (2 * K) * Real.exp (-Real.sqrt n) + C / n := by
        rw [mul_add, hnK]
        refine add_le_add ?_ (le_of_eq ?_)
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (pow_nonneg hs.le _)
        · rw [← hnK, pow_succ]
          field_simp

/-- **(CTRFM.12).**  `n³ m_n → 105/8`. -/
theorem tendsto_pow_three_mul_m :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * PrimeHodgeHistory.m n) atTop (𝓝 (105 / 8)) := by
  have hc : ∀ c : ℝ, Tendsto (fun n : ℕ => 2 + c / (n : ℝ)) atTop (𝓝 2) := fun c => by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat c)
  have hprod := (((hc 3).mul (hc 5)).mul (hc 7)).inv₀ (by norm_num)
  have h := hprod.const_mul 105
  rw [show (105 : ℝ) * (2 * 2 * 2)⁻¹ = 105 / 8 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [PrimeHodgeHistory.m]
  push_cast
  field_simp

/-- **Corollary CTRFM-D, moments.**  For every `a` some survival moment differs. -/
theorem exists_survivalMoment_ne (a : ℝ) :
    ∃ n, PrimeHodgeHistory.m n ≠ thetaSurvivalMoment a n := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have h1 := tendsto_pow_mul_thetaSurvivalMoment a 3
  simp only [← h] at h1
  have := tendsto_nhds_unique tendsto_pow_three_mul_m h1
  norm_num at this

/-- **Corollary CTRFM-D, cyclic form.**  No correspondence of the marked orbits preserves the
survival norms. -/
theorem not_forall_norm_survival_eq (a : ℝ) :
    ¬∀ n, ‖(thetaSurvival a ^ n) (thetaState a)‖
      = ‖(hodgeSpectralSurvival ^ n) hodgeSpectralState‖ := by
  intro h
  obtain ⟨n, hn⟩ := exists_survivalMoment_ne a
  apply hn
  rw [← norm_hodgeSpectralSurvival_pow_sq, ← norm_thetaSurvival_pow_sq, h n]

/-- **Corollary CTRFM-D.**  No state-preserving isometric intertwiner `U S_H = S_a U`. -/
theorem no_theta_completion_intertwiner (a : ℝ)
    (U : Lp ℂ 2 hodgeSpectralLaw →L[ℂ] Lp ℂ 2 (thetaBalanceLaw a))
    (hU : ∀ f, ‖U f‖ = ‖f‖) (hΩ : U hodgeSpectralState = thetaState a)
    (hS : U ∘L hodgeSpectralSurvival = thetaSurvival a ∘L U) : False := by
  have hc : ∀ f, U (hodgeSpectralSurvival f) = thetaSurvival a (U f) := fun f => by
    have := congrArg (fun A : Lp ℂ 2 hodgeSpectralLaw →L[ℂ] Lp ℂ 2 (thetaBalanceLaw a) => A f) hS
    simpa using this
  have h : ∀ n, U ((hodgeSpectralSurvival ^ n) hodgeSpectralState)
      = (thetaSurvival a ^ n) (thetaState a) := by
    intro n
    induction n with
    | zero => simpa [one_def] using hΩ
    | succ n ih =>
      rw [pow_succ' hodgeSpectralSurvival n, mul_def, comp_apply, hc, ih, pow_succ', mul_def,
        comp_apply]
  refine not_forall_norm_survival_eq a fun n => ?_
  rw [← h n, hU]

/-- **Corollary CTRFM-D, spectral form.**  The prime and theta contrast laws differ. -/
theorem hodgeSpectralLaw_ne_thetaContrastLaw (a : ℝ) : hodgeSpectralLaw ≠ thetaContrastLaw a := by
  intro heq
  obtain ⟨C, hC⟩ := thetaContrastLaw_endpoint_le a 4
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), hodgeSpectralLaw.real {v : ℝ | 1 - ε < |v|} / ε ^ 3 ≤ C * ε := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hε3 : 0 < ε ^ 3 := pow_pos hε.1 3
    rw [div_le_iff₀ hε3, heq]
    calc (thetaContrastLaw a).real {v : ℝ | 1 - ε < |v|} ≤ C * ε ^ 4 := hC ε hε
      _ = C * ε * ε ^ 3 := by ring
  have hR : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => C * ε := continuous_const.mul continuous_id
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using this
  have := le_of_tendsto_of_tendsto tendsto_hodgeSpectralLaw_endpoint hR hle
  norm_num at this

end Moments

/-- **ULF-CTRFM-001.**  The prime and theta contrast colligations share the conservative
observability law, but the prime spectral law has cubic endpoint mass `35/2` while every theta
contrast law is flat to all orders; the theta survival record decays superpolynomially while
`n³ m_n → 105/8`, so no state-preserving isometric intertwiner exists and the laws differ. -/
theorem cayley_theta_record_flatness_mismatch :
    (∀ f, ‖observability hodgeSpectral_colligation hodgeSpectral_stable f‖ = ‖f‖) ∧
      (∀ n, ‖(hodgeSpectralSurvival ^ n) hodgeSpectralState‖ ^ 2 = PrimeHodgeHistory.m n) ∧
      (∀ a : ℝ, ∀ f, ‖observability (theta_colligation a) (theta_stable a) f‖ = ‖f‖) ∧
      (∀ a : ℝ, |a| ≤ 1 → thetaBalanceLaw a = balancedLaw (thetaTiltProb a) (thetaTiltProb (-a))) ∧
      Tendsto (fun ε => hodgeSpectralLaw.real {v : ℝ | 1 - ε < |v|} / ε ^ 3) (𝓝[>] 0)
        (𝓝 (35 / 2)) ∧
      (∀ a : ℝ, ∀ N : ℕ, ∃ C, ∀ ε ∈ Ioo (0 : ℝ) 1,
        (thetaContrastLaw a).real {v : ℝ | 1 - ε < |v|} ≤ C * ε ^ N) ∧
      (∀ a : ℝ, ∀ K : ℕ,
        Tendsto (fun n : ℕ => (n : ℝ) ^ K * thetaSurvivalMoment a n) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * PrimeHodgeHistory.m n) atTop (𝓝 (105 / 8)) ∧
      (∀ a : ℝ, hodgeSpectralLaw ≠ thetaContrastLaw a) :=
  ⟨norm_observability_apply _ _, norm_hodgeSpectralSurvival_pow_sq,
    fun _ => norm_observability_apply _ _, fun _ ha => thetaBalanceLaw_eq_balancedLaw ha,
    tendsto_hodgeSpectralLaw_endpoint, thetaContrastLaw_endpoint_le,
    tendsto_pow_mul_thetaSurvivalMoment, tendsto_pow_three_mul_m,
    hodgeSpectralLaw_ne_thetaContrastLaw⟩

end GaloisForLFunctions.HTGeometry
