import GaloisForLFunctions.RHTower.ThetaQuantileChargedPort
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.HedenmalmSourceMoments

/-!
# The Xi divisor is a two-ended domain selector

For `0 < Im z < 1` put `G_z(x) = e^{−izx} ∫_x^∞ e^{izy} ρ(y) dy` and `u_z = G_z'`.  Then `u_z`
lies in the flat energy space `L²(ℝ)`, has mean zero, first-moment charge `−i∫ x u_z = −1/z`, and
solves the flat one-port equation

`i ∫_{−∞}^x u_z = −z⁻¹ (u_z(x) + ρ(x))`

for every such `z`, whether or not `Ξ_C(z) = 0`.  With the connection coefficient
`C_z = ∫ e^{izy} ρ(y) dy = Ξ_C(z)/M`,

`G_z(x) = C_z e^{−izx} − e^{−izx} ∫_{−∞}^x e^{izy} ρ(y) dy`,

so `e^{izx} u_z(x) → −iz C_z` as `x → −∞`.  The original theta domain selects the divisor:
`∫ |u_z|²/ρ < ∞ ⟺ Ξ_C(z) = 0`; at a zero, `u_z(Q(t))/h(t)` is the normalized quotient mode `f_z`,
and off the divisor it is not square integrable.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmPrimeTranslation
  GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The flat right primitive -/

/-- The normalized character density `ρ(y) e^{izy}`. -/
def flatCharDensity (z : ℂ) (y : ℝ) : ℂ := (thetaSource.normalized y : ℂ) * sourceChar z y

theorem continuous_flatCharDensity (z : ℂ) : Continuous (flatCharDensity z) :=
  (Complex.continuous_ofReal.comp continuous_normalized_theta).mul (continuous_sourceChar z)

theorem norm_flatCharDensity (z : ℂ) (y : ℝ) :
    ‖flatCharDensity z y‖ = thetaSource.normalized y * Real.exp (-(z.im) * y) := by
  rw [flatCharDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos y), norm_sourceChar]

theorem integrable_flatCharDensity {z : ℂ} (hz : |z.im| < 1) : Integrable (flatCharDensity z) := by
  have h := (integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)).div_const
    (thetaSource.mass : ℂ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  rw [flatCharDensity, PositiveDensitySource.normalized]
  push_cast; ring

/-- **The connection coefficient** `C_z = ∫ e^{izy} ρ(y) dy`. -/
def flatConnection (z : ℂ) : ℂ := ∫ y, flatCharDensity z y

theorem flatConnection_eq {z : ℂ} (hz : |z.im| < 1) : flatConnection z = XiC z / (thetaSource.mass : ℂ) := by
  rw [← xiC_thetaSource hz, xiC, flatConnection, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [flatCharDensity, PositiveDensitySource.normalized]
  push_cast; ring

/-- **The right primitive** `G_z(x) = e^{−izx} ∫_x^∞ e^{izy} ρ(y) dy`. -/
def flatPrimitiveMode (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * z) * x) * ∫ y in Ioi x, flatCharDensity z y

/-- **The flat mode** `u_z = −izG_z − ρ`. -/
def flatMode (z : ℂ) (x : ℝ) : ℂ := -(Complex.I * z) * flatPrimitiveMode z x - thetaSource.normalized x

theorem setIntegral_Ioi_eq {z : ℂ} (hz : |z.im| < 1) (x : ℝ) :
    ∫ y in Ioi x, flatCharDensity z y = flatConnection z - ∫ y in Iic x, flatCharDensity z y := by
  have h := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := x)
    (integrable_flatCharDensity hz).integrableOn (integrable_flatCharDensity hz).integrableOn
  rw [flatConnection, ← h]; ring

/-- **The connection formula (9)**: `G_z = C_z e^{−izx} − e^{−izx} ∫_{−∞}^x e^{izy} ρ`. -/
theorem flatPrimitiveMode_eq {z : ℂ} (hz : |z.im| < 1) (x : ℝ) :
    flatPrimitiveMode z x = flatConnection z * Complex.exp (-(Complex.I * z) * x) -
      Complex.exp (-(Complex.I * z) * x) * ∫ y in Iic x, flatCharDensity z y := by
  rw [flatPrimitiveMode, setIntegral_Ioi_eq hz]; ring

theorem exp_mul_sourceChar (z : ℂ) (x : ℝ) :
    Complex.exp (-(Complex.I * z) * x) * sourceChar z x = 1 := by
  rw [sourceChar, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero

/-- `G_z' = u_z`. -/
theorem hasDerivAt_flatPrimitiveMode {z : ℂ} (hz : |z.im| < 1) (x : ℝ) :
    HasDerivAt (flatPrimitiveMode z) (flatMode z x) x := by
  have hI := hasDerivAt_setIntegral_Iic (continuous_flatCharDensity z) (integrable_flatCharDensity hz) x
  have he : HasDerivAt (fun x : ℝ => Complex.exp (-(Complex.I * z) * x))
      (-(Complex.I * z) * Complex.exp (-(Complex.I * z) * x)) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (-(Complex.I * z))).cexp
    simpa [mul_comm] using this.comp_ofReal
  have hfun : flatPrimitiveMode z = fun x : ℝ => Complex.exp (-(Complex.I * z) * x) *
      (flatConnection z - ∫ y in Iic x, flatCharDensity z y) := by
    funext x; rw [flatPrimitiveMode, setIntegral_Ioi_eq hz]
  rw [hfun]
  have h := he.mul ((hasDerivAt_const x (flatConnection z)).sub hI)
  refine h.congr_deriv ?_
  show _ = -(Complex.I * z) * flatPrimitiveMode z x - thetaSource.normalized x
  rw [flatPrimitiveMode, setIntegral_Ioi_eq hz, flatCharDensity]
  simp only [Pi.sub_apply]
  have h1 := exp_mul_sourceChar z x
  linear_combination (-(thetaSource.normalized x : ℂ)) * h1

/-! ## Two-sided exponential decay of the right primitive -/

/-- The exponential envelope constant of `ρ`: `ρ(y) ≤ B e^{−|y|}`. -/
def flatEnvelopeConst : ℝ := thetaCuspDerivativeExpConstant 0 / thetaSource.mass

theorem flatEnvelopeConst_nonneg : 0 ≤ flatEnvelopeConst :=
  div_nonneg (thetaCuspDerivativeExpConstant_nonneg 0) thetaSource.mass_pos.le

theorem normalized_le_exp (y : ℝ) : thetaSource.normalized y ≤ flatEnvelopeConst * Real.exp (-|y|) := by
  have h := abs_thetaCuspFullSource_le y
  rw [abs_of_pos (thetaCuspFullSource_pos y)] at h
  show thetaSource.k y / thetaSource.mass ≤ _
  rw [div_le_iff₀ thetaSource.mass_pos, flatEnvelopeConst]
  have hM := thetaSource.mass_pos.ne'
  calc thetaSource.k y ≤ thetaCuspDerivativeExpConstant 0 * Real.exp (-|y|) := h
    _ = thetaCuspDerivativeExpConstant 0 / thetaSource.mass * Real.exp (-|y|) * thetaSource.mass := by
        field_simp

theorem norm_exp_neg_I_mul (z : ℂ) (x : ℝ) : ‖Complex.exp (-(Complex.I * z) * x)‖ = Real.exp (z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The total character mass `K = ∫ ρ(y) e^{−(Im z) y} dy`. -/
def flatCharMass (z : ℂ) : ℝ := ∫ y, ‖flatCharDensity z y‖

theorem norm_flatPrimitiveMode_le_of_nonneg {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) {x : ℝ} (hx : 0 ≤ x) :
    ‖flatPrimitiveMode z x‖ ≤ flatEnvelopeConst * Real.exp (-x) := by
  have hzabs : |z.im| < 1 := by rw [abs_of_pos hz]; exact hz1
  have hint := integrable_flatCharDensity hzabs
  rw [flatPrimitiveMode, norm_mul, norm_exp_neg_I_mul]
  have h1 : ‖∫ y in Ioi x, flatCharDensity z y‖ ≤ ∫ y in Ioi x, ‖flatCharDensity z y‖ :=
    norm_integral_le_integral_norm _
  have h2 : Real.exp (z.im * x) * ∫ y in Ioi x, ‖flatCharDensity z y‖ ≤
      ∫ y in Ioi x, flatEnvelopeConst * Real.exp (-y) := by
    rw [← integral_const_mul]
    have hexpint : IntegrableOn (fun y : ℝ => flatEnvelopeConst * Real.exp (-y)) (Ioi x) := by
      have h0 : IntegrableOn (fun y : ℝ => flatEnvelopeConst * Real.exp (-1 * y)) (Ioi x) :=
        (exp_neg_integrableOn_Ioi x one_pos).const_mul flatEnvelopeConst
      exact IntegrableOn.congr_fun h0 (fun y _ => by simp) measurableSet_Ioi
    refine setIntegral_mono_on (hint.norm.integrableOn.const_mul _) hexpint measurableSet_Ioi
      fun y hy => ?_
    have hy : x < y := hy
    rw [norm_flatCharDensity]
    have hρ := normalized_le_exp y
    rw [abs_of_pos (hx.trans_lt hy)] at hρ
    have he : Real.exp (z.im * x) * Real.exp (-(z.im) * y) ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.2 (by nlinarith)
    have hρ0 := (thetaSource.normalized_pos y).le
    calc Real.exp (z.im * x) * (thetaSource.normalized y * Real.exp (-(z.im) * y))
        = thetaSource.normalized y * (Real.exp (z.im * x) * Real.exp (-(z.im) * y)) := by ring
      _ ≤ thetaSource.normalized y * 1 := mul_le_mul_of_nonneg_left he hρ0
      _ ≤ flatEnvelopeConst * Real.exp (-y) := by rw [mul_one]; exact hρ
  have h3 : ∫ y in Ioi x, flatEnvelopeConst * Real.exp (-y) = flatEnvelopeConst * Real.exp (-x) := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
  calc Real.exp (z.im * x) * ‖∫ y in Ioi x, flatCharDensity z y‖
      ≤ Real.exp (z.im * x) * ∫ y in Ioi x, ‖flatCharDensity z y‖ :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ _ := h2.trans (le_of_eq h3)

theorem norm_flatPrimitiveMode_le_of_nonpos {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) {x : ℝ} (_hx : x ≤ 0) :
    ‖flatPrimitiveMode z x‖ ≤ (‖flatConnection z‖ + flatCharMass z) * Real.exp (z.im * x) := by
  have hzabs : |z.im| < 1 := by rw [abs_of_pos hz]; exact hz1
  have hint := integrable_flatCharDensity hzabs
  rw [flatPrimitiveMode_eq hzabs, ← mul_comm (Complex.exp _), ← mul_sub, norm_mul, norm_exp_neg_I_mul,
    mul_comm]
  refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add le_rfl ?_)) (Real.exp_pos _).le
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral hint.norm (Eventually.of_forall fun y => norm_nonneg _))

/-- The two-sided decay rate `c = min(Im z, 1)`. -/
def flatDecayRate (z : ℂ) : ℝ := min z.im 1

/-- The two-sided decay constant. -/
def flatDecayConst (z : ℂ) : ℝ := flatEnvelopeConst + ‖flatConnection z‖ + flatCharMass z

theorem flatCharMass_nonneg (z : ℂ) : 0 ≤ flatCharMass z := integral_nonneg fun _ => norm_nonneg _

/-- **Two-sided decay**: `‖G_z(x)‖ ≤ D e^{−c|x|}`. -/
theorem norm_flatPrimitiveMode_le {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) (x : ℝ) :
    ‖flatPrimitiveMode z x‖ ≤ flatDecayConst z * Real.exp (-(flatDecayRate z * |x|)) := by
  have hc1 : flatDecayRate z ≤ 1 := min_le_right _ _
  have hca : flatDecayRate z ≤ z.im := min_le_left _ _
  have hB := flatEnvelopeConst_nonneg
  have hK := flatCharMass_nonneg z
  rcases le_total 0 x with hx | hx
  · refine (norm_flatPrimitiveMode_le_of_nonneg hz hz1 hx).trans ?_
    rw [abs_of_nonneg hx]
    have he : Real.exp (-x) ≤ Real.exp (-(flatDecayRate z * x)) := Real.exp_le_exp.2 (by nlinarith)
    calc flatEnvelopeConst * Real.exp (-x) ≤ flatEnvelopeConst * Real.exp (-(flatDecayRate z * x)) :=
          mul_le_mul_of_nonneg_left he hB
      _ ≤ flatDecayConst z * Real.exp (-(flatDecayRate z * x)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          simp only [flatDecayConst]; linarith [norm_nonneg (flatConnection z)]
  · refine (norm_flatPrimitiveMode_le_of_nonpos hz hz1 hx).trans ?_
    rw [abs_of_nonpos hx]
    have he : Real.exp (z.im * x) ≤ Real.exp (-(flatDecayRate z * -x)) := Real.exp_le_exp.2 (by nlinarith)
    calc (‖flatConnection z‖ + flatCharMass z) * Real.exp (z.im * x)
        ≤ (‖flatConnection z‖ + flatCharMass z) * Real.exp (-(flatDecayRate z * -x)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ flatDecayConst z * Real.exp (-(flatDecayRate z * -x)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          simp only [flatDecayConst]; linarith

theorem flatDecayRate_pos {z : ℂ} (hz : 0 < z.im) : 0 < flatDecayRate z := lt_min hz one_pos

theorem integrable_exp_neg_mul_abs_flat {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * |x|))) := by
  have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hc
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [neg_mul]

theorem integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => |x| * Real.exp (-(c * |x|))) := by
  have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 hc
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [neg_mul]

theorem tendsto_mul_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => y * Real.exp (-(c * y))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (1 / c)
  rw [mul_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, id, pow_one]
  field_simp

theorem tendsto_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => |x| * Real.exp (-(c * |x|))) l (𝓝 0) :=
  (tendsto_mul_exp_neg_mul_atTop hc).comp hl

theorem tendsto_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => Real.exp (-(c * |x|))) l (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot).comp (hl.const_mul_atTop hc))

theorem integrable_normalized_complex : Integrable fun x : ℝ => (thetaSource.normalized x : ℂ) :=
  (thetaSource.integrable_k.div_const thetaSource.mass).ofReal

theorem integral_normalized_complex : ∫ x : ℝ, (thetaSource.normalized x : ℂ) = 1 := by
  rw [integral_complex_ofReal]
  have h : ∫ x, thetaSource.normalized x = 1 := by
    simp only [PositiveDensitySource.normalized]
    rw [integral_div]
    exact div_self thetaSource.mass_pos.ne'
  rw [h]; rfl

theorem tendsto_setIntegral_Iic_atBot {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun x => ∫ y in Iic x, g y) atBot (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := g) (s := fun t : ℝ => Iic (-t))
    (fun _ => measurableSet_Iic) (fun a b hab => Iic_subset_Iic.2 (neg_le_neg hab)) ⟨0, hg.integrableOn⟩
  have hempty : (⋂ t : ℝ, Iic (-t)) = (∅ : Set ℝ) := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨-y + 1, by linarith⟩
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at h
  have h2 := h.comp tendsto_neg_atBot_atTop
  refine h2.congr fun x => ?_
  simp

section Flat

variable {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1)
include hz hz1

theorem abs_im_lt_one_of_flat : |z.im| < 1 := by rw [abs_of_pos hz]; exact hz1

theorem continuous_flatPrimitiveMode : Continuous (flatPrimitiveMode z) :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_flatPrimitiveMode (abs_im_lt_one_of_flat hz hz1) x).continuousAt

theorem integrable_flatPrimitiveMode : Integrable (flatPrimitiveMode z) :=
  ((integrable_exp_neg_mul_abs_flat (flatDecayRate_pos hz)).const_mul (flatDecayConst z)).mono'
    (continuous_flatPrimitiveMode hz hz1).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_flatPrimitiveMode_le hz hz1 x)

theorem integrable_mul_flatPrimitiveMode : Integrable fun x : ℝ => (x : ℂ) * flatPrimitiveMode z x :=
  ((integrable_abs_mul_exp_neg_mul_abs (flatDecayRate_pos hz)).const_mul (flatDecayConst z)).mono'
    ((Complex.continuous_ofReal.mul (continuous_flatPrimitiveMode hz hz1))).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |x| * ‖flatPrimitiveMode z x‖ ≤ |x| * (flatDecayConst z * Real.exp (-(flatDecayRate z * |x|))) :=
            mul_le_mul_of_nonneg_left (norm_flatPrimitiveMode_le hz hz1 x) (abs_nonneg x)
        _ = flatDecayConst z * (|x| * Real.exp (-(flatDecayRate z * |x|))) := by ring)

theorem tendsto_flatPrimitiveMode {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (flatPrimitiveMode z) l (𝓝 0) := by
  have h := (tendsto_exp_neg_mul_abs (flatDecayRate_pos hz) hl).const_mul (flatDecayConst z)
  rw [mul_zero] at h
  exact squeeze_zero_norm (fun x => norm_flatPrimitiveMode_le hz hz1 x) h

theorem tendsto_mul_flatPrimitiveMode {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => (x : ℂ) * flatPrimitiveMode z x) l (𝓝 0) := by
  have h := (tendsto_abs_mul_exp_neg_mul_abs (flatDecayRate_pos hz) hl).const_mul (flatDecayConst z)
  rw [mul_zero] at h
  refine squeeze_zero_norm (fun x => ?_) h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |x| * ‖flatPrimitiveMode z x‖ ≤ |x| * (flatDecayConst z * Real.exp (-(flatDecayRate z * |x|))) :=
        mul_le_mul_of_nonneg_left (norm_flatPrimitiveMode_le hz hz1 x) (abs_nonneg x)
    _ = flatDecayConst z * (|x| * Real.exp (-(flatDecayRate z * |x|))) := by ring

theorem integrable_flatMode : Integrable (flatMode z) :=
  ((integrable_flatPrimitiveMode hz hz1).const_mul _).sub integrable_normalized_complex

theorem integrable_mul_flatMode : Integrable fun x : ℝ => (x : ℂ) * flatMode z x := by
  have h1 := (integrable_mul_flatPrimitiveMode hz hz1).const_mul (-(Complex.I * z))
  have h2 : Integrable fun x : ℝ => ((x * thetaSource.normalized x : ℝ) : ℂ) := by
    refine ((integrable_mul_thetaSource.div_const thetaSource.mass)).ofReal.congr
      (Eventually.of_forall fun x => ?_)
    simp only [PositiveDensitySource.normalized]
    push_cast
    rw [mul_div_assoc]
    rfl
  refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
  simp only [flatMode, Pi.sub_apply]
  push_cast; ring

/-- **The flat mode lies in the energy space** `L²(ℝ)`. -/
theorem memLp_flatMode : MemLp (flatMode z) 2 volume := by
  have hG : MemLp (flatPrimitiveMode z) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (continuous_flatPrimitiveMode hz hz1).aestronglyMeasurable).2 ?_
    have hc := flatDecayRate_pos hz
    refine ((integrable_exp_neg_mul_abs_flat (by positivity : 0 < 2 * flatDecayRate z)).const_mul
      (flatDecayConst z ^ 2)).mono' ((continuous_flatPrimitiveMode hz hz1).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h := norm_flatPrimitiveMode_le hz hz1 x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖flatPrimitiveMode z x‖ ^ 2 ≤ (flatDecayConst z * Real.exp (-(flatDecayRate z * |x|))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = flatDecayConst z ^ 2 * Real.exp (-(2 * flatDecayRate z * |x|)) := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
  exact (hG.const_mul _).sub memLp_normalized

/-- **Mean zero**: `∫ u_z = 0`. -/
theorem integral_flatMode : ∫ x, flatMode z x = 0 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_flatPrimitiveMode (abs_im_lt_one_of_flat hz hz1))
    (integrable_flatMode hz hz1) (tendsto_flatPrimitiveMode hz hz1 tendsto_abs_atBot_atTop)
    (tendsto_flatPrimitiveMode hz hz1 tendsto_abs_atTop_atTop)
  rw [h, sub_zero]

theorem integral_flatPrimitiveMode : ∫ x, flatPrimitiveMode z x = Complex.I / z := by
  have h := integral_flatMode hz hz1
  simp only [flatMode] at h
  rw [integral_sub ((integrable_flatPrimitiveMode hz hz1).const_mul _) integrable_normalized_complex,
    integral_const_mul, integral_normalized_complex] at h
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hz; exact lt_irrefl _ hz
  rw [eq_div_iff hz0]
  linear_combination Complex.I * h + (z * ∫ x, flatPrimitiveMode z x) * Complex.I_sq

/-- **The first-moment charge** `−i ∫ x u_z = −1/z`. -/
theorem flatMode_charge : -Complex.I * ∫ x : ℝ, (x : ℂ) * flatMode z x = -z⁻¹ := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * flatPrimitiveMode z x)
      (flatPrimitiveMode z x + (x : ℂ) * flatMode z x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    have h2 := h1.mul (hasDerivAt_flatPrimitiveMode (abs_im_lt_one_of_flat hz hz1) x)
    refine h2.congr_deriv ?_
    ring
  have h := integral_of_hasDerivAt_of_tendsto hd
    ((integrable_flatPrimitiveMode hz hz1).add (integrable_mul_flatMode hz hz1))
    (tendsto_mul_flatPrimitiveMode hz hz1 tendsto_abs_atBot_atTop)
    (tendsto_mul_flatPrimitiveMode hz hz1 tendsto_abs_atTop_atTop)
  rw [integral_add (integrable_flatPrimitiveMode hz hz1) (integrable_mul_flatMode hz hz1),
    integral_flatPrimitiveMode hz hz1, sub_zero] at h
  have hx : ∫ x : ℝ, (x : ℂ) * flatMode z x = -(Complex.I / z) := by linear_combination h
  rw [hx]
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hz; exact lt_irrefl _ hz
  field_simp
  exact Complex.I_sq

/-- **The flat one-port equation (7)**: `i ∫_{−∞}^x u_z = −z⁻¹ (u_z(x) + ρ(x))`. -/
theorem flatMode_onePort_equation (x : ℝ) :
    Complex.I * ∫ y in Iic x, flatMode z y = -z⁻¹ * (flatMode z x + thetaSource.normalized x) := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto (a := x)
    (continuous_flatPrimitiveMode hz hz1).continuousWithinAt
    (fun y _ => hasDerivAt_flatPrimitiveMode (abs_im_lt_one_of_flat hz hz1) y)
    (integrable_flatMode hz hz1).integrableOn
    (tendsto_flatPrimitiveMode hz hz1 tendsto_abs_atBot_atTop)
  rw [h, sub_zero]
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hz; exact lt_irrefl _ hz
  rw [show flatMode z x + (thetaSource.normalized x : ℂ) = -(Complex.I * z) * flatPrimitiveMode z x by
    simp only [flatMode]; ring]
  field_simp

/-! ### The left tail and the connection coefficient -/

omit hz in
theorem tendsto_sourceChar_mul_normalized_atBot :
    Tendsto (fun x : ℝ => sourceChar z x * (thetaSource.normalized x : ℂ)) atBot (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => flatEnvelopeConst * Real.exp ((1 - z.im) * x)) atBot (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by linarith : (0 : ℝ) < 1 - z.im)))
    simpa using this.const_mul flatEnvelopeConst
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_le_atBot 0] with x hx
  rw [norm_mul, norm_sourceChar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos x)]
  have h := normalized_le_exp x
  rw [abs_of_nonpos hx, neg_neg] at h
  calc Real.exp (-z.im * x) * thetaSource.normalized x ≤ Real.exp (-z.im * x) * (flatEnvelopeConst * Real.exp x) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = flatEnvelopeConst * Real.exp ((1 - z.im) * x) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **The forbidden left exponential**: `e^{izx} u_z(x) → −iz C_z` as `x → −∞`. -/
theorem tendsto_sourceChar_mul_flatMode_atBot :
    Tendsto (fun x : ℝ => sourceChar z x * flatMode z x) atBot
      (𝓝 (-(Complex.I * z) * flatConnection z)) := by
  have hzabs := abs_im_lt_one_of_flat hz hz1
  have hI := tendsto_setIntegral_Iic_atBot (integrable_flatCharDensity hzabs)
  have h1 : Tendsto (fun x : ℝ => -(Complex.I * z) * (flatConnection z - ∫ y in Iic x, flatCharDensity z y))
      atBot (𝓝 (-(Complex.I * z) * (flatConnection z - 0))) :=
    (tendsto_const_nhds.sub hI).const_mul _
  rw [sub_zero] at h1
  have h2 := h1.sub (tendsto_sourceChar_mul_normalized_atBot hz1)
  rw [sub_zero] at h2
  refine h2.congr fun x => ?_
  rw [flatMode, flatPrimitiveMode_eq hzabs]
  have h3 := exp_mul_sourceChar z x
  linear_combination (Complex.I * z * (flatConnection z - ∫ y in Iic x, flatCharDensity z y)) * h3

end Flat

/-! ## The two-ended domain selector -/

theorem tendsto_normalized_mul_exp_atBot {a : ℝ} (ha : a < 1) :
    Tendsto (fun x : ℝ => thetaSource.normalized x * Real.exp (-(2 * a * x))) atBot (𝓝 0) := by
  -- the double-exponential theta envelope beats every exponential
  set U := thetaEnvelopeUpper / thetaSource.mass
  have hU : 0 ≤ U := by
    have := (thetaCuspFullSource_pos 0).le.trans (thetaCuspFullSource_le_envelope le_rfl)
    have h0 := thetaEnvelope_pos 0
    exact div_nonneg (nonneg_of_mul_nonneg_left this h0) thetaSource.mass_pos.le
  have hbound : ∀ x ≤ (0 : ℝ), thetaSource.normalized x * Real.exp (-(2 * a * x)) ≤
      U * Real.exp (7 * (-x) - Real.pi * Real.exp (2 * (-x))) := by
    intro x hx
    have hk : thetaSource.k x ≤ thetaEnvelopeUpper * thetaEnvelope (-x) := by
      rw [← thetaSource_even x]
      exact thetaCuspFullSource_le_envelope (by linarith)
    have hρ : thetaSource.normalized x ≤ U * thetaEnvelope (-x) := by
      show thetaSource.k x / thetaSource.mass ≤ _
      rw [div_le_iff₀ thetaSource.mass_pos]
      calc thetaSource.k x ≤ thetaEnvelopeUpper * thetaEnvelope (-x) := hk
        _ = U * thetaEnvelope (-x) * thetaSource.mass := by
            have := thetaSource.mass_pos.ne'
            simp only [U]; field_simp
    have he : thetaEnvelope (-x) * Real.exp (-(2 * a * x)) ≤
        Real.exp (7 * (-x) - Real.pi * Real.exp (2 * (-x))) := by
      rw [thetaEnvelope, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc thetaSource.normalized x * Real.exp (-(2 * a * x)) ≤ U * thetaEnvelope (-x) * Real.exp (-(2 * a * x)) :=
          mul_le_mul_of_nonneg_right hρ (Real.exp_pos _).le
      _ = U * (thetaEnvelope (-x) * Real.exp (-(2 * a * x))) := by ring
      _ ≤ U * Real.exp (7 * (-x) - Real.pi * Real.exp (2 * (-x))) := mul_le_mul_of_nonneg_left he hU
  have hlim : Tendsto (fun t : ℝ => U * Real.exp (7 * t - Real.pi * Real.exp (2 * t))) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => 7 * t - Real.pi * Real.exp (2 * t)) atTop atBot := by
      refine tendsto_atBot_mono' atTop ?_ (tendsto_neg_atTop_atBot.comp tendsto_id)
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with t ht
      have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * t by linarith)
      have hpi := Real.pi_gt_three
      simp only [Function.comp_apply, id]
      nlinarith
    simpa using (Real.tendsto_exp_atBot.comp hexp).const_mul U
  refine squeeze_zero' (Eventually.of_forall fun x => by
    have := thetaSource.normalized_pos x; positivity) ?_ (hlim.comp tendsto_neg_atBot_atTop)
  filter_upwards [eventually_le_atBot 0] with x hx
  exact hbound x hx

/-- The flat-domain energy density `|u_z|²/ρ`. -/
def flatModeWeightedDensity (z : ℂ) (x : ℝ) : ℝ := ‖flatMode z x‖ ^ 2 / thetaSource.normalized x

/-- `u_z/ρ ∈ L²(ρ dx)` is the same integrability: `|u_z/ρ|² ρ = |u_z|²/ρ`. -/
theorem norm_div_normalized_sq_mul (z : ℂ) (x : ℝ) :
    ‖flatMode z x / (thetaSource.normalized x : ℂ)‖ ^ 2 * thetaSource.normalized x = flatModeWeightedDensity z x := by
  have hρ := thetaSource.normalized_pos x
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, flatModeWeightedDensity]
  field_simp

/-- Off the divisor the left tail is forbidden: `∫ |u_z|²/ρ = ∞` when `Ξ_C(z) ≠ 0`. -/
theorem not_integrable_flatModeWeightedDensity {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) (hXi : XiC z ≠ 0) :
    ¬ Integrable (flatModeWeightedDensity z) := by
  intro hint
  have hzabs := abs_im_lt_one_of_flat hz hz1
  have hC : flatConnection z ≠ 0 := by
    rw [flatConnection_eq hzabs]
    exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hz; exact lt_irrefl _ hz
  set c : ℝ := ‖z‖ * ‖flatConnection z‖ / 2
  have hc : 0 < c := by positivity
  have hlim := tendsto_sourceChar_mul_flatMode_atBot hz hz1
  have hev1 : ∀ᶠ x in atBot, ‖sourceChar z x * flatMode z x - (-(Complex.I * z) * flatConnection z)‖ < c :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hc)
  have hev2 : ∀ᶠ x in atBot, thetaSource.normalized x * Real.exp (-(2 * z.im * x)) < c ^ 2 / 2 :=
    (tendsto_normalized_mul_exp_atBot hz1).eventually (gt_mem_nhds (by positivity))
  obtain ⟨X, hX⟩ := eventually_atBot.1 (hev1.and hev2)
  have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic X) := by
    refine (hint.integrableOn (s := Iic X)).mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => ?_)
    obtain ⟨h1, h2⟩ := hX x hx
    have hnorm : ‖-(Complex.I * z) * flatConnection z‖ = 2 * c := by
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul]; simp only [c]; ring
    have hlow : c ≤ ‖sourceChar z x * flatMode z x‖ := by
      have := norm_sub_norm_le (-(Complex.I * z) * flatConnection z) (sourceChar z x * flatMode z x)
      rw [norm_sub_rev, hnorm] at this
      linarith
    rw [norm_mul, norm_sourceChar] at hlow
    have hρ := thetaSource.normalized_pos x
    have hu : c * Real.exp (z.im * x) ≤ ‖flatMode z x‖ := by
      have he : Real.exp (-z.im * x) * Real.exp (z.im * x) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc c * Real.exp (z.im * x) ≤ Real.exp (-z.im * x) * ‖flatMode z x‖ * Real.exp (z.im * x) :=
            mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
        _ = ‖flatMode z x‖ := by rw [mul_comm (Real.exp _) ‖_‖, mul_assoc, he, mul_one]
    have hρle : thetaSource.normalized x ≤ c ^ 2 / 2 * Real.exp (2 * z.im * x) := by
      have he : Real.exp (-(2 * z.im * x)) * Real.exp (2 * z.im * x) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc thetaSource.normalized x = thetaSource.normalized x * Real.exp (-(2 * z.im * x)) *
            Real.exp (2 * z.im * x) := by rw [mul_assoc, he, mul_one]
        _ ≤ c ^ 2 / 2 * Real.exp (2 * z.im * x) := mul_le_mul_of_nonneg_right h2.le (Real.exp_pos _).le
    have hsq : (c * Real.exp (z.im * x)) ^ 2 ≤ ‖flatMode z x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
    have he2 : (c * Real.exp (z.im * x)) ^ 2 = c ^ 2 * Real.exp (2 * z.im * x) := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
    have hE : 0 < Real.exp (2 * z.im * x) := Real.exp_pos _
    have hfinal : 1 ≤ ‖flatMode z x‖ ^ 2 / thetaSource.normalized x := by
      rw [le_div_iff₀ hρ, one_mul]
      nlinarith
    rw [Real.norm_eq_abs, abs_one]
    exact hfinal
  rw [integrableOn_const_iff] at hon
  rcases hon with h0 | hfin
  · simp at h0
  · rw [Real.volume_Iic] at hfin; exact lt_irrefl _ hfin

/-! ### At a zero the flat mode is the weighted divisor mode -/

theorem flatPrimitiveMode_of_zero {z : ℂ} (hz : XiC z = 0) (x : ℝ) :
    flatPrimitiveMode z x = -Complex.I * sourceModeU thetaSource z x / (thetaSource.mass : ℂ) := by
  have hzabs := abs_im_lt_one_of_XiC_eq_zero hz
  have hM : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast thetaSource.mass_ne_zero
  rw [flatPrimitiveMode_eq hzabs, flatConnection_eq hzabs, hz, zero_div, zero_mul, zero_sub,
    sourceModeU, sourceModeI]
  have hI : ∫ y in Iic x, (thetaSource.k y : ℂ) * sourceChar z y =
      (thetaSource.mass : ℂ) * ∫ y in Iic x, flatCharDensity z y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [flatCharDensity, PositiveDensitySource.normalized]
    push_cast
    field_simp
  rw [hI]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

theorem flatMode_of_zero {z : ℂ} (hz : XiC z = 0) (x : ℝ) :
    flatMode z x = sourceModeF thetaSource z x / (thetaSource.mass : ℂ) - thetaSource.normalized x := by
  have hM : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast thetaSource.mass_ne_zero
  rw [flatMode, flatPrimitiveMode_of_zero hz, sourceModeF]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

theorem continuous_flatMode {z : ℂ} (hz : |z.im| < 1) : Continuous (flatMode z) := by
  have hG : Continuous (flatPrimitiveMode z) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_flatPrimitiveMode hz x).continuousAt
  exact (continuous_const.mul hG).sub (Complex.continuous_ofReal.comp continuous_normalized_theta)

theorem continuous_flatModeWeightedDensity {z : ℂ} (hz : |z.im| < 1) :
    Continuous (flatModeWeightedDensity z) :=
  ((continuous_flatMode hz).norm.pow 2).div continuous_normalized_theta fun x =>
    (thetaSource.normalized_pos x).ne'

theorem integrable_flatModeWeightedDensity_of_zero {z : ℂ} (hz : XiC z = 0) :
    Integrable (flatModeWeightedDensity z) := by
  have hzabs := abs_im_lt_one_of_XiC_eq_zero hz
  have hz0 := xiC_eq_zero_of_XiC_eq_zero hz
  have hF := integrable_sourceModeFWeightedEnergyDensity hzabs hz0
  have hρ : Integrable thetaSource.normalized := thetaSource.integrable_k.div_const _
  refine ((hF.const_mul (2 / thetaSource.mass)).add (hρ.const_mul 2)).mono'
    (continuous_flatModeWeightedDensity hzabs).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hM := thetaSource.mass_pos
  have hρx := thetaSource.normalized_pos x
  have hk : thetaSource.k x = thetaSource.mass * thetaSource.normalized x := by
    simp only [PositiveDensitySource.normalized]; field_simp
  show ‖flatModeWeightedDensity z x‖ ≤
    2 / thetaSource.mass * sourceModeFWeightedEnergyDensity z x + 2 * thetaSource.normalized x
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold flatModeWeightedDensity; positivity),
    flatModeWeightedDensity, flatMode_of_zero hz, sourceModeFWeightedEnergyDensity]
  have hn : ‖sourceModeF thetaSource z x / (thetaSource.mass : ℂ) - (thetaSource.normalized x : ℂ)‖ ≤
      ‖sourceModeF thetaSource z x‖ / thetaSource.mass + thetaSource.normalized x := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hM, abs_of_pos hρx]
  set a := ‖sourceModeF thetaSource z x‖
  have hsq : ‖sourceModeF thetaSource z x / (thetaSource.mass : ℂ) - (thetaSource.normalized x : ℂ)‖ ^ 2 ≤
      2 * (a / thetaSource.mass) ^ 2 + 2 * thetaSource.normalized x ^ 2 := by
    have h0 := norm_nonneg (sourceModeF thetaSource z x / (thetaSource.mass : ℂ) - (thetaSource.normalized x : ℂ))
    nlinarith [sq_nonneg (a / thetaSource.mass - thetaSource.normalized x), norm_nonneg (sourceModeF thetaSource z x)]
  rw [div_le_iff₀ hρx, hk]
  have ha : 0 ≤ a := norm_nonneg _
  calc ‖sourceModeF thetaSource z x / (thetaSource.mass : ℂ) - (thetaSource.normalized x : ℂ)‖ ^ 2
      ≤ 2 * (a / thetaSource.mass) ^ 2 + 2 * thetaSource.normalized x ^ 2 := hsq
    _ = (2 / thetaSource.mass * (a ^ 2 / (thetaSource.mass * thetaSource.normalized x)) +
          2 * thetaSource.normalized x) * thetaSource.normalized x := by
        field_simp

/-- **The two-ended domain selector (8)**: for `0 < Im z < 1`,
`∫ |u_z|²/ρ < ∞ ⟺ Ξ_C(z) = 0`. -/
theorem integrable_flatModeWeightedDensity_iff {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) :
    Integrable (flatModeWeightedDensity z) ↔ XiC z = 0 := by
  constructor
  · intro h
    by_contra hXi
    exact not_integrable_flatModeWeightedDensity hz hz1 hXi h
  · exact integrable_flatModeWeightedDensity_of_zero

/-! ### The quantile pull-back -/

/-- The quantile pull-back `u_z(Q(t))/h(t)`. -/
def flatModePullback (z : ℂ) (t : ℝ) : ℂ := flatMode z (thetaSource.quantileFun t) / metricSymbol thetaSource t

/-- **At a zero** the pull-back is the normalized quotient mode `f_z`; **off the divisor** it is not
square integrable: `u_z∘Q/h ∈ L²(0,1) ⟺ Ξ_C(z) = 0`. -/
theorem memLp_flatModePullback_iff {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) :
    MemLp (flatModePullback z) 2 unitIntervalMeasure ↔ XiC z = 0 := by
  have hzabs := abs_im_lt_one_of_flat hz hz1
  have hmeas : Measurable (flatModePullback z) :=
    ((continuous_flatMode hzabs).measurable.comp thetaSource.measurable_quantileFun).div
      (measurable_metricSymbol thetaSource)
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable,
    integrable_unitInterval_iff_cdf (hmeas.norm.pow_const 2).aestronglyMeasurable,
    ← integrable_flatModeWeightedDensity_iff hz hz1]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  have hρ := thetaSource.normalized_pos x
  simp only [flatModePullback, smul_eq_mul, flatModeWeightedDensity]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ]
  field_simp

theorem portEigenmode_ae_flatModePullback {z : ℂ} (hz : XiC z = 0) :
    (portEigenmode z : ℝ → ℂ) =ᵐ[unitIntervalMeasure] flatModePullback z := by
  have hz1 := abs_im_lt_one_of_XiC_eq_zero hz
  have hz0 := xiC_eq_zero_of_XiC_eq_zero hz
  have hM : (thetaSource.mass : ℂ) ≠ 0 := by exact_mod_cast thetaSource.mass_ne_zero
  have hsM := sqrt_mass_ne_zero
  rw [portEigenmode, divisorVec_of_zero hz, thetaDivisorEigenvector]
  filter_upwards [Lp.coeFn_sub ((Real.sqrt thetaSource.mass : ℂ)⁻¹ •
      quantileUnitary thetaSource (thetaDivisorSourceVector z hz1 hz0)) constMode,
    Lp.coeFn_smul ((Real.sqrt thetaSource.mass : ℂ)⁻¹) (quantileUnitary thetaSource (thetaDivisorSourceVector z hz1 hz0)),
    quantileUnitary_ae thetaSource (thetaDivisorSourceVector z hz1 hz0),
    thetaDivisorSourceVector_quantile_ae z hz1 hz0, coeFn_unitFourierBasis 0] with t h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h5,
    fourierMode_zero, smul_eq_mul]
  rw [h4, flatModePullback, flatMode_of_zero hz, metricSymbol]
  have hk : (thetaSource.k (thetaSource.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.pos_k _).ne'
  rw [PositiveDensitySource.normalized]
  push_cast
  field_simp

end

end RHTower
