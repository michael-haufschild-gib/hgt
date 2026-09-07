import GaloisForLFunctions.RHTower.ArithmeticLogarithmicResponseHeight

/-!
# Height-saving cubic error for the complete reflected source

The literal odd Mellin residual has an arithmetic right derivative at every
integer join. Exact hyperbolic bounds and logarithmic moments control that
full derivative on every compact substrip. Both primitive boundaries vanish,
giving inverse-height decay of the complete cubic source error. At an off-line
strip zero this sharpens the simultaneous complex zero-constraint disk, using
the parameter's actual distance from the strip edges. No signed arithmetic
comparison excluding that disk, or RH proof, is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Global quadratic majorant for the even hyperbolic defect. -/
theorem reflection_abs_cosh_sub_one_le (a : ℝ) :
    |Real.cosh a-1| ≤ |a|^2/2*Real.exp |a| := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh a))]
  have h := RHTower.cosh_sub_one_le (abs_nonneg a)
  rw [Real.cosh_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (incoming_cosh_le_exp_abs a) (by positivity))

/-- Compact-substrip bounds retain the exact odd and even horizontal defects. -/
theorem reflection_hyperbolic_substrip_bounds {x δ ε : ℝ} (hx : 1 ≤ x)
    (hδ : |δ| ≤ 1/2-ε) :
    |Real.sinh (δ*Real.log x)-δ*Real.log x| ≤ |δ|^3*(Real.log x)^3/6*x^(1/2-ε) ∧
    |Real.cosh (δ*Real.log x)-1| ≤ |δ|^2*(Real.log x)^2/2*x^(1/2-ε) := by
  have hl := Real.log_nonneg hx
  have he : Real.exp (|δ| * Real.log x) ≤ x^(1/2-ε) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hδ hl])
  have hs := incoming_abs_sinh_sub_self_le (δ*Real.log x)
  have hc := reflection_abs_cosh_sub_one_le (δ*Real.log x)
  rw [abs_mul,abs_of_nonneg hl,mul_pow] at hs hc
  exact ⟨hs.trans (mul_le_mul_of_nonneg_left he (by positivity)),
    hc.trans (mul_le_mul_of_nonneg_left he (by positivity))⟩

/-- Actual cubic reflection residual, including the arithmetic kernel. -/
def reflectionCubicKernel (δ x : ℝ) : ℝ :=
  -2*(RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*(Real.sinh (δ*Real.log x)-δ*Real.log x)

/-- Primitive amplitude for the unchanged logarithmic height character. -/
def reflectionCubicPrimitive (δ x : ℝ) : ℝ :=
  -2*(RHTower.bernoulliPeriodic x+1/12)*x^(-(3/2:ℝ))*(Real.sinh (δ*Real.log x)-δ*Real.log x)

/-- Literal right derivative of the full cubic primitive. -/
def reflectionCubicDerivative (δ x : ℝ) : ℝ :=
  -2*(Int.fract x-1/2)*x^(-(3/2:ℝ))*(Real.sinh (δ*Real.log x)-δ*Real.log x)+
    (RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*
      (3*(Real.sinh (δ*Real.log x)-δ*Real.log x)-2*δ*(Real.cosh (δ*Real.log x)-1))

/-- Positive full-derivative majorant on a compact substrip. -/
def reflectionCubicMajorant (ε x : ℝ) : ℝ :=
  x^(-1-ε)*(Real.log x)^3/6+x^(-2-ε)*(Real.log x)^3/24+x^(-2-ε)*(Real.log x)^2/12

/-- Exact integrated cost of the full arithmetic derivative on a compact substrip. -/
def reflectionCubicHeightCost (ε : ℝ) : ℝ :=
  1/ε^4+1/(4*(1+ε)^4)+1/(6*(1+ε)^3)

/-- The primitive equals the source amplitude times its positive integration coordinate. -/
theorem reflectionCubicPrimitive_eq_mul {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    reflectionCubicPrimitive δ x = x*reflectionCubicKernel δ x := by
  have he : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc
      _ = x^((-(5/2:ℝ))+1) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  unfold reflectionCubicPrimitive reflectionCubicKernel
  rw [he]; ring

/-- Differentiation preserves every integer join and the complete cubic defect. -/
theorem hasDerivWithinAt_reflectionCubicPrimitive {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    HasDerivWithinAt (reflectionCubicPrimitive δ) (reflectionCubicDerivative δ x) (Ioi x) x := by
  have hp := ((bernoulliPeriodic_hasDerivWithinAt_right x).add_const (1/12)).mono Ioi_subset_Ici_self
  have hw := Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne')
  have ha := (Real.hasDerivAt_log hx.ne').const_mul δ
  have hr := ((Real.hasDerivAt_sinh (δ*Real.log x)).comp x ha).sub ha
  have he : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc
      _ = x^((-(5/2:ℝ))+1) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  convert! (((hp.const_mul (-2)).mul hw.hasDerivWithinAt).mul hr.hasDerivWithinAt) using 1
  unfold reflectionCubicDerivative
  simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
  norm_num only
  rw [he]
  field_simp
  ring

/-- The full cubic derivative has a displacement-sensitive integrable majorant. -/
theorem abs_reflectionCubicDerivative_le {x δ ε : ℝ} (hx : 1 ≤ x)
    (hδ : |δ| ≤ 1/2-ε) :
    |reflectionCubicDerivative δ x| ≤ |δ|^3*reflectionCubicMajorant ε x := by
  have hx0 := zero_lt_one.trans_le hx
  have hl := Real.log_nonneg hx
  have hp : 0 ≤ x^(-(5/2:ℝ)) := Real.rpow_nonneg hx0.le _
  have hq : 0 ≤ x^(-(3/2:ℝ)) := Real.rpow_nonneg hx0.le _
  have hf : |Int.fract x-1/2| ≤ 1/2 := by
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hs,hc⟩ := reflection_hyperbolic_substrip_bounds hx hδ
  have hi : |3*(Real.sinh (δ*Real.log x)-δ*Real.log x)-2*δ*(Real.cosh (δ*Real.log x)-1)| ≤
      3*|Real.sinh (δ*Real.log x)-δ*Real.log x|+2*|δ| * |Real.cosh (δ*Real.log x)-1| := by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),abs_of_pos (by norm_num : (0:ℝ)<2)] using
      abs_sub (3*(Real.sinh (δ*Real.log x)-δ*Real.log x)) (2*δ*(Real.cosh (δ*Real.log x)-1))
  have ha : |reflectionCubicDerivative δ x| ≤
      2*|Int.fract x-1/2| *x^(-(3/2:ℝ))*|Real.sinh (δ*Real.log x)-δ*Real.log x|+
      |RHTower.bernoulliPeriodic x+1/12| *x^(-(5/2:ℝ))*
        (3*|Real.sinh (δ*Real.log x)-δ*Real.log x|+2*|δ| * |Real.cosh (δ*Real.log x)-1|) := by
    unfold reflectionCubicDerivative
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg hq,abs_of_nonneg hp,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    gcongr
  have hb : |reflectionCubicDerivative δ x| ≤
      2*(1/2)*x^(-(3/2:ℝ))*(|δ|^3*(Real.log x)^3/6*x^(1/2-ε))+
      (1/12)*x^(-(5/2:ℝ))*(3*(|δ|^3*(Real.log x)^3/6*x^(1/2-ε))+
        2*|δ| * (|δ|^2*(Real.log x)^2/2*x^(1/2-ε))) := by
    apply ha.trans
    gcongr
    exact abs_centeredBernoulliKernel_le x
  have he1 : x^(-(3/2:ℝ))*x^(1/2-ε)=x^(-1-ε) := by
    rw [←Real.rpow_add hx0]; congr 1; ring
  have he2 : x^(-(5/2:ℝ))*x^(1/2-ε)=x^(-2-ε) := by
    rw [←Real.rpow_add hx0]; congr 1; ring
  apply hb.trans_eq
  unfold reflectionCubicMajorant
  calc
    _ = |δ|^3*((x^(-(3/2:ℝ))*x^(1/2-ε))*(Real.log x)^3/6+
      (x^(-(5/2:ℝ))*x^(1/2-ε))*(Real.log x)^3/24+
      (x^(-(5/2:ℝ))*x^(1/2-ε))*(Real.log x)^2/12) := by ring
    _ = _ := by rw [he1,he2]

/-- The complete majorant has finite mass on every compact substrip. -/
theorem integrable_reflectionCubicMajorant {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (reflectionCubicMajorant ε) (Ioi (1:ℝ)) := by
  have h1 : IntegrableOn (fun x : ℝ => x^(-1-ε)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -ε-1=(-1:ℝ)-ε by ring] using RHTower.integrableOn_rpow_mul_log_pow_Ioi_one hε 3
  have h2 : IntegrableOn (fun x : ℝ => x^(-2-ε)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -(1+ε)-1=(-2:ℝ)-ε by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 3
  have h3 : IntegrableOn (fun x : ℝ => x^(-2-ε)*(Real.log x)^2) (Ioi (1:ℝ)) := by
    simpa only [show -(1+ε)-1=(-2:ℝ)-ε by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 2
  exact ((h1.div_const 6).add (h2.div_const 24)).add (h3.div_const 12)

/-- Exact logarithmic moments evaluate the derivative cost. -/
theorem integral_reflectionCubicMajorant {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi (1:ℝ), reflectionCubicMajorant ε x)=reflectionCubicHeightCost ε := by
  have h1 : IntegrableOn (fun x : ℝ => x^(-1-ε)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -ε-1=(-1:ℝ)-ε by ring] using RHTower.integrableOn_rpow_mul_log_pow_Ioi_one hε 3
  have h2 : IntegrableOn (fun x : ℝ => x^(-2-ε)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -(1+ε)-1=(-2:ℝ)-ε by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 3
  have h3 : IntegrableOn (fun x : ℝ => x^(-2-ε)*(Real.log x)^2) (Ioi (1:ℝ)) := by
    simpa only [show -(1+ε)-1=(-2:ℝ)-ε by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 2
  have h12 : IntegrableOn (fun x : ℝ => x^(-1-ε)*(Real.log x)^3/6+x^(-2-ε)*(Real.log x)^3/24) (Ioi (1:ℝ)) :=
    (h1.div_const 6).add (h2.div_const 24)
  unfold reflectionCubicMajorant
  rw [integral_add h12 (h3.div_const 12),integral_add (h1.div_const 6) (h2.div_const 24),
    integral_div,integral_div,integral_div]
  have he1 := RHTower.integral_rpow_mul_log_pow_Ioi_one hε 3
  have he2 := RHTower.integral_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 3
  have he3 := RHTower.integral_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 2
  rw [show -ε-1=(-1:ℝ)-ε by ring] at he1
  rw [show -(1+ε)-1=(-2:ℝ)-ε by ring] at he2 he3
  rw [he1,he2,he3]
  norm_num [Nat.factorial,reflectionCubicHeightCost]
  ring

/-- The source residual itself has a cubic logarithmic majorant. -/
theorem abs_reflectionCubicKernel_le {x δ ε : ℝ} (hx : 1 ≤ x) (hδ : |δ| ≤ 1/2-ε) :
    |reflectionCubicKernel δ x| ≤ |δ|^3/36*(x^(-2-ε)*(Real.log x)^3) := by
  have hx0 := zero_lt_one.trans_le hx
  have hl := Real.log_nonneg hx
  have hp := Real.rpow_nonneg hx0.le (-(5/2:ℝ))
  have hs := (reflection_hyperbolic_substrip_bounds hx hδ).1
  have he : x^(-(5/2:ℝ))*x^(1/2-ε)=x^(-2-ε) := by
    rw [←Real.rpow_add hx0]; congr 1; ring
  unfold reflectionCubicKernel
  simp only [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg hp]
  calc
    _ ≤ 2*(1/12)*x^(-(5/2:ℝ))*(|δ|^3*(Real.log x)^3/6*x^(1/2-ε)) := by
      gcongr
      exact abs_centeredBernoulliKernel_le x
    _ = |δ|^3/36*((x^(-(5/2:ℝ))*x^(1/2-ε))*(Real.log x)^3) := by ring
    _ = _ := by rw [he]

/-- The primitive retains the same cubic coefficient and vanishes with a decaying log-power bound. -/
theorem abs_reflectionCubicPrimitive_le {x δ ε : ℝ} (hx : 1 ≤ x) (hδ : |δ| ≤ 1/2-ε) :
    |reflectionCubicPrimitive δ x| ≤ |δ|^3/36*(x^(-1-ε)*(Real.log x)^3) := by
  have hx0 := zero_lt_one.trans_le hx
  rw [reflectionCubicPrimitive_eq_mul hx0,abs_mul,abs_of_pos hx0]
  have he : x*x^(-2-ε)=x^(-1-ε) := by
    calc
      _ = x^(1:ℝ)*x^(-2-ε) := by rw [Real.rpow_one]
      _ = x^((1:ℝ)+(-2-ε)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ x*(|δ|^3/36*(x^(-2-ε)*(Real.log x)^3)) :=
      mul_le_mul_of_nonneg_left (abs_reflectionCubicKernel_le hx hδ) hx0.le
    _ = |δ|^3/36*((x*x^(-2-ε))*(Real.log x)^3) := by ring
    _ = _ := by rw [he]

/-- The actual full cubic source density. -/
def reflectionCubicDensity (δ t x : ℝ) : ℂ :=
  (reflectionCubicKernel δ x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The signed flux of the full cubic arithmetic derivative. -/
def reflectionCubicFlux (δ t x : ℝ) : ℂ :=
  (reflectionCubicDerivative δ x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Boundary primitive with the unchanged height phase. -/
def reflectionCubicBoundary (δ t x : ℝ) : ℂ :=
  (reflectionCubicPrimitive δ x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Absolute integrability of the actual residual density on any compact substrip. -/
theorem integrable_reflectionCubicDensity {δ ε : ℝ} (hε : 0 < ε) (hδ : |δ| ≤ 1/2-ε) (t : ℝ) :
    IntegrableOn (reflectionCubicDensity δ t) (Ioi (1:ℝ)) := by
  have hm : IntegrableOn (fun x : ℝ => x^(-2-ε)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -(1+ε)-1=(-2:ℝ)-ε by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < 1+ε) 3
  apply Integrable.mono (hm.const_mul (|δ|^3/36))
  · unfold reflectionCubicDensity reflectionCubicKernel RHTower.bernoulliPeriodic
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [reflectionCubicDensity,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
    exact (abs_reflectionCubicKernel_le hx.le hδ).trans (le_abs_self _)

/-- Absolute integrability of the complete signed residual flux. -/
theorem integrable_reflectionCubicFlux {δ ε : ℝ} (hε : 0 < ε) (hδ : |δ| ≤ 1/2-ε) (t : ℝ) :
    IntegrableOn (reflectionCubicFlux δ t) (Ioi (1:ℝ)) := by
  apply Integrable.mono ((integrable_reflectionCubicMajorant hε).const_mul (|δ|^3))
  · unfold reflectionCubicFlux reflectionCubicDerivative RHTower.bernoulliPeriodic
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [reflectionCubicFlux,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
    exact (abs_reflectionCubicDerivative_le hx.le hδ).trans (le_abs_self _)

/-- The residual boundary is continuous across all arithmetic joins. -/
theorem continuousAt_reflectionCubicBoundary (δ t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (reflectionCubicBoundary δ t) x := by
  have hp := (Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne')).continuousAt
  have hl := ((Real.hasDerivAt_log hx.ne').const_mul δ).continuousAt
  have hr : ContinuousAt (fun y : ℝ => Real.sinh (δ*Real.log y)-δ*Real.log y) x :=
    ((Real.hasDerivAt_sinh (δ*Real.log x)).continuousAt.comp (f := fun y : ℝ => δ*Real.log y) hl).sub hl
  have hA : ContinuousAt (reflectionCubicPrimitive δ) x :=
    (((continuous_centeredBernoulliKernel.continuousAt.const_mul (-2)).mul hp).mul hr)
  exact (Complex.continuous_ofReal.continuousAt.comp hA).mul (hasDerivAt_logHeightCharacter t hx).continuousAt

/-- The exact boundary derivative retains both flux and source terms. -/
theorem hasDerivWithinAt_reflectionCubicBoundary (δ t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (reflectionCubicBoundary δ t)
      (reflectionCubicFlux δ t x+(t:ℂ)*Complex.I*reflectionCubicDensity δ t x) (Ioi x) x := by
  convert! (hasDerivWithinAt_reflectionCubicPrimitive hx δ).ofReal_comp.mul
    (hasDerivAt_logHeightCharacter t hx).hasDerivWithinAt using 1
  unfold reflectionCubicFlux reflectionCubicDensity
  rw [reflectionCubicPrimitive_eq_mul hx]
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp [hxC]

/-- No infinite boundary survives on a compact substrip. -/
theorem tendsto_reflectionCubicBoundary_zero {δ ε : ℝ} (hε : 0 < ε)
    (hδ : |δ| ≤ 1/2-ε) (t : ℝ) : Tendsto (reflectionCubicBoundary δ t) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x^(-1-ε)*(Real.log x)^3) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((3:ℕ):ℝ) (by linarith : 0 < 1+ε)).tendsto_div_nhds_zero
    simp only [Real.rpow_natCast] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [show (-1:ℝ)-ε=-(1+ε) by ring,Real.rpow_neg hx.le]
    ring
  have ht' : Tendsto (fun x : ℝ => (|δ|^3/36)*(x^(-1-ε)*(Real.log x)^3)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (|δ|^3/36)
  apply squeeze_zero_norm' ?_ ht'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  simp only [reflectionCubicBoundary,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
    Real.exp_zero,mul_one]
  exact abs_reflectionCubicPrimitive_le hx hδ

/-- Exact full residual flux identity, including every join and both boundaries. -/
theorem reflectionCubic_flux_identity {δ ε : ℝ} (hε : 0 < ε) (hδ : |δ| ≤ 1/2-ε) (t : ℝ) :
    (t:ℂ)*Complex.I*(∫ x in Ioi (1:ℝ), reflectionCubicDensity δ t x) =
      -(∫ x in Ioi (1:ℝ), reflectionCubicFlux δ t x) := by
  let D : ℝ → ℂ := fun x => reflectionCubicFlux δ t x+(t:ℂ)*Complex.I*reflectionCubicDensity δ t x
  have hD : IntegrableOn D (Ioi (1:ℝ)) := (integrable_reflectionCubicFlux hε hδ t).add
    ((integrable_reflectionCubicDensity hε hδ t).const_mul ((t:ℂ)*Complex.I))
  have hi := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (1:ℝ) hD tendsto_id
  have he : ∀ᶠ b : ℝ in atTop, (∫ x in (1:ℝ)..b, D x)=reflectionCubicBoundary δ t b := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with b hb
    have hc : ContinuousOn (reflectionCubicBoundary δ t) (uIcc (1:ℝ) b) := by
      intro x hx
      exact (continuousAt_reflectionCubicBoundary δ t
        (zero_lt_one.trans_le ((uIcc_of_le hb ▸ hx).1))).continuousWithinAt
    have hd : ∀ x ∈ Ioo (min (1:ℝ) b) (max (1:ℝ) b),
        HasDerivWithinAt (reflectionCubicBoundary δ t) (D x) (Ioi x) x := by
      intro x hx
      rw [min_eq_left hb,max_eq_right hb] at hx
      exact hasDerivWithinAt_reflectionCubicBoundary δ t (zero_lt_one.trans hx.1)
    have hint : IntervalIntegrable D volume 1 b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (hD.mono_set Ioc_subset_Ioi_self)
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right hc hd hint
    simpa [reflectionCubicBoundary,reflectionCubicPrimitive] using h
  have hzero : (∫ x in Ioi (1:ℝ), D x)=0 :=
    tendsto_nhds_unique hi ((tendsto_reflectionCubicBoundary_zero hε hδ t).congr' (he.mono (fun _ h => h.symm)))
  dsimp only [D] at hzero
  rw [integral_add (integrable_reflectionCubicFlux hε hδ t)
    ((integrable_reflectionCubicDensity hε hδ t).const_mul ((t:ℂ)*Complex.I)),integral_const_mul] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- Height saving for the actual full cubic error integral. -/
theorem height_mul_norm_reflectionCubic_integral_le {δ ε : ℝ} (hε : 0 < ε)
    (hδ : |δ| ≤ 1/2-ε) (t : ℝ) :
    |t| * ‖∫ x in Ioi (1:ℝ), reflectionCubicDensity δ t x‖ ≤ |δ|^3*reflectionCubicHeightCost ε := by
  have hn : ‖∫ x in Ioi (1:ℝ), reflectionCubicFlux δ t x‖ ≤ |δ|^3*reflectionCubicHeightCost ε := by
    rw [←integral_reflectionCubicMajorant hε,←integral_const_mul]
    apply norm_integral_le_of_norm_le ((integrable_reflectionCubicMajorant hε).const_mul (|δ|^3))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [reflectionCubicFlux,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
      Real.exp_zero,mul_one]
    exact abs_reflectionCubicDerivative_le hx.le hδ
  have h := congrArg norm (reflectionCubic_flux_identity hε hδ t)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,norm_neg] at h
  exact h ▸ hn

/-- The literal positive-real complex power retains exactly the source's logarithmic height phase. -/
theorem fullFourier_cpow_eq_logMode (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(-star s-2) = (x^(-(s.re+2)):ℝ)*Complex.exp (((s.im*Real.log x:ℝ):ℂ)*Complex.I) := by
  have h := fourier_mul_cpow_eq_mode 0 (star s) hx
  simpa only [fourier_zero,one_mul,Complex.star_def,Complex.conj_re,Complex.conj_im,
    neg_neg,Int.cast_zero,mul_zero,logarithmicFourierMode,zero_mul,zero_add] using h

/-- Absolute integrability of the literal full Fourier density. -/
theorem integrable_unitFullFourierDensity {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun x : ℝ => ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star s-2)) (Ioi (1:ℝ)) := by
  have hb : IntegrableOn (fun x : ℝ => (RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2)) (Ioi (1:ℝ)) := by
    simpa only [Nat.cast_one,show -star s-1-1=-star s-2 by ring] using
      RHTower.integrableOn_bernoulli_cpow (show -1 < (star s).re by simpa) (by omega : 1≤(1:ℕ))
  have hc := integrableOn_Ioi_cpow_of_lt
    (show (-star s-2).re < -1 by simp only [Complex.sub_re,Complex.neg_re,Complex.star_def,Complex.conj_re]; norm_num; linarith) zero_lt_one
  apply (hb.add (hc.const_mul (1/12:ℂ))).congr
  filter_upwards with x
  simp only [Pi.add_apply]
  push_cast
  ring

/-- The full previously reconstructed source error is exactly the actual cubic residual integral. -/
theorem unitFullFourierSource_error_eq_cubic {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) :
    unitFullFourierSource s-unitFullFourierSource (1-star s)+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im =
      ∫ x in Ioi (1:ℝ), reflectionCubicDensity (s.re-1/2) s.im x := by
  have hi := integrable_unitFullFourierDensity (by linarith : -1 < s.re)
  have hr : -1 < (1-star s).re := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; linarith
  have hj := integrable_unitFullFourierDensity hr
  have hd : IntegrableOn (fun x : ℝ =>
      ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star s-2)-
      ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star (1-star s)-2)) (Ioi (1:ℝ)) := hi.sub hj
  rw [←integral_criticalLogSourceDensity]
  unfold unitFullFourierSource
  rw [←integral_sub hi hj,←integral_const_mul,
    ←integral_add hd ((integrable_criticalLogSourceDensity s.im).const_mul (((2*(s.re-1/2):ℝ):ℂ)))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  rw [fullFourier_cpow_eq_logMode s hx0,fullFourier_cpow_eq_logMode (1-star s) hx0]
  simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re,
    Complex.sub_im,Complex.one_im,Complex.conj_im,zero_sub,neg_neg]
  unfold criticalLogSourceDensity reflectionCubicDensity reflectionCubicKernel
  have hp := congrArg Complex.ofReal (incoming_reflected_power_identity hx0 (s.re-1/2))
  rw [show -(5/2:ℝ)-(s.re-1/2)=-(s.re+2) by ring,
    show -(5/2:ℝ)+(s.re-1/2)=-((1-s.re)+2) by ring] at hp
  push_cast at hp ⊢
  linear_combination (((RHTower.bernoulliPeriodic x:ℂ)+1/12)*
    Complex.exp ((s.im:ℂ)*(Real.log x:ℂ)*Complex.I))*hp

/-- The complete reflected source error has uniform cubic displacement and inverse-height control. -/
theorem height_mul_norm_unitFullFourierSource_error_le {s : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hδ : |s.re-1/2| ≤ 1/2-ε) :
    |s.im| * ‖unitFullFourierSource s-unitFullFourierSource (1-star s)+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im‖ ≤
      |s.re-1/2|^3*reflectionCubicHeightCost ε := by
  have hd := abs_le.mp hδ
  rw [unitFullFourierSource_error_eq_cubic (by linarith : 0 ≤ s.re) (by linarith : s.re ≤ 1)]
  exact height_mul_norm_reflectionCubic_integral_le hε hδ s.im

/-- The complete complex zero-constraint disk gains inverse-height decay on every compact substrip. -/
theorem norm_criticalFullLogResponse_zero_constraint_substrip_height {s : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hδ : |s.re-1/2| ≤ 1/2-ε) (hd : s.re ≠ 1/2)
    (ht : s.im ≠ 0) (hz : riemannZeta s=0) :
    ‖criticalFullLogResponse s.im+
      (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
        1/(12*(star s+1)*(2-s)))‖ ≤
      (s.re-1/2)^2*reflectionCubicHeightCost ε/(2*|s.im|) := by
  have hab := abs_le.mp hδ
  have h := height_mul_norm_unitFullFourierSource_error_le hε hδ
  rw [unitFullFourierSource_reflection_at_zero (by linarith : 0 < s.re) (by linarith : s.re < 1) hz,
    show 2*s.re-1=2*(s.re-1/2) by ring,←mul_add,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  rw [pow_succ,sq_abs] at h
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (abs_pos.mpr ht))).mpr
  apply (mul_le_mul_iff_of_pos_right (abs_pos.mpr (sub_ne_zero.mpr hd))).mp
  rw [add_comm] at h
  nlinarith

/-- Every off-line strip zero inherits the improved disk using its actual distance from the strip edges. -/
theorem norm_criticalFullLogResponse_zero_constraint_height {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hd : s.re ≠ 1/2) (ht : s.im ≠ 0) (hz : riemannZeta s=0) :
    ‖criticalFullLogResponse s.im+
      (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
        1/(12*(star s+1)*(2-s)))‖ ≤
      (s.re-1/2)^2*reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|) := by
  have hε : 0 < 1/2-|s.re-1/2| := by
    have ha : |s.re-1/2| < 1/2 := abs_lt.mpr ⟨by linarith,by linarith⟩
    linarith
  exact norm_criticalFullLogResponse_zero_constraint_substrip_height hε (by linarith) hd ht hz

end RHTower.DeletionMixedRefinement
