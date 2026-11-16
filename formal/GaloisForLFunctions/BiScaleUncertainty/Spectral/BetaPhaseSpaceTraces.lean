import GaloisForLFunctions.RHTower.MobiusAbelPrefixFourierMultiplier

/-!
# Beta integrals for triangular and rectangular phase spaces

The nonlinear shear `(x,y) ↦ (x,y + log(1 + exp x))` preserves plane volume
and separates the triangular kernel into two existing logarithmic Beta kernels.
This proves joint integrability and exact Gamma formulas throughout the full
right half-plane of shape parameters. Rectangular kernels separate directly.
-/

open Complex MeasureTheory
open RHTower.CubicGamma
namespace GaloisForLFunctions.BiScaleUncertainty.Spectral
noncomputable section

/-- A translation on each vertical slice, with displacement fixed by the first coordinate. -/
def triangularShear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1, p.2 + Real.log (1 + Real.exp p.1))
  invFun p := (p.1, p.2 - Real.log (1 + Real.exp p.1))
  left_inv p := by rcases p with ⟨x,y⟩; simp
  right_inv p := by rcases p with ⟨x,y⟩; simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.2 + Real.log (1 + Real.exp p.1)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.2 - Real.log (1 + Real.exp p.1)))
    fun_prop

theorem triangularShear_preserving :
    MeasurePreserving triangularShear (volume : Measure (ℝ × ℝ)) volume := by
  change MeasurePreserving triangularShear ((volume : Measure ℝ).prod volume) (volume.prod volume)
  refine ⟨triangularShear.measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply triangularShear.measurable hS,
    Measure.prod_apply (hS.preimage triangularShear.measurable), Measure.prod_apply hS]
  -- Each vertical slice has unchanged one-dimensional volume.
  apply lintegral_congr
  intro x
  change volume ((fun y : ℝ => y + Real.log (1 + Real.exp x)) ⁻¹' {y : ℝ | (x,y) ∈ S}) =
    volume {y : ℝ | (x,y) ∈ S}
  exact (measurePreserving_add_right (volume : Measure ℝ) _).measure_preimage
    ((hS.preimage (measurable_const.prodMk measurable_id)).nullMeasurableSet)


private theorem cpow_pos {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem shiftedBetaLine_translate (u v : ℂ) (r t : ℝ) : Complex.exp (u * (t + r)) *
    ((Real.exp r + Real.exp (t + r) : ℝ) : ℂ) ^ (-(u + v)) =
    Complex.exp (-v * r) *
      (Complex.exp (u * t) * ((1 + Real.exp t : ℝ) : ℂ) ^ (-(u + v))) := by
  have hlog : Real.log (Real.exp r + Real.exp (t + r)) = r + Real.log (1 + Real.exp t) := by
    rw [Real.exp_add]
    rw [show Real.exp r + Real.exp t * Real.exp r = Real.exp r * (1 + Real.exp t) by ring]
    rw [Real.log_mul (Real.exp_pos r).ne' (by positivity), Real.log_exp]
  rw [cpow_pos (by positivity), cpow_pos (by positivity), hlog,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem shiftedBetaLine_integral (u v : ℂ) (r : ℝ) :
    (∫ t : ℝ, Complex.exp (u * t) * ((Real.exp r + Real.exp t : ℝ) : ℂ) ^ (-(u + v))) =
      Complex.exp (-v * r) * Complex.betaIntegral u v := by
  calc
    _ = ∫ t : ℝ, Complex.exp (u * (t + r)) *
        ((Real.exp r + Real.exp (t + r) : ℝ) : ℂ) ^ (-(u + v)) := by
      symm
      simpa only [Complex.ofReal_add] using
        (integral_add_right_eq_self (μ := (volume : Measure ℝ))
          (fun t : ℝ => Complex.exp (u * t) *
            ((Real.exp r + Real.exp t : ℝ) : ℂ) ^ (-(u + v))) r)
    _ = _ := by
      simp only [shiftedBetaLine_translate]
      rw [integral_const_mul, integral_exp_mul_one_add_exp_cpow]

def triangularBetaTrace (a b c : ℂ) : ℂ :=
  ∫ x : ℝ, ∫ y : ℝ,
    Complex.exp (a * x) * Complex.exp (b * y) *
      ((1 + Real.exp x + Real.exp y : ℝ) : ℂ) ^ (-(a + b + c))

theorem triangularBetaTrace_eq (a b c : ℂ) :
    triangularBetaTrace a b c = Complex.betaIntegral a c * Complex.betaIntegral b (a + c) := by
  have hpoint (x : ℝ) :
      (∫ y : ℝ, Complex.exp (a * x) * Complex.exp (b * y) *
        ((1 + Real.exp x + Real.exp y : ℝ) : ℂ) ^ (-(a + b + c))) =
      (Complex.exp (a * x) * ((1 + Real.exp x : ℝ) : ℂ) ^ (-(a + c))) *
        Complex.betaIntegral b (a + c) := by
    simp only [mul_assoc]
    rw [integral_const_mul]
    have hs := shiftedBetaLine_integral b (a + c) (Real.log (1 + Real.exp x))
    rw [Real.exp_log (by positivity), show b + (a + c) = a + b + c by ring] at hs
    rw [hs, cpow_pos (by positivity)]
    rw [show -(a + c) * (Real.log (1 + Real.exp x) : ℂ) =
      (Real.log (1 + Real.exp x) : ℂ) * (-(a + c)) by ring]
  unfold triangularBetaTrace
  simp only [hpoint]
  rw [integral_mul_const, integral_exp_mul_one_add_exp_cpow]

/-- Coordinates covering the entire open right half-plane. -/
def positiveMellinShape (a : ℝ × ℝ) : ℂ := Real.exp a.1 + Complex.I * a.2

theorem positiveMellinShape_re (a : ℝ × ℝ) : (positiveMellinShape a).re = Real.exp a.1 := by
  simp only [positiveMellinShape, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

theorem positiveMellinShape_range :
    Set.range positiveMellinShape = {s : ℂ | 0 < s.re} := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    change 0 < (positiveMellinShape a).re
    rw [positiveMellinShape_re]
    exact Real.exp_pos _
  · intro hs
    refine ⟨(Real.log s.re, s.im), ?_⟩
    apply Complex.ext
    · rw [positiveMellinShape_re]
      exact Real.exp_log hs
    · simp [positiveMellinShape]

private theorem gamma_ne_zero_right {s : ℂ} (hs : 0 < s.re) : Complex.Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  rw [hn] at hs
  simp only [Complex.neg_re, Complex.natCast_re] at hs
  linarith only [hs, Nat.cast_nonneg (α := ℝ) n]

theorem triangularBetaTrace_gamma (a b c : ℝ × ℝ) :
    triangularBetaTrace (positiveMellinShape a) (positiveMellinShape b) (positiveMellinShape c) =
      Complex.Gamma (positiveMellinShape a) * Complex.Gamma (positiveMellinShape b) *
        Complex.Gamma (positiveMellinShape c) /
          Complex.Gamma (positiveMellinShape a + positiveMellinShape b + positiveMellinShape c) := by
  have ha : 0 < (positiveMellinShape a).re := by rw [positiveMellinShape_re]; positivity
  have hb : 0 < (positiveMellinShape b).re := by rw [positiveMellinShape_re]; positivity
  have hc : 0 < (positiveMellinShape c).re := by rw [positiveMellinShape_re]; positivity
  have hac : 0 < (positiveMellinShape a + positiveMellinShape c).re := by
    rw [Complex.add_re]; linarith only [ha, hc]
  have habc : 0 < (positiveMellinShape a + positiveMellinShape b + positiveMellinShape c).re := by
    simp only [Complex.add_re]; linarith only [ha, hb, hc]
  rw [triangularBetaTrace_eq,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ ha hc,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ hb hac,
    show positiveMellinShape b + (positiveMellinShape a + positiveMellinShape c) =
      positiveMellinShape a + positiveMellinShape b + positiveMellinShape c by ring]
  field_simp [gamma_ne_zero_right hac, gamma_ne_zero_right habc]


/-- Beta density in logarithmic coordinates. -/
def betaLineKernel (a b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (a * x) * ((1 + Real.exp x : ℝ) : ℂ) ^ (-(a + b))

/-- Three-term exponential denominator of the triangular phase-space model. -/
def triangularPhaseKernel (a b c : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (a * p.1) * Complex.exp (b * p.2) *
    ((1 + Real.exp p.1 + Real.exp p.2 : ℝ) : ℂ) ^ (-(a + b + c))

theorem triangularPhaseKernel_shear (a b c : ℂ) (p : ℝ × ℝ) :
    triangularPhaseKernel a b c (triangularShear p) =
      betaLineKernel a c p.1 * betaLineKernel b (a + c) p.2 := by
  have ht := shiftedBetaLine_translate b (a + c)
    (Real.log (1 + Real.exp p.1)) p.2
  rw [Real.exp_log (by positivity)] at ht
  change Complex.exp (a * p.1) * Complex.exp (b * ((p.2 + Real.log (1 + Real.exp p.1) : ℝ) : ℂ)) *
    ((1 + Real.exp p.1 + Real.exp (p.2 + Real.log (1 + Real.exp p.1)) : ℝ) : ℂ) ^
      (-(a + b + c)) = _
  rw [Complex.ofReal_add, show a + b + c = b + (a + c) by ring, mul_assoc, ht]
  unfold betaLineKernel
  rw [cpow_pos (x := 1 + Real.exp p.1) (by positivity)]
  rw [show -(a + c) * (Real.log (1 + Real.exp p.1) : ℂ) =
    (Real.log (1 + Real.exp p.1) : ℂ) * (-(a + c)) by ring]
  ring

/-- The genuine integral over the two-dimensional phase plane. -/
def triangularPhaseTrace (a b c : ℂ) : ℂ := ∫ p : ℝ × ℝ, triangularPhaseKernel a b c p

theorem triangularPhaseTrace_eq (a b c : ℂ) :
    triangularPhaseTrace a b c = Complex.betaIntegral a c * Complex.betaIntegral b (a + c) := by
  unfold triangularPhaseTrace
  rw [← triangularShear_preserving.integral_comp' (triangularPhaseKernel a b c)]
  simp only [triangularPhaseKernel_shear]
  change (∫ p, betaLineKernel a c p.1 * betaLineKernel b (a + c) p.2
    ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_mul]
  simp only [betaLineKernel, integral_exp_mul_one_add_exp_cpow]

theorem triangularPhaseKernel_integrable (a b c : ℝ × ℝ) :
    Integrable (triangularPhaseKernel (positiveMellinShape a) (positiveMellinShape b)
      (positiveMellinShape c)) := by
  have ha : 0 < (positiveMellinShape a).re := by rw [positiveMellinShape_re]; positivity
  have hb : 0 < (positiveMellinShape b).re := by rw [positiveMellinShape_re]; positivity
  have hc : 0 < (positiveMellinShape c).re := by rw [positiveMellinShape_re]; positivity
  have hac : 0 < (positiveMellinShape a + positiveMellinShape c).re := by
    rw [Complex.add_re]; linarith only [ha, hc]
  apply (triangularShear_preserving.integrable_comp_emb triangularShear.measurableEmbedding).mp
  simp only [Function.comp_def, triangularPhaseKernel_shear]
  exact (integrable_exp_mul_one_add_exp_cpow ha hc).mul_prod
    (integrable_exp_mul_one_add_exp_cpow hb hac)

theorem triangularPhaseTrace_gamma (a b c : ℝ × ℝ) :
    triangularPhaseTrace (positiveMellinShape a) (positiveMellinShape b) (positiveMellinShape c) =
      Complex.Gamma (positiveMellinShape a) * Complex.Gamma (positiveMellinShape b) *
        Complex.Gamma (positiveMellinShape c) /
          Complex.Gamma (positiveMellinShape a + positiveMellinShape b + positiveMellinShape c) := by
  rw [triangularPhaseTrace_eq, ← triangularBetaTrace_eq, triangularBetaTrace_gamma]

/-- Separable rectangular phase-space trace. -/
def rectangularPhaseTrace (a b c d : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, betaLineKernel a b p.1 * betaLineKernel c d p.2

theorem rectangularPhaseTrace_eq (a b c d : ℂ) :
    rectangularPhaseTrace a b c d = Complex.betaIntegral a b * Complex.betaIntegral c d := by
  unfold rectangularPhaseTrace
  change (∫ p, betaLineKernel a b p.1 * betaLineKernel c d p.2
    ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_mul]
  simp only [betaLineKernel, integral_exp_mul_one_add_exp_cpow]

theorem rectangularPhaseKernel_integrable (a b c d : ℝ × ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      betaLineKernel (positiveMellinShape a) (positiveMellinShape b) p.1 *
        betaLineKernel (positiveMellinShape c) (positiveMellinShape d) p.2) := by
  exact (integrable_exp_mul_one_add_exp_cpow
    (by rw [positiveMellinShape_re]; positivity)
    (by rw [positiveMellinShape_re]; positivity)).mul_prod
      (integrable_exp_mul_one_add_exp_cpow
        (by rw [positiveMellinShape_re]; positivity)
        (by rw [positiveMellinShape_re]; positivity))

theorem rectangularPhaseTrace_gamma (a b c d : ℝ × ℝ) :
    rectangularPhaseTrace (positiveMellinShape a) (positiveMellinShape b)
      (positiveMellinShape c) (positiveMellinShape d) =
      (Complex.Gamma (positiveMellinShape a) * Complex.Gamma (positiveMellinShape b) /
        Complex.Gamma (positiveMellinShape a + positiveMellinShape b)) *
      (Complex.Gamma (positiveMellinShape c) * Complex.Gamma (positiveMellinShape d) /
        Complex.Gamma (positiveMellinShape c + positiveMellinShape d)) := by
  rw [rectangularPhaseTrace_eq,
    Complex.betaIntegral_eq_Gamma_mul_div _ _
      (by rw [positiveMellinShape_re]; positivity) (by rw [positiveMellinShape_re]; positivity),
    Complex.betaIntegral_eq_Gamma_mul_div _ _
      (by rw [positiveMellinShape_re]; positivity) (by rw [positiveMellinShape_re]; positivity)]

#print axioms triangularShear_preserving
#print axioms positiveMellinShape_range
#print axioms triangularPhaseKernel_shear
#print axioms triangularPhaseKernel_integrable
#print axioms triangularPhaseTrace_gamma
#print axioms rectangularPhaseKernel_integrable
#print axioms rectangularPhaseTrace_gamma

end
end GaloisForLFunctions.BiScaleUncertainty.Spectral
