import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.WeightedCausalExponentialReflection

/-!
# Real profiles for causal exponential reflection

The real convolution and reflection have exactly the complex representatives
used by the Fourier multiplier. Measurability and negative-half-line support
therefore belong to the actual profiles, without choosing new representatives.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- The real normalized causal resolvent kernel. -/
def realCausalExponential (a : ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun t => Real.pi * Real.exp (-(Real.pi * a * t)))

/-- Literal real exponential convolution. -/
def realCausalConvolution (a : ℝ) (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t, realCausalExponential a t * F (y - t)

/-- A real profile acted on by one causal Blaschke factor. -/
def realCausalReflection (a : ℝ) (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  -F y + 2 * a * realCausalConvolution a F y

theorem coe_realCausalExponential (a t : ℝ) :
    (realCausalExponential a t : ℂ) = causalFourierExponential a t := by
  unfold realCausalExponential causalFourierExponential
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht, indicator_of_mem ht, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, Complex.ofReal_zero]

theorem coe_realCausalConvolution (a : ℝ) (F : ℝ → ℝ) (y : ℝ) :
    (realCausalConvolution a F y : ℂ) =
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun u => (F u : ℂ))) y := by
  unfold realCausalConvolution
  rw [convolution_def]
  calc
    _ = ∫ t, ((realCausalExponential a t * F (y - t) : ℝ) : ℂ) := integral_complex_ofReal.symm
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [Complex.ofReal_mul, coe_realCausalExponential]
      rfl

theorem coe_realCausalReflection (a : ℝ) (F : ℝ → ℝ) (y : ℝ) :
    (realCausalReflection a F y : ℂ) = causalBlaschkeStep a (fun u => (F u : ℂ)) y := by
  unfold realCausalReflection causalBlaschkeStep
  push_cast
  rw [coe_realCausalConvolution]

theorem measurable_realCausalExponential (a : ℝ) : Measurable (realCausalExponential a) :=
  (by fun_prop : Continuous (fun t : ℝ => Real.pi * Real.exp (-(Real.pi * a * t)))).measurable.indicator
    measurableSet_Ioi

theorem measurable_realCausalConvolution (a : ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (realCausalConvolution a F) := by
  have hs : StronglyMeasurable (realCausalConvolution a F) := by
    apply StronglyMeasurable.integral_prod_right
    exact (((measurable_realCausalExponential a).comp measurable_snd).mul
      (hF.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact hs.measurable

theorem measurable_realCausalReflection (a : ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (realCausalReflection a F) :=
  hF.neg.add (measurable_const.mul (measurable_realCausalConvolution a hF))

/-- A real Laplace zero preserves the actual reflected profile's half-line support. -/
theorem realCausalReflection_support_of_laplace_zero (a : ℝ) {F : ℝ → ℝ}
    (hF : ∀ u, 0 ≤ u → F u = 0)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) :
    ∀ y, 0 ≤ y → realCausalReflection a F y = 0 := by
  have hzc : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * (F u : ℂ)) = 0 := by
    calc
      _ = ((∫ u, Real.exp (Real.pi * a * u) * F u : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        simp only [Complex.ofReal_mul, Complex.ofReal_exp]
      _ = 0 := by rw [hz, Complex.ofReal_zero]
  intro y hy
  have hc := causalBlaschkeStep_support_of_laplace_zero a (f := fun u => (F u : ℂ))
    (fun u hu => by rw [hF u hu, Complex.ofReal_zero]) hzc y hy
  rw [← coe_realCausalReflection] at hc
  exact_mod_cast hc

/-- The real resolvent is integrable whenever its input is. -/
theorem integrable_realCausalConvolution {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : Integrable F) : Integrable (realCausalConvolution a F) := by
  have hc := (causalFourierExponential_integrable ha).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (hF.ofReal (𝕜 := ℂ))
  apply hc.re.congr
  exact Eventually.of_forall fun y => (congrArg Complex.re (coe_realCausalConvolution a F y)).symm

/-- Real reflection preserves ordinary absolute integrability. -/
theorem integrable_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF : Integrable F) : Integrable (realCausalReflection a F) :=
  hF.neg.add ((integrable_realCausalConvolution ha hF).const_mul (2 * a))

/-- The complex weighted square is exactly the real exponential mass. -/
theorem norm_sq_causalLaplaceWeighted_real (x : ℝ) (F : ℝ → ℝ) (u : ℝ) :
    ‖causalLaplaceWeighted x (fun t => (F t : ℂ)) u‖ ^ 2 =
      F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)) := by
  simp only [causalLaplaceWeighted, norm_mul, mul_pow, Complex.norm_exp,
    Complex.neg_re, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have he : Real.exp (-(Real.pi * x * u)) ^ 2 = Real.exp (-(2 * Real.pi * x * u)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, mul_comm]

/-- Actual real weighted mass gives the complex L² datum used by the resolvent. -/
theorem memLp_causalLaplaceWeighted_real {x : ℝ} {F : ℝ → ℝ} (hF : Integrable F)
    (hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)))) :
    MemLp (causalLaplaceWeighted x (fun u => (F u : ℂ))) 2 volume := by
  have hm : AEStronglyMeasurable (causalLaplaceWeighted x (fun u => (F u : ℂ))) :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(Real.pi * x * u : ℝ)))).aestronglyMeasurable.mul
      (hF.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_sq_causalLaplaceWeighted_real] using hw

/-- The real resolvent preserves the full exponential square domain. -/
theorem integrable_weighted_sq_realCausalConvolution {a x : ℝ} (hb : 0 < a + x)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)))) :
    Integrable (fun u => realCausalConvolution a F u ^ 2 * Real.exp (-(2 * Real.pi * x * u))) := by
  have hc := memLp_weighted_causalExponentialConvolution hb (memLp_causalLaplaceWeighted_real hF hw)
  have he : (fun u => (realCausalConvolution a F u : ℂ)) =
      causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun u => (F u : ℂ)) :=
    funext (coe_realCausalConvolution a F)
  rw [← he] at hc
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  simpa only [norm_sq_causalLaplaceWeighted_real] using hi

/-- The real reflected profile preserves the full exponential square domain. -/
theorem integrable_weighted_sq_realCausalReflection {a x : ℝ} (hb : 0 < a + x)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)))) :
    Integrable (fun u => realCausalReflection a F u ^ 2 * Real.exp (-(2 * Real.pi * x * u))) := by
  have hc := memLp_weighted_causalBlaschkeStep hb (memLp_causalLaplaceWeighted_real hF hw)
  have he : (fun u => (realCausalReflection a F u : ℂ)) = causalBlaschkeStep a (fun u => (F u : ℂ)) :=
    funext (coe_realCausalReflection a F)
  rw [← he] at hc
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  simpa only [norm_sq_causalLaplaceWeighted_real] using hi

/-- Exact exponential-mass loss for the actual real reflection. -/
theorem realCausalReflection_weighted_energy {a x : ℝ} (hb : 0 < a + x)
    {F : ℝ → ℝ} (hF : Integrable F)
    (hw : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)))) :
    (∫ u, F u ^ 2 * Real.exp (-(2 * Real.pi * x * u))) =
      (∫ u, realCausalReflection a F u ^ 2 * Real.exp (-(2 * Real.pi * x * u))) +
      (4 * a * x) * ∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(2 * Real.pi * x * u)) := by
  have hc := integral_weighted_causalBlaschkeStep_energy hb (memLp_causalLaplaceWeighted_real hF hw)
  have he1 : (fun u => (realCausalReflection a F u : ℂ)) = causalBlaschkeStep a (fun u => (F u : ℂ)) :=
    funext (coe_realCausalReflection a F)
  have he2 : (fun u => (realCausalConvolution a F u : ℂ)) =
      causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun u => (F u : ℂ)) :=
    funext (coe_realCausalConvolution a F)
  rw [← he1, ← he2] at hc
  simpa only [norm_sq_causalLaplaceWeighted_real] using hc

/-- The unweighted square domain is the zero-weight case. -/
theorem integrable_sq_realCausalReflection {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2)) :
    Integrable (fun u => realCausalReflection a F u ^ 2) := by
  have h0 : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * 0 * u))) := by
    simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] using hF2
  simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] using
    integrable_weighted_sq_realCausalReflection (a := a) (x := 0)
      (by simpa only [add_zero] using ha) hF1 h0

/-- The normalized complex Laplace weight of a real profile is its literal real weight. -/
theorem causalLaplaceWeighted_real_eq (x : ℝ) (F : ℝ → ℝ) (u : ℝ) :
    causalLaplaceWeighted x (fun t => (F t : ℂ)) u =
      ((F u * Real.exp (-(Real.pi * x * u)) : ℝ) : ℂ) := by
  unfold causalLaplaceWeighted
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  ring

/-- Real and complex Laplace integrals have exactly the same normalization. -/
theorem causalLaplaceIntegral_real_eq (x : ℝ) (F : ℝ → ℝ) :
    causalLaplaceIntegral x (fun u => (F u : ℂ)) =
      ((∫ u, F u * Real.exp (-(Real.pi * x * u)) : ℝ) : ℂ) := by
  unfold causalLaplaceIntegral
  simp only [causalLaplaceWeighted_real_eq, integral_complex_ofReal]

/-- A real Laplace zero removes the actual resolvent's positive tail. -/
theorem realCausalConvolution_support_of_laplace_zero (a : ℝ) {F : ℝ → ℝ}
    (hF : ∀ u, 0 ≤ u → F u = 0)
    (hz : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0) :
    ∀ y, 0 ≤ y → realCausalConvolution a F y = 0 := by
  have hzc : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * (F u : ℂ)) = 0 := by
    calc
      _ = ((∫ u, Real.exp (Real.pi * a * u) * F u : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        simp only [Complex.ofReal_mul, Complex.ofReal_exp]
      _ = 0 := by rw [hz, Complex.ofReal_zero]
  intro y hy
  have hc := causalExponentialConvolution_support_of_laplace_zero a (f := fun u => (F u : ℂ))
    (fun u hu => by rw [hF u hu, Complex.ofReal_zero]) hzc y hy
  rw [← coe_realCausalConvolution] at hc
  exact_mod_cast hc

/-- The real resolvent also preserves the unweighted square domain. -/
theorem integrable_sq_realCausalConvolution {a : ℝ} (ha : 0 < a)
    {F : ℝ → ℝ} (hF1 : Integrable F) (hF2 : Integrable (fun u => F u ^ 2)) :
    Integrable (fun u => realCausalConvolution a F u ^ 2) := by
  have h0 : Integrable (fun u => F u ^ 2 * Real.exp (-(2 * Real.pi * 0 * u))) := by
    simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] using hF2
  simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] using
    integrable_weighted_sq_realCausalConvolution (a := a) (x := 0)
      (by simpa only [add_zero] using ha) hF1 h0

end GaloisForLFunctions.HTGeometry
