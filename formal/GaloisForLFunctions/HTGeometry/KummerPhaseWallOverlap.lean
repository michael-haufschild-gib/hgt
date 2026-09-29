import GaloisForLFunctions.HTGeometry.PhaseCoherenceIntegral
import GaloisForLFunctions.HTGeometry.SourceStokesComovingLanding
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison
import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier

/-!
# Kummer phase mixing of the cubic Stokes wall

On the exponential wall carrier `H = L²((0, ∞), e^{-x} dx)` with the wall operator
`(Af)(x) = ∫ κ(x, y) f(y) e^{-y} dy`, the Kummer phase `(M_τ f)(x) = e^{iτx} f(x)` moves `A` on the
unitary orbit `A_τ = M_τ A M_τ*`.

* **(SKPM.1)** every `A_τ` is positive, Schatten-one, of trace one, with `‖A_τ‖ ≤ 4/√35 < 1`;
  its kernel is `e^{iτx} κ(x, y) e^{-iτy}`.
* **(SKPM.2)–(SKPM.3)** the phase-survival overlap is
  `C(τ) = Re⟨A, A_τ⟩_HS = ∬ κ² e^{-(x+y)} cos(τ(x - y)) = 6 ∫₀¹ v²(1 - v²)²/(1 + τ²v²) dv`.
* **(SKPM.6)** `‖A - A_τ‖²_HS = 32/35 - 2 C(τ)`, since `|1 - e^{iθ}|² = 2 - 2 cos θ`.

Hence the overlap is positive, even, `16/35` at `τ = 0`, strictly decreasing in `|τ|`, with
`C(τ) → 0` and `τ² C(τ) → 16/5`, a normalized `Beta(3/2, 3)` Stieltjes transform, and strictly
completely monotone in `τ²`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_kummer : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

local instance factTwoNeTopKummer : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## The phase orbit -/

/-- The Kummer phase `x ↦ e^{iτx}` on the exponential wall carrier. -/
def wallPhase (τ : ℝ) : GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ (expMeasure 1) where
  toFun x := Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)
  aestronglyMeasurable := (by fun_prop : Continuous fun x : ℝ =>
    Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  norm_eq_one := Eventually.of_forall fun x => Complex.norm_exp_ofReal_mul_I _

/-- The Kummer phase multiplier `M_τ`. -/
def phaseMultiplier (τ : ℝ) : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1) :=
  ((wallPhase τ).mulUnitary : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1))

theorem adjoint_phaseMultiplier_comp (τ : ℝ) :
    adjoint (phaseMultiplier τ) ∘L phaseMultiplier τ = ContinuousLinearMap.id ℂ _ := by
  rw [phaseMultiplier, LinearIsometryEquiv.adjoint_eq_symm]
  ext1 f
  exact (wallPhase τ).mulUnitary.symm_apply_apply f

theorem phaseMultiplier_ae (τ : ℝ) (f : Lp ℂ 2 (expMeasure 1)) :
    (phaseMultiplier τ f : ℝ → ℂ) =ᵐ[expMeasure 1]
      fun x => Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * f x :=
  (wallPhase τ).mulUnitary_ae f

theorem adjoint_phaseMultiplier_ae (τ : ℝ) (f : Lp ℂ 2 (expMeasure 1)) :
    (adjoint (phaseMultiplier τ) f : ℝ → ℂ) =ᵐ[expMeasure 1]
      fun x => Complex.exp (((-(τ * x) : ℝ) : ℂ) * Complex.I) * f x := by
  rw [phaseMultiplier, LinearIsometryEquiv.adjoint_eq_symm]
  filter_upwards [(wallPhase τ).conj.mulAux_ae f] with x hx
  change ((wallPhase τ).conj.mulAux f : ℝ → ℂ) x = _
  rw [hx, GaloisForLFunctions.RHTower.UnitModulusL2Phase.conj_apply]
  congr 1
  change (starRingEnd ℂ) (Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

theorem norm_phaseMultiplier_le (τ : ℝ) : ‖phaseMultiplier τ‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul, phaseMultiplier]
    exact le_of_eq ((wallPhase τ).mulUnitary.norm_map f)

/-- **(SKPM.1).**  The phase orbit `A_τ = M_τ A M_τ*`. -/
def phaseWallOperator (τ : ℝ) : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1) :=
  phaseMultiplier τ ∘L wallOperator ∘L adjoint (phaseMultiplier τ)

theorem phaseWallOperator_eq_adjoint_comp (τ : ℝ) :
    phaseWallOperator τ = adjoint (burnolSynthesis ∘L adjoint (phaseMultiplier τ)) ∘L
      (burnolSynthesis ∘L adjoint (phaseMultiplier τ)) := by
  rw [phaseWallOperator, wallOperator_eq_adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_adjoint, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]

theorem isHilbertSchmidt_phaseSynthesis (τ : ℝ) :
    IsHilbertSchmidt (burnolSynthesis ∘L adjoint (phaseMultiplier τ)) :=
  isHilbertSchmidt_burnolSynthesis.comp_right _

theorem isPositive_phaseWallOperator (τ : ℝ) : (phaseWallOperator τ).IsPositive :=
  isPositive_wallOperator.conj_adjoint (phaseMultiplier τ)

theorem memSchattenClass_one_phaseWallOperator (τ : ℝ) :
    MemSchattenClass 1 (phaseWallOperator τ) := by
  rw [phaseWallOperator_eq_adjoint_comp]
  exact memSchattenClass_one_comp (isHilbertSchmidt_phaseSynthesis τ).adjoint
    (isHilbertSchmidt_phaseSynthesis τ)

theorem isHilbertSchmidt_phaseWallOperator (τ : ℝ) : IsHilbertSchmidt (phaseWallOperator τ) := by
  rw [phaseWallOperator_eq_adjoint_comp]
  exact (isHilbertSchmidt_phaseSynthesis τ).comp_left _

theorem opTrace_phaseWallOperator (τ : ℝ) : opTrace (phaseWallOperator τ) = 1 := by
  have h := opTrace_conj_pow_succ (adjoint_phaseMultiplier_comp τ)
    isHilbertSchmidt_burnolSynthesis 0
  rw [zero_add, pow_one, pow_one, ← wallOperator_eq_adjoint_comp, opTrace_wallOperator] at h
  exact h

theorem norm_phaseWallOperator_le (τ : ℝ) : ‖phaseWallOperator τ‖ ≤ 4 / Real.sqrt 35 := by
  have hM := norm_phaseMultiplier_le τ
  have hM' : ‖adjoint (phaseMultiplier τ)‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hM
  refine (opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) hM).trans ?_
  refine (opNorm_comp_le _ _).trans ?_
  exact (mul_le_of_le_one_right (norm_nonneg _) hM').trans norm_wallOperator_le

/-- **(SKPM.1).**  `A_τ ≥ 0`, Schatten-one, `tr A_τ = 1`, `‖A_τ‖ ≤ 4/√35 < 1`. -/
theorem phaseWallOperator_wall (τ : ℝ) :
    (phaseWallOperator τ).IsPositive ∧ MemSchattenClass 1 (phaseWallOperator τ) ∧
      opTrace (phaseWallOperator τ) = 1 ∧ ‖phaseWallOperator τ‖ ≤ 4 / Real.sqrt 35 ∧
      4 / Real.sqrt 35 < 1 :=
  ⟨isPositive_phaseWallOperator τ, memSchattenClass_one_phaseWallOperator τ,
    opTrace_phaseWallOperator τ, norm_phaseWallOperator_le τ, four_div_sqrt_thirtyFive_lt_one⟩

/-! ## The phase kernel -/

theorem norm_phaseKernel (τ x y : ℝ) :
    ‖Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((wallCubicKernel x y : ℝ) : ℂ) *
      Complex.exp (((-(τ * y)) : ℝ) * Complex.I)‖ = ‖((wallCubicKernel x y : ℝ) : ℂ)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul,
    mul_one]

theorem enorm_phaseKernel (τ x y : ℝ) :
    ‖Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((wallCubicKernel x y : ℝ) : ℂ) *
      Complex.exp (((-(τ * y)) : ℝ) * Complex.I)‖ₑ = ‖((wallCubicKernel x y : ℝ) : ℂ)‖ₑ := by
  rw [← enorm_norm, norm_phaseKernel, enorm_norm]

/-- The phase kernel `e^{iτx} κ(x, y) e^{-iτy}`. -/
def phaseWallKernel (τ : ℝ) : SqIntKernel (expMeasure 1) (expMeasure 1) where
  toFun x y := Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((wallCubicKernel x y : ℝ) : ℂ) *
    Complex.exp (((-(τ * y)) : ℝ) * Complex.I)
  measurable := by
    have hk : Measurable fun p : ℝ × ℝ => ((wallCubicKernel p.1 p.2 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp continuous_wallCubicKernel_sq
    exact ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      Complex.exp (((τ * p.1 : ℝ) : ℂ) * Complex.I)).mul hk).mul
      (by fun_prop : Measurable fun p : ℝ × ℝ => Complex.exp (((-(τ * p.2)) : ℝ) * Complex.I))
  energy_lt_top := by
    simp_rw [enorm_phaseKernel]
    exact wallKernel.energy_lt_top

theorem energy_phaseWallKernel (τ : ℝ) : (phaseWallKernel τ).energy = wallKernel.energy := by
  change ∫⁻ x, ∫⁻ y, ‖Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) *
      ((wallCubicKernel x y : ℝ) : ℂ) * Complex.exp (((-(τ * y)) : ℝ) * Complex.I)‖ₑ ^ 2
        ∂(expMeasure 1) ∂(expMeasure 1) = _
  simp_rw [enorm_phaseKernel]
  rfl

/-- `A_τ` is the kernel operator of `e^{iτx} κ(x, y) e^{-iτy}`. -/
theorem phaseWallKernel_op (τ : ℝ) : (phaseWallKernel τ).op = phaseWallOperator τ := by
  ext1 f
  refine Lp.ext ?_
  set g := adjoint (phaseMultiplier τ) f
  have h1 := phaseMultiplier_ae τ (wallOperator g)
  have h2 := wallKernel.op_coeFn g
  have h3 := (phaseWallKernel τ).op_coeFn f
  have hg := adjoint_phaseMultiplier_ae τ f
  filter_upwards [h1, h2, h3] with x h1 h2 h3
  rw [h3]
  change _ = (phaseMultiplier τ (wallOperator g) : ℝ → ℂ) x
  rw [h1]
  change _ = _ * (wallKernel.op g : ℝ → ℂ) x
  rw [h2]
  change ∫ y, (Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((wallCubicKernel x y : ℝ) : ℂ) *
      Complex.exp (((-(τ * y)) : ℝ) * Complex.I)) * f y ∂(expMeasure 1)
    = Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) *
      ∫ y, ((wallCubicKernel x y : ℝ) : ℂ) * g y ∂(expMeasure 1)
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hg] with y hy
  rw [hy]
  ring

theorem hsNormSq_phaseWallOperator (τ : ℝ) :
    ContinuousLinearMap.hsNormSq (phaseWallOperator τ) = 16 / 35 := by
  rw [← phaseWallKernel_op, SqIntKernel.hsNormSq_op, energy_phaseWallKernel, wallKernel_energy,
    ENNReal.toReal_ofReal (by norm_num)]

/-! ## The overlap -/

theorem norm_one_sub_exp_mul_I_sq (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.sub_im,
    Complex.one_im, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem enorm_wallKernel_sub_phaseKernel_sq (τ x y : ℝ) :
    ‖((wallCubicKernel x y : ℝ) : ℂ) - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) *
        ((wallCubicKernel x y : ℝ) : ℂ) * Complex.exp (((-(τ * y)) : ℝ) * Complex.I)‖ₑ ^ 2
      = ENNReal.ofReal (wallCubicKernel x y ^ 2 * (2 - 2 * Real.cos (τ * (x - y)))) := by
  have hfac : ((wallCubicKernel x y : ℝ) : ℂ) - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) *
        ((wallCubicKernel x y : ℝ) : ℂ) * Complex.exp (((-(τ * y)) : ℝ) * Complex.I)
      = ((wallCubicKernel x y : ℝ) : ℂ) *
          (1 - Complex.exp (((τ * (x - y) : ℝ) : ℂ) * Complex.I)) := by
    have he : Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-(τ * y)) : ℝ) * Complex.I)
          = Complex.exp (((τ * (x - y) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [mul_sub, mul_one, ← he]
    ring
  rw [hfac, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_mul, mul_pow,
    norm_one_sub_exp_mul_I_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **(SKPM.6).**  `‖A - A_τ‖²_HS = 32/35 - 2 C(τ)`. -/
theorem hsNormSq_wallOperator_sub_phaseWallOperator (τ : ℝ) :
    ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator τ)
      = 32 / 35 - 2 * phaseSurvivalProfile τ := by
  set F : ℝ × ℝ → ℝ := fun z =>
    routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
      (2 - 2 * Real.cos (τ * (z.1 - z.2)))
  have hFm : Measurable F := by
    unfold F routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
    fun_prop
  have hint : Integrable F ((expMeasure 1).prod (expMeasure 1)) := by
    refine Integrable.mono' (integrable_const (4 : ℝ)) hFm.aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
      ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
    have h := routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one h1 h2
    have hc := Real.neg_one_le_cos (τ * (z.1 - z.2))
    have hc' := Real.cos_le_one (τ * (z.1 - z.2))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1 (by linarith))]
    nlinarith
  have hF0 : 0 ≤ᵐ[(expMeasure 1).prod (expMeasure 1)] F := by
    filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
      ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
    exact mul_nonneg (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one
      h1 h2).1 (by linarith [Real.cos_le_one (τ * (z.1 - z.2))])
  have henergy : (wallKernel.sub (phaseWallKernel τ)).energy
      = ENNReal.ofReal (∫ z, F z ∂((expMeasure 1).prod (expMeasure 1))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hF0]
    change ∫⁻ x, ∫⁻ y, ‖((wallCubicKernel x y : ℝ) : ℂ) -
      Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((wallCubicKernel x y : ℝ) : ℂ) *
        Complex.exp (((-(τ * y)) : ℝ) * Complex.I)‖ₑ ^ 2 ∂(expMeasure 1) ∂(expMeasure 1) = _
    simp_rw [enorm_wallKernel_sub_phaseKernel_sq]
    rw [lintegral_prod _ hFm.ennreal_ofReal.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_expMeasure_one] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_expMeasure_one] with y hy
    simp only [F]
    rw [wallCubicKernel_sq hx.le hy.le]
  have hval : ∫ z, F z ∂((expMeasure 1).prod (expMeasure 1))
      = 32 / 35 - 2 * phaseSurvivalProfile τ := by
    have hcoh := integrable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod
    have hcos : Integrable (fun z : ℝ × ℝ =>
        routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
          Real.cos (τ * (z.1 - z.2))) ((expMeasure 1).prod (expMeasure 1)) := by
      refine hcoh.norm.mono' ?_ ?_
      · unfold routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
        exact (by fun_prop : Measurable _).aestronglyMeasurable
      · refine Eventually.of_forall fun z => ?_
        rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
    have hsplit : F = fun z => 2 * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
        z.1 z.2 - 2 * (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
          Real.cos (τ * (z.1 - z.2))) := by
      funext z
      simp only [F]
      ring
    rw [hsplit, integral_sub (hcoh.const_mul 2) (hcos.const_mul 2), integral_const_mul,
      integral_const_mul,
      integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq,
      integral_coherence_mul_cos]
    ring
  have hop : wallOperator - phaseWallOperator τ = (wallKernel.sub (phaseWallKernel τ)).op := by
    rw [SqIntKernel.op_sub, phaseWallKernel_op]
    rfl
  have hle : phaseSurvivalProfile τ ≤ 16 / 35 := by
    have h := phaseSurvivalProfile_strictAntiOn.antitoneOn (Set.self_mem_Ici (a := (0 : ℝ)))
      (show |τ| ∈ Ici 0 from abs_nonneg τ) (abs_nonneg τ)
    rw [phaseSurvivalProfile_zero] at h
    rcases abs_choice τ with hτ | hτ <;> rw [hτ] at h
    · exact h
    · rwa [phaseSurvivalProfile_neg] at h
  rw [hop, SqIntKernel.hsNormSq_op, henergy, hval, ENNReal.toReal_ofReal (by linarith)]

/-- The phase-survival overlap `C(τ) = Re⟨A, A_τ⟩_HS`. -/
def phaseSurvivalOverlap (τ : ℝ) : ℝ := (hsInner wallOperator (phaseWallOperator τ)).re

/-- **Theorem A (SKPM.3).**  `C(τ) = Re⟨A, A_τ⟩_HS = 6 ∫₀¹ v²(1 - v²)²/(1 + τ²v²) dv`. -/
theorem phaseSurvivalOverlap_eq (τ : ℝ) : phaseSurvivalOverlap τ = phaseSurvivalProfile τ := by
  have h := hsNormSq_sub isHilbertSchmidt_wallOperator (isHilbertSchmidt_phaseWallOperator τ)
  rw [hsNormSq_wallOperator_sub_phaseWallOperator, hsNormSq_wallOperator,
    hsNormSq_phaseWallOperator] at h
  rw [phaseSurvivalOverlap]
  change RCLike.re (hsInner wallOperator (phaseWallOperator τ)) = _
  linarith

/-- **Theorems A–C.**  The Kummer phase overlap is a positive, even, strictly mixing,
completely monotone resolvent transform with the universal `16/(5τ²)` tail. -/
theorem kummer_phase_mixing :
    (∀ τ, phaseSurvivalOverlap τ
        = ∫ z, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
            Real.cos (τ * (z.1 - z.2)) ∂((expMeasure 1).prod (expMeasure 1))) ∧
      (∀ τ, 0 < phaseSurvivalOverlap τ) ∧
      (∀ τ, phaseSurvivalOverlap (-τ) = phaseSurvivalOverlap τ) ∧
      phaseSurvivalOverlap 0 = 16 / 35 ∧
      StrictAntiOn phaseSurvivalOverlap (Ici 0) ∧
      Tendsto phaseSurvivalOverlap atTop (𝓝 0) ∧ Tendsto phaseSurvivalOverlap atBot (𝓝 0) ∧
      Tendsto (fun τ => τ ^ 2 * phaseSurvivalOverlap τ) atTop (𝓝 (16 / 5)) ∧
      Tendsto (fun τ => τ ^ 2 * phaseSurvivalOverlap τ) atBot (𝓝 (16 / 5)) ∧
      (∀ τ, ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator τ)
        = 32 / 35 - 2 * phaseSurvivalOverlap τ) ∧
      (∀ q, 0 ≤ q → phaseSurvivalOverlap (Real.sqrt q) / (16 / 35)
        = ∫ s, 1 / (1 + q * s) ∂phaseBetaLaw) := by
  have hC : phaseSurvivalOverlap = phaseSurvivalProfile := funext phaseSurvivalOverlap_eq
  rw [hC]
  exact ⟨fun τ => (integral_coherence_mul_cos τ).symm, phaseSurvivalProfile_pos,
    phaseSurvivalProfile_neg, phaseSurvivalProfile_zero, phaseSurvivalProfile_strictAntiOn,
    tendsto_phaseSurvivalProfile_atTop, tendsto_phaseSurvivalProfile_atBot,
    tendsto_sq_mul_phaseSurvivalProfile_atTop, tendsto_sq_mul_phaseSurvivalProfile_atBot,
    hsNormSq_wallOperator_sub_phaseWallOperator, fun q hq => phaseSurvivalProfile_sqrt_div hq⟩

/-- **(SKPM.6).**  `‖A - A_τ‖²_HS` increases strictly in `|τ|` from `0` to `32/35`. -/
theorem hsNormSq_wallOperator_sub_phaseWallOperator_mixing :
    ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator 0) = 0 ∧
      StrictMonoOn (fun τ => ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator τ))
        (Ici 0) ∧
      Tendsto (fun τ => ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator τ)) atTop
        (𝓝 (32 / 35)) ∧
      Tendsto (fun τ => ContinuousLinearMap.hsNormSq (wallOperator - phaseWallOperator τ)) atBot
        (𝓝 (32 / 35)) := by
  simp_rw [hsNormSq_wallOperator_sub_phaseWallOperator]
  refine ⟨by rw [phaseSurvivalProfile_zero]; norm_num, fun a ha b hb hab => ?_, ?_, ?_⟩
  · have := phaseSurvivalProfile_strictAntiOn ha hb hab
    linarith
  · have := (tendsto_phaseSurvivalProfile_atTop.const_mul 2).const_sub (32 / 35 : ℝ)
    simpa using this
  · have := (tendsto_phaseSurvivalProfile_atBot.const_mul 2).const_sub (32 / 35 : ℝ)
    simpa using this

/-- **Theorem C.**  `C(√q) = F(q) = 3 ∫₀¹ λ^{1/2}(1 - λ)²/(1 + qλ) dλ` for `q ≥ 0`, and
`(-1)ⁿ F⁽ⁿ⁾(q) = 6 n! ∫₀¹ v^{2n+2}(1 - v²)²/(1 + qv²)^{n+1} dv > 0` with
`(-1)ⁿ F⁽ⁿ⁾(0) = 48 n!/((2n+3)(2n+5)(2n+7))`. -/
theorem phaseSurvivalOverlap_beta_completelyMonotone :
    (∀ q, 0 ≤ q → phaseSurvivalOverlap (Real.sqrt q) = phaseResponse q) ∧
      (∀ q, 0 ≤ q → phaseResponse q
        = 3 * ∫ s in (0 : ℝ)..1, Real.sqrt s * (1 - s) ^ 2 / (1 + q * s)) ∧
      (∀ (n : ℕ) (q : ℝ), 0 ≤ q →
        (-1) ^ n * iteratedDeriv n phaseResponse q = 6 * n.factorial * phaseResponseMoment n q ∧
          0 < (-1) ^ n * iteratedDeriv n phaseResponse q) ∧
      (∀ n : ℕ, (-1) ^ n * iteratedDeriv n phaseResponse 0
        = 48 * n.factorial / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7))) :=
  ⟨fun q hq => by rw [phaseSurvivalOverlap_eq, phaseSurvivalProfile, Real.sq_sqrt hq],
    fun q hq => phaseResponse_eq_beta (by linarith),
    fun n q hq => phaseResponse_completelyMonotone n hq, phaseResponse_jet_zero⟩

end GaloisForLFunctions.HTGeometry
