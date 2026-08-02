import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezin
import GaloisForLFunctions.RHTower.RealCharacterDenseL2
import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.PositiveOperatorKernel
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Faithfulness of the co-Poisson Berezin diagonal

The completed Mellin quotient kernels on Burnol's right strip have dense span.  The proof changes
variables by `x = exp t`, turns the Mellin evaluations into all real characters of one integrable
logarithmic density, invokes uniqueness of those characters, then uses the exact logarithmic
unitary for even `L²` functions.

Consequently, positivity makes the Berezin diagonal faithful on operators supported on the closed
quotient `L_b ∩ C_bᵮ`.  Quotient operators are represented canonically as their ambient
zero-extensions `T = E_b T E_b`, where `E_b` is the orthogonal quotient projection.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Change of variables `x = exp t` for complex integrals on the positive half-line. -/
theorem integral_Ioi_eq_integral_exp_smul (g : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), g x) = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  rw [← Real.range_exp, ← Set.image_univ]
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using
    (MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g)

/-- Integrability form of the logarithmic change of variables. -/
theorem integrableOn_Ioi_iff_integrable_exp_smul (g : ℝ → ℂ) :
    IntegrableOn g (Ioi (0 : ℝ)) ↔
      Integrable (fun t : ℝ => Real.exp t • g (Real.exp t)) := by
  rw [← Real.range_exp, ← Set.image_univ,
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn,
    integrableOn_univ]
  simp only [abs_of_pos (Real.exp_pos _)]

/-- Logarithmic density whose Fourier characters are completed Mellin evaluations. -/
def burnolLogMellinDensity (sigma : ℝ) (f : evenSubspace) (t : ℝ) : ℂ :=
  Complex.exp (((1 - sigma) * t : ℝ) : ℂ) *
    (((f : evenSubspace) : SoninL2) (Real.exp t))

theorem exp_smul_mellinIntegrand_eq_character_mul_density
    (sigma tau t : ℝ) (f : evenSubspace) :
    (Real.exp t) •
        ((((f : evenSubspace) : SoninL2) (Real.exp t)) *
          soninMellinKernel ((sigma : ℂ) - (tau : ℂ) * Complex.I) (Real.exp t)) =
      realProbCharacter tau t * burnolLogMellinDensity sigma f t := by
  rw [soninMellinKernel_eq_exp (Real.exp_pos t)]
  simp only [Complex.real_smul, burnolLogMellinDensity, realProbCharacter]
  rw [show ((Real.exp t : ℝ) : ℂ) = Complex.exp (t : ℂ) by
    rw [← Complex.ofReal_exp]]
  rw [Real.log_exp]
  calc
    Complex.exp (t : ℂ) *
        ((((f : evenSubspace) : SoninL2) (Real.exp t)) *
          Complex.exp ((t : ℂ) * (-((sigma : ℂ) - (tau : ℂ) * Complex.I)))) =
        Complex.exp ((t : ℂ) +
          (t : ℂ) * (-((sigma : ℂ) - (tau : ℂ) * Complex.I))) *
          (((f : evenSubspace) : SoninL2) (Real.exp t)) := by
            rw [Complex.exp_add]
            ring
    _ = Complex.exp (((tau * t : ℝ) : ℂ) * Complex.I +
          (((1 - sigma) * t : ℝ) : ℂ)) *
          (((f : evenSubspace) : SoninL2) (Real.exp t)) := by
            congr 2
            push_cast
            ring
    _ = Complex.exp (((tau * t : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((((1 - sigma) * t : ℝ) : ℂ)) *
            (((f : evenSubspace) : SoninL2) (Real.exp t))) := by
              rw [Complex.exp_add]
              ring

theorem integrable_burnolLogMellinDensity
    {b sigma : ℝ} (hlo : 1 / 2 < sigma) (hhi : sigma < 1) (hb : 0 < b)
    (f : soninExtendedSpace b) :
    Integrable (burnolLogMellinDensity sigma (f : evenSubspace)) := by
  have hbase := integrableOn_extendedSonin_mul_mellinKernel
    (w := (sigma : ℂ)) (by simpa using hlo) (by simpa using hhi) hb f
  rw [integrableOn_Ioi_iff_integrable_exp_smul] at hbase
  refine hbase.congr ?_
  filter_upwards with t
  simpa [realProbCharacter] using
    (exp_smul_mellinIntegrand_eq_character_mul_density sigma 0 t (f : evenSubspace))

/-- Completed Mellin evaluation as the Fourier transform of the logarithmic density. -/
theorem soninMellinEvaluation_eq_logFourier
    (sigma tau : ℝ) (f : evenSubspace) :
    soninMellinEvaluation ((sigma : ℂ) - (tau : ℂ) * Complex.I)
        ((((f : evenSubspace) : SoninL2)) : ℝ → ℂ) =
      mellinCompletionFactor ((sigma : ℂ) - (tau : ℂ) * Complex.I) *
        ∫ t : ℝ, realProbCharacter tau t * burnolLogMellinDensity sigma f t := by
  rw [soninMellinEvaluation, integral_Ioi_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact exp_smul_mellinIntegrand_eq_character_mul_density sigma tau t f

theorem mellinCompletionFactor_ne_zero_of_re_pos
    {w : ℂ} (hw : 0 < w.re) : mellinCompletionFactor w ≠ 0 := by
  rw [mellinCompletionFactor]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · apply Complex.Gamma_ne_zero_of_re_pos
    simpa [Complex.div_re] using (half_pos hw)

/-- Completed Mellin evaluations throughout the right strip separate the actual quotient. -/
theorem burnolCoPoissonQuotientEvaluation_separates
    {b : ℝ} (hb : 0 < b) (f : burnolCoPoissonQuotientSpace b)
    (hzero : ∀ (w : ℂ) (_hlo : 1 / 2 < w.re) (_hhi : w.re < 1),
      soninMellinEvaluation w ((((f : evenSubspace) : SoninL2)) : ℝ → ℂ) = 0) :
    f = 0 := by
  let sigma : ℝ := 3 / 4
  have hslo : 1 / 2 < sigma := by norm_num [sigma]
  have hshi : sigma < 1 := by norm_num [sigma]
  let fext : soninExtendedSpace b := ⟨(f : evenSubspace), f.property.1⟩
  have hdint : Integrable (burnolLogMellinDensity sigma (f : evenSubspace)) :=
    integrable_burnolLogMellinDensity hslo hshi hb fext
  have hdmeas : Measurable (burnolLogMellinDensity sigma (f : evenSubspace)) := by
    exact (Complex.continuous_exp.measurable.comp
      (Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_id))).mul
      ((Lp.stronglyMeasurable (((f : evenSubspace) : SoninL2))).measurable.comp
        Real.measurable_exp)
  have hfourier (tau : ℝ) :
      ∫ t : ℝ, realProbCharacter tau t *
        burnolLogMellinDensity sigma (f : evenSubspace) t = 0 := by
    let w : ℂ := (sigma : ℂ) - (tau : ℂ) * Complex.I
    have hwre : w.re = sigma := by simp [w]
    have hz := hzero w (by rw [hwre]; exact hslo) (by rw [hwre]; exact hshi)
    rw [show w = (sigma : ℂ) - (tau : ℂ) * Complex.I from rfl,
      soninMellinEvaluation_eq_logFourier] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (mellinCompletionFactor_ne_zero_of_re_pos (by rw [hwre]; norm_num [sigma]))
  have hdzero : burnolLogMellinDensity sigma (f : evenSubspace) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
      (volume : Measure ℝ) hdmeas hdint hfourier
  have hlogzero : logEvenFun (f : evenSubspace) =ᵐ[volume] 0 := by
    filter_upwards [hdzero] with t ht
    have hfexp : (((f : evenSubspace) : SoninL2) (Real.exp t)) = 0 := by
      exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)
    simp [logEvenFun, hfexp]
  have haux : logEvenAux (f : evenSubspace) = 0 := by
    apply Lp.ext
    filter_upwards [logEvenAux_ae (f : evenSubspace), hlogzero,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t haux ht hzero
    rw [haux, ht, hzero]
  have hfeven : (f : evenSubspace) = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_logEvenAux, haux, norm_zero]
  exact Subtype.ext hfeven

/-- Right-strip points at which the completed Mellin evaluator is continuous. -/
def BurnolCoPoissonRightPoint :=
  {w : ℂ // 1 / 2 < w.re ∧ w.re < 1}

/-- Quotient reproducing kernels indexed by the full right regularity strip. -/
def burnolCoPoissonQuotientEvaluationFamily
    (b : ℝ) (hb : 0 < b) (w : BurnolCoPoissonRightPoint) :
    burnolCoPoissonQuotientSpace b :=
  burnolCoPoissonQuotientEvaluationVector w.1 b w.property.1 w.property.2 hb

/-- The actual quotient evaluation kernels have dense linear span. -/
theorem isCyclicFamily_burnolCoPoissonQuotientEvaluationFamily
    {b : ℝ} (hb : 0 < b) :
    IsCyclicFamily (𝕜 := ℂ)
      (burnolCoPoissonQuotientEvaluationFamily b hb) := by
  letI : NormedSpace ℂ (burnolCoPoissonQuotientSpace b) :=
    (burnolCoPoissonQuotientSpace b).normedSpace
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  change Dense (Submodule.span ℂ
    (Set.range (burnolCoPoissonQuotientEvaluationFamily b hb)) :
      Set (burnolCoPoissonQuotientSpace b))
  refine @dense_span_of_forall_dual_eq_zero
    (burnolCoPoissonQuotientSpace b) BurnolCoPoissonRightPoint
    (burnolCoPoissonQuotientSpace b).normedAddCommGroup
    (burnolCoPoissonQuotientSpace b).normedSpace
    (burnolCoPoissonQuotientEvaluationFamily b hb) ?_
  intro L hL
  let g : burnolCoPoissonQuotientSpace b :=
    (InnerProductSpace.toDual ℂ (burnolCoPoissonQuotientSpace b)).symm L
  have hEval (w : BurnolCoPoissonRightPoint) :
      soninMellinEvaluation w.1 ((((g : evenSubspace) : SoninL2)) : ℝ → ℂ) = 0 := by
    have h := hL w
    change L (burnolCoPoissonQuotientEvaluationFamily b hb w) = 0 at h
    have hinner : ⟪g, burnolCoPoissonQuotientEvaluationFamily b hb w⟫_ℂ = 0 := by
      simpa [g, InnerProductSpace.toDual_symm_apply] using h
    have hinner' :
        ⟪burnolCoPoissonQuotientEvaluationFamily b hb w, g⟫_ℂ = 0 := by
      rw [inner_eq_zero_symm]
      exact hinner
    rw [burnolCoPoissonQuotientEvaluationFamily,
      inner_burnolCoPoissonQuotientEvaluationVector] at hinner'
    exact hinner'
  have hgzero : g = 0 := by
    apply burnolCoPoissonQuotientEvaluation_separates hb g
    intro w hlo hhi
    exact hEval ⟨w, hlo, hhi⟩
  calc
    L = (InnerProductSpace.toDual ℂ (burnolCoPoissonQuotientSpace b)) g := by
      symm
      exact (InnerProductSpace.toDual ℂ
        (burnolCoPoissonQuotientSpace b)).apply_symm_apply L
    _ = (InnerProductSpace.toDual ℂ (burnolCoPoissonQuotientSpace b)) 0 := by
      exact congrArg
        (InnerProductSpace.toDual ℂ (burnolCoPoissonQuotientSpace b)) hgzero
    _ = 0 := (InnerProductSpace.toDual ℂ
      (burnolCoPoissonQuotientSpace b)).map_zero

/-- Orthogonal projection onto the closed source quotient `L_b ∩ C_bᵮ`. -/
def burnolCoPoissonQuotientProjection (b : ℝ) (hb : 0 < b) :
    evenSubspace →L[ℂ] evenSubspace := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  exact (burnolCoPoissonQuotientSpace b).starProjection

theorem burnolCoPoissonQuotientProjection_apply_mem
    (b : ℝ) (hb : 0 < b) (f : evenSubspace) :
    burnolCoPoissonQuotientProjection b hb f ∈ burnolCoPoissonQuotientSpace b := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  exact (burnolCoPoissonQuotientSpace b).starProjection_apply_mem f

/-- Ambient zero-extension characterization of operators on the closed quotient. -/
def BurnolCoPoissonQuotientSupported
    {b : ℝ} (hb : 0 < b) (T : evenSubspace →L[ℂ] evenSubspace) : Prop :=
  T = burnolCoPoissonQuotientProjection b hb ∘L T ∘L
    burnolCoPoissonQuotientProjection b hb

/-- The Berezin diagonal family is faithful on positive quotient-supported operators. -/
theorem burnolCoPoissonBerezin_faithful_of_quotientSupported
    {b : ℝ} (hb : 0 < b) {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : T.IsPositive) (hsupport : BurnolCoPoissonQuotientSupported hb T)
    (hzero : ∀ w : BurnolCoPoissonRightPoint,
      burnolCoPoissonBerezin T w.1 w.property.1 w.property.2 hb = 0) :
    T = 0 := by
  have hTy (w : BurnolCoPoissonRightPoint) :
      T (burnolCoPoissonQuotientEvaluationFamily b hb w : evenSubspace) = 0 := by
    let y : evenSubspace := burnolCoPoissonQuotientEvaluationFamily b hb w
    have hz := hzero w
    change ⟪y, T y⟫_ℂ = 0 at hz
    exact hT.apply_eq_zero_of_inner_eq_zero hz
  let TQ : burnolCoPoissonQuotientSpace b →L[ℂ] evenSubspace :=
    T.comp (burnolCoPoissonQuotientSpace b).subtypeL
  have hTQzero : TQ = 0 := by
    refine ContinuousLinearMap.ext_on
      (isCyclicFamily_burnolCoPoissonQuotientEvaluationFamily hb) ?_
    rintro _ ⟨w, rfl⟩
    change T (burnolCoPoissonQuotientEvaluationFamily b hb w : evenSubspace) = 0
    exact hTy w
  have hT_on_quotient (q : burnolCoPoissonQuotientSpace b) :
      T (q : evenSubspace) = 0 := by
    have h := congrArg (fun A : burnolCoPoissonQuotientSpace b →L[ℂ] evenSubspace => A q)
      hTQzero
    simpa [TQ] using h
  have hTE (x : evenSubspace) :
      T (burnolCoPoissonQuotientProjection b hb x) = 0 := by
    exact hT_on_quotient
      ⟨burnolCoPoissonQuotientProjection b hb x,
        burnolCoPoissonQuotientProjection_apply_mem b hb x⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [hsupport]
  simp only [ContinuousLinearMap.comp_apply, hTE, map_zero]
  rfl

end RHTower
