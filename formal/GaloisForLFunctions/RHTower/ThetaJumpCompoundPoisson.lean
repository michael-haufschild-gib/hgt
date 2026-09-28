import GaloisForLFunctions.RHTower.ThetaReflectedJumpExponents
import GaloisForLFunctions.HTGeometry.OscillatoryPacketFourier

/-!
# The theta dispersion semigroup is a symmetric compound Poisson family

The finite positive Lévy measure `dν = ω(x)/x dx` on `(0, ∞)` has mass `m > 0`.  The jump law
`J` draws a magnitude from `ν/m` and an independent fair sign, so `φ_J(u) = (1/m)∫₀^∞ cos(ux) dν`;
its convolution powers have characteristic functions `φ_J^n`.  For `t ≥ 0` the compound Poisson
law `Σ_n e^{-tm}(tm)^n/n! J^{⋆n}` (rate `tm`) is a probability measure with characteristic
function `exp(-t(m - ∫cos(u·) dν)) = e^{-tG(u)}`.  The semigroup `e^{-tG}` extends to an entire
nowhere-zero function of `z`.
-/
open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The symmetric jump law -/

/-- The total Lévy mass `m = ν((0, ∞)) = ∫₀^∞ ω(x)/x dx`. -/
def thetaLevyMass : ℝ := ∫ x in Ioi (0 : ℝ), thetaLevyDensity x

theorem thetaLevyMass_pos : 0 < thetaLevyMass :=
  setIntegral_Ioi_pos integrableOn_thetaLevyDensity fun _ hx => thetaLevyDensity_pos hx

/-- The normalized jump density `ν/m` as a nonnegative density. -/
def thetaJumpMagnitudeDensity (x : ℝ) : ℝ≥0 := Real.toNNReal (thetaLevyDensity x / thetaLevyMass)

theorem measurable_thetaJumpMagnitudeDensity : Measurable thetaJumpMagnitudeDensity := by
  have h : Measurable thetaLevyDensity := by
    unfold thetaLevyDensity
    exact continuous_thetaJumpDensity.measurable.div measurable_id
  exact (h.div_const _).real_toNNReal

/-- The jump-magnitude law `ν/m` on `(0, ∞)`. -/
def thetaJumpMagnitudeLaw : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => (thetaJumpMagnitudeDensity x : ℝ≥0∞)

theorem integral_thetaJumpMagnitudeLaw (g : ℝ → ℂ) :
    ∫ x, g x ∂thetaJumpMagnitudeLaw =
      ∫ x in Ioi (0 : ℝ), ((thetaLevyDensity x / thetaLevyMass : ℝ) : ℂ) * g x := by
  rw [thetaJumpMagnitudeLaw, integral_withDensity_eq_integral_smul
    measurable_thetaJumpMagnitudeDensity]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : (0 : ℝ) < x := hx
  rw [NNReal.smul_def, thetaJumpMagnitudeDensity,
    Real.coe_toNNReal _ (div_nonneg (thetaLevyDensity_pos hx).le thetaLevyMass_pos.le),
    Complex.real_smul]

instance : IsProbabilityMeasure thetaJumpMagnitudeLaw := by
  constructor
  rw [thetaJumpMagnitudeLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x => thetaLevyDensity x / thetaLevyMass) (volume.restrict (Ioi 0)) :=
    integrableOn_thetaLevyDensity.div_const _
  have h := ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx =>
      div_nonneg (thetaLevyDensity_pos hx).le thetaLevyMass_pos.le))
  rw [integral_div, show (∫ a in Ioi (0 : ℝ), thetaLevyDensity a) = thetaLevyMass from rfl,
    div_self thetaLevyMass_pos.ne', ENNReal.ofReal_one] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  simp [thetaJumpMagnitudeDensity, ENNReal.ofReal]

/-- The symmetric jump law: magnitude `∼ ν/m` with an independent fair sign. -/
def thetaSymmetricJumpLaw : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (thetaJumpMagnitudeLaw + thetaJumpMagnitudeLaw.map Neg.neg)

instance : IsProbabilityMeasure thetaSymmetricJumpLaw := by
  constructor
  have h1 : thetaJumpMagnitudeLaw univ = 1 := measure_univ
  have h2 : thetaJumpMagnitudeLaw.map Neg.neg univ = 1 := by
    rw [Measure.map_apply measurable_neg MeasurableSet.univ, preimage_univ, h1]
  rw [thetaSymmetricJumpLaw, Measure.smul_apply, Measure.add_apply, h1, h2, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem thetaSymmetricJumpLaw_map_neg : thetaSymmetricJumpLaw.map Neg.neg = thetaSymmetricJumpLaw := by
  rw [thetaSymmetricJumpLaw, Measure.map_smul, Measure.map_add _ _ measurable_neg,
    Measure.map_map measurable_neg measurable_neg]
  simp only [Function.comp_def, neg_neg, Measure.map_id', add_comm]

theorem integrableOn_thetaLevyDensity_mul_cexp (c : ℝ) :
    IntegrableOn (fun x : ℝ => ((thetaLevyDensity x / thetaLevyMass : ℝ) : ℂ) * cexp (↑c * ↑x * I))
      (Ioi 0) := by
  have h := (integrableOn_thetaLevyDensity.div_const thetaLevyMass).norm
  refine h.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_thetaLevyDensity.div_const _)).mul
      (by fun_prop : Continuous fun x : ℝ => cexp (↑c * ↑x * I)).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  · rw [norm_mul, show (c : ℂ) * x * I = ((c * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

/-- The characteristic function of the jump law is `(1/m) ∫₀^∞ cos(ux) ω(x)/x dx`. -/
theorem charFun_thetaSymmetricJumpLaw (u : ℝ) :
    charFun thetaSymmetricJumpLaw u =
      (((∫ x in Ioi (0 : ℝ), thetaLevyDensity x * Real.cos (u * x)) / thetaLevyMass : ℝ) : ℂ) := by
  have hb : ∀ x : ℝ, ‖cexp (↑u * ↑x * I)‖ ≤ 1 := fun x => by
    rw [show (u : ℂ) * x * I = ((u * x : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hm : Continuous fun x : ℝ => cexp (↑u * ↑x * I) := by fun_prop
  have hi1 : Integrable (fun x : ℝ => cexp (↑u * ↑x * I)) thetaJumpMagnitudeLaw :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)
  haveI : IsProbabilityMeasure (thetaJumpMagnitudeLaw.map Neg.neg) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  have hi2 : Integrable (fun x : ℝ => cexp (↑u * ↑x * I)) (thetaJumpMagnitudeLaw.map Neg.neg) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)
  rw [charFun_apply_real, thetaSymmetricJumpLaw, integral_smul_measure, integral_add_measure hi1 hi2,
    integral_map measurable_neg.aemeasurable hm.aestronglyMeasurable,
    integral_thetaJumpMagnitudeLaw, integral_thetaJumpMagnitudeLaw]
  have e2 : ∀ x : ℝ, cexp (↑u * ↑(-x) * I) = cexp (↑(-u) * ↑x * I) := fun x => by
    push_cast; ring_nf
  simp_rw [e2]
  rw [← integral_add (integrableOn_thetaLevyDensity_mul_cexp u)
    (integrableOn_thetaLevyDensity_mul_cexp (-u))]
  rw [show ((2⁻¹ : ℝ≥0∞)).toReal = 1 / 2 by simp, Complex.real_smul, ← integral_const_mul,
    show (((∫ x in Ioi (0 : ℝ), thetaLevyDensity x * Real.cos (u * x)) / thetaLevyMass : ℝ) : ℂ)
      = ((∫ x in Ioi (0 : ℝ), thetaLevyDensity x * Real.cos (u * x) / thetaLevyMass : ℝ) : ℂ) by
        rw [integral_div], ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show ((-u : ℝ) : ℂ) * (x : ℂ) * I = -(((u * x : ℝ) : ℂ) * I) by push_cast; ring,
    show (u : ℂ) * (x : ℂ) * I = ((u * x : ℝ) : ℂ) * I by push_cast; ring,
    ← mul_add, add_comm (cexp _), GaloisForLFunctions.HTGeometry.cexp_neg_mul_I_add_cexp_mul_I]
  push_cast; ring

/-! ## The compound Poisson law -/

/-- The convolution powers `J^{⋆n}` of the jump law. -/
def thetaJumpConvPow : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => thetaSymmetricJumpLaw ∗ thetaJumpConvPow n

instance (n : ℕ) : IsProbabilityMeasure (thetaJumpConvPow n) := by
  induction n with
  | zero => simp only [thetaJumpConvPow]; infer_instance
  | succ n ih => simp only [thetaJumpConvPow]; infer_instance

theorem charFun_thetaJumpConvPow (n : ℕ) (u : ℝ) :
    charFun (thetaJumpConvPow n) u = charFun thetaSymmetricJumpLaw u ^ n := by
  induction n with
  | zero => simp [thetaJumpConvPow, charFun_dirac]
  | succ n ih => rw [thetaJumpConvPow, charFun_conv, ih, pow_succ, mul_comm]

/-- The Poisson weights `e^{-λ} λ^n/n!` with rate `λ = t ν((0, ∞))`. -/
def thetaPoissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(t * thetaLevyMass)) * (t * thetaLevyMass) ^ n / n.factorial

theorem thetaPoissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ thetaPoissonWeight t n := by
  have := thetaLevyMass_pos
  unfold thetaPoissonWeight; positivity

theorem hasSum_thetaPoissonWeight (t : ℝ) : HasSum (thetaPoissonWeight t) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (t * thetaLevyMass)).mul_left
    (Real.exp (-(t * thetaLevyMass)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun fun n => ?_
  rw [thetaPoissonWeight, mul_div_assoc]

/-- The symmetric compound Poisson law with rate `t ν((0, ∞))`: a Poisson number of independent
jumps, each of magnitude `∼ ν/m` with a fair sign. -/
def thetaCompoundPoissonLaw (t : ℝ) : Measure ℝ :=
  Measure.sum fun n => ENNReal.ofReal (thetaPoissonWeight t n) • thetaJumpConvPow n

theorem isProbabilityMeasure_thetaCompoundPoissonLaw {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (thetaCompoundPoissonLaw t) := by
  constructor
  rw [thetaCompoundPoissonLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (thetaPoissonWeight_nonneg ht)
    (hasSum_thetaPoissonWeight t).summable, (hasSum_thetaPoissonWeight t).tsum_eq,
    ENNReal.ofReal_one]

/-- `G(u) = m - ∫₀^∞ cos(ux) dν`. -/
theorem thetaDispersionExponentReal_eq (u : ℝ) :
    thetaDispersionExponentReal u =
      thetaLevyMass - ∫ x in Ioi (0 : ℝ), thetaLevyDensity x * Real.cos (u * x) := by
  have hcos : IntegrableOn (fun x => thetaLevyDensity x * Real.cos (u * x)) (Ioi 0) := by
    refine integrableOn_thetaLevyDensity.norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (continuousOn_thetaLevyDensity.mul (by fun_prop : Continuous fun x : ℝ =>
        Real.cos (u * x)).continuousOn).aestronglyMeasurable measurableSet_Ioi
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [thetaDispersionExponentReal, thetaLevyMass, ← integral_sub integrableOn_thetaLevyDensity hcos]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- **The Lévy–Khintchine identity.** For `t ≥ 0`, `e^{-tG(u)}` is the characteristic function of
the symmetric compound Poisson law. -/
theorem charFun_thetaCompoundPoissonLaw {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    charFun (thetaCompoundPoissonLaw t) u = cexp (-(t * thetaDispersionExponentReal u)) := by
  haveI := isProbabilityMeasure_thetaCompoundPoissonLaw ht
  have hm : Continuous fun x : ℝ => cexp (↑u * ↑x * I) := by fun_prop
  have hint : Integrable (fun x : ℝ => cexp (↑u * ↑x * I)) (thetaCompoundPoissonLaw t) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [show (u : ℂ) * x * I = ((u * x : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply_real, thetaCompoundPoissonLaw, integral_sum_measure hint]
  simp_rw [integral_smul_measure, ← charFun_apply_real, charFun_thetaJumpConvPow,
    ENNReal.toReal_ofReal (thetaPoissonWeight_nonneg ht _), charFun_thetaSymmetricJumpLaw]
  set φ : ℝ := (∫ x in Ioi (0 : ℝ), thetaLevyDensity x * Real.cos (u * x)) / thetaLevyMass
  set lam := t * thetaLevyMass
  have h := ((NormedSpace.expSeries_div_hasSum_exp ((lam * φ : ℝ) : ℂ)).mul_left
    ((Real.exp (-lam) : ℝ) : ℂ))
  rw [← Complex.exp_eq_exp_ℂ] at h
  have hsum : HasSum (fun n => thetaPoissonWeight t n • ((φ : ℂ)) ^ n)
      ((Real.exp (-lam) : ℂ) * cexp ((lam * φ : ℝ) : ℂ)) := by
    refine h.congr_fun fun n => ?_
    rw [thetaPoissonWeight, Complex.real_smul]
    simp only [lam]
    push_cast
    ring
  rw [hsum.tsum_eq, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hm0 : (thetaLevyMass : ℂ) ≠ 0 := by exact_mod_cast thetaLevyMass_pos.ne'
  rw [thetaDispersionExponentReal_eq]
  simp only [φ, lam]
  push_cast
  field_simp
  ring

/-- The semigroup `e^{-tG}` extends to an entire nowhere-zero function of `z`. -/
theorem differentiable_cexp_neg_mul_thetaDispersionExponent (t : ℂ) :
    Differentiable ℂ (fun z => cexp (-t * thetaDispersionExponent z)) ∧
      ∀ z, cexp (-t * thetaDispersionExponent z) ≠ 0 :=
  ⟨fun z => (hasDerivAt_cexp_neg_mul_thetaDispersionExponent t z).differentiableAt,
    fun _ => Complex.exp_ne_zero _⟩

end

end RHTower
