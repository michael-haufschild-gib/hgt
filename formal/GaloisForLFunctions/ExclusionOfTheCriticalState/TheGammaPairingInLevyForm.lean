import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateHasPolesAtTheZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy

/-!
# The Gamma pairing in Lévy form

On the energy domain the Gamma form is a mass term plus a Lévy jump energy,
`archForm F = 2θ'(0) ∫ F² + ∫_{x>0} ω(x) ∫ (F(u) - F(u+x))² du dx` (AHD). Polarizing gives the
mixed form `γ(F,G) = 2θ'(0) ∫ FG + ∫_{x>0} ω(x) ∫ ΔₓF ΔₓG`. On a probe the inner integral is explicit:

  `∫ (F(u) - F(u+x)) (e_p(u) - e_p(u+x)) du = L F(p) (2 - e^{-px}) - e^{px} ∫_{u<-x} F(u) e^{pu} du`.

The density `ω(x) = e^{-x/2}/(1 - e^{-2x})` decays like `e^{-x/2}`, so this formula makes sense for
every `Re p > -½`: the Gamma pairing continues across the critical line without contour deformation.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The mixed Lévy jump energy. -/
def levyMixed (F G : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi 0, archLevyDensity x * ∫ u, (F u - F (u + x)) * (G u - G (u + x))

theorem memLp_two_shift {F : ℝ → ℝ} (hF : MemLp F 2 volume) (x : ℝ) :
    MemLp (fun u => F (u + x)) 2 volume :=
  hF.comp_measurePreserving (measurePreserving_add_right volume x)

theorem integrable_sq_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Integrable fun u => f u ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

theorem integrable_mul_of_memLp {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable fun u => f u * g u := by
  refine ((integrable_sq_of_memLp hf).add (integrable_sq_of_memLp hg)).mono'
    (hf.1.mul hg.1) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (f u + g u), sq_nonneg (f u - g u)]

/-- **Polarized Lévy form.** On the energy domain `γ(F,G) = 2θ'(0) ∫ FG + levyMixed F G`. -/
theorem gammaMixedForm_eq_levy {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    gammaMixedForm F G = 2 * gammaHardyPhaseRate 0 * (∫ u, F u * G u) + levyMixed F G := by
  have hp := archForm_add_const_mul_of_integrable hF.integrable hG.integrable hF.gamma hG.gamma 1
  have hm := archForm_add_const_mul_of_integrable hF.integrable hG.integrable hF.gamma hG.gamma (-1)
  have hdp := hF.add_const_mul hG 1
  have hdm := hF.add_const_mul hG (-1)
  have ep := hdp.archForm_eq_levyEnergy
  have em := hdm.archForm_eq_levyEnergy
  have hFm := hF.memLp_real
  have hGm := hG.memLp_real
  have hsq : (∫ u, (F u + 1 * G u) ^ 2) - (∫ u, (F u + -1 * G u) ^ 2) = 4 * ∫ u, F u * G u := by
    rw [← integral_sub hdp.sq hdm.sq, ← integral_const_mul]
    congr 1; funext u; ring
  have hjump : levyEnergy (fun u => F u + 1 * G u) - levyEnergy (fun u => F u + -1 * G u) =
      4 * levyMixed F G := by
    simp only [levyEnergy, levyMixed]
    rw [← integral_sub hdp.integrableOn_levyIntegrand hdm.integrableOn_levyIntegrand,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hΔF : MemLp (fun u => F u - F (u + x)) 2 volume := hFm.sub (memLp_two_shift hFm x)
    have hΔG : MemLp (fun u => G u - G (u + x)) 2 volume := hGm.sub (memLp_two_shift hGm x)
    have iP : Integrable fun u => (F u + 1 * G u - (F (u + x) + 1 * G (u + x))) ^ 2 :=
      (integrable_sq_of_memLp (hΔF.add hΔG)).congr (Eventually.of_forall fun u => by
        simp only [Pi.add_apply]; ring)
    have iM : Integrable fun u => (F u + -1 * G u - (F (u + x) + -1 * G (u + x))) ^ 2 :=
      (integrable_sq_of_memLp (hΔF.sub hΔG)).congr (Eventually.of_forall fun u => by
        simp only [Pi.sub_apply]; ring)
    rw [← mul_sub, ← integral_sub iP iM, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    congr 1; funext u; ring
  linear_combination (-(1 : ℝ) / 4) * hp + (1 / 4) * hm + (1 / 4) * ep - (1 / 4) * em +
    (gammaHardyPhaseRate 0 / 2) * hsq + (1 / 4) * hjump

theorem memLp_two_probe {p : ℝ} (hp : 0 < p) : MemLp (probe p) 2 volume := by
  refine (memLp_two_iff_integrable_sq (measurable_probe p).aestronglyMeasurable).mpr ?_
  simp_rw [sq, probe_mul_probe]
  exact integrable_probe (by linarith)

/-- **The Lévy inner integral on a probe.** -/
theorem levyInner_probe {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℝ} (hp : 0 < p)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ u, (F u - F (u + x)) * (probe p u - probe p (u + x))) =
      (∫ u, F u * Real.exp (p * u)) * (2 - Real.exp (-(p * x))) -
        Real.exp (p * x) * ∫ u in Iio (-x), F u * Real.exp (p * u) := by
  have hFm := hF.memLp_real
  have hFx := memLp_two_shift hFm x
  have hPm := memLp_two_probe hp
  have hPx := memLp_two_shift hPm x
  have i1 := integrable_mul_of_memLp hFm hPm
  have i2 := integrable_mul_of_memLp hFm hPx
  have i3 := integrable_mul_of_memLp hFx hPm
  have i4 := integrable_mul_of_memLp hFx hPx
  have hexp : (fun u => (F u - F (u + x)) * (probe p u - probe p (u + x))) = fun u =>
      (F u * probe p u - F u * probe p (u + x)) - (F (u + x) * probe p u -
        F (u + x) * probe p (u + x)) := by
    funext u; ring
  have h1 : (∫ u, F u * probe p u) = ∫ u, F u * Real.exp (p * u) := by
    have := integral_mul_probe_sub hF.support p (le_refl (0 : ℝ))
    simpa using this
  have h2 := integral_mul_probe_add F p x
  have h3 : (∫ u, F (u + x) * probe p u) = Real.exp (-(p * x)) * ∫ u, F u * Real.exp (p * u) := by
    have h := integral_add_right_eq_self (μ := volume) (fun v => F v * probe p (v - x)) x
    simp only [add_sub_cancel_right] at h
    rw [h, integral_mul_probe_sub hF.support p hx]
  have h4 : (∫ u, F (u + x) * probe p (u + x)) = ∫ u, F u * Real.exp (p * u) := by
    rw [integral_add_right_eq_self (μ := volume) (fun v => F v * probe p v) x, h1]
  have i12 : Integrable fun u => F u * probe p u - F u * probe p (u + x) := i1.sub i2
  have i34 : Integrable fun u => F (u + x) * probe p u - F (u + x) * probe p (u + x) := i3.sub i4
  rw [hexp, integral_sub i12 i34, integral_sub i1 i2, integral_sub i3 i4, h1, h2, h3, h4]
  ring

/-- **The Gamma pairing of a probe in Lévy form.** -/
theorem gammaMixedForm_probe_levy {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℝ}
    (hp : 4 < p) :
    gammaMixedForm F (probe p) = 2 * gammaHardyPhaseRate 0 * (∫ u, F u * Real.exp (p * u)) +
      ∫ x in Ioi 0, archLevyDensity x * ((∫ u, F u * Real.exp (p * u)) *
        (2 - Real.exp (-(p * x))) - Real.exp (p * x) * ∫ u in Iio (-x), F u * Real.exp (p * u)) := by
  rw [gammaMixedForm_eq_levy hF (criticalHalfLineEnergyDomain_probe hp)]
  have h1 : (∫ u, F u * probe p u) = ∫ u, F u * Real.exp (p * u) := by
    have := integral_mul_probe_sub hF.support p (le_refl (0 : ℝ))
    simpa using this
  rw [h1]
  congr 1
  unfold levyMixed
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [levyInner_probe hF (by linarith) (le_of_lt hx)]

/-! ### The holomorphic Lévy pairing -/

/-- The tail transform `∫_{u<-x} e^{pu} F(u) du`. -/
def levyTail (F : ℝ → ℝ) (p : ℂ) (x : ℝ) : ℂ := ∫ u in Iio (-x), cexp (p * u) * (F u : ℂ)

/-- The Lévy kernel at probe exponent `p` and jump length `x`. -/
def levyKernel (F : ℝ → ℝ) (p : ℂ) (x : ℝ) : ℂ :=
  negativeHalfLineLaplace (cx F) p * (2 - cexp (-(p * x))) - cexp (p * x) * levyTail F p x

/-- The Lévy integrand, zero off `x > 0`. -/
def levyIntegrand (F : ℝ → ℝ) (p : ℂ) (x : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun x => (archLevyDensity x : ℂ) * levyKernel F p x) x

/-- The Gamma pairing of a profile with the probe of exponent `p`, in Lévy form. -/
def levyGamma (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  2 * gammaHardyPhaseRate 0 * negativeHalfLineLaplace (cx F) p + ∫ x, levyIntegrand F p x

theorem archLevyDensity_le_near {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    archLevyDensity x ≤ 3 / (2 * x) := by
  unfold archLevyDensity
  set E := Real.exp (-2 * x) with hEdef
  have hE1 : E * (1 + 2 * x) ≤ 1 := by
    have h := Real.add_one_le_exp (2 * x)
    have hm : E * Real.exp (2 * x) = 1 := by rw [hEdef, ← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-2 * x)]
  have hE0 : 0 < E := Real.exp_pos _
  have hden : 0 < 1 - E := by nlinarith
  have hh : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [div_le_div_iff₀ hden (by positivity)]
  nlinarith [Real.exp_pos (-x / 2)]

theorem archLevyDensity_le_far {x : ℝ} (hx : 1 ≤ x) :
    archLevyDensity x ≤ 2 * Real.exp (-(x / 2)) := by
  unfold archLevyDensity
  have hE : Real.exp (-2 * x) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (2 * x)
    have hm : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-2 * x), Real.exp_pos (2 * x)]
  have hden : 0 < 1 - Real.exp (-2 * x) := by linarith
  rw [div_le_iff₀ hden, show -x / 2 = -(x / 2) by ring]
  nlinarith [Real.exp_pos (-(x / 2))]

/-- The half-pole mass `∫ |F(u)| e^{-u/2} du`, which bounds every transform on `Re p ≥ -½`. -/
def halfPoleMass (F : ℝ → ℝ) : ℝ := ∫ u, |F u| * Real.exp (-(1 / 2) * u)

theorem norm_laplace_le_halfPoleMass {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) ≤ p.re) : ‖negativeHalfLineLaplace (cx F) p‖ ≤ halfPoleMass F := by
  refine norm_integral_le_of_norm_le (integrable_abs_mul_exp_of_domain hF (by norm_num))
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal]
  simp only [cx, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_ge u 0 with hu | hu
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
  · simp [hF.support u hu]

theorem norm_cexp_mul_levyTail_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) ≤ p.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖cexp (p * x) * levyTail F p x‖ ≤ halfPoleMass F := by
  have hI := integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num)
  unfold levyTail
  rw [← integral_const_mul]
  calc ‖∫ u in Iio (-x), cexp (p * x) * (cexp (p * u) * (F u : ℂ))‖
      ≤ ∫ u in Iio (-x), |F u| * Real.exp (-(1 / 2) * u) := by
        refine norm_integral_le_of_norm_le hI.integrableOn
          ((ae_restrict_iff' measurableSet_Iio).mpr (Eventually.of_forall fun u hu => ?_))
        have hu' : u < -x := hu
        rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, norm_cexp_mul_ofReal, Complex.norm_real,
          Real.norm_eq_abs, ← mul_assoc, ← Real.exp_add, mul_comm (Real.exp _)]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        nlinarith
    _ ≤ halfPoleMass F :=
        setIntegral_le_integral hI (Eventually.of_forall fun u => by positivity)

theorem integrable_cexp_mul_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -4 < p.re) : Integrable fun u => cexp (p * u) * (F u : ℂ) := by
  refine (integrable_abs_mul_exp_of_domain hF hp).mono'
    ((by fun_prop : Continuous fun u : ℝ => cexp (p * u)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hF.meas).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- The transform splits at `-x` into the tail and the head. -/
theorem laplace_eq_levyTail_add {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -4 < p.re) (x : ℝ) :
    negativeHalfLineLaplace (cx F) p =
      levyTail F p x + ∫ u in Ici (-x), cexp (p * u) * (F u : ℂ) := by
  unfold levyTail negativeHalfLineLaplace
  rw [← compl_Iio, integral_add_compl measurableSet_Iio (integrable_cexp_mul_of_domain hF hp)]
  rfl

/-- The head `∫_{-x}^0 |F|` is `O(√x)`. -/
theorem setIntegral_Ici_abs_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {x : ℝ}
    (hx : 0 < x) :
    (∫ u in Ici (-x), |F u|) ≤ Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  set g : ℝ → ℝ := fun u => (Real.sqrt x * F u ^ 2 +
    (Real.sqrt x)⁻¹ * (Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) u) / 2 with hg
  have hgi : IntegrableOn g (Ici (-x)) := by
    have h1 : IntegrableOn (fun u => Real.sqrt x * F u ^ 2) (Ici (-x)) :=
      (hF.sq.const_mul _).integrableOn
    have h2 : IntegrableOn (fun u => (Real.sqrt x)⁻¹ * (Iio (0 : ℝ)).indicator
        (fun _ => (1 : ℝ)) u) (Ici (-x)) := by
      have : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (-x) ∩ Iio 0) := by
        rw [Ici_inter_Iio]; exact integrableOn_const (by simp)
      refine Integrable.const_mul ?_ _
      rw [IntegrableOn, ← integrable_indicator_iff measurableSet_Iio] at *
      simpa [Measure.restrict_restrict measurableSet_Iio, Set.inter_comm] using this
    exact (h1.add h2).div_const 2
  calc (∫ u in Ici (-x), |F u|)
      ≤ ∫ u in Ici (-x), g u := by
        refine setIntegral_mono_on hF.integrable.abs.integrableOn hgi measurableSet_Ici
          fun u _ => ?_
        simp only [hg]
        rcases lt_or_ge u 0 with hu | hu
        · rw [indicator_of_mem (Set.mem_Iio.mpr hu)]
          have := sq_nonneg (Real.sqrt x * |F u| - 1)
          have hF2 : |F u| ^ 2 = F u ^ 2 := sq_abs _
          field_simp
          nlinarith [abs_nonneg (F u)]
        · rw [hF.support u hu, indicator_of_notMem (fun h => (not_lt.mpr hu) (Set.mem_Iio.mp h))]
          simp
    _ = (Real.sqrt x * (∫ u in Ici (-x), F u ^ 2) + (Real.sqrt x)⁻¹ * x) / 2 := by
        simp only [hg]
        rw [integral_div, integral_add (hF.sq.const_mul _).integrableOn, integral_const_mul,
          integral_const_mul, integral_indicator measurableSet_Iio, Measure.restrict_restrict
          measurableSet_Iio, Set.inter_comm, Ici_inter_Iio, setIntegral_const]
        · simp [Real.volume_Ico, hx.le]
        · have : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (-x) ∩ Iio 0) := by
            rw [Ici_inter_Iio]; exact integrableOn_const (by simp)
          refine Integrable.const_mul ?_ _
          rw [IntegrableOn, ← integrable_indicator_iff measurableSet_Iio] at *
          simpa [Measure.restrict_restrict measurableSet_Iio, Set.inter_comm] using this
    _ ≤ Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2 := by
        have hle : (∫ u in Ici (-x), F u ^ 2) ≤ ∫ u, F u ^ 2 :=
          setIntegral_le_integral hF.sq (Eventually.of_forall fun u => sq_nonneg _)
        have hinv : (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
          rw [← hsx]; field_simp
        rw [hinv]
        nlinarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
