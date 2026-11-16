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
  simp only
  rw [levyInner_probe hF (by linarith) (le_of_lt hx)]

end GaloisForLFunctions.ExclusionOfTheCriticalState
