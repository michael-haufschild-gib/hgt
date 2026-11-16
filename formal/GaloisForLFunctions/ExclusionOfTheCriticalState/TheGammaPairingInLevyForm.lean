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
def levyTail (F : ℝ → ℝ) (p : ℂ) (x : ℝ) : ℂ := ∫ u : ℝ in Iio (-x), cexp (p * u) * (F u : ℂ)

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
  calc ‖∫ u : ℝ in Iio (-x), cexp (p * x) * (cexp (p * u) * (F u : ℂ))‖
      ≤ ∫ u : ℝ in Iio (-x), |F u| * Real.exp (-(1 / 2) * u) := by
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
    (hp : -4 < p.re) : Integrable fun u : ℝ => cexp (p * u) * (F u : ℂ) := by
  refine (integrable_abs_mul_exp_of_domain hF hp).mono'
    ((by fun_prop : Continuous fun u : ℝ => cexp (p * u)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hF.meas).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- The transform splits at `-x` into the tail and the head. -/
theorem laplace_eq_levyTail_add {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -4 < p.re) (x : ℝ) :
    negativeHalfLineLaplace (cx F) p =
      levyTail F p x + ∫ u : ℝ in Ici (-x), cexp (p * u) * (F u : ℂ) := by
  have h := integral_add_compl measurableSet_Iio (integrable_cexp_mul_of_domain hF hp) (s := Iio (-x))
  rw [compl_Iio] at h
  unfold levyTail negativeHalfLineLaplace
  simp only [cx]
  exact h.symm

/-- The head `∫_{-x}^0 |F|` is `O(√x)`. -/
theorem setIntegral_Ici_abs_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {x : ℝ}
    (hx : 0 < x) :
    (∫ u in Ici (-x), |F u|) ≤ Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  set g : ℝ → ℝ := fun u => (Real.sqrt x * F u ^ 2 +
    (Real.sqrt x)⁻¹ * (Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ)) u) / 2 with hg
  have hind : IntegrableOn ((Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ))) (Ici (-x)) := by
    have hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico (-x) 0) :=
      integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Ici_inter_Iio]
    exact hfin
  have hgi : IntegrableOn g (Ici (-x)) := by
    have h1 : IntegrableOn (fun u => Real.sqrt x * F u ^ 2) (Ici (-x)) :=
      (hF.sq.const_mul _).integrableOn
    have h2 : IntegrableOn (fun u => (Real.sqrt x)⁻¹ * (Iio (0 : ℝ)).indicator
        (fun _ => (1 : ℝ)) u) (Ici (-x)) := hind.const_mul _
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
        rw [integral_div, integral_add (hF.sq.const_mul _).integrableOn (hind.const_mul _),
          integral_const_mul, integral_const_mul, integral_indicator measurableSet_Iio,
          Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Ici_inter_Iio,
          setIntegral_const]
        simp [hx.le]
    _ ≤ Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2 := by
        have hle : (∫ u in Ici (-x), F u ^ 2) ≤ ∫ u, F u ^ 2 :=
          setIntegral_le_integral hF.sq (Eventually.of_forall fun u => sq_nonneg _)
        have hinv : (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
          rw [inv_mul_eq_iff_eq_mul₀ hs.ne']; exact hsx.symm
        rw [hinv]
        nlinarith

/-- Near the origin the Lévy kernel is `O(x) + O(√x)`. -/
theorem norm_levyKernel_le_near {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} {P : ℝ}
    (hpP : ‖p‖ ≤ P) (hp : -(1 / 2) ≤ p.re) {x : ℝ} (hx : 0 < x) (hxP : P * x ≤ 1) :
    ‖levyKernel F p x‖ ≤ 4 * halfPoleMass F * P * x +
      9 * (Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2) := by
  have hL := norm_laplace_le_halfPoleMass hF hp
  have hsplit := laplace_eq_levyTail_add hF (p := p) (by linarith) x
  have hpx : ‖p * x‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]; nlinarith [norm_nonneg p]
  have hpx' : ‖-(p * x)‖ ≤ 1 := by rwa [norm_neg]
  have hpxle : ‖p * x‖ ≤ P * x := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
    exact mul_le_mul_of_nonneg_right hpP hx.le
  have he1 := Complex.norm_exp_sub_one_le hpx
  have he2 := Complex.norm_exp_sub_one_le hpx'
  rw [norm_neg] at he2
  have hexp : ‖cexp (p * x)‖ ≤ 3 := by
    rw [norm_cexp_mul_ofReal]
    have : p.re * x ≤ 1 := by
      have := Complex.re_le_norm p
      nlinarith [norm_nonneg p]
    calc Real.exp (p.re * x) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- the head integral
  set H := ∫ u : ℝ in Ici (-x), cexp (p * u) * (F u : ℂ) with hHdef
  have hH : ‖H‖ ≤ 3 * (Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2) := by
    have hint : IntegrableOn (fun u => |F u|) (Ici (-x)) := hF.integrable.abs.integrableOn
    calc ‖H‖ ≤ ∫ u in Ici (-x), 3 * |F u| := by
          refine norm_integral_le_of_norm_le (hint.const_mul 3)
            ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
          rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
          rcases lt_or_ge u 0 with h0 | h0
          · have hu' : -x ≤ u := hu
            have hb : p.re * u ≤ 1 := by
              have h1 := Complex.abs_re_le_norm p
              have h2 : |p.re * u| ≤ ‖p‖ * x := by
                rw [abs_mul]; exact mul_le_mul h1 (by rw [abs_of_neg h0]; linarith)
                  (abs_nonneg _) (norm_nonneg _)
              have := le_abs_self (p.re * u)
              nlinarith [norm_nonneg p]
            have : Real.exp (p.re * u) ≤ 3 := by
              calc Real.exp (p.re * u) ≤ Real.exp 1 := Real.exp_le_exp.mpr hb
                _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
            nlinarith [abs_nonneg (F u)]
          · simp [hF.support u h0]
      _ = 3 * ∫ u in Ici (-x), |F u| := integral_const_mul _ _
      _ ≤ 3 * (Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2) := by
          have := setIntegral_Ici_abs_le hF hx; linarith
  have hK : levyKernel F p x = negativeHalfLineLaplace (cx F) p *
      (-(cexp (-(p * x)) - 1) - (cexp (p * x) - 1)) + cexp (p * x) * H := by
    unfold levyKernel
    rw [show levyTail F p x = negativeHalfLineLaplace (cx F) p - H by rw [hsplit]; ring]
    ring
  rw [hK]
  calc ‖negativeHalfLineLaplace (cx F) p * (-(cexp (-(p * x)) - 1) - (cexp (p * x) - 1)) +
        cexp (p * x) * H‖
      ≤ ‖negativeHalfLineLaplace (cx F) p‖ * (‖cexp (-(p * x)) - 1‖ + ‖cexp (p * x) - 1‖) +
          ‖cexp (p * x)‖ * ‖H‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by rw [norm_neg])
    _ ≤ halfPoleMass F * (2 * (P * x) + 2 * (P * x)) +
          3 * (3 * (Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2)) := by
        have hC0 : 0 ≤ halfPoleMass F := le_trans (norm_nonneg _) hL
        gcongr
        · linarith
        · linarith
    _ = 4 * halfPoleMass F * P * x + 9 * (Real.sqrt x * ((∫ u, F u ^ 2) + 1) / 2) := by ring

/-- Far from the origin the Lévy kernel is bounded by `(3 + e^{-Re p·x})` half-pole masses. -/
theorem norm_levyKernel_le_far {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -(1 / 2) ≤ p.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖levyKernel F p x‖ ≤ halfPoleMass F * (3 + Real.exp (-(p.re * x))) := by
  have hL := norm_laplace_le_halfPoleMass hF hp
  have hT := norm_cexp_mul_levyTail_le hF hp hx
  have hC0 : 0 ≤ halfPoleMass F := le_trans (norm_nonneg _) hL
  unfold levyKernel
  have h2 : ‖(2 : ℂ) - cexp (-(p * x))‖ ≤ 2 + Real.exp (-(p.re * x)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [show -(p * (x : ℂ)) = (-p) * x by ring, norm_cexp_mul_ofReal]
    simp
  calc ‖negativeHalfLineLaplace (cx F) p * (2 - cexp (-(p * x))) - cexp (p * x) * levyTail F p x‖
      ≤ ‖negativeHalfLineLaplace (cx F) p‖ * ‖(2 : ℂ) - cexp (-(p * x))‖ +
          ‖cexp (p * x) * levyTail F p x‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ halfPoleMass F * (2 + Real.exp (-(p.re * x))) + halfPoleMass F := by
        gcongr
    _ = halfPoleMass F * (3 + Real.exp (-(p.re * x))) := by ring

/-- The tail transform is strongly measurable in the jump length. -/
theorem stronglyMeasurable_levyTail {F : ℝ → ℝ} (hFm : Measurable F) (p : ℂ) :
    StronglyMeasurable fun x => levyTail F p x := by
  set f : ℝ × ℝ → ℂ := fun q => if q.2 < -q.1 then cexp (p * q.2) * (F q.2 : ℂ) else 0 with hf
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_fst.neg)
      ((by fun_prop : Measurable fun q : ℝ × ℝ => cexp (p * q.2)).mul
        (Complex.measurable_ofReal.comp (hFm.comp measurable_snd))) measurable_const
  have h := hfm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert h using 1
  funext x
  unfold levyTail
  rw [← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Set.indicator, Set.mem_Iio, hf]

/-- The Lévy tail is holomorphic in the exponent on `Re p > -4`. -/
theorem differentiableOn_levyTail {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    DifferentiableOn ℂ (fun p => levyTail F p x) {p : ℂ | -4 < p.re} := by
  have hU : IsOpen {p : ℂ | -4 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  refine differentiableOn_integral_of_locally_bounded (ν := volume.restrict (Iio (-x)))
    (F := fun (u : ℝ) (p : ℂ) => cexp (p * u) * (F u : ℂ)) hU
    (fun u => (by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * u) * (F u : ℂ)).differentiableOn)
    (fun p _ => ((by fun_prop : Continuous fun u : ℝ => cexp (p * u)).measurable.mul
      (Complex.measurable_ofReal.comp hF.meas)).aestronglyMeasurable) ?_
  intro z₀ hz₀
  have hz₀' : -4 < z₀.re := hz₀
  set r := (z₀.re + 4) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  refine ⟨r, hrpos, fun z hz => ?_, fun u => |F u| * Real.exp ((z₀.re - r) * u),
    (integrable_abs_mul_exp_of_domain hF (by rw [hr]; linarith)).integrableOn, fun u z hz => ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hz
    have := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
    show -4 < z.re
    simp at this; rw [hr] at this; linarith
  · rw [mem_closedBall, dist_eq_norm] at hz
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
    simp only [Complex.sub_re] at hre
    rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    rcases lt_or_ge u 0 with hu | hu
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
    · simp [hF.support u hu]

theorem measurable_archLevyDensity' : Measurable archLevyDensity := by
  unfold archLevyDensity; fun_prop

/-- **The Lévy pairing is holomorphic on `Re p > -½`.** -/
theorem differentiableOn_levyGamma {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (levyGamma F) {p : ℂ | -(1 / 2) < p.re} := by
  have hU : IsOpen {p : ℂ | -(1 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hLapU : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {p : ℂ | -(1 / 2) < p.re} :=
    hLap.mono fun p hp => by show -(8 / 2) < p.re; have : -(1 / 2) < p.re := hp; linarith
  refine (hLapU.const_mul _).add ?_
  refine differentiableOn_integral_of_locally_bounded (ν := volume)
    (F := fun (x : ℝ) (p : ℂ) => levyIntegrand F p x) hU ?_ ?_ ?_
  · intro x
    by_cases hx : 0 < x
    · have hk : DifferentiableOn ℂ (fun p => levyKernel F p x) {p : ℂ | -(1 / 2) < p.re} := by
        unfold levyKernel
        refine (hLapU.mul (by fun_prop : Differentiable ℂ fun p : ℂ =>
          (2 : ℂ) - cexp (-(p * x))).differentiableOn).sub
          ((by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * x)).differentiableOn.mul
            ((differentiableOn_levyTail hF x).mono fun p hp => by
              show -4 < p.re; have : -(1 / 2) < p.re := hp; linarith))
      refine (hk.const_mul ((archLevyDensity x : ℂ))).congr fun p _ => ?_
      simp [levyIntegrand, Set.indicator, hx]
    · refine (differentiableOn_const (c := (0 : ℂ))).congr fun p _ => ?_
      simp [levyIntegrand, Set.indicator, hx]
  · intro p _
    have hm : AEStronglyMeasurable (fun x : ℝ => (archLevyDensity x : ℂ) * levyKernel F p x) volume := by
      unfold levyKernel
      exact ((Complex.measurable_ofReal.comp measurable_archLevyDensity').aestronglyMeasurable).mul
        (((aestronglyMeasurable_const.mul ((by fun_prop : Continuous fun x : ℝ =>
          (2 : ℂ) - cexp (-(p * x))).aestronglyMeasurable)).sub
          (((by fun_prop : Continuous fun x : ℝ => cexp (p * x)).aestronglyMeasurable).mul
            (stronglyMeasurable_levyTail hF.meas p).aestronglyMeasurable)))
    exact hm.indicator measurableSet_Ioi
  · intro z₀ hz₀
    have hz₀' : -(1 / 2) < z₀.re := hz₀
    set r := (z₀.re + 1 / 2) / 2 with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    set P := max 1 (‖z₀‖ + r) with hPdef
    have hP1 : 1 ≤ P := le_max_left _ _
    set x₁ := 1 / P with hx₁
    have hx₁pos : 0 < x₁ := by rw [hx₁]; positivity
    have hx₁1 : x₁ ≤ 1 := by rw [hx₁, div_le_one (by linarith)]; exact hP1
    set C := halfPoleMass F with hC
    set M₂ := ∫ u, F u ^ 2 with hM₂
    set M₀ := max 2 (3 / (2 * x₁) * Real.exp (1 / 2)) with hM₀
    have hball : ∀ p ∈ closedBall z₀ r, -(1 / 2) + r ≤ p.re ∧ ‖p‖ ≤ P := by
      intro p hp
      rw [mem_closedBall, dist_eq_norm] at hp
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (p - z₀)).trans hp)).1
      simp only [Complex.sub_re] at h1
      refine ⟨by rw [hrdef] at h1 ⊢; linarith, ?_⟩
      have h2 : ‖p‖ ≤ ‖z₀‖ + r := by
        have := norm_sub_norm_le p z₀; linarith
      exact h2.trans (le_max_right _ _)
    set g : ℝ → ℝ := fun x =>
      (Ioc 0 x₁).indicator (fun x => 3 / (2 * x) * (4 * C * P * x +
        9 * (Real.sqrt x * (M₂ + 1) / 2))) x +
      (Ioi x₁).indicator (fun x => M₀ * Real.exp (-(x / 2)) * (C * 3) +
        M₀ * C * Real.exp (-(r * x))) x with hg
    refine ⟨r, hr, fun z hz => ?_, g, ?_, fun x p hp => ?_⟩
    · have := (hball z hz).1; show -(1 / 2) < z.re; linarith
    · -- integrability of the dominating function
      have hnear : IntegrableOn (fun x : ℝ => 3 / (2 * x) * (4 * C * P * x +
          9 * (Real.sqrt x * (M₂ + 1) / 2))) (Ioc 0 x₁) := by
        have hrpow : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (Ioc 0 x₁) := by
          rw [integrableOn_Ioc_iff_integrableOn_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff hx₁pos]
          norm_num
        have hconst : IntegrableOn (fun _ : ℝ => 6 * C * P) (Ioc 0 x₁) :=
          integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        refine (hconst.add (hrpow.const_mul (27 / 4 * (M₂ + 1)))).congr_fun (fun x hx => ?_)
          measurableSet_Ioc
        have hx0 : 0 < x := hx.1
        simp only [Pi.add_apply]
        rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
        set s := Real.sqrt x with hsdef
        have hs2 : x = s ^ 2 := (Real.sq_sqrt hx0.le).symm
        have hsp : 0 < s := Real.sqrt_pos.mpr hx0
        clear_value s
        subst hs2
        field_simp
        ring
      have hfar : IntegrableOn (fun x : ℝ => M₀ * Real.exp (-(x / 2)) * (C * 3) +
          M₀ * C * Real.exp (-(r * x))) (Ioi x₁) := by
        have e1 : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x)) (Ioi x₁) :=
          exp_neg_integrableOn_Ioi _ (by norm_num)
        have e2 : IntegrableOn (fun x : ℝ => Real.exp (-r * x)) (Ioi x₁) :=
          exp_neg_integrableOn_Ioi _ hr
        refine (IntegrableOn.add (e1.const_mul (M₀ * (C * 3))) (e2.const_mul (M₀ * C))).congr_fun
          (fun x _ => ?_) measurableSet_Ioi
        simp only [Pi.add_apply]
        rw [show -(x / 2) = -(1 / 2) * x by ring, show -(r * x) = -r * x by ring]
        ring
      exact (hnear.integrable_indicator measurableSet_Ioc).add
        (hfar.integrable_indicator measurableSet_Ioi)
    · -- the pointwise bound
      obtain ⟨hpre, hpP⟩ := hball p hp
      have hp12 : -(1 / 2) ≤ p.re := by linarith
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (norm_laplace_le_halfPoleMass hF hp12)
      have hM₀0 : 0 ≤ M₀ := le_trans (by norm_num) (le_max_left _ _)
      have hgnn : 0 ≤ g x := by
        simp only [hg]
        refine add_nonneg (Set.indicator_nonneg (fun y hy => ?_) _)
          (Set.indicator_nonneg (fun y _ => by positivity) _)
        have hy0 : 0 < y := hy.1
        positivity
      by_cases hx : 0 < x
      · have hval : levyIntegrand F p x = (archLevyDensity x : ℂ) * levyKernel F p x := by
          simp [levyIntegrand, Set.indicator, hx]
        rw [hval, norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLevyDensity_pos hx).le]
        by_cases hx1 : x ≤ x₁
        · have hxP : P * x ≤ 1 := by
            have := mul_le_mul_of_nonneg_left hx1 (by linarith : (0 : ℝ) ≤ P)
            rw [hx₁, mul_one_div_cancel (by linarith)] at this; exact this
          have hω := archLevyDensity_le_near hx (hx1.trans hx₁1)
          have hK := norm_levyKernel_le_near hF hpP hp12 hx hxP
          have hgx : g x = 3 / (2 * x) * (4 * C * P * x + 9 * (Real.sqrt x * (M₂ + 1) / 2)) := by
            simp only [hg, Set.indicator, Set.mem_Ioc, hx, hx1, true_and, Set.mem_Ioi,
              not_lt.mpr hx1, if_true, if_false, add_zero]
          rw [hgx]
          exact mul_le_mul hω hK (norm_nonneg _) (by positivity)
        · have hx1' : x₁ < x := lt_of_not_ge hx1
          have hω : archLevyDensity x ≤ M₀ * Real.exp (-(x / 2)) := by
            rcases le_or_gt 1 x with h1 | h1
            · exact (archLevyDensity_le_far h1).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
            · have h3 := archLevyDensity_le_near hx h1.le
              have h4 : 3 / (2 * x) ≤ 3 / (2 * x₁) :=
                div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
              have h5 : 1 ≤ Real.exp (1 / 2) * Real.exp (-(x / 2)) := by
                rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
              calc archLevyDensity x ≤ 3 / (2 * x₁) := h3.trans h4
                _ ≤ 3 / (2 * x₁) * (Real.exp (1 / 2) * Real.exp (-(x / 2))) :=
                    le_mul_of_one_le_right (by positivity) h5
                _ = 3 / (2 * x₁) * Real.exp (1 / 2) * Real.exp (-(x / 2)) := by ring
                _ ≤ M₀ * Real.exp (-(x / 2)) :=
                    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
          have hK := norm_levyKernel_le_far hF hp12 hx.le
          have hexp : Real.exp (-(x / 2)) * Real.exp (-(p.re * x)) ≤ Real.exp (-(r * x)) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
          have hgx : g x = M₀ * Real.exp (-(x / 2)) * (C * 3) + M₀ * C * Real.exp (-(r * x)) := by
            simp only [hg, Set.indicator, Set.mem_Ioc, hx, true_and, hx1, if_false, zero_add,
              Set.mem_Ioi, hx1', if_true]
          rw [hgx]
          calc archLevyDensity x * ‖levyKernel F p x‖
              ≤ M₀ * Real.exp (-(x / 2)) * (C * (3 + Real.exp (-(p.re * x)))) :=
                mul_le_mul hω hK (norm_nonneg _) (by positivity)
            _ = M₀ * Real.exp (-(x / 2)) * (C * 3) +
                  M₀ * C * (Real.exp (-(x / 2)) * Real.exp (-(p.re * x))) := by ring
            _ ≤ M₀ * Real.exp (-(x / 2)) * (C * 3) + M₀ * C * Real.exp (-(r * x)) := by
                gcongr
      · have : levyIntegrand F p x = 0 := by simp [levyIntegrand, Set.indicator, hx]
        rw [this, norm_zero]; exact hgnn

/-- At real exponents `p > 4` the Lévy pairing is the Gamma form of the probe. -/
theorem levyGamma_ofReal {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℝ} (hp : 4 < p) :
    levyGamma F p = (gammaMixedForm F (probe p) : ℂ) := by
  rw [gammaMixedForm_probe_levy hF hp]
  unfold levyGamma
  rw [negativeHalfLineLaplace_ofReal]
  have hint : (∫ x, levyIntegrand F (p : ℂ) x) = ((∫ x in Ioi 0, archLevyDensity x *
      ((∫ u, F u * Real.exp (p * u)) * (2 - Real.exp (-(p * x))) -
        Real.exp (p * x) * ∫ u in Iio (-x), F u * Real.exp (p * u)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : 0 < x
    · simp only [levyIntegrand, Set.indicator, Set.mem_Ioi, hx, if_true]
      unfold levyKernel levyTail
      rw [negativeHalfLineLaplace_ofReal]
      have ht : (∫ u : ℝ in Iio (-x), cexp ((p : ℂ) * u) * (F u : ℂ)) =
          ((∫ u in Iio (-x), F u * Real.exp (p * u) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        push_cast; ring
      rw [ht]
      push_cast
      ring
    · simp [levyIntegrand, Set.indicator, hx]
  rw [hint]
  push_cast
  ring

/-- **The Lévy pairing is the Fourier-side Gamma pairing on `Re p > 0`.** -/
theorem levyGamma_eq_stateGamma {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : 0 < p.re) : levyGamma F p = stateGamma F p := by
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (fun p => levyGamma F p - stateGamma F p) {p : ℂ | 0 < p.re} :=
    ((differentiableOn_levyGamma hF).mono fun q hq => by
      show -(1 / 2) < q.re; have : 0 < q.re := hq; linarith).sub (differentiableOn_stateGamma hF)
  have hreal : ∀ x : ℝ, 4 < x → (fun p => levyGamma F p - stateGamma F p) x = 0 := by
    intro x hx
    have hγ : gammaMixedForm F (probe x) = 1 / (2 * Real.pi) *
        ∫ r : ℝ, (paperFT (cx F) (r : ℂ) / ((x : ℂ) - I * r)).re * EF.gammaBracket r := by
      unfold gammaMixedForm
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [gammaFourierPair_probe_right F (by linarith : (0 : ℝ) < x)]
    show levyGamma F x - stateGamma F x = 0
    rw [levyGamma_ofReal hF hx, stateGamma_ofReal, hγ, sub_self]
  have h := (hdiff.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (show 0 < (5 : ℂ).re by norm_num)
    (frequently_eq_zero_of_real hreal) hp
  simpa [sub_eq_zero] using h

end GaloisForLFunctions.ExclusionOfTheCriticalState
