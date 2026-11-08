import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentGrowsExponentiallyBelowTheOnset
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstDerivativeRegularity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits

/-!
# The polar source is continuous in the exponential norm

The source kernel is bounded in the deep tail and has a logarithmic terminal
singularity. Its dual exponential square integral is finite, so Cauchy–Schwarz
extends the exact terminal-window source to strong weighted limits.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The exponential Chebyshev contribution to the polar kernel is globally bounded. -/
lemma exp_mul_chebyshevPsi_le_six (u : ℝ) :
    0 ≤ Real.exp u * Chebyshev.psi (Real.exp (-u)) ∧
      Real.exp u * Chebyshev.psi (Real.exp (-u)) ≤ 6 := by
  have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_pos (-u)).le
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hh := Real.log_two_lt_d9
    norm_num at hh ⊢
    linarith only [hh]
  have hpsi6 : Chebyshev.psi (Real.exp (-u)) ≤ 6 * Real.exp (-u) :=
    hpsi.trans (mul_le_mul_of_nonneg_right (by linarith only [hlog4]) (Real.exp_pos (-u)).le)
  have hm := mul_le_mul_of_nonneg_left hpsi6 (Real.exp_pos u).le
  have he : Real.exp u * (6 * Real.exp (-u)) = 6 := by
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  exact ⟨mul_nonneg (Real.exp_pos u).le (Chebyshev.psi_nonneg _), hm.trans_eq he⟩

/-- Only the terminal logarithm can make the polar source kernel unbounded. -/
lemma abs_terminalPolarKernel_le_log {u : ℝ} (hu : u ≤ 0) :
    |terminalPolarKernel u| ≤ 7 + |Real.log (2 * Real.pi)| +
      |Real.log (1 - Real.exp (2 * u))| / 2 := by
  have heu : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
  have hpsi := exp_mul_chebyshevPsi_le_six u
  have hlog : |Real.exp u * Real.log (1 - Real.exp (2 * u)) / 2| ≤
      |Real.log (1 - Real.exp (2 * u))| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos u), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right heu (abs_nonneg _)).trans_eq (one_mul _)) (by norm_num)
  have hconstant : |Real.log (2 * Real.pi) * Real.exp u| ≤ |Real.log (2 * Real.pi)| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos u)]
    exact (mul_le_mul_of_nonneg_left heu (abs_nonneg _)).trans_eq (mul_one _)
  have hprime : |Real.exp u * Chebyshev.psi (Real.exp (-u))| ≤ 6 := by
    rw [abs_of_nonneg hpsi.1]
    exact hpsi.2
  unfold terminalPolarKernel
  have htri : |1 - Real.exp u * Real.log (1 - Real.exp (2 * u)) / 2 -
      Real.log (2 * Real.pi) * Real.exp u - Real.exp u * Chebyshev.psi (Real.exp (-u))| ≤
      |(1 : ℝ)| + |Real.log (1 - Real.exp (2 * u))| / 2 + |Real.log (2 * Real.pi)| + 6 :=
    (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add le_rfl hlog)) hconstant)) hprime)
  norm_num only [abs_one] at htri
  exact htri.trans_eq (by ring)

/-- Near the terminal endpoint the squared kernel has a squared-logarithm majorant. -/
lemma terminalPolarKernel_sq_le_on_terminal_interval {u : ℝ} (hu : u ∈ Icc (-2 : ℝ) 0) :
    terminalPolarKernel u ^ 2 ≤
      2 * (7 + |Real.log (2 * Real.pi)|) ^ 2 + 16 + Real.log u ^ 2 := by
  have hbase := abs_terminalPolarKernel_le_log hu.2
  have hlog : |Real.log (1 - Real.exp (2 * u))| ≤ 4 + |Real.log u| := by
    by_cases hu0 : u = 0
    · subst u
      norm_num
    have hu_neg : u < 0 := lt_of_le_of_ne hu.2 hu0
    have hy0 : 0 < 1 - Real.exp (2 * u) := sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by linarith only [hu_neg]))
    have hy1 : 1 - Real.exp (2 * u) ≤ 1 := by linarith only [Real.exp_pos (2 * u)]
    have hlowexp : Real.exp (-4 : ℝ) ≤ Real.exp (2 * u) :=
      Real.exp_le_exp.mpr (by linarith only [hu.1])
    have hpart : (-u) * Real.exp (-4) ≤ (-2 * u) * Real.exp (2 * u) :=
      mul_le_mul (by linarith only [hu_neg]) hlowexp (Real.exp_pos _).le (by linarith only [hu_neg])
    have hadd := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2 * u)) (Real.exp_pos (2 * u)).le
    have hexp : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by
      rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
    rw [hexp] at hadd
    have hlower : (-u) * Real.exp (-4) ≤ 1 - Real.exp (2 * u) := by
      nlinarith only [hpart, hadd]
    have hl := Real.log_le_log (mul_pos (neg_pos.mpr hu_neg) (Real.exp_pos _)) hlower
    rw [Real.log_mul (neg_ne_zero.mpr hu0) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_neg_eq_log] at hl
    rw [abs_of_nonpos (Real.log_nonpos hy0.le hy1)]
    linarith only [hl, neg_abs_le (Real.log u)]
  have hs := pow_le_pow_left₀ (abs_nonneg _) hbase 2
  have hl := pow_le_pow_left₀ (abs_nonneg _) hlog 2
  rw [sq_abs] at hs hl
  nlinarith only [hs, hl,
    sq_nonneg ((7 + |Real.log (2 * Real.pi)|) - |Real.log (1 - Real.exp (2 * u))| / 2),
    sq_nonneg (4 - |Real.log u|), sq_abs (Real.log u),
    sq_abs (Real.log (1 - Real.exp (2 * u)))]

lemma measurable_terminalPolarKernel : Measurable terminalPolarKernel := by
  unfold terminalPolarKernel
  have hpsi : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp (-u))) :=
    Chebyshev.psi_mono.measurable.comp (Real.continuous_exp.comp continuous_neg).measurable
  exact (((measurable_const.sub
    ((Real.continuous_exp.measurable.mul
      (Real.measurable_log.comp (measurable_const.sub
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable))).div_const 2))).sub
      (measurable_const.mul Real.continuous_exp.measurable)).sub
        (Real.continuous_exp.measurable.mul hpsi)


/-- The source kernel is bounded on the deep negative half-line. -/
lemma abs_terminalPolarKernel_le_deep {u : ℝ} (hu : u ≤ -2) :
    |terminalPolarKernel u| ≤ 8 + |Real.log (2 * Real.pi)| := by
  have he : Real.exp (2 * u) ≤ 1 / 2 := by
    have h4 : (2 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp 4]
    have hh : Real.exp (2 * u) ≤ Real.exp (-4) :=
      Real.exp_le_exp.mpr (by linarith only [hu])
    rw [Real.exp_neg, ← one_div] at hh
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) h4)
  have hy0 : 0 < 1 - Real.exp (2 * u) := by linarith only [he]
  have hlog : |Real.log (1 - Real.exp (2 * u))| ≤ 1 := by
    rw [abs_of_neg (Real.log_neg hy0 (by linarith only [Real.exp_pos (2 * u)]))]
    have hinv : 1 / (1 - Real.exp (2 * u)) ≤ 2 := by
      rw [div_le_iff₀ hy0]
      linarith only [he]
    have hl := Real.log_le_sub_one_of_pos (one_div_pos.mpr hy0)
    rw [one_div, Real.log_inv] at hl
    linarith only [hinv, hl]
  have hb := abs_terminalPolarKernel_le_log (by linarith only [hu] : u ≤ 0)
  linarith only [hb, hlog]

/-- Exponential weighting makes the squared polar source kernel integrable on the negative
half-line, including its logarithmic singularity at the terminal endpoint. -/
theorem integrableOn_exp_mul_terminalPolarKernel_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (a * u) * terminalPolarKernel u ^ 2) (Iic 0) := by
  have hm : Measurable (fun u : ℝ => Real.exp (a * u) * terminalPolarKernel u ^ 2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id : Continuous (fun u : ℝ => a * u))).measurable.mul
      (measurable_terminalPolarKernel.pow_const 2)
  have hdeep : IntegrableOn
      (fun u : ℝ => Real.exp (a * u) * terminalPolarKernel u ^ 2) (Iic (-2)) := by
    have hi := (integrableOn_exp_mul_Iic ha (-2)).mul_const
      ((8 + |Real.log (2 * Real.pi)|) ^ 2)
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_terminalPolarKernel_le_deep hu) 2
    simpa only [sq_abs] using hh
  have hnear : IntegrableOn
      (fun u : ℝ => Real.exp (a * u) * terminalPolarKernel u ^ 2) (Icc (-2) 0) := by
    have hl : IntegrableOn (fun u : ℝ => Real.log u ^ 2) (Icc (-2) 0) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 0)).mp
        (RHTower.intervalIntegrable_log_sq (-2) 0)
    have hi := (integrableOn_const (s := Icc (-2 : ℝ) 0)
      (C := 2 * (7 + |Real.log (2 * Real.pi)|) ^ 2 + 16)
      isCompact_Icc.measure_ne_top).add hl
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : Real.exp (a * u) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos ha.le hu.2)
    exact ((mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans_eq (one_mul _)).trans
      (terminalPolarKernel_sq_le_on_terminal_interval hu)
  have hunion : Iic (-2 : ℝ) ∪ Icc (-2) 0 = Iic 0 := by
    ext u
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h)
      · linarith only [h]
      · exact h.2
    · intro h
      rcases le_total u (-2) with hu | hu
      · exact Or.inl hu
      · exact Or.inr ⟨hu, h⟩
  rw [← hunion]
  exact hdeep.union hnear

#print axioms integrableOn_exp_mul_terminalPolarKernel_sq
#print axioms terminalPolarKernel_sq_le_on_terminal_interval
#print axioms measurable_terminalPolarKernel
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri Filter Topology

/-- The physical polar source on the negative half-line, before the spline normalization. -/
def polarSourceProfile (u : ℝ) : ℝ :=
  (Iic (0 : ℝ)).indicator (fun u => Real.exp (-u / 2) * terminalPolarKernel u) u

lemma measurable_polarSourceProfile : Measurable polarSourceProfile :=
  ((Real.continuous_exp.comp ((continuous_neg : Continuous (fun u : ℝ => -u)).div_const 2)).measurable.mul
    measurable_terminalPolarKernel).indicator measurableSet_Iic

/-- The physical polar source belongs to the dual of the exponential source norm. -/
theorem integrable_weighted_polarSourceProfile_sq :
    Integrable (fun u : ℝ => (Real.exp (-|u|) * polarSourceProfile u) ^ 2) := by
  have hi := (integrableOn_exp_mul_terminalPolarKernel_sq (by norm_num : (0 : ℝ) < 1)).integrable_indicator
    measurableSet_Iic
  apply hi.congr
  exact Eventually.of_forall fun u => by
    by_cases hu : u ∈ Iic (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
      unfold polarSourceProfile
      rw [Set.indicator_of_mem hu, abs_of_nonpos hu]
      have he : Real.exp (- -u) * Real.exp (-u / 2) = Real.exp (u / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have he2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
        rw [sq, ← Real.exp_add, add_halves]
      rw [← mul_assoc, he, mul_pow, he2, one_mul]
    · rw [Set.indicator_of_notMem hu]
      unfold polarSourceProfile
      rw [Set.indicator_of_notMem hu, mul_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Weighted square integrability suffices for pairing with the polar source. -/
theorem integrable_mul_polarSourceProfile {f : ℝ → ℝ} (hf : WeightedTwo f) :
    Integrable (fun u => f u * polarSourceProfile u) := by
  have ham : AEStronglyMeasurable (fun u => Real.exp |u| * f u) volume :=
    (Real.continuous_exp.comp continuous_abs).aestronglyMeasurable.mul hf.meas
  have hbm : AEStronglyMeasurable (fun u => Real.exp (-|u|) * polarSourceProfile u) volume :=
    (Real.continuous_exp.comp continuous_abs.neg).aestronglyMeasurable.mul
      measurable_polarSourceProfile.aestronglyMeasurable
  have hi := HTGeometry.integrable_mul_of_sq_integrable ham hbm hf.sq
    integrable_weighted_polarSourceProfile_sq
  apply hi.congr
  exact Eventually.of_forall fun u => by
    have he : Real.exp |u| * Real.exp (-|u|) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ = (Real.exp |u| * Real.exp (-|u|)) * (f u * polarSourceProfile u) := by ring
      _ = _ := by rw [he, one_mul]

/-- Cauchy--Schwarz bounds the polar source functional in the exponential source norm. -/
theorem sq_integral_mul_polarSourceProfile_le {f : ℝ → ℝ} (hf : WeightedTwo f) :
    (∫ u, f u * polarSourceProfile u) ^ 2 ≤ exponentialSourceMass f *
      ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2 := by
  have ham : AEStronglyMeasurable (fun u => Real.exp |u| * f u) volume :=
    (Real.continuous_exp.comp continuous_abs).aestronglyMeasurable.mul hf.meas
  have hbm : AEStronglyMeasurable (fun u => Real.exp (-|u|) * polarSourceProfile u) volume :=
    (Real.continuous_exp.comp continuous_abs.neg).aestronglyMeasurable.mul
      measurable_polarSourceProfile.aestronglyMeasurable
  have hh := HTGeometry.sq_integral_mul_le ham hbm hf.sq integrable_weighted_polarSourceProfile_sq
  have heq : (fun u => (Real.exp |u| * f u) *
      (Real.exp (-|u|) * polarSourceProfile u)) = fun u => f u * polarSourceProfile u := by
    funext u
    have he : Real.exp |u| * Real.exp (-|u|) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ = (Real.exp |u| * Real.exp (-|u|)) * (f u * polarSourceProfile u) := by ring
      _ = _ := by rw [he, one_mul]
  rw [heq] at hh
  exact hh

/-- Polar source pairings are continuous under convergence in the exponential source norm. -/
theorem tendsto_integral_mul_polarSourceProfile {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ n, WeightedTwo (U n)) (hF : WeightedTwo F)
    (hlim : Tendsto (fun n => exponentialSourceMass (fun u => U n u - F u)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u, U n u * polarSourceProfile u) atTop
      (𝓝 (∫ u, F u * polarSourceProfile u)) := by
  have hs : Tendsto (fun n => (∫ u, (U n u - F u) * polarSourceProfile u) ^ 2)
      atTop (𝓝 0) := by
    have hb := hlim.mul_const (∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2)
    rw [zero_mul] at hb
    exact squeeze_zero (fun n => sq_nonneg _)
      (fun n => sq_integral_mul_polarSourceProfile_le ((hU n).sub hF)) hb
  have ha := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply ha.congr
  intro n
  rw [Real.norm_eq_abs, ← integral_sub (integrable_mul_polarSourceProfile (hU n))
    (integrable_mul_polarSourceProfile hF)]
  congr 2
  funext u
  ring

/-- The continuous polar functional agrees with the exact terminal-window source. -/
theorem generalTerminalPolarSource_eq_integral_polarSourceProfile {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ u, u ∉ Icc (-A) 0 → h u = 0) :
    generalTerminalPolarSource A h = splineAtom * ∫ u, halfWeight h u * polarSourceProfile u := by
  rw [(generalTerminalPolarSource_eq_integral_terminalPolarKernel hh hA hsupp).1]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    by_cases hu : u ≤ 0
    · unfold halfWeight polarSourceProfile
      rw [Set.indicator_of_mem hu]
      have he : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      calc
        _ = (Real.exp (u / 2) * Real.exp (-u / 2)) * (h u * terminalPolarKernel u) := by rw [he, one_mul]
        _ = _ := by ring
    · have hz : h u = 0 := hsupp u (fun hm => hu hm.2)
      simp only [halfWeight, hz, mul_zero, zero_mul]

#print axioms integrable_weighted_polarSourceProfile_sq
#print axioms tendsto_integral_mul_polarSourceProfile
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
