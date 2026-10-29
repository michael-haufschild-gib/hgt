import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The complete receiver in length and height coordinates

For `β > 2`, let `c_N = loglog N (logloglog N)^β` and `T_N = N/c_N`.
The exact RH receiver is evaluated at height `T_N`. Its overlap diverges but
its bandwidth tends to one. Replacing `N` by `T_N` inside the slow factor
preserves asymptotic equivalence, not exact equality.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Asymptotics

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis SpacingScaleHarmonicAnalysis.LengthHeight
  ArithmeticElectrostatics

/-- The real extension of the overlap schedule, needed to evaluate it at spectral height. -/
def superGevreyRealRatio (β X : ℝ) : ℝ :=
  Real.log (Real.log X) * Real.log (Real.log (Real.log X)) ^ β

/-- Spectral height of the super-Gevrey complete atomic family. -/
def superGevreyHeight (β : ℝ) (N : ℕ) : ℝ := height N (superGevreyRatio β N)

private theorem log_nat_atTop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_atTop

private theorem logloglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N))) atTop atTop :=
  Real.tendsto_log_atTop.comp loglog_nat_atTop

theorem superGevreyHeight_atTop {β : ℝ} (hβ : 2 < β) :
    Tendsto (superGevreyHeight β) atTop atTop :=
  (overlapGrowthSuperGevrey_of_two_lt hβ).1

/-- The complete receiver requires genuinely unbounded overlap. -/
theorem superGevreyRatio_atTop {β : ℝ} (hβ : 2 < β) :
    Tendsto (superGevreyRatio β) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ loglog_nat_atTop
  filter_upwards [loglog_nat_atTop.eventually_ge_atTop 0,
    logloglog_nat_atTop.eventually_ge_atTop 1] with N hll hlll
  have hp : 1 ≤ Real.log (Real.log (Real.log N)) ^ β :=
    Real.one_le_rpow hlll (by linarith only [hβ])
  exact (mul_one _).symm.trans_le (mul_le_mul_of_nonneg_left hp hll)

theorem superGevreyHeight_overlap (β : ℝ) {N : ℕ} (hN : N ≠ 0) :
    overlap N (superGevreyHeight β N) = superGevreyRatio β N :=
  overlap_height (by exact_mod_cast hN) _

private theorem eventually_superGevreyRatio_le_log_sq (β : ℝ) :
    ∀ᶠ N : ℕ in atTop, superGevreyRatio β N ≤ Real.log N ^ (2 : ℝ) := by
  have hbound := (superGevreyRatio_isLittleO_loglog_rpow β one_pos).bound one_pos
  filter_upwards [hbound, loglog_nat_atTop.eventually_gt_atTop 1,
    log_nat_atTop.eventually_gt_atTop 1] with N hN hll hl
  have hc : 0 ≤ superGevreyRatio β N :=
    mul_nonneg (by linarith only [hll]) (Real.rpow_pos_of_pos (Real.log_pos hll) β).le
  rw [one_mul, Real.norm_of_nonneg hc,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hll]) _),
    show (1 : ℝ) + 1 = 2 by norm_num] at hN
  have hll_le : Real.log (Real.log N) ≤ Real.log N :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans hl)).trans (by linarith)
  exact hN.trans (Real.rpow_le_rpow (by linarith only [hll]) hll_le (by norm_num))

/-- The logarithm of the complete overlap schedule is negligible relative to `log N`. -/
theorem tendsto_log_superGevreyRatio_div_log {β : ℝ} (hβ : 2 < β) :
    Tendsto (fun N : ℕ => Real.log (superGevreyRatio β N) / Real.log N) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) one_pos).tendsto_div_nhds_zero.comp log_nat_atTop)
  have hup : Tendsto (fun N : ℕ => 2 * (Real.log (Real.log N) / Real.log N))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsmall.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [(superGevreyRatio_atTop hβ).eventually_ge_atTop 1,
      log_nat_atTop.eventually_gt_atTop 0] with N hc hl
    exact div_nonneg (Real.log_nonneg hc) hl.le
  · filter_upwards [(superGevreyRatio_atTop hβ).eventually_gt_atTop 0,
      eventually_superGevreyRatio_le_log_sq β,
      log_nat_atTop.eventually_gt_atTop 0] with N hc hbound hl
    have hlog := Real.log_le_log hc hbound
    rw [Real.log_rpow hl] at hlog
    exact (div_le_div_of_nonneg_right hlog hl.le).trans_eq (by ring)

/-- The logarithms of length and spectral height are asymptotically equivalent. -/
theorem superGevrey_log_height_equivalent {β : ℝ} (hβ : 2 < β) :
    (fun N : ℕ => Real.log (superGevreyHeight β N)) ~[atTop] fun N => Real.log N := by
  apply isEquivalent_of_tendsto_one
  have hlim : Tendsto (fun N : ℕ => 1 - Real.log (superGevreyRatio β N) / Real.log N)
      atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_log_superGevreyRatio_div_log hβ)
  apply hlim.congr'
  filter_upwards [(superGevreyRatio_atTop hβ).eventually_gt_atTop 0,
    eventually_gt_atTop (1 : ℕ)] with N hc hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  simp only [Pi.div_apply, superGevreyHeight, height,
    Real.log_div (zero_lt_one.trans hN1).ne' hc.ne', sub_div,
    div_self (Real.log_pos hN1).ne']

/-- An RH-complete schedule and every fixed overlap have the same limiting bandwidth. -/
theorem tendsto_superGevrey_bandwidth {β : ℝ} (hβ : 2 < β) :
    Tendsto (fun N : ℕ => bandwidth N (superGevreyHeight β N)) atTop (𝓝 1) := by
  have hlogH := Real.tendsto_log_atTop.comp (superGevreyHeight_atTop hβ)
  exact (isEquivalent_iff_tendsto_one (hlogH.eventually_ne_atTop 0)).mp
    (superGevrey_log_height_equivalent hβ).symm

/-- The slow overlap factor may be evaluated at height only up to asymptotic equivalence. -/
theorem superGevrey_ratio_at_height_equivalent {β : ℝ} (hβ : 2 < β) :
    (fun N : ℕ => superGevreyRealRatio β (superGevreyHeight β N)) ~[atTop]
      superGevreyRatio β := by
  have hll := (superGevrey_log_height_equivalent hβ).log log_nat_atTop
  have hlll := hll.log loglog_nat_atTop
  have hquot := (isEquivalent_iff_tendsto_one
    (logloglog_nat_atTop.eventually_ne_atTop 0)).mp hlll
  have hp := hquot.rpow_const (Or.inl (one_ne_zero : (1 : ℝ) ≠ 0))
  rw [Real.one_rpow] at hp
  have hHlll := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (superGevreyHeight_atTop hβ)))
  have hpow : (fun N : ℕ => Real.log (Real.log (Real.log (superGevreyHeight β N))) ^ β)
      ~[atTop] fun N => Real.log (Real.log (Real.log N)) ^ β := by
    apply isEquivalent_of_tendsto_one
    apply hp.congr'
    filter_upwards [hHlll.eventually_gt_atTop 0,
      logloglog_nat_atTop.eventually_gt_atTop 0] with N hH hN
    exact Real.div_rpow hH.le hN.le β
  exact hll.mul hpow

/-- In height coordinates, length is asymptotic to height times the same slow overlap law. -/
theorem superGevrey_length_equivalent_height_mul_ratio {β : ℝ} (hβ : 2 < β) :
    (fun N : ℕ => (N : ℝ)) ~[atTop]
      fun N => superGevreyHeight β N * superGevreyRealRatio β (superGevreyHeight β N) := by
  apply IsEquivalent.symm
  apply isEquivalent_of_tendsto_one
  have hr := (isEquivalent_iff_tendsto_one
    ((superGevreyRatio_atTop hβ).eventually_ne_atTop 0)).mp
      (superGevrey_ratio_at_height_equivalent hβ)
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  dsimp only [Pi.div_apply, superGevreyHeight, height]
  field_simp

/-- The complete receiver lies below every fixed power length `T^α`, `α>1`. -/
theorem eventually_superGevrey_length_lt_height_rpow {β α : ℝ} (hβ : 2 < β) (hα : 1 < α) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) < superGevreyHeight β N ^ α := by
  filter_upwards [(tendsto_superGevrey_bandwidth hβ).eventually (gt_mem_nhds hα),
    (superGevreyHeight_atTop hβ).eventually_gt_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with N hband hH hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH0 := zero_lt_one.trans hH
  rw [← Real.log_lt_log_iff hN0 (Real.rpow_pos_of_pos hH0 α), Real.log_rpow hH0]
  exact (div_lt_iff₀ (Real.log_pos hH)).mp hband

/-- Exact transport of the existing RH equivalence to inverse-width spectral height. -/
theorem riemannHypothesis_iff_steklovDCProfile_nonneg_at_height {β : ℝ} (hβ : 2 < β) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (superGevreyHeight β N) steklovDCProfile)) :=
  riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey hβ

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_superGevrey_bandwidth
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.superGevrey_ratio_at_height_equivalent
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.superGevrey_length_equivalent_height_mul_ratio
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_steklovDCProfile_nonneg_at_height
