import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Selection of the first active arithmetic atom by the complete theta tail

The infinite original Mangoldt tail, divided by its first theta translate, converges
to that translate's atom. The archimedean tail vanishes in the same normalization.
These are statements about the complete source, not finite prime truncations.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDTail
open HedenmalmThetaSource

def envelopeRatio : ℝ := thetaEnvelopeUpper / thetaEnvelopeLower

theorem envelopeRatio_pos : 0 < envelopeRatio :=
  div_pos thetaEnvelopeUpper_pos thetaEnvelopeLower_pos

theorem theta_ratio_le {x t : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t) :
    thetaCuspFullSource (x + t) / thetaCuspFullSource x ≤
      envelopeRatio * Real.exp (-2 * t) := by
  have hK : thetaEnvelopeUpper * thetaEnvelope x ≤
      envelopeRatio * thetaCuspFullSource x := by
    calc
      _ = envelopeRatio * (thetaEnvelopeLower * thetaEnvelope x) := by
        unfold envelopeRatio
        field_simp [thetaEnvelopeLower_pos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (thetaCuspFullSource_ge_envelope (by linarith)) envelopeRatio_pos.le
  have hA : 2 ≤ Real.pi * Real.exp (2 * x) := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_gt_three]
  apply (div_le_iff₀ (thetaCuspFullSource_pos_all x)).2
  calc
    thetaCuspFullSource (x + t) ≤
        (thetaEnvelopeUpper * thetaEnvelope x) *
          Real.exp (-(Real.pi * Real.exp (2 * x)) * t) := by
      simpa only [add_sub_cancel_left] using
        thetaCuspFullSource_le_shift hx (show x ≤ x + t by linarith)
    _ ≤ (thetaEnvelopeUpper * thetaEnvelope x) * Real.exp (-2 * t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
        (mul_pos thetaEnvelopeUpper_pos (thetaEnvelope_pos x)).le
    _ ≤ (envelopeRatio * thetaCuspFullSource x) * Real.exp (-2 * t) :=
      mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = _ := by ring

theorem theta_log_ratio_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {x : ℝ} (hx : 1 ≤ x) :
    thetaCuspFullSource (x + Real.log n) /
        thetaCuspFullSource (x + Real.log m) ≤
      envelopeRatio * (m : ℝ)^2 / (n : ℝ)^2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log (m : ℝ) ≤ Real.log n :=
    Real.log_le_log hm0 (by exact_mod_cast hmn)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have h := theta_ratio_le (x := x + Real.log m)
    (t := Real.log n - Real.log m) (by linarith) (by linarith)
  have he : Real.exp (-2 * (Real.log (n : ℝ) - Real.log m)) =
      (m : ℝ)^2 / (n : ℝ)^2 := by
    rw [show -2 * (Real.log (n : ℝ) - Real.log m) =
      (Real.log m + Real.log m) - (Real.log n + Real.log n) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hm0, Real.exp_log hn0]
    ring
  simpa only [show x + Real.log m + (Real.log n - Real.log m) =
    x + Real.log n by ring, he, mul_div_assoc] using h

def primeTailTerm (m : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if m ≤ n then vonMangoldtAtom n * thetaCuspFullSource (x + Real.log n) else 0

def primeTail (m : ℕ) (x : ℝ) : ℝ := ∑' n, primeTailTerm m x n

theorem primeTailTerm_nonneg (m : ℕ) (x : ℝ) (n : ℕ) :
    0 ≤ primeTailTerm m x n := by
  unfold primeTailTerm
  split_ifs
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (thetaCuspFullSource_pos_all _).le
  · rfl

theorem primeTail_nonneg (m : ℕ) (x : ℝ) : 0 ≤ primeTail m x :=
  tsum_nonneg (primeTailTerm_nonneg m x)

theorem atom_le_mangoldt {n : ℕ} (hn : 2 ≤ n) :
    vonMangoldtAtom n ≤ |(ArithmeticFunction.vonMangoldt n : ℝ)| := by
  rw [vonMangoldtAtom, if_pos hn]
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
  have hnon := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  rw [abs_of_nonneg hnon]
  exact div_le_self hnon hs

theorem primeTailTerm_ratio_le {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 1 ≤ x)
    (n : ℕ) :
    ‖primeTailTerm m x n / thetaCuspFullSource (x + Real.log m)‖ ≤
      (envelopeRatio * (m : ℝ)^2) *
        (|(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ)^2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (primeTailTerm_nonneg m x n) (thetaCuspFullSource_pos_all _).le)]
  by_cases hmn : m ≤ n
  · rw [primeTailTerm, if_pos hmn, mul_div_assoc]
    calc
      _ ≤ vonMangoldtAtom n * (envelopeRatio * (m : ℝ)^2 / (n : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (theta_log_ratio_le hm hmn hx) (vonMangoldtAtom_nonneg n)
      _ ≤ |(ArithmeticFunction.vonMangoldt n : ℝ)| *
          (envelopeRatio * (m : ℝ)^2 / (n : ℝ)^2) :=
        mul_le_mul_of_nonneg_right (atom_le_mangoldt (hm.trans hmn))
          (div_nonneg (mul_nonneg envelopeRatio_pos.le (sq_nonneg _)) (sq_nonneg _))
      _ = _ := by ring
  · simp only [primeTailTerm, if_neg hmn, zero_div]
    exact mul_nonneg (mul_nonneg envelopeRatio_pos.le (sq_nonneg _))
      (div_nonneg (abs_nonneg _) (sq_nonneg _))

theorem summable_primeTailTerm {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 1 ≤ x) :
    Summable (primeTailTerm m x) := by
  have hs := Summable.of_norm_bounded
    (summable_vonMangoldt_abs_div_sq.mul_left (envelopeRatio * (m : ℝ)^2))
    (primeTailTerm_ratio_le hm hx)
  have h := hs.mul_right (thetaCuspFullSource (x + Real.log m))
  simpa only [div_mul_cancel₀ _ (thetaCuspFullSource_pos_all _).ne'] using h

/-- The full countable arithmetic tail selects its first atom. -/
theorem primeTail_selects_first {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun x => primeTail m x / thetaCuspFullSource (x + Real.log m))
      atTop (𝓝 (vonMangoldtAtom m)) := by
  have hpoint (n : ℕ) :
      Tendsto (fun x => primeTailTerm m x n / thetaCuspFullSource (x + Real.log m))
        atTop (𝓝 (if n = m then vonMangoldtAtom m else 0)) := by
    by_cases hnm : n = m
    · subst n
      simpa only [primeTailTerm, if_pos (le_refl m), if_true,
        mul_div_cancel_right₀ _ (thetaCuspFullSource_pos_all _).ne'] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => vonMangoldtAtom m) atTop _)
    · by_cases hmn : m ≤ n
      · have hlog : Real.log (m : ℝ) < Real.log n :=
          Real.log_lt_log (by exact_mod_cast (by omega : 0 < m))
            (by exact_mod_cast (by omega : m < n))
        simpa only [primeTailTerm, if_pos hmn, if_neg hnm, mul_div_assoc, mul_zero] using
          (thetaCuspFullSource_add_div_add_tendsto_zero hlog).const_mul (vonMangoldtAtom n)
      · simpa only [primeTailTerm, if_neg hmn, if_neg hnm, zero_div] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  have h := tendsto_tsum_of_dominated_convergence
    (summable_vonMangoldt_abs_div_sq.mul_left (envelopeRatio * (m : ℝ)^2))
    hpoint (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact primeTailTerm_ratio_le hm hx)
  simpa only [tsum_div_const, primeTail, tsum_ite_eq] using h

/-- Advancing the initial state kills the complete prime tail in the old normalization. -/
theorem primeTail_advanced_vanishes {m : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun x => primeTail m (x + h) / thetaCuspFullSource (x + Real.log m))
      atTop (𝓝 0) := by
  have hp := (primeTail_selects_first hm).comp
    (tendsto_atTop_add_const_right atTop h tendsto_id)
  have ht := thetaCuspFullSource_add_div_add_tendsto_zero
    (show Real.log (m : ℝ) < h + Real.log m by linarith)
  have he (x : ℝ) :
      (primeTail m (x + h) / thetaCuspFullSource (x + h + Real.log m)) *
        (thetaCuspFullSource (x + (h + Real.log m)) /
          thetaCuspFullSource (x + Real.log m)) =
      primeTail m (x + h) / thetaCuspFullSource (x + Real.log m) := by
    rw [← add_assoc]
    field_simp [(thetaCuspFullSource_pos_all _).ne']
  simpa only [Function.comp_def, id_eq, he, mul_zero] using hp.mul ht

def archTail (s x : ℝ) : ℝ :=
  ∫ t in Ioi s, archLevyDensity t * thetaCuspFullSource (x + t)

theorem archTail_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 ≤ archTail s x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (archLevyDensity_pos (hs.trans ht)).le (thetaCuspFullSource_pos_all _).le

theorem archTail_ratio_measurable (s x : ℝ) :
    AEStronglyMeasurable (fun t =>
      archLevyDensity t * thetaCuspFullSource (x + t) / thetaCuspFullSource (x + s))
      (volume.restrict (Ioi s)) :=
  ((measurable_archLevyDensity.mul
    (thetaSource.continuous_k.measurable.comp (measurable_const.add measurable_id))).div_const
      _).aestronglyMeasurable

theorem archTail_ratio_bound {s x t : ℝ} (hs : 0 < s) (hx : 1 ≤ x + s) (ht : s < t) :
    ‖archLevyDensity t * thetaCuspFullSource (x + t) / thetaCuspFullSource (x + s)‖ ≤
      envelopeRatio * archLevyDensity t := by
  have hw := (archLevyDensity_pos (hs.trans ht)).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (mul_nonneg hw (thetaCuspFullSource_pos_all _).le)
      (thetaCuspFullSource_pos_all _).le), mul_div_assoc]
  have hr : thetaCuspFullSource (x + t) / thetaCuspFullSource (x + s) ≤
      envelopeRatio := by
    have h := theta_ratio_le (x := x + s) (t := t - s) hx (by linarith)
    rw [show x + s + (t - s) = x + t by ring] at h
    exact h.trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith)) envelopeRatio_pos.le).trans_eq (mul_one _))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr hw

theorem integrable_archTail {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x + s) :
    IntegrableOn (fun t => archLevyDensity t * thetaCuspFullSource (x + t)) (Ioi s) := by
  have hi : IntegrableOn (fun t =>
      archLevyDensity t * thetaCuspFullSource (x + t) / thetaCuspFullSource (x + s))
      (Ioi s) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hs).const_mul
      envelopeRatio).mono' (archTail_ratio_measurable s x) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact archTail_ratio_bound hs hx ht
  have h := hi.mul_const (thetaCuspFullSource (x + s))
  simpa only [IntegrableOn, div_mul_cancel₀ _ (thetaCuspFullSource_pos_all _).ne'] using h

/-- The full archimedean tail carries no atom at its positive endpoint. -/
theorem archTail_vanishes {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x => archTail s x / thetaCuspFullSource (x + s)) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi s)) (fun t => envelopeRatio * archLevyDensity t)
    (Eventually.of_forall (archTail_ratio_measurable s))
    (by
      filter_upwards [eventually_ge_atTop (1 - s)] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact archTail_ratio_bound hs (by linarith) ht)
    ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hs).const_mul envelopeRatio)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [mul_div_assoc, mul_zero] using
        (thetaCuspFullSource_add_div_add_tendsto_zero ht).const_mul (archLevyDensity t))
  simpa only [integral_div, archTail, integral_zero] using h

end RHTower.CHMDTail
