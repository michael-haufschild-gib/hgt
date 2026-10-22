import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarDLVPRate
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszFUCurvatureTransport


/-!
# Polynomial cancellation of the actual completed critical-Mellin source

The corpus PNT remainder survives its absolute primitive and exact Volterra
completion after multiplication by every fixed polynomial in log height.
The moving half-cut retains the full early interval. These actual-source
estimates pay for the frequency factor in Stieltjes integration by parts.
-/

open MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower

/-- Absolute primitive of the actual normalized Chebyshev driver. -/
def criticalMellinAbsoluteChebyshevPrimitive (h : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..h, |criticalMellinNormalizedChebyshevError t|

private theorem normalizedError_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable criticalMellinNormalizedChebyshevError volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp b) + Real.exp b) (by simp)
    measurable_criticalMellinNormalizedChebyshevError.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_criticalMellinNormalizedChebyshevError_le_endpoint ⟨ha.trans ht.1.le, ht.2⟩

private theorem absolutePrimitive_nonneg {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ criticalMellinAbsoluteChebyshevPrimitive h :=
  intervalIntegral.integral_nonneg hh (fun _ _ => abs_nonneg _)

private theorem pow_exp_decay (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-c * h)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) c hc

private theorem pow_sqrt_exp_decay (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-c * Real.sqrt h)) atTop (𝓝 0) := by
  have hh := (pow_exp_decay (2 * m) hc).comp Real.tendsto_sqrt_atTop
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
  simp only [Function.comp_apply, pow_mul, Real.sq_sqrt hh]

/-- Every fixed polynomial factor is absorbed by the actual PNT remainder. -/
theorem tendsto_pow_mul_exp_neg_half_mul_abs_criticalMellinNormalizedChebyshevError
    (m : ℕ) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-h / 2) *
      |criticalMellinNormalizedChebyshevError h|) atTop (𝓝 0) := by
  obtain ⟨c, B, hc, hB, hr⟩ :=
    exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt
  have hlim := (pow_sqrt_exp_decay m hc).const_mul B
  simp only [mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    positivity
  · filter_upwards [hr, eventually_ge_atTop (0 : ℝ)] with h hr hh
    have hscaled := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ h ^ m * Real.exp (-h / 2))
    refine hscaled.trans_eq ?_
    have he : Real.exp (-h / 2) * Real.exp (h / 2 - c * Real.sqrt h) =
        Real.exp (-c * Real.sqrt h) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = B * (h ^ m * (Real.exp (-h / 2) *
          Real.exp (h / 2 - c * Real.sqrt h))) := by ring
      _ = _ := by rw [he]

private theorem integral_exp_half (a b : ℝ) :
    (∫ t in a..b, Real.exp (t / 2)) =
      2 * Real.exp (b / 2) - 2 * Real.exp (a / 2) := by
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => 2 * Real.exp (t / 2)) (Real.exp (t / 2)) t := by
    intro t _
    have hlin : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const (2 : ℝ)
    have he : HasDerivAt (fun y : ℝ => 2 * Real.exp (y / 2))
        (2 * (Real.exp (t / 2) * (1 / 2))) t := by
      simpa only [Function.comp_apply] using
        ((Real.hasDerivAt_exp (t / 2)).comp t hlin).const_mul (2 : ℝ)
    convert he using 1
    ring

  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).intervalIntegrable a b)

private theorem absolutePrimitive_half_split_bound {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hr : ∀ᶠ h : ℝ in atTop, |criticalMellinNormalizedChebyshevError h| ≤
      B * Real.exp (h / 2 - c * Real.sqrt h)) :
    ∀ᶠ h : ℝ in atTop,
      criticalMellinAbsoluteChebyshevPrimitive h ≤
        (h / 2) * (h + 1) * Real.exp (h / 4) +
          2 * B * Real.exp (h / 2 - c * Real.sqrt (h / 2)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hr
  filter_upwards [eventually_ge_atTop (max 0 (2 * T))] with h hh
  have hh0 : 0 ≤ h := (le_max_left _ _).trans hh
  have hTh : T ≤ h / 2 := by linarith [(le_max_right 0 (2 * T)).trans hh]
  have hhalf : 0 ≤ h / 2 := by positivity
  have hhalfh : h / 2 ≤ h := by linarith
  have hhead : (∫ t in (0 : ℝ)..h / 2, |criticalMellinNormalizedChebyshevError t|) ≤
      (h / 2) * (h + 1) * Real.exp (h / 4) := by
    have hb := intervalIntegral.integral_mono_on hhalf
      (normalizedError_integrable (by rfl) hhalf).abs
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => (h + 1) * Real.exp (h / 4)) volume 0 (h / 2))
      (fun t ht => (abs_criticalMellinNormalizedChebyshevError_le_log_sqrt ht.1).trans ?_)
    · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using hb
    · exact mul_le_mul (by linarith [ht.2])
        (Real.exp_le_exp.mpr (by linarith [ht.2]))
        (Real.exp_pos _).le (by linarith)
  have htail : (∫ t in h / 2..h, |criticalMellinNormalizedChebyshevError t|) ≤
      2 * B * Real.exp (h / 2 - c * Real.sqrt (h / 2)) := by
    have hb := intervalIntegral.integral_mono_on hhalfh
      (normalizedError_integrable hhalf hhalfh).abs
      ((by fun_prop : Continuous
        (fun t : ℝ => B * Real.exp (-c * Real.sqrt (h / 2)) * Real.exp (t / 2))).intervalIntegrable _ _)
      (fun t ht => (hT t (hTh.trans ht.1)).trans ?_)
    · rw [intervalIntegral.integral_const_mul, integral_exp_half] at hb
      refine hb.trans ?_
      have heq : 2 * B * Real.exp (h / 2 - c * Real.sqrt (h / 2)) =
          B * Real.exp (-c * Real.sqrt (h / 2)) * (2 * Real.exp (h / 2)) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_pos ((h / 2) / 2)])
        (by positivity)
    · rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_le_sqrt ht.1]
  rw [criticalMellinAbsoluteChebyshevPrimitive,
    ← intervalIntegral.integral_add_adjacent_intervals
      (normalizedError_integrable (by rfl) hhalf).abs
      (normalizedError_integrable hhalf hhalfh).abs]
  exact add_le_add hhead htail

/-- Absolute integration retains all fixed polynomial savings of the actual
normalized Chebyshev driver. The moving half-cut retains the entire head. -/
theorem tendsto_pow_mul_exp_neg_half_mul_criticalMellinAbsoluteChebyshevPrimitive
    (m : ℕ) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-h / 2) *
      criticalMellinAbsoluteChebyshevPrimitive h) atTop (𝓝 0) := by
  obtain ⟨c, B, hc, hB, hr⟩ :=
    exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt
  have hfirst : Tendsto (fun h : ℝ =>
      (h ^ (m + 2) * Real.exp (-(1 / 4 : ℝ) * h) +
        h ^ (m + 1) * Real.exp (-(1 / 4 : ℝ) * h)) / 2) atTop (𝓝 0) := by
    simpa only [zero_add, zero_div] using
      ((pow_exp_decay (m + 2) (by norm_num : (0 : ℝ) < 1 / 4)).add
        (pow_exp_decay (m + 1) (by norm_num : (0 : ℝ) < 1 / 4))).div_const 2
  have hc' : 0 < c / Real.sqrt 2 := by positivity
  have hsecond := (pow_sqrt_exp_decay m hc').const_mul (2 * B)
  simp only [mul_zero] at hsecond
  have hlim := hfirst.add hsecond
  simp only [zero_add] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    exact mul_nonneg (by positivity) (absolutePrimitive_nonneg hh)
  · filter_upwards [absolutePrimitive_half_split_bound hc hB hr,
      eventually_ge_atTop (0 : ℝ)] with h hb hh
    have hscaled := mul_le_mul_of_nonneg_left hb
      (by positivity : 0 ≤ h ^ m * Real.exp (-h / 2))
    refine hscaled.trans_eq ?_
    rw [mul_add]
    have hsplit : Real.sqrt (h / 2) = Real.sqrt h / Real.sqrt 2 :=
      Real.sqrt_div hh 2
    rw [hsplit]
    have he1 : Real.exp (-h / 2) * Real.exp (h / 4) =
        Real.exp (-(1 / 4 : ℝ) * h) := by rw [← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (-h / 2) * Real.exp (h / 2 - c * (Real.sqrt h / Real.sqrt 2)) =
        Real.exp (-(c / Real.sqrt 2) * Real.sqrt h) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (h ^ (m + 2) + h ^ (m + 1)) / 2 *
            (Real.exp (-h / 2) * Real.exp (h / 4)) +
          (2 * B) * (h ^ m * (Real.exp (-h / 2) *
            Real.exp (h / 2 - c * (Real.sqrt h / Real.sqrt 2)))) := by
              simp only [pow_add, pow_one, pow_two]
              ring
      _ = _ := by rw [he1, he2]; ring

private theorem completedError_abs_le_driver_primitive {h : ℝ} (hh : 0 ≤ h) :
    |criticalMellinCompletedError h| ≤
      3 + |criticalMellinNormalizedChebyshevError h| +
        criticalMellinAbsoluteChebyshevPrimitive h / 2 := by
  have hs : 1 ≤ Real.sqrt (Real.exp h) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (Real.one_le_exp hh)
  have hz : 0 ≤ 2 / Real.sqrt (Real.exp h) := by positivity
  have hu : 2 / Real.sqrt (Real.exp h) ≤ 2 := by
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hsmall : |1 - 2 / Real.sqrt (Real.exp h)| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  have hi := intervalIntegral.abs_integral_le_integral_abs
    (f := criticalMellinNormalizedChebyshevError) (μ := volume) hh
  rw [criticalMellinCompletedError_eq_volterraPotential hh,
    criticalMellinChebyshevVolterraPotential, ← intervalIntegral.integral_of_le hh]
  have htri := (abs_sub
    (1 - 2 / Real.sqrt (Real.exp h) - criticalMellinNormalizedChebyshevError h)
    ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..h, criticalMellinNormalizedChebyshevError t)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at htri
  change |∫ t in (0 : ℝ)..h, criticalMellinNormalizedChebyshevError t| ≤
    criticalMellinAbsoluteChebyshevPrimitive h at hi
  linarith

private theorem completedError_absolutePrimitive_le {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, |criticalMellinCompletedError t|) ≤
      3 * h + (1 + h / 2) * criticalMellinAbsoluteChebyshevPrimitive h := by
  have hE := (normalizedError_integrable (by rfl) hh).abs
  have hD :=
    (GaloisForLFunctions.RHTower.intervalIntegrable_criticalMellinCompletedError_on_Icc hh).abs
  have hJ : ∀ t ∈ Icc (0 : ℝ) h,
      criticalMellinAbsoluteChebyshevPrimitive t ≤ criticalMellinAbsoluteChebyshevPrimitive h := by
    intro t ht
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall fun _ => abs_nonneg _) hE
  have hc : IntervalIntegrable
      (fun t : ℝ => 3 + |criticalMellinNormalizedChebyshevError t|) volume 0 h :=
    intervalIntegrable_const.add hE
  have hb := intervalIntegral.integral_mono_on hh hD
    (hc.add (intervalIntegrable_const (c := criticalMellinAbsoluteChebyshevPrimitive h / 2)))
    (fun t ht => (completedError_abs_le_driver_primitive ht.1).trans
      (add_le_add le_rfl (div_le_div_of_nonneg_right (hJ t ht) (by norm_num : (0 : ℝ) ≤ 2))))
  rw [intervalIntegral.integral_add hc intervalIntegrable_const,
    intervalIntegral.integral_add intervalIntegrable_const hE,
    intervalIntegral.integral_const, intervalIntegral.integral_const] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  change (∫ t in (0 : ℝ)..h, |criticalMellinCompletedError t|) ≤
    h * 3 + criticalMellinAbsoluteChebyshevPrimitive h +
      h * (criticalMellinAbsoluteChebyshevPrimitive h / 2) at hb
  convert hb using 1
  ring

private theorem pow_half_exp_decay (m : ℕ) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-h / 2)) atTop (𝓝 0) := by
  convert pow_exp_decay m (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext h
  congr 1
  congr 1
  ring

/-- The completed critical-Mellin error retains every fixed polynomial
saving after its exact Volterra completion. -/
theorem tendsto_pow_mul_exp_neg_half_mul_abs_criticalMellinCompletedError (m : ℕ) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-h / 2) *
      |criticalMellinCompletedError h|) atTop (𝓝 0) := by
  have hlim := ((pow_half_exp_decay m).mul_const 3).add
    (tendsto_pow_mul_exp_neg_half_mul_abs_criticalMellinNormalizedChebyshevError m) |>.add
      ((tendsto_pow_mul_exp_neg_half_mul_criticalMellinAbsoluteChebyshevPrimitive m).div_const 2)
  simp only [zero_mul, zero_add, zero_div] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    have hb := mul_le_mul_of_nonneg_left (completedError_abs_le_driver_primitive hh)
      (by positivity : 0 ≤ h ^ m * Real.exp (-h / 2))
    convert hb using 1 <;> first | rfl | ring

/-- The absolute completed-error primitive retains every fixed polynomial
saving, allowing a growing polynomial band of Stieltjes test frequencies. -/
theorem tendsto_pow_mul_exp_neg_half_mul_completedError_absolutePrimitive (m : ℕ) :
    Tendsto (fun h : ℝ => h ^ m * Real.exp (-h / 2) *
      (∫ t in (0 : ℝ)..h, |criticalMellinCompletedError t|)) atTop (𝓝 0) := by
  have hlim := ((pow_half_exp_decay (m + 1)).mul_const 3).add
    (tendsto_pow_mul_exp_neg_half_mul_criticalMellinAbsoluteChebyshevPrimitive m) |>.add
      ((tendsto_pow_mul_exp_neg_half_mul_criticalMellinAbsoluteChebyshevPrimitive (m + 1)).div_const 2)
  simp only [zero_mul, zero_add, zero_div] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hh (fun _ _ => abs_nonneg _))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    have hb := mul_le_mul_of_nonneg_left (completedError_absolutePrimitive_le hh)
      (by positivity : 0 ≤ h ^ m * Real.exp (-h / 2))
    convert hb using 1 <;> first | rfl | (simp only [pow_succ]; ring)

end RHTower
end
