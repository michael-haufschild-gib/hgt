import GaloisForLFunctions.RHTower.SoninPrimePolarHeadMellin
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier

/-!
# Euler-chamber identity for the original prime–polar head

The original finite scalar cell assemblies converge, in their absolute
convergence chamber, to prime zeta minus the literal polar Laplace integral.
This identifies the physical source primitive without changing the source.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
open scoped BigOperators

namespace RHTower

/-- Original scalar polar integrand, before taking an infinite-cutoff limit. -/
def soninPolarHeadIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  (((Real.exp u + 1) / u : ℝ) : ℂ) * Complex.exp (-s * u)

/-- Original scalar polar head integral in its absolute convergence chamber. -/
def soninPolarHeadLaplace (b : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi b, soninPolarHeadIntegrand s u

private theorem continuousOn_polarIntegrand (s : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousOn (soninPolarHeadIntegrand s) (Ici b) := by
  intro u hu
  have hu0 : u ≠ 0 := ne_of_gt (hb.trans_le hu)
  apply ContinuousAt.continuousWithinAt
  unfold soninPolarHeadIntegrand
  fun_prop

private theorem norm_polarIntegrand_le (s : ℂ) {b u : ℝ} (hb : 0 < b) (hu : b ≤ u) :
    ‖soninPolarHeadIntegrand s u‖ ≤ (2 / b) * Real.exp ((1 - s.re) * u) := by
  have hu0 : 0 < u := hb.trans_le hu
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
  have hd : (Real.exp u + 1) / u ≤ (2 / b) * Real.exp u := by
    calc
      (Real.exp u + 1) / u ≤ (2 * Real.exp u) / u := by gcongr; linarith
      _ ≤ (2 * Real.exp u) / b := by gcongr
      _ = _ := by ring
  have he : Real.exp u * Real.exp (-s.re * u) = Real.exp ((1 - s.re) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [soninPolarHeadIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Complex.norm_exp]
  simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ ((2 / b) * Real.exp u) * Real.exp (-s.re * u) := by
      exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, he]

/-- The original polar head is absolutely integrable on the Euler chamber. -/
theorem integrableOn_soninPolarHeadIntegrand {b : ℝ} (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (soninPolarHeadIntegrand s) (Ioi b) := by
  have hdom := (integrableOn_exp_mul_Ioi (a := 1 - s.re) (by linarith) b).const_mul (2 / b)
  apply hdom.mono'
  · exact ((continuousOn_polarIntegrand s hb).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_polarIntegrand_le s hb hu.le

/-- Negative derivative of the original polar head integral starting at `b`. -/
def soninPolarHeadCurrent (b : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s - 1) * b) / (s - 1) + Complex.exp (-s * b) / s

/-- The current forced by a native physical source, with the exact polar correction. -/
def soninSourcePrimeCurrent (b : ℝ) (f : SoninL2) (s : ℂ) : ℂ :=
  -deriv (soninSourceMellinPrimitive f) s + soninPolarHeadCurrent b s

private theorem polarIntegrand_hasDerivAt {u : ℝ} (hu : 0 < u) (s : ℂ) :
    HasDerivAt (fun z => soninPolarHeadIntegrand z u)
      (-((Real.exp u + 1 : ℝ) : ℂ) * Complex.exp (-s * u)) s := by
  have h := (((hasDerivAt_id s).neg.mul_const (u : ℂ)).cexp).const_mul
    (((Real.exp u + 1) / u : ℝ) : ℂ)
  refine h.congr_deriv ?_
  dsimp only [Pi.neg_apply, id_eq]
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  push_cast
  field_simp

/-- The exact polar derivative, including the retained lower endpoint. -/
theorem hasDerivAt_soninPolarHeadLaplace {b : ℝ} (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (soninPolarHeadLaplace b) (-soninPolarHeadCurrent b s) s := by
  let ε : ℝ := (s.re - 1) / 2
  let c : ℝ := (s.re + 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hc : 1 < c := by dsimp [c]; linarith
  let F' : ℂ → ℝ → ℂ := fun z u =>
    -((Real.exp u + 1 : ℝ) : ℂ) * Complex.exp (-z * u)
  have hm (z : ℂ) : AEStronglyMeasurable (soninPolarHeadIntegrand z)
      (volume.restrict (Ioi b)) :=
    ((continuousOn_polarIntegrand z hb).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  have hm' : AEStronglyMeasurable (F' s) (volume.restrict (Ioi b)) := by
    exact (show Continuous (F' s) by dsimp [F']; fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi b), ∀ z ∈ Metric.ball s ε,
      ‖F' z u‖ ≤ 2 * Real.exp ((1 - c) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hu0 : 0 < u := hb.trans hu
    have hzc : c ≤ z.re := by
      have hr := Complex.abs_re_le_norm (z - s)
      have hd : ‖z - s‖ < ε := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have hlo := (abs_lt.mp (hr.trans_lt hd)).1
      simp only [sub_re] at hlo
      dsimp [ε, c] at hlo ⊢
      linarith
    have he1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
    dsimp only [F']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Complex.norm_exp]
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ (2 * Real.exp u) * Real.exp (-c * u) := by gcongr; linarith
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hd : ∀ᵐ u ∂volume.restrict (Ioi b), ∀ z ∈ Metric.ball s ε,
      HasDerivAt (fun w => soninPolarHeadIntegrand w u) (F' z u) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z _
    exact polarIntegrand_hasDerivAt (hb.trans hu) z
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hε) (Eventually.of_forall hm)
    (integrableOn_soninPolarHeadIntegrand hb hs) hm' hbound
    ((integrableOn_exp_mul_Ioi (a := 1 - c) (by linarith) b).const_mul 2) hd
  have hsneg : (-(s - 1)).re < 0 := by simp; linarith
  have hsneg' : (-s).re < 0 := by simp; linarith
  have hfun : F' s = fun u : ℝ =>
      -(Complex.exp (-(s - 1) * u) + Complex.exp (-s * u)) := by
    funext u
    have he : Complex.exp (u : ℂ) * Complex.exp (-s * u) =
        Complex.exp (-(s - 1) * u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    dsimp only [F']
    push_cast
    rw [neg_mul, add_mul, one_mul, he]
  have hvalue : (∫ u in Ioi b, F' s u) = -soninPolarHeadCurrent b s := by
    rw [hfun, integral_neg, integral_add
      (integrableOn_exp_mul_complex_Ioi hsneg b)
      (integrableOn_exp_mul_complex_Ioi hsneg' b),
      integral_exp_mul_complex_Ioi hsneg b, integral_exp_mul_complex_Ioi hsneg' b]
    simp only [neg_div_neg_eq, soninPolarHeadCurrent]
  rw [hvalue] at hkey
  exact hkey.2

private theorem primeHead_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => if (n + 2).Prime then
      Complex.exp (-s * Real.log (n + 2 : ℝ)) else 0) (coronaPrimeZeta s) := by
  have hsum := (summable_coronaPrimeEigenvalue hs).hasSum
  have hnat : HasSum (fun n : ℕ => if n.Prime then (n : ℂ) ^ (-s) else 0)
      (coronaPrimeZeta s) := by
    have hi := (hasSum_subtype_iff_indicator (s := {n : ℕ | n.Prime})
      (f := fun n : ℕ => (n : ℂ) ^ (-s))).mp hsum
    have he : ({n : ℕ | n.Prime}.indicator fun n => (n : ℂ) ^ (-s)) =
        fun n => if n.Prime then (n : ℂ) ^ (-s) else 0 := by
      funext n
      by_cases hn : n.Prime <;> simp [hn]
    rw [he] at hi
    exact hi
  have hshift : HasSum (fun n : ℕ => if (n + 2).Prime then
      ((n + 2 : ℕ) : ℂ) ^ (-s) else 0) (coronaPrimeZeta s) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ =>
      if n.Prime then (n : ℂ) ^ (-s) else 0) 2).mpr
    simpa [Finset.sum_range_succ, show ¬ Nat.Prime 0 by decide,
      show ¬ Nat.Prime 1 by decide] using hnat
  have heq : (fun n : ℕ => if (n + 2).Prime then
      Complex.exp (-s * Real.log (n + 2 : ℝ)) else 0) =
      fun n : ℕ => if (n + 2).Prime then ((n + 2 : ℕ) : ℂ) ^ (-s) else 0 := by
    funext n
    by_cases hp : (n + 2).Prime
    · simp only [hp, if_true]
      have hn : 0 < (n + 2 : ℝ) := by positivity
      rw [show ((n + 2 : ℕ) : ℂ) = ((n + 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
        ← Complex.ofReal_log hn.le]
      congr 1
      ring
    · simp only [hp, if_false]
  rw [heq]
  exact hshift

private theorem polarCells_eq_integral (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.range (N + 1),
      ∫ u in Icc (Real.log (n + 2 : ℝ)) (Real.log (n + 3 : ℝ)),
        soninPolarHeadIntegrand s u) =
      ∫ u in Real.log 2..Real.log (N + 3 : ℝ), soninPolarHeadIntegrand s u := by
  have hint (n : ℕ) : IntervalIntegrable (soninPolarHeadIntegrand s) volume
      (Real.log (n + 2 : ℝ)) (Real.log (n + 3 : ℝ)) := by
    have hlog : Real.log (n + 2 : ℝ) ≤ Real.log (n + 3 : ℝ) :=
      Real.log_le_log (by positivity) (by linarith)
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlog]
    exact (continuousOn_polarIntegrand s
      (Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n]))).mono
      (fun _ hu => hu.1)
  have heq (n : ℕ) :
      (∫ u in Icc (Real.log (n + 2 : ℝ)) (Real.log (n + 3 : ℝ)), soninPolarHeadIntegrand s u) =
      ∫ u in Real.log (n + 2 : ℝ)..Real.log (n + 3 : ℝ), soninPolarHeadIntegrand s u := by
    rw [intervalIntegral.integral_of_le (Real.log_le_log (by positivity) (by linarith)),
      integral_Icc_eq_integral_Ioc]
  simp_rw [heq]
  simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, add_assoc,
    show (1 : ℝ) + 2 = 3 by norm_num] using intervalIntegral.sum_integral_adjacent_intervals
    (f := soninPolarHeadIntegrand s) (μ := volume)
    (a := fun n : ℕ => Real.log (n + 2 : ℝ)) (n := N + 1)
    (fun n _ => by simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using hint n)

/-- Exact absolute-convergence limit of the original finite arithmetic head. -/
theorem soninPrimePolarHeadScalar_tendsto_euler {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => soninPrimePolarHeadScalar N s) atTop
      (𝓝 (coronaPrimeZeta s - soninPolarHeadLaplace (Real.log 2) s)) := by
  have hp := (primeHead_hasSum hs).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 3 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono
      (fun N : ℕ => show (N : ℝ) ≤ N + 3 by linarith) tendsto_natCast_atTop_atTop)
  have hi := intervalIntegral_tendsto_integral_Ioi (Real.log 2)
    (integrableOn_soninPolarHeadIntegrand (Real.log_pos (by norm_num)) hs) hlog
  have h := hp.sub hi
  convert h using 1
  · funext N
    simp only [soninPrimePolarHeadScalar, Finset.sum_sub_distrib, Function.comp_apply]
    congr 1
    exact polarCells_eq_integral N s
  · rfl

/-- An admitted native source agrees with prime zeta minus the original polar integral wherever
both arithmetic terms converge absolutely. -/
theorem soninSourceMellinPrimitive_eq_euler_of_source_limit
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {f : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarCellSource 1 (φ k)) atTop (𝓝 f))
    {s : ℂ} (hs : 1 < s.re) :
    soninSourceMellinPrimitive f s =
      coronaPrimeZeta s - soninPolarHeadLaplace (Real.log 2) s :=
  tendsto_nhds_unique (soninPrimePolarHeadScalar_tendsto_of_source_limit hf (by linarith))
    ((soninPrimePolarHeadScalar_tendsto_euler hs).comp hφ)

/-- Native admission supplies the exact Euler-chamber first-prime current identity. -/
theorem soninSourcePrimeCurrent_eq_primeLog_of_source_limit
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {f : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarCellSource 1 (φ k)) atTop (𝓝 f))
    {s : ℂ} (hs : 1 < s.re) :
    soninSourcePrimeCurrent (Real.log 2) f s = xiPrimeLogDirichlet s := by
  have heq : soninSourceMellinPrimitive f =ᶠ[𝓝 s] fun z =>
      coronaPrimeZeta z - soninPolarHeadLaplace (Real.log 2) z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact soninSourceMellinPrimitive_eq_euler_of_source_limit hφ hf hz
  have hp := (differentiableAt_coronaPrimeZeta hs).hasDerivAt
  have hi := hasDerivAt_soninPolarHeadLaplace (b := Real.log 2)
    (Real.log_pos (by norm_num)) hs
  have hd : HasDerivAt (fun z => coronaPrimeZeta z - soninPolarHeadLaplace (Real.log 2) z)
      (deriv coronaPrimeZeta s - -soninPolarHeadCurrent (Real.log 2) s) s := hp.sub hi
  rw [soninSourcePrimeCurrent, heq.deriv_eq, hd.deriv]
  have hprime := neg_deriv_coronaPrimeZeta_eq_xiPrimeLogDirichlet hs
  linear_combination hprime

end RHTower
