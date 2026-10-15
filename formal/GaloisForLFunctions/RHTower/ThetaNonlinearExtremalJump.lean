import GaloisForLFunctions.RHTower.ThetaRealGroundPolarization
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Extremal links of the complete nonlinear theta action

Exponential normalization of the cosh action selects exactly maximal
profile jumps. The squared-jump bound retains absolute convergence at
the singular Gamma endpoint. Both arithmetic link measures are kept.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def scaledCoshJump (a d : ℝ) : ℝ := Real.exp (-2 * a) * (Real.cosh (a * d) - 1)

theorem scaledCoshJump_nonneg (a d : ℝ) : 0 ≤ scaledCoshJump a d :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_cosh _))

private theorem sinh_convex_nonneg : ConvexOn ℝ (Ici 0) Real.sinh := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := Real.cosh) (f'' := Real.sinh)
    (convex_Ici 0) Real.continuous_sinh.continuousOn
  · exact fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt
  · exact fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt
  · intro x hx
    exact Real.sinh_nonneg_iff.mpr (interior_subset hx)

/-- A uniform quadratic majorant, including arbitrarily small jumps. -/
theorem scaledCoshJump_le_sq {a d : ℝ} (ha : 0 ≤ a) (hd : |d| ≤ 2) :
    scaledCoshJump a d ≤ d ^ 2 / 8 := by
  have hs : Real.sinh (a * |d| / 2) ≤ |d| / 2 * Real.sinh a := by
    have h := sinh_convex_nonneg.2 (show (0 : ℝ) ∈ Ici 0 by simp)
      ha (show 0 ≤ 1 - |d| / 2 by linarith) (show 0 ≤ |d| / 2 by positivity)
      (show 1 - |d| / 2 + |d| / 2 = 1 by ring)
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero,
      show |d| / 2 * a = a * |d| / 2 by ring] using h
  have he : Real.exp (-a) * Real.sinh a ≤ 1 / 2 := by
    rw [Real.sinh_eq]
    have hcancel : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-a), Real.exp_pos a]
  have hb : Real.exp (-a) * Real.sinh (a * |d| / 2) ≤ |d| / 4 := by
    calc
      _ ≤ Real.exp (-a) * (|d| / 2 * Real.sinh a) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = |d| / 2 * (Real.exp (-a) * Real.sinh a) := by ring
      _ ≤ |d| / 2 * (1 / 2) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  have hpos : 0 ≤ Real.exp (-a) * Real.sinh (a * |d| / 2) :=
    mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr (by positivity))
  have hsq := pow_le_pow_left₀ hpos hb 2
  have hid : scaledCoshJump a d =
      2 * (Real.exp (-a) * Real.sinh (a * |d| / 2)) ^ 2 := by
    have hc : Real.cosh (a * d) = Real.cosh (a * |d|) := by
      rw [← Real.cosh_abs (x := a * d), abs_mul, abs_of_nonneg ha]
    have hx : Real.exp (-2 * a) = Real.exp (-a) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1; ring
    rw [scaledCoshJump, hc, show a * |d| = 2 * (a * |d| / 2) by ring,
      Real.cosh_two_mul, Real.cosh_sq, hx]
    ring
  rw [hid]
  nlinarith [sq_abs d]

theorem scaledCoshJump_eq_exp (a d : ℝ) :
    scaledCoshJump a d =
      (Real.exp ((d - 2) * a) + Real.exp ((-d - 2) * a)) / 2 - Real.exp (-2 * a) := by
  unfold scaledCoshJump
  rw [Real.cosh_eq]
  have h₁ : Real.exp (-2 * a) * Real.exp (a * d) = Real.exp ((d - 2) * a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp (-2 * a) * Real.exp (-(a * d)) = Real.exp ((-d - 2) * a) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith

private theorem exp_mul_tendsto_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun a : ℝ => Real.exp (c * a)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)

/-- The exact pointwise limit records only jumps attaining the maximal size. -/
theorem tendsto_scaledCoshJump {d : ℝ} (hd : |d| ≤ 2) :
    Tendsto (fun a => scaledCoshJump a d) atTop (𝓝 (if |d| = 2 then 1 / 2 else 0)) := by
  simp_rw [scaledCoshJump_eq_exp]
  have h₂ := exp_mul_tendsto_zero (show (-2 : ℝ) < 0 by norm_num)
  by_cases hp : d = 2
  · subst d
    simpa [show (-2 : ℝ) - 2 = -4 by ring] using (((tendsto_const_nhds (x := (1 : ℝ))).add
      (exp_mul_tendsto_zero (show (-4 : ℝ) < 0 by norm_num))).div_const 2).sub h₂
  by_cases hn : d = -2
  · subst d
    simpa [show (-2 : ℝ) - 2 = -4 by ring] using (((exp_mul_tendsto_zero (show (-4 : ℝ) < 0 by norm_num)).add
      (tendsto_const_nhds (x := (1 : ℝ)))).div_const 2).sub h₂
  have hlt : d - 2 < 0 := by have := (abs_le.mp hd).2; exact sub_neg.mpr (lt_of_le_of_ne this hp)
  have hlt' : -d - 2 < 0 := by
    have := lt_of_le_of_ne (abs_le.mp hd).1 (Ne.symm hn)
    linarith
  have hne : |d| ≠ 2 := by
    intro h
    rcases le_total 0 d with hpos | hneg
    · exact hp (by rwa [abs_of_nonneg hpos] at h)
    · exact hn (by rw [abs_of_nonpos hneg] at h; linarith)
  simpa [hne] using (((exp_mul_tendsto_zero hlt).add
    (exp_mul_tendsto_zero hlt')).div_const 2).sub h₂

/-- Signed link weights are allowed; the majorant is the absolute quadratic density. -/
theorem integrable_weighted_scaledCoshJump {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w d : α → ℝ} (hw : Measurable w) (hd : Measurable d)
    (hb : ∀ x, |d x| ≤ 2) (hi : Integrable (fun x => w x * d x ^ 2) μ)
    {a : ℝ} (ha : 0 ≤ a) : Integrable (fun x => w x * scaledCoshJump a (d x)) μ := by
  apply (hi.norm.div_const 8).mono' (by unfold scaledCoshJump; fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledCoshJump_nonneg _ _)]
  calc
    _ ≤ |w x| * (d x ^ 2 / 8) :=
      mul_le_mul_of_nonneg_left (scaledCoshJump_le_sq ha (hb x)) (abs_nonneg _)
    _ = ‖w x * d x ^ 2‖ / 8 := by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]; ring

/-- Exact concentration on extremal links, without assuming a finite unsigned link measure. -/
theorem tendsto_integral_scaledCoshJump {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w d : α → ℝ} (hw : Measurable w) (hd : Measurable d)
    (hb : ∀ x, |d x| ≤ 2) (hi : Integrable (fun x => w x * d x ^ 2) μ) :
    Tendsto (fun a => Real.exp (-2 * a) *
      ∫ x, w x * (Real.cosh (a * d x) - 1) ∂μ) atTop
      (𝓝 (∫ x, if |d x| = 2 then w x / 2 else 0 ∂μ)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := atTop (α := ℝ)) (F := fun a x => w x * scaledCoshJump a (d x))
    (f := fun x => if |d x| = 2 then w x / 2 else 0)
    (fun x => ‖w x * d x ^ 2‖ / 8)
    (Eventually.of_forall fun a => by unfold scaledCoshJump; fun_prop) ?_
    (hi.norm.div_const 8) ?_
  · convert h using 1
    ext a
    rw [← integral_const_mul]
    congr 1
    ext x
    unfold scaledCoshJump
    ring
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledCoshJump_nonneg _ _)]
    calc
      _ ≤ |w x| * (d x ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left (scaledCoshJump_le_sq ha (hb x)) (abs_nonneg _)
      _ = ‖w x * d x ^ 2‖ / 8 := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]; ring
  · filter_upwards with x
    convert (tendsto_scaledCoshJump (hb x)).const_mul (w x) using 1
    split_ifs <;> ring

/-- The extremal density is integrable under exactly the same quadratic control. -/
theorem integrable_extremalJumpDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w d : α → ℝ} (hw : Measurable w) (hd : Measurable d)
    (hi : Integrable (fun x => w x * d x ^ 2) μ) :
    Integrable (fun x => if |d x| = 2 then w x / 2 else 0) μ := by
  apply (hi.norm.div_const 8).mono'
    (((hw.div_const 2).ite (measurableSet_eq_fun hd.abs measurable_const)
      measurable_const).aestronglyMeasurable)
  filter_upwards with x
  split_ifs with h
  · have hs : d x ^ 2 = 4 := by nlinarith [sq_abs (d x)]
    have he : ‖w x / 2‖ = ‖w x * d x ^ 2‖ / 8 := by
      rw [hs]
      norm_num [norm_div, norm_mul]; ring
    exact he.le
  · simp only [norm_zero]
    positivity

/-- The unnormalized action is absolutely admitted for every real amplitude. -/
theorem integrable_weighted_coshJump {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w d : α → ℝ} (hw : Measurable w) (hd : Measurable d)
    (hb : ∀ x, |d x| ≤ 2) (hi : Integrable (fun x => w x * d x ^ 2) μ) (a : ℝ) :
    Integrable (fun x => w x * (Real.cosh (a * d x) - 1)) μ := by
  apply ((integrable_weighted_scaledCoshJump hw hd hb hi (abs_nonneg a)).const_mul
    (Real.exp (2 * |a|))).congr
  filter_upwards with x
  have hc : Real.cosh (|a| * d x) = Real.cosh (a * d x) := by
    rw [← Real.cosh_abs (x := |a| * d x), ← Real.cosh_abs (x := a * d x),
      abs_mul, abs_mul, abs_abs]
  have he : Real.exp (2 * |a|) * Real.exp (-2 * |a|) = 1 := by
    rw [← Real.exp_add, show 2 * |a| + -2 * |a| = 0 by ring, Real.exp_zero]
  unfold scaledCoshJump
  rw [hc]
  calc
    _ = (Real.exp (2 * |a|) * Real.exp (-2 * |a|)) *
        (w x * (Real.cosh (a * d x) - 1)) := by ring
    _ = _ := by rw [he, one_mul]

def thetaRealJump (chi : 𝓢(ℝ, ℝ)) (u x : ℝ) : ℝ := chi (x + u) - chi x

def thetaContinuousWeight (p : ℝ × ℝ) : ℝ :=
  thetaGammaPolarScalingKernel p.1 * thetaCuspFullSource p.2 *
    thetaCuspFullSource (p.2 + p.1)

def thetaNonlinearAction (chi : 𝓢(ℝ, ℝ)) (a : ℝ) : ℝ :=
  (∫ p, (thetaPrimeLinkDensity thetaCuspTiltSource thetaCuspTiltSource p).re *
    (Real.cosh (a * thetaRealJump chi (Real.log p.1) p.2) - 1) ∂thetaPrimeLinkMeasure) -
  ∫ p, thetaContinuousWeight p *
    (Real.cosh (a * thetaRealJump chi p.1 p.2) - 1) ∂thetaContinuousLinkMeasure

def thetaPrimeExtremalMass (chi : 𝓢(ℝ, ℝ)) : ℝ :=
  ∫ p, if |thetaRealJump chi (Real.log p.1) p.2| = 2 then
    (thetaPrimeLinkDensity thetaCuspTiltSource thetaCuspTiltSource p).re / 2 else 0
      ∂thetaPrimeLinkMeasure

def thetaContinuousExtremalDensity (chi : 𝓢(ℝ, ℝ)) (p : ℝ × ℝ) : ℝ :=
  if |thetaRealJump chi p.1 p.2| = 2 then thetaContinuousWeight p / 2 else 0

def thetaContinuousExtremalMass (chi : 𝓢(ℝ, ℝ)) : ℝ :=
  ∫ p, thetaContinuousExtremalDensity chi p ∂thetaContinuousLinkMeasure

theorem measurable_thetaContinuousWeight : Measurable thetaContinuousWeight := by
  have hk := contDiff_thetaCuspFullSource.continuous.measurable
  unfold thetaContinuousWeight thetaGammaPolarScalingKernel
  fun_prop

theorem measurable_thetaRealJump_continuous (chi : 𝓢(ℝ, ℝ)) :
    Measurable (fun p : ℝ × ℝ => thetaRealJump chi p.1 p.2) := by
  have hc := chi.continuous.measurable
  unfold thetaRealJump
  fun_prop

theorem measurable_thetaRealJump_prime (chi : 𝓢(ℝ, ℝ)) :
    Measurable (fun p : ℕ × ℝ => thetaRealJump chi (Real.log p.1) p.2) := by
  have hc := chi.continuous.measurable
  have hl : Measurable (fun n : ℕ => Real.log n) := (continuous_of_discreteTopology).measurable
  unfold thetaRealJump
  exact (hc.comp (measurable_snd.add (hl.comp measurable_fst))).sub (hc.comp measurable_snd)

theorem thetaRealJump_abs_le_two {chi : 𝓢(ℝ, ℝ)} (hb : ∀ x, |chi x| ≤ 1)
    (u x : ℝ) : |thetaRealJump chi u x| ≤ 2 := by
  exact (abs_sub (chi (x + u)) (chi x)).trans (by linarith [hb (x + u), hb x])

theorem integrable_thetaContinuousWeight_jump_sq (chi : 𝓢(ℝ, ℝ)) :
    Integrable (fun p => thetaContinuousWeight p * thetaRealJump chi p.1 p.2 ^ 2)
      thetaContinuousLinkMeasure := by
  apply (integrable_thetaGammaPolarScalingDensity thetaCuspTiltSource
    (thetaComplexify chi)).congr
  filter_upwards with p
  simp only [thetaGammaPolarScalingDensity, thetaComplexify_apply, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, thetaContinuousWeight, thetaRealJump]
  rfl

theorem integrable_thetaPrimeWeight_jump_sq (chi : 𝓢(ℝ, ℝ)) :
    Integrable (fun p : ℕ × ℝ => (thetaPrimeLinkDensity thetaCuspTiltSource thetaCuspTiltSource p).re *
      thetaRealJump chi (Real.log p.1) p.2 ^ 2) thetaPrimeLinkMeasure := by
  apply (integrable_thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
    (thetaComplexify chi).toBoundedContinuousFunction).congr
  filter_upwards with p
  simp only [thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement,
    SchwartzMap.toBoundedContinuousFunction_apply, thetaComplexify_apply, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, thetaRealJump, mul_comm]

theorem integrable_thetaContinuousExtremalDensity (chi : 𝓢(ℝ, ℝ)) :
    Integrable (thetaContinuousExtremalDensity chi) thetaContinuousLinkMeasure :=
  integrable_extremalJumpDensity measurable_thetaContinuousWeight
    (measurable_thetaRealJump_continuous chi) (integrable_thetaContinuousWeight_jump_sq chi)

theorem integrable_thetaNonlinearAction_terms (chi : 𝓢(ℝ, ℝ))
    (hb : ∀ x, |chi x| ≤ 1) (a : ℝ) :
    Integrable (fun p : ℕ × ℝ => (thetaPrimeLinkDensity thetaCuspTiltSource thetaCuspTiltSource p).re *
      (Real.cosh (a * thetaRealJump chi (Real.log p.1) p.2) - 1)) thetaPrimeLinkMeasure ∧
    Integrable (fun p => thetaContinuousWeight p *
      (Real.cosh (a * thetaRealJump chi p.1 p.2) - 1)) thetaContinuousLinkMeasure := by
  constructor
  · exact integrable_weighted_coshJump
      (Complex.continuous_re.comp (continuous_thetaPrimeLinkDensity thetaCuspTiltSource
        thetaCuspTiltSource)).measurable (measurable_thetaRealJump_prime chi)
      (fun p => thetaRealJump_abs_le_two hb (Real.log p.1) p.2)
      (integrable_thetaPrimeWeight_jump_sq chi) a
  · exact integrable_weighted_coshJump measurable_thetaContinuousWeight
      (measurable_thetaRealJump_continuous chi) (fun p => thetaRealJump_abs_le_two hb p.1 p.2)
      (integrable_thetaContinuousWeight_jump_sq chi) a

/-- Complete arithmetic concentration law: no prime power or continuous shift is discarded. -/
theorem tendsto_thetaNonlinearAction_scaled (chi : 𝓢(ℝ, ℝ)) (hb : ∀ x, |chi x| ≤ 1) :
    Tendsto (fun a => Real.exp (-2 * a) * thetaNonlinearAction chi a) atTop
      (𝓝 (thetaPrimeExtremalMass chi - thetaContinuousExtremalMass chi)) := by
  have hp := tendsto_integral_scaledCoshJump
    (Complex.continuous_re.comp (continuous_thetaPrimeLinkDensity thetaCuspTiltSource
      thetaCuspTiltSource)).measurable (measurable_thetaRealJump_prime chi)
    (fun p => thetaRealJump_abs_le_two hb (Real.log p.1) p.2)
    (integrable_thetaPrimeWeight_jump_sq chi)
  have hc := tendsto_integral_scaledCoshJump measurable_thetaContinuousWeight
    (measurable_thetaRealJump_continuous chi) (fun p => thetaRealJump_abs_le_two hb p.1 p.2)
    (integrable_thetaContinuousWeight_jump_sq chi)
  simpa only [thetaNonlinearAction, mul_sub, thetaPrimeExtremalMass,
    thetaContinuousExtremalMass, thetaContinuousExtremalDensity, Function.comp_def] using hp.sub hc

end RHTower.ThetaSourceWard
