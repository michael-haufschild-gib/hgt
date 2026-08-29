import GaloisForLFunctions.HTGeometry.SteinhausComplexSum
import GaloisForLFunctions.RHTower.RVCumulantAverage

/-!
# The Chernoff bound for the modulus of a Steinhaus sum

`P(|Y| ≥ q)·I₀(tq) ≤ ∏ I₀(t a_i)` for every `t, q ≥ 0`.

The rotational average of the exponential is exactly `I₀` of the modulus, so no covering of the
circle of directions is needed: Markov's inequality applied to the (monotone) function
`x ↦ I₀(t|Y(x)|)` gives the bound with the sharp constant.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

local instance phaseCirclePositiveChernoff : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The one-circle Laplace transform is monotone on the nonnegative ray. -/
theorem steinhausLaplace_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    steinhausLaplace x ≤ steinhausLaplace y := by
  have h := steinhausLogLaplace_mono hx hxy
  have hx0 : 0 < steinhausLaplace x := steinhausLaplace_pos x
  have hy0 : 0 < steinhausLaplace y := steinhausLaplace_pos y
  have hex : Real.exp (steinhausLogLaplace x) = steinhausLaplace x := by
    rw [steinhausLogLaplace, Real.exp_log hx0]
  have hey : Real.exp (steinhausLogLaplace y) = steinhausLaplace y := by
    rw [steinhausLogLaplace, Real.exp_log hy0]
  rw [← hex, ← hey]
  exact Real.exp_le_exp.2 h

theorem continuous_steinhausSum_norm {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous fun x : ι → PhaseCircle => ‖steinhausSum a x‖ := by
  refine continuous_norm.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul (continuous_steinhausPhase.comp (continuous_apply i))

theorem measurableSet_normGe {ι : Type*} [Fintype ι] (a : ι → ℝ) (q : ℝ) :
    MeasurableSet {x : ι → PhaseCircle | q ≤ ‖steinhausSum a x‖} :=
  measurableSet_le measurable_const (continuous_steinhausSum_norm a).measurable

/-- **The Chernoff bound.** -/
theorem meas_norm_ge_mul_le {ι : Type*} [Fintype ι] (a : ι → ℝ) {t q : ℝ} (ht : 0 ≤ t)
    (hq : 0 ≤ q) :
    ((Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x : ι → PhaseCircle | q ≤ ‖steinhausSum a x‖}).toReal * steinhausLaplace (t * q)
      ≤ ∏ i, steinhausLaplace (t * a i) := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  set S : Set (ι → PhaseCircle) := {x | q ≤ ‖steinhausSum a x‖} with hS
  have hSm : MeasurableSet S := measurableSet_normGe a q
  set f : (ι → PhaseCircle) → ℝ := fun x => steinhausLaplace (t * ‖steinhausSum a x‖) with hf
  have hfcont : Continuous f := by
    rw [hf]
    have hbase : Continuous fun x : ι → PhaseCircle =>
        Real.exp (steinhausLogLaplace (t * ‖steinhausSum a x‖)) :=
      Real.continuous_exp.comp (continuous_steinhausLogLaplace.comp
        (continuous_const.mul (continuous_steinhausSum_norm a)))
    refine hbase.congr fun x => ?_
    rw [steinhausLogLaplace, Real.exp_log (steinhausLaplace_pos _)]
  have hfnn : ∀ x, 0 ≤ f x := fun x => (steinhausLaplace_pos _).le
  have hbd : ∀ x, ‖f x‖ ≤ Real.exp (|t| * ∑ i, |a i|) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x), hf]
    have hnorm : ‖steinhausSum a x‖ ≤ ∑ i, |a i| := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_steinhausPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hmono : steinhausLaplace (t * ‖steinhausSum a x‖)
        ≤ steinhausLaplace (|t| * ∑ i, |a i|) := by
      refine steinhausLaplace_mono (by positivity) ?_
      have h1 : t * ‖steinhausSum a x‖ ≤ |t| * ‖steinhausSum a x‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg _)
      have h2 : |t| * ‖steinhausSum a x‖ ≤ |t| * ∑ i, |a i| :=
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg t)
      linarith
    calc steinhausLaplace (t * ‖steinhausSum a x‖)
        ≤ steinhausLaplace (|t| * ∑ i, |a i|) := hmono
      _ ≤ Real.exp |(|t| * ∑ i, |a i|)| := steinhausLaplace_le_exp_abs _
      _ = Real.exp (|t| * ∑ i, |a i|) := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |t| * ∑ i, |a i|)]
  have hint : Integrable f μ := by
    refine Integrable.mono' (integrable_const (Real.exp (|t| * ∑ i, |a i|)))
      hfcont.aestronglyMeasurable ?_
    filter_upwards with x
    exact hbd x
  have hlow : ∀ x ∈ S, steinhausLaplace (t * q) ≤ f x := by
    intro x hx
    rw [hf]
    refine steinhausLaplace_mono (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hx ht
  have hsetle : (μ S).toReal * steinhausLaplace (t * q) ≤ ∫ x in S, f x ∂μ := by
    have hconst : ∫ _x in S, steinhausLaplace (t * q) ∂μ
        = (μ S).toReal * steinhausLaplace (t * q) := by
      rw [setIntegral_const, measureReal_def, smul_eq_mul]
    rw [← hconst]
    exact setIntegral_mono_on ((integrable_const _).integrableOn) hint.integrableOn hSm hlow
  have hall : ∫ x in S, f x ∂μ ≤ ∫ x, f x ∂μ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => hfnn x)
  have hprod : ∫ x, f x ∂μ = ∏ i, steinhausLaplace (t * a i) := by
    rw [hf, hμ]
    exact integral_steinhausLaplace_norm a t
  linarith [hsetle, hall, hprod.le, hprod.ge]

end

end RHTower
