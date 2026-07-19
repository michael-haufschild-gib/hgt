import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceEntropy
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Universal phase-coherence target measure

This file supplies the analytic core of the lower half of the universal
coherence-entropy law.  The first theorem is the sharp linear chord floor on
the standard fundamental interval.  Integrating its Gaussian majorant gives
an explicit inverse-square-root bound for the one-circle exponential moment.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- On the standard fundamental interval, the unit-circle chord from `1`
dominates four times the additive coordinate. -/
theorem four_mul_abs_le_norm_fourier_one_sub_one
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    4 * |x| ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ := by
  have hxabs : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have habs : |x| ≤ 1 / 2 := (abs_le).2 hx
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_abs_le_abs_sin hxabs
  have hsin : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    calc
      2 * |x| = 2 / Real.pi * |Real.pi * x| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * x)| := hjordan
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- The Laplace transform of the squared chord distance from `1` under
normalized Haar measure on the additive unit circle. -/
def circleChordExponentialMoment (lam : ℝ) : ℝ :=
  ∫ z : UnitAddCircle, Real.exp (-lam * ‖fourier 1 z - 1‖ ^ 2)

/-- **One-circle Gaussian domination.**  The chord Laplace transform is at
most the full-line Gaussian integral with coefficient `16 * lam`. -/
theorem circleChordExponentialMoment_le_gaussian
    {lam : ℝ} (hlam : 0 < lam) :
    circleChordExponentialMoment lam ≤
      Real.sqrt (Real.pi / (16 * lam)) := by
  let f : ℝ → ℝ := fun x ↦
    Real.exp (-lam * ‖fourier 1 (x : UnitAddCircle) - 1‖ ^ 2)
  let g : ℝ → ℝ := fun x ↦ Real.exp (-(16 * lam) * x ^ 2)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgint : Integrable g := by
    dsimp only [g]
    exact integrable_exp_neg_mul_sq (by positivity)
  have hfint : IntegrableOn f (Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    apply IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc hfcont.continuousOn)
    exact Ioc_subset_Icc_self
  have hgset : IntegrableOn g (Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    hgint.integrableOn
  have hfg : ∀ x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤ g x := by
    intro x hx
    have hchord := four_mul_abs_le_norm_fourier_one_sub_one
      (show x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) from
        Ioc_subset_Icc_self hx)
    have hsq : 16 * x ^ 2 ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ ^ 2 := by
      have hsquare := (sq_le_sq₀
        (mul_nonneg (by norm_num) (abs_nonneg x)) (norm_nonneg _)).2 hchord
      nlinarith [sq_abs x]
    dsimp only [f, g]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [circleChordExponentialMoment, ← UnitAddCircle.integral_preimage
    (-(1 / 2 : ℝ))]
  have hhalf : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hhalf]
  change (∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x) ≤ _
  have hset :
      ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤
        ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), g x := by
    exact integral_mono_ae hfint hgset
      (ae_restrict_iff' measurableSet_Ioc |>.2 <|
        ae_of_all _ fun x hx ↦ hfg x hx)
  calc
    ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤
        ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), g x := hset
    _ ≤ ∫ x : ℝ, g x := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _x ↦ (Real.exp_pos _).le) hgint
    _ = Real.sqrt (Real.pi / (16 * lam)) := by
      simpa only [g] using integral_gaussian (16 * lam)

end RHTower
