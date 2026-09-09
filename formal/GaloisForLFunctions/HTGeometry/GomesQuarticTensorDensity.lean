import GaloisForLFunctions.HTGeometry.DilatonEinastoMoments
import GaloisForLFunctions.HTGeometry.GomesGaussianChargeMeasure

/-!
# Quartic integer tensor densities and their exact finite sector

Experimental application of the integer tensor charges of arXiv:2509.25276v7 section 5.2
to the corpus's quartic dilaton and Einasto density. Positive effective charge recovers
the existing quartic ground-state density. Nonpositive charge dominates the constant
unit density on the real line and cannot be integrable.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The signed quartic log-weight, extending the corpus's positive exponential parameter. -/
def gomesQuarticLogWeight (a : ℝ) : ℝ[X] := C (-a) * X ^ 4

/-- The log-weight of an integer tensor charge. -/
def gomesQuarticTensorLogWeight (b : ℝ) (n : ℤ) : ℝ[X] :=
  gomesQuarticLogWeight ((n : ℝ) * b)

/-- Literal scalar density of an integer tensor charge on the real base. -/
def gomesQuarticTensorDensity (b : ℝ) (n : ℤ) : ℝ → ℝ :=
  dilatonWeight (gomesQuarticTensorLogWeight b n)

/-- The existing positive quartic family embeds exactly into the signed family. -/
theorem gomesQuarticLogWeight_exp (k : ℝ) :
    gomesQuarticLogWeight (Real.exp k) = quarticDilatonLogWeight k := rfl

/-- Evaluation of the complete signed quartic profile. -/
theorem gomesQuarticLogWeight_eval (a x : ℝ) :
    (gomesQuarticLogWeight a).eval x = -a * x ^ 4 := by
  simp [gomesQuarticLogWeight]

/-- The common connection term scales linearly with effective charge. -/
theorem gomesQuarticLogWeight_derivative_eval (a x : ℝ) :
    (gomesQuarticLogWeight a).derivative.eval x = -4 * a * x ^ 3 := by
  simp [gomesQuarticLogWeight]
  ring

/-- Its curvature term is quadratic in position. -/
theorem gomesQuarticLogWeight_second_derivative_eval (a x : ℝ) :
    (gomesQuarticLogWeight a).derivative.derivative.eval x = -12 * a * x ^ 2 := by
  simp [gomesQuarticLogWeight]
  ring

/-- Charge reversal is literal negation of the polynomial log-weight. -/
theorem gomesQuarticLogWeight_neg (a : ℝ) :
    gomesQuarticLogWeight (-a) = -gomesQuarticLogWeight a := by
  apply Polynomial.funext
  intro x
  rw [gomesQuarticLogWeight_eval, eval_neg, gomesQuarticLogWeight_eval]
  ring

/-- Explicit quartic density of every integer charge. -/
theorem gomesQuarticTensorDensity_formula (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesQuarticTensorDensity b n x = Real.exp (-((n : ℝ) * b) * x ^ 4) := by
  simp only [gomesQuarticTensorDensity, gomesQuarticTensorLogWeight, dilatonWeight,
    gomesQuarticLogWeight_eval]

/-- Tensor addition multiplies densities on the same base. -/
theorem gomesQuarticTensorDensity_add (b : ℝ) (m n : ℤ) (x : ℝ) :
    gomesQuarticTensorDensity b (m + n) x =
      gomesQuarticTensorDensity b m x * gomesQuarticTensorDensity b n x := by
  simp only [gomesQuarticTensorDensity_formula, ← Real.exp_add, Int.cast_add]
  congr 1
  ring

/-- The dual charge is the pointwise reciprocal density. -/
theorem gomesQuarticTensorDensity_neg (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesQuarticTensorDensity b (-n) x = (gomesQuarticTensorDensity b n x)⁻¹ := by
  simp only [gomesQuarticTensorDensity_formula, Int.cast_neg, ← Real.exp_neg]
  congr 1
  ring

/-- Every integer-charge density remains strictly positive. -/
theorem gomesQuarticTensorDensity_pos (b : ℝ) (n : ℤ) (x : ℝ) :
    0 < gomesQuarticTensorDensity b n x := by
  rw [gomesQuarticTensorDensity_formula]
  exact Real.exp_pos _

/-- Every signed density is continuous, regardless of its integrability. -/
theorem gomesQuarticTensorDensity_continuous (b : ℝ) (n : ℤ) :
    Continuous (gomesQuarticTensorDensity b n) := by
  have h : gomesQuarticTensorDensity b n =
      fun x => Real.exp (-((n : ℝ) * b) * x ^ 4) := funext (gomesQuarticTensorDensity_formula b n)
  rw [h]
  fun_prop

/-- Literal integral powers recover every tensor charge from its generating density. -/
theorem gomesQuarticTensorDensity_zpow (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesQuarticTensorDensity b n x = (gomesQuarticTensorDensity b 1 x) ^ n := by
  simp only [gomesQuarticTensorDensity_formula, Int.cast_one, one_mul]
  rw [show -((n : ℝ) * b) * x ^ 4 = (-b * x ^ 4) * (n : ℝ) by ring,
    Real.exp_mul, Real.rpow_intCast]

/-- Exact real-line integrability cutoff: only strictly positive effective charge survives. -/
theorem gomesQuarticTensorDensity_integrable_iff (b : ℝ) (n : ℤ) :
    Integrable (gomesQuarticTensorDensity b n) ↔ 0 < (n : ℝ) * b := by
  constructor
  · intro h
    by_contra hp
    have hq : (n : ℝ) * b ≤ 0 := le_of_not_gt hp
    have hc : Integrable (fun _ : ℝ => (1 : ℝ)) := h.mono' aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun x => by
        simp only [norm_one, gomesQuarticTensorDensity_formula]
        exact Real.one_le_exp_iff.mpr (mul_nonneg (neg_nonneg.mpr hq) (by positivity)))
    have hf := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp hc
    have hi : ¬ IsFiniteMeasure (volume : Measure ℝ) := by
      rw [not_isFiniteMeasure_iff]
      exact Real.volume_univ
    exact hi hf
  · intro hp
    have h := quarticDilatonGroundState_absolute_moments_integrable 0 (Real.log ((n : ℝ) * b))
    simp only [pow_zero, one_mul] at h
    have he : (fun x => ‖quarticDilatonGroundState (Real.log ((n : ℝ) * b)) x‖ ^ 2) =
        gomesQuarticTensorDensity b n := by
      funext x
      rw [quarticDilatonGroundState_norm_sq, Real.exp_log hp, gomesQuarticTensorDensity_formula]
    rw [he] at h
    exact h

/-- A positive effective charge, suitable for exact transport of the existing quartic ground state. -/
abbrev GomesQuarticFiniteCharge (b : ℝ) := {n : ℤ // 0 < (n : ℝ) * b}

/-- Finite tensor charges recover the previously formalized ground-state density without alteration. -/
theorem gomesQuarticTensorDensity_ground_norm (b : ℝ) (n : GomesQuarticFiniteCharge b) (x : ℝ) :
    gomesQuarticTensorDensity b n.val x =
      ‖quarticDilatonGroundState (Real.log ((n.val : ℝ) * b)) x‖ ^ 2 := by
  rw [gomesQuarticTensorDensity_formula, quarticDilatonGroundState_norm_sq, Real.exp_log n.property]

/-- Every absolute moment transfers exactly from the existing Einasto/Gamma formula. -/
theorem gomesQuarticTensorDensity_absolute_moments (b : ℝ) (n : GomesQuarticFiniteCharge b) (j : ℕ) :
    (∫ x : ℝ, |x| ^ j * gomesQuarticTensorDensity b n.val x) =
      Real.exp (-Real.log ((n.val : ℝ) * b) / 4) ^ (j + 1) / 2 *
        Real.Gamma (((j : ℝ) + 1) / 4) := by
  simp only [gomesQuarticTensorDensity_ground_norm b n]
  exact quarticDilatonGroundState_absolute_moments j (Real.log ((n.val : ℝ) * b))

/-- All of those charged absolute moments are integrable. -/
theorem gomesQuarticTensorDensity_absolute_moments_integrable (b : ℝ)
    (n : GomesQuarticFiniteCharge b) (j : ℕ) :
    Integrable (fun x : ℝ => |x| ^ j * gomesQuarticTensorDensity b n.val x) := by
  simp only [gomesQuarticTensorDensity_ground_norm b n]
  exact quarticDilatonGroundState_absolute_moments_integrable j (Real.log ((n.val : ℝ) * b))

end GaloisForLFunctions.HTGeometry
