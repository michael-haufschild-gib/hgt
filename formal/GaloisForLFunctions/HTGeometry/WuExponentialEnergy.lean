import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Exponential energy integration

The one-direction estimate underlying Lemma 2.3 of Shengrong Wu,
*Picard Iteration for the Characteristic Initial Value Problem in Einstein Equations*,
arXiv:2609.08421. The rate is `exp d`, so every rate parameter gives a positive
weight without a positivity premise. The exact finite-interval factor is retained.
-/

namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section

/-- The squared exponential weight, normalized at the terminal point. -/
def weight (d t s : ℝ) : ℝ := Real.exp (2 * Real.exp d * (s - |t|))

/-- The exact mass of the squared exponential weight on a finite interval. -/
def mass (d t : ℝ) : ℝ :=
  (1 - Real.exp (-(2 * Real.exp d * |t|))) / (2 * Real.exp d)

theorem continuous_weight (d t : ℝ) : Continuous (weight d t) := by
  unfold weight
  fun_prop

theorem weight_pos (d t s : ℝ) : 0 < weight d t s := Real.exp_pos _

theorem integral_weight (d t : ℝ) :
    ∫ s in (0 : ℝ)..|t|, weight d t s = mass d t := by
  have hD : 2 * Real.exp d ≠ 0 := ne_of_gt (by positivity)
  have hd (s : ℝ) : HasDerivAt
      (fun x => weight d t x / (2 * Real.exp d)) (weight d t s) s := by
    simpa [weight, hD] using ((((hasDerivAt_id s).sub_const |t|).const_mul
      (2 * Real.exp d)).exp.div_const (2 * Real.exp d))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) ((continuous_weight d t).intervalIntegrable 0 |t|)
  simpa [weight, mass, sub_div, mul_neg] using hi

theorem mass_nonneg (d t : ℝ) : 0 ≤ mass d t := by
  rw [← integral_weight]
  exact intervalIntegral.integral_nonneg (abs_nonneg t) (fun s _ => (weight_pos d t s).le)

theorem mass_le (d t : ℝ) : mass d t ≤ 1 / (2 * Real.exp d) := by
  unfold mass
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(2 * Real.exp d * |t|))])
    (by positivity)

/-- A terminally normalized squared energy. -/
def energy {E : Type*} [SeminormedAddCommGroup E] (d t : ℝ) (f : ℝ → E) : ℝ :=
  ∫ s in (0 : ℝ)..|t|, weight d t s * ‖f s‖ ^ (2 : ℕ)

theorem energy_nonneg {E : Type*} [SeminormedAddCommGroup E]
    (d t : ℝ) (f : ℝ → E) : 0 ≤ energy d t f := by
  exact intervalIntegral.integral_nonneg (abs_nonneg t)
    (fun s _ => mul_nonneg (weight_pos d t s).le (sq_nonneg _))

/-- Exact saturation by constant data, including the zero-length interval. -/
theorem energy_const {E : Type*} [SeminormedAddCommGroup E]
    (d t : ℝ) (x : E) : energy d t (fun _ => x) = mass d t * ‖x‖ ^ (2 : ℕ) := by
  rw [energy, intervalIntegral.integral_mul_const, integral_weight]

/-- The finite-interval energy bound for arbitrary bounded continuous data. -/
theorem energy_le_mass {E : Type*} [SeminormedAddCommGroup E]
    (d t : ℝ) (f : BoundedContinuousFunction ℝ E) :
    energy d t f ≤ mass d t * ‖f‖ ^ (2 : ℕ) := by
  rw [← energy_const d t f]
  apply intervalIntegral.integral_mono_on (abs_nonneg t)
    (((continuous_weight d t).mul (f.continuous.norm.pow 2)).intervalIntegrable 0 |t|)
    (((continuous_weight d t).mul continuous_const).intervalIntegrable 0 |t|)
  intro s _
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (f.norm_coe_le_norm s))
    (weight_pos d t s).le

/-- Lemma 2.3's squared one-direction gain, with every analytic bound discharged. -/
theorem energy_le {E : Type*} [SeminormedAddCommGroup E]
    (d t : ℝ) (f : BoundedContinuousFunction ℝ E) :
    energy d t f ≤ ‖f‖ ^ (2 : ℕ) / (2 * Real.exp d) := by
  calc energy d t f ≤ mass d t * ‖f‖ ^ (2 : ℕ) := energy_le_mass d t f
    _ ≤ (1 / (2 * Real.exp d)) * ‖f‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (mass_le d t) (sq_nonneg _)
    _ = _ := by ring

/-- The square-root energy gain is independent of the interval length. -/
theorem sqrt_energy_le {E : Type*} [SeminormedAddCommGroup E]
    (d t : ℝ) (f : BoundedContinuousFunction ℝ E) :
    Real.sqrt (energy d t f) ≤ ‖f‖ / Real.sqrt (2 * Real.exp d) := by
  calc Real.sqrt (energy d t f) ≤ Real.sqrt (‖f‖ ^ (2 : ℕ) / (2 * Real.exp d)) :=
      Real.sqrt_le_sqrt (energy_le d t f)
    _ = _ := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end
end GaloisForLFunctions.HTGeometry.Wu
