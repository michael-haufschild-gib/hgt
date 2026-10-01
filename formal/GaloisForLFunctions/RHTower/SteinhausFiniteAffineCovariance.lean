import GaloisForLFunctions.RHTower.SteinhausFiniteAffineDensity
import GaloisForLFunctions.RHTower.SteinhausAffineCircleVariance
import Mathlib.Probability.Independence.Integration


open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal ComplexConjugate

noncomputable section
namespace RHTower
open SteinhausModel

/-- Literal phase minus its prescribed mean on the finite biased product. -/
def steinhausFiniteCenteredPhase {n : ℕ} (m : Fin n → ℂ) (i : Fin n) (x : Fin n → ℝ) : ℂ :=
  charFactor 1 (x i) - m i

theorem continuous_steinhausFiniteCenteredPhase {n : ℕ} (m : Fin n → ℂ) (i : Fin n) :
    Continuous (steinhausFiniteCenteredPhase m i) :=
  ((continuous_charFactor 1).comp (continuous_apply i)).sub continuous_const

theorem norm_steinhausFiniteCenteredPhase_le {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (i : Fin n) (x : Fin n → ℝ) :
    ‖steinhausFiniteCenteredPhase m i x‖ ≤ 2 := by
  have h := norm_sub_le (charFactor 1 (x i)) (m i)
  rw [norm_charFactor] at h
  exact h.trans (by linarith [hm i])

theorem integral_steinhausFiniteCenteredPhase {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (i : Fin n) :
    (∫ x, steinhausFiniteCenteredPhase m i x ∂steinhausFiniteAffineMeasure m) = 0 := by
  letI (j : Fin n) : IsProbabilityMeasure (steinhausAffineCircleMeasure (m j)) :=
    isProbabilityMeasure_steinhausAffineCircleMeasure (hm j)
  unfold steinhausFiniteCenteredPhase steinhausFiniteAffineMeasure
  rw [integral_comp_eval (μ := fun j => steinhausAffineCircleMeasure (m j))
    (i := i) (f := fun x => charFactor 1 x - m i)
    (((continuous_charFactor 1).sub continuous_const).aestronglyMeasurable)]
  exact integral_centered_phase_affineCircle (hm i)

/-- All pair products are integrable; no formal integral of a nonintegrable expression is used. -/
theorem integrable_steinhausFiniteCenteredPhase_product {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (i j : Fin n) :
    Integrable (fun x => conj (steinhausFiniteCenteredPhase m i x) *
      steinhausFiniteCenteredPhase m j x) (steinhausFiniteAffineMeasure m) := by
  letI := isProbabilityMeasure_steinhausFiniteAffineMeasure hm
  apply (integrable_const (4 : ℝ)).mono'
    (((continuous_star.comp (continuous_steinhausFiniteCenteredPhase m i)).mul
      (continuous_steinhausFiniteCenteredPhase m j)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖conj (steinhausFiniteCenteredPhase m i x) * steinhausFiniteCenteredPhase m j x‖ ≤ 4
  rw [norm_mul, RCLike.norm_conj]
  exact (mul_le_mul (norm_steinhausFiniteCenteredPhase_le hm i x)
    (norm_steinhausFiniteCenteredPhase_le hm j x) (norm_nonneg _) (by norm_num)).trans
      (by norm_num)

/-- Exact diagonal covariance of the literal centered phases under the product law. -/
theorem integral_steinhausFiniteCenteredPhase_product {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (i j : Fin n) :
    (∫ x, conj (steinhausFiniteCenteredPhase m i x) * steinhausFiniteCenteredPhase m j x
      ∂steinhausFiniteAffineMeasure m) =
      if i = j then ((1 - ‖m i‖ ^ 2 : ℝ) : ℂ) else 0 := by
  letI (k : Fin n) : IsProbabilityMeasure (steinhausAffineCircleMeasure (m k)) :=
    isProbabilityMeasure_steinhausAffineCircleMeasure (hm k)
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp_rw [Complex.conj_mul', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal]
    congr 1
    unfold steinhausFiniteCenteredPhase steinhausFiniteAffineMeasure
    rw [integral_comp_eval (μ := fun k => steinhausAffineCircleMeasure (m k))
      (i := i) (f := fun x => ‖charFactor 1 x - m i‖ ^ 2)
      (((continuous_charFactor 1).sub continuous_const).norm.pow 2).aestronglyMeasurable]
    exact integral_norm_sq_centered_phase_affineCircle (hm i)
  · rw [if_neg hij]
    have hi : iIndepFun (steinhausFiniteCenteredPhase m) (steinhausFiniteAffineMeasure m) :=
      iIndepFun_pi (fun k => ((continuous_charFactor 1).sub continuous_const).measurable.aemeasurable)
    have hp : IndepFun (fun x => conj (steinhausFiniteCenteredPhase m i x))
        (steinhausFiniteCenteredPhase m j) (steinhausFiniteAffineMeasure m) :=
      (hi.indepFun hij).comp continuous_star.measurable measurable_id
    rw [hp.integral_fun_mul_eq_mul_integral
      (continuous_star.comp (continuous_steinhausFiniteCenteredPhase m i)).aestronglyMeasurable
      (continuous_steinhausFiniteCenteredPhase m j).aestronglyMeasurable,
      integral_conj, integral_steinhausFiniteCenteredPhase hm i]
    simp

end RHTower

