import GaloisForLFunctions.RHTower.SteinhausFiniteAffineCovariance
import Mathlib.Analysis.InnerProductSpace.Basic


open MeasureTheory Complex
open scoped ENNReal ComplexConjugate

noncomputable section
namespace RHTower
open SteinhausModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The actual centered sum of channel columns under the finite biased phase law. -/
def steinhausFiniteCenteredSum {n : ℕ} (m : Fin n → ℂ) (a : Fin n → E) (x : Fin n → ℝ) : E :=
  ∑ i, steinhausFiniteCenteredPhase m i x • a i

theorem continuous_steinhausFiniteCenteredSum {n : ℕ} (m : Fin n → ℂ) (a : Fin n → E) :
    Continuous (steinhausFiniteCenteredSum m a) :=
  continuous_finsetSum _ (fun i _ =>
    (continuous_steinhausFiniteCenteredPhase m i).smul continuous_const)

/-- Integrability of the literal squared norm follows from a uniform finite-sum bound. -/
theorem integrable_norm_sq_steinhausFiniteCenteredSum {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (a : Fin n → E) :
    Integrable (fun x => ‖steinhausFiniteCenteredSum m a x‖ ^ 2)
      (steinhausFiniteAffineMeasure m) := by
  letI := isProbabilityMeasure_steinhausFiniteAffineMeasure hm
  have hb (x : Fin n → ℝ) : ‖steinhausFiniteCenteredSum m a x‖ ≤ 2 * ∑ i, ‖a i‖ := by
    calc
      _ ≤ ∑ i, ‖steinhausFiniteCenteredPhase m i x • a i‖ := norm_sum_le _ _
      _ ≤ ∑ i, 2 * ‖a i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_steinhausFiniteCenteredPhase_le hm i x)
          (norm_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  apply (integrable_const ((2 * ∑ i, ‖a i‖) ^ 2)).mono'
    ((continuous_steinhausFiniteCenteredSum m a).norm.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2

/-- Independent centered circle phases give the exact finite-vector variance. -/
theorem integral_norm_sq_steinhausFiniteCenteredSum {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (a : Fin n → E) :
    (∫ x, ‖steinhausFiniteCenteredSum m a x‖ ^ 2 ∂steinhausFiniteAffineMeasure m) =
      ∑ i, (1 - ‖m i‖ ^ 2) * ‖a i‖ ^ 2 := by
  have hp (i j : Fin n) : Integrable (fun x =>
      (conj (steinhausFiniteCenteredPhase m i x) * steinhausFiniteCenteredPhase m j x) *
        inner ℂ (a i) (a j)) (steinhausFiniteAffineMeasure m) :=
    (integrable_steinhausFiniteCenteredPhase_product hm i j).mul_const _
  have hexpand (x : Fin n → ℝ) : ((‖steinhausFiniteCenteredSum m a x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j,
        (conj (steinhausFiniteCenteredPhase m i x) * steinhausFiniteCenteredPhase m j x) *
          inner ℂ (a i) (a j) := by
    have hself : ((‖steinhausFiniteCenteredSum m a x‖ ^ 2 : ℝ) : ℂ) =
        inner ℂ (steinhausFiniteCenteredSum m a x) (steinhausFiniteCenteredSum m a x) := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      exact inner_self_ofReal_re _
    rw [hself]
    simp only [steinhausFiniteCenteredSum]
    rw [sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrow (i : Fin n) :
      (∫ x, ∑ j,
        (conj (steinhausFiniteCenteredPhase m i x) * steinhausFiniteCenteredPhase m j x) *
          inner ℂ (a i) (a j) ∂steinhausFiniteAffineMeasure m) =
        (((1 - ‖m i‖ ^ 2) * ‖a i‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_finsetSum _ (fun j _ => hp i j)]
    simp_rw [integral_mul_const, integral_steinhausFiniteCenteredPhase_product hm]
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j))]
  simp_rw [hrow]
  exact (Complex.ofReal_sum _ _).symm

/-- Prescribing the means never increases variance above the original column energy. -/
theorem integral_norm_sq_steinhausFiniteCenteredSum_le {n : ℕ} {m : Fin n → ℂ}
    (hm : ∀ i, ‖m i‖ ≤ 1 / 2) (a : Fin n → E) :
    (∫ x, ‖steinhausFiniteCenteredSum m a x‖ ^ 2 ∂steinhausFiniteAffineMeasure m) ≤
      ∑ i, ‖a i‖ ^ 2 := by
  rw [integral_norm_sq_steinhausFiniteCenteredSum hm]
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (sub_le_self 1 (sq_nonneg _)) (sq_nonneg _)).trans_eq
    (one_mul _)

end RHTower
