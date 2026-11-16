import GaloisForLFunctions.HTGeometry.SimplexEffectiveHarmonic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weighted simplex response

Inverse diagonal metric weights determine a probability law and a projection onto the
zero-sum tangent space. Weighted centering gives the unique constrained quadratic minimizer;
its objective gap is an exact sum of squares. The uniform case recovers the complement of
the existing simplex harmonic projection.
-/

open scoped BigOperators Matrix
namespace GaloisForLFunctions.HilbertMetric.Optimization
noncomputable section
variable {n : ℕ}

def simplexCompliance (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ := (Real.exp (c i))⁻¹

def simplexComplianceMass (c : Fin (n + 1) → ℝ) : ℝ := ∑ i, simplexCompliance c i

private theorem mass_pos (c : Fin (n + 1) → ℝ) : 0 < simplexComplianceMass c :=
  Finset.sum_pos (fun _ _ => inv_pos.mpr (Real.exp_pos _)) Finset.univ_nonempty

def simplexSampling (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  simplexCompliance c i / simplexComplianceMass c

theorem simplexSampling_pos (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 < simplexSampling c i := div_pos (inv_pos.mpr (Real.exp_pos _)) (mass_pos c)

theorem simplexSampling_sum (c : Fin (n + 1) → ℝ) : ∑ i, simplexSampling c i = 1 := by
  simp only [simplexSampling, ← Finset.sum_div]
  exact div_self (mass_pos c).ne'

def weightedSimplexProjection (c v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  v i - simplexSampling c i * ∑ j, v j

theorem weightedSimplexProjection_sum (c v : Fin (n + 1) → ℝ) :
    ∑ i, weightedSimplexProjection c v i = 0 := by
  simp only [weightedSimplexProjection, Finset.sum_sub_distrib, ← Finset.sum_mul,
    simplexSampling_sum, one_mul, sub_self]

theorem weightedSimplexProjection_fixed_iff (c v : Fin (n + 1) → ℝ) :
    weightedSimplexProjection c v = v ↔ ∑ i, v i = 0 := by
  constructor
  · intro h; rw [← h]; exact weightedSimplexProjection_sum c v
  · intro h; funext i; simp only [weightedSimplexProjection, h, mul_zero, sub_zero]

def simplexDualMean (c g : Fin (n + 1) → ℝ) : ℝ := ∑ i, simplexSampling c i * g i

def weightedSimplexResponse (c g : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  simplexCompliance c i * (g i - simplexDualMean c g)

theorem weightedSimplexResponse_stationary (c g : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Real.exp (c i) * weightedSimplexResponse c g i = g i - simplexDualMean c g := by
  rw [weightedSimplexResponse, simplexCompliance, ← mul_assoc,
    mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]

theorem weightedSimplexResponse_sum (c g : Fin (n + 1) → ℝ) :
    ∑ i, weightedSimplexResponse c g i = 0 := by
  have hm : simplexDualMean c g = (∑ i, simplexCompliance c i * g i) / simplexComplianceMass c := by
    simp only [simplexDualMean, simplexSampling, div_mul_eq_mul_div, Finset.sum_div]
  simp only [weightedSimplexResponse, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hm]
  change (∑ i, simplexCompliance c i * g i) - simplexComplianceMass c *
    ((∑ i, simplexCompliance c i * g i) / simplexComplianceMass c) = 0
  field_simp [(mass_pos c).ne']
  ring

theorem weightedSimplexResponse_kernel (c g : Fin (n + 1) → ℝ) :
    weightedSimplexResponse c g = 0 ↔ ∃ a : ℝ, ∀ i, g i = a := by
  constructor
  · intro h
    refine ⟨simplexDualMean c g, fun i => ?_⟩
    have hs := weightedSimplexResponse_stationary c g i
    rw [h] at hs
    simp only [Pi.zero_apply, mul_zero] at hs
    exact (sub_eq_zero.mp hs.symm)
  · rintro ⟨a, ha⟩
    have hm : simplexDualMean c g = a := by
      simp only [simplexDualMean, ha, ← Finset.sum_mul, simplexSampling_sum, one_mul]
    funext i
    simp only [weightedSimplexResponse, ha, hm, sub_self, mul_zero, Pi.zero_apply]

def simplexQuadraticObjective (c g v : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, (Real.exp (c i) * v i ^ 2 / 2 - g i * v i)

private theorem objective_gap (c g v : Fin (n + 1) → ℝ) (hv : ∑ i, v i = 0) :
    simplexQuadraticObjective c g v - simplexQuadraticObjective c g (weightedSimplexResponse c g) =
      ∑ i, Real.exp (c i) * (v i - weightedSimplexResponse c g i) ^ 2 / 2 := by
  have hp (i : Fin (n + 1)) :
      (Real.exp (c i) * v i ^ 2 / 2 - g i * v i) -
      (Real.exp (c i) * weightedSimplexResponse c g i ^ 2 / 2 -
        g i * weightedSimplexResponse c g i) =
      Real.exp (c i) * (v i - weightedSimplexResponse c g i) ^ 2 / 2 -
        simplexDualMean c g * (v i - weightedSimplexResponse c g i) := by
    have hs := weightedSimplexResponse_stationary c g i
    linear_combination (v i - weightedSimplexResponse c g i) * hs
  simp only [simplexQuadraticObjective, ← Finset.sum_sub_distrib, hp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hv, weightedSimplexResponse_sum, sub_self, mul_zero, sub_zero]

theorem weightedSimplexResponse_exact_regret (c g v : Fin (n + 1) → ℝ) :
    simplexQuadraticObjective c g (weightedSimplexProjection c v) -
      simplexQuadraticObjective c g (weightedSimplexResponse c g) =
      ∑ i, Real.exp (c i) *
        (weightedSimplexProjection c v i - weightedSimplexResponse c g i) ^ 2 / 2 :=
  objective_gap c g _ (weightedSimplexProjection_sum c v)

theorem weightedSimplexResponse_minimum (c g v : Fin (n + 1) → ℝ) :
    simplexQuadraticObjective c g (weightedSimplexResponse c g) ≤
      simplexQuadraticObjective c g (weightedSimplexProjection c v) := by
  apply sub_nonneg.mp
  rw [weightedSimplexResponse_exact_regret]
  exact Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (by norm_num)

theorem weightedSimplexResponse_uniform (g : Fin (n + 1) → ℝ) :
    weightedSimplexResponse (fun _ => 0) g =
      fun i => g i - (∑ j, g j) / (n + 1) := by
  funext i
  simp [weightedSimplexResponse, simplexCompliance, simplexDualMean,
    simplexSampling, simplexComplianceMass, div_eq_mul_inv, Finset.sum_mul, mul_comm]


theorem simplexSampling_inverse_metric (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Real.exp (c i) * simplexSampling c i = (simplexComplianceMass c)⁻¹ := by
  simp only [simplexSampling, simplexCompliance, div_eq_mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]

theorem weightedSimplexResponse_unique (c g v : Fin (n + 1) → ℝ) :
    simplexQuadraticObjective c g (weightedSimplexProjection c v) =
      simplexQuadraticObjective c g (weightedSimplexResponse c g) ↔
      weightedSimplexProjection c v = weightedSimplexResponse c g := by
  rw [← sub_eq_zero, weightedSimplexResponse_exact_regret,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      div_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (by norm_num))]
  simp only [Finset.mem_univ, forall_const, div_eq_zero_iff,
    show (2 : ℝ) ≠ 0 by norm_num, or_false, mul_eq_zero,
    Real.exp_ne_zero, false_or, sq_eq_zero_iff, sub_eq_zero]
  exact funext_iff.symm

theorem weightedSimplexResponse_uniform_hodge (g : Fin (n + 1) → ℝ) :
    (fun i => (weightedSimplexResponse (fun _ => 0) g i : ℂ)) =
      (1 - HTGeometry.simplexEffectiveHarmonicProjection) *ᵥ (fun i => (g i : ℂ)) := by
  rw [weightedSimplexResponse_uniform, Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct,
    HTGeometry.simplexEffectiveHarmonicProjection, Fintype.card_fin, ← Finset.mul_sum]
  push_cast
  ring

#print axioms simplexSampling_inverse_metric
#print axioms weightedSimplexResponse_exact_regret
#print axioms weightedSimplexResponse_unique
#print axioms weightedSimplexResponse_uniform_hodge

end
end GaloisForLFunctions.HilbertMetric.Optimization
