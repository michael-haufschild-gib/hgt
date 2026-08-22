import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# The operator logarithm along real powers

Three facts about `CFC.log` that the Lie–Trotter limit of the Wasserstein barycentre needs and
that mathlib does not state: `log (a^y) = y·log a`, `log (a⁻¹) = -log a`, and the first-order
expansion `p⁻¹(a^p − 1) → log a` as `p ↓ 0` in the *operator* form (mathlib states it for the
functional calculus of the corresponding scalar function).

Also recorded here is the elementary comparison `0 ≤ P ≤ Q ⟹ ‖P‖ ≤ ‖Q‖`, which converts a
two-sided Loewner sandwich into a norm estimate.
-/

open scoped NNReal Ring Topology
open Filter

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator norm is monotone on the positive cone. -/
theorem norm_le_norm_of_le {P Q : A} (hP : 0 ≤ P) (hPQ : P ≤ Q) : ‖P‖ ≤ ‖Q‖ := by
  have hQsa : IsSelfAdjoint Q := (hP.trans hPQ).isSelfAdjoint
  have hQ : Q ≤ ‖Q‖ • (1 : A) := by
    have h := hQsa.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  exact norm_le_of_le_smul_one hP (norm_nonneg Q) (hPQ.trans hQ)

/-- **The logarithm of a real power.** -/
theorem log_rpow_eq_smul {a : A} (ha : IsStrictlyPositive a) (y : ℝ) :
    CFC.log (a ^ y) = y • CFC.log a := by
  have hspec : ∀ x ∈ spectrum ℝ a, 0 < x := fun x hx =>
    IsStrictlyPositive.spectrum_pos (𝕜 := ℝ) ha hx
  have hc1 : ContinuousOn (fun x : ℝ => x ^ y) (spectrum ℝ a) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x hx
    exact Or.inl (ne_of_gt (hspec x hx))
  have hc2 : ContinuousOn Real.log ((fun x : ℝ => x ^ y) '' spectrum ℝ a) := by
    refine Real.continuousOn_log.mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ne_of_gt (Real.rpow_pos_of_pos (hspec x hx) y)
  have hclog : ContinuousOn Real.log (spectrum ℝ a) := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    exact ne_of_gt (hspec x hx)
  rw [rpow_eq_cfc_real ha.nonneg, CFC.log, CFC.log,
    ← cfc_comp' Real.log (fun x : ℝ => x ^ y) a hc2 hc1,
    ← cfc_smul (f := Real.log) (a := a) (hf := hclog)]
  refine cfc_congr fun x hx => ?_
  simp [Real.log_rpow (hspec x hx)]

/-- **The logarithm of the inverse.** -/
theorem log_ringInverse {a : A} (ha : IsStrictlyPositive a) :
    CFC.log (a⁻¹ʳ : A) = - CFC.log a := by
  have h1 : (a⁻¹ʳ : A) = a ^ (-1 : ℝ) := CFC.inverse_eq_rpow_neg_one ha
  rw [h1, log_rpow_eq_smul ha]
  simp

/-- **First-order expansion of the logarithm.**  `p⁻¹(a^p − 1) → log a` as `p ↓ 0`. -/
theorem tendsto_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a) :
    Tendsto (fun p : ℝ => p⁻¹ • (a ^ p - (1 : A))) (𝓝[>] 0) (𝓝 (CFC.log a)) := by
  refine (CFC.tendsto_cfc_rpow_sub_one_log ha).congr fun p => ?_
  simp only [← smul_eq_mul]
  rw [cfc_smul _ (hf := by fun_prop (disch := grind)),
    cfc_sub _ _ (hf := by fun_prop (disch := grind)),
    cfc_const_one .., rpow_eq_cfc_real ..]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
