import GaloisForLFunctions.RHTower.DeningerMeyerObservableSourceSpectrum

/-!
# Actual reflection covariance of the causal Xi sources

Paugam reflection preserves the invisible sector and the whole finite causal
span. The latter statement is proved on the actual all-weight sources by Mellin
injectivity and the Xi functional equation, not by substituting proxy classes.
The actual generator obeys the affine reflection law `A J = J - J A`.
-/

open Complex Set
open scoped Classical

namespace RHTower
noncomputable section

theorem deningerMeyerStrongLogGenerator_J (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGenerator (deningerMeyerStrongLogJ g) =
      deningerMeyerStrongLogJ g -
        deningerMeyerStrongLogJ (deningerMeyerStrongLogGenerator g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  change deningerMeyerStrongLogMellin _ s =
    deningerMeyerStrongLogMellinLM s
      (deningerMeyerStrongLogJ g -
        deningerMeyerStrongLogJ (deningerMeyerStrongLogGenerator g))
  rw [map_sub]
  change deningerMeyerStrongLogMellin _ s =
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogJ g) s -
      deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogJ (deningerMeyerStrongLogGenerator g)) s
  rw [deningerMeyerStrongLogGenerator_mellin,
    deningerMeyerStrongLogMellin_J, deningerMeyerStrongLogMellin_J,
    deningerMeyerStrongLogGenerator_mellin]
  ring

/-- The original source reflection acts on the actual generator by `A ↦ 1-A`. -/
theorem deningerMeyerCohomologyGenerator_J (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyGenerator (deningerMeyerStrongLogCohomologyJ u) =
      deningerMeyerStrongLogCohomologyJ u -
        deningerMeyerStrongLogCohomologyJ (deningerMeyerCohomologyGenerator u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    simp only [deningerMeyerStrongLogCohomologyJ_mk, deningerMeyerCohomologyGenerator_mk,
      deningerMeyerStrongLogGenerator_J, Submodule.Quotient.mk_sub]

theorem deningerMeyerCohomologyJ_generator (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyJ (deningerMeyerCohomologyGenerator u) =
      deningerMeyerStrongLogCohomologyJ u -
        deningerMeyerCohomologyGenerator (deningerMeyerStrongLogCohomologyJ u) := by
  rw [deningerMeyerCohomologyGenerator_J]
  module

theorem deningerMeyerXiSupportJetEvaluationLM_J (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerStrongLogCohomologyJ u) =
      (-1 : ℂ) ^ j.val * deningerMeyerXiSupportJetEvaluationLM (xiZeroReflectEquiv rho)
        ⟨j.val, by rw [xiSupportMultiplicity_reflect]; exact j.isLt⟩ u := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    exact deningerMeyerStrongLogMellinJetLM_J g j.val (rho : ℂ)

theorem deningerMeyerInvisible_J_mem (u : DeningerMeyerInvisible) :
    deningerMeyerStrongLogCohomologyJ u ∈ DeningerMeyerInvisible := by
  apply (mem_deningerMeyerInvisible_iff _).mpr
  intro rho j
  rw [deningerMeyerXiSupportJetEvaluationLM_J,
    (mem_deningerMeyerInvisible_iff _).mp u.property, mul_zero]

/-- Reflection covariance holds before taking the Poisson quotient. -/
theorem deningerMeyerXiCausalSource_J (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) :
    deningerMeyerStrongLogJ (deningerMeyerXiCausalSource rho k hk) =
      (-1 : ℂ) ^ k • deningerMeyerXiCausalSource (xiZeroReflectEquiv rho) k
        (by rw [xiSupportMultiplicity_reflect]; exact hk) := by
  let hkr : k ≤ xiSupportMultiplicity (xiZeroReflectEquiv rho) := by
    rw [xiSupportMultiplicity_reflect]
    exact hk
  apply deningerMeyerStrongLogMellin_injective
  apply Continuous.ext_on (dense_compl_singleton (xiZeroReflectEquiv rho : ℂ))
    (differentiable_deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogJ (deningerMeyerXiCausalSource rho k hk)).property).continuous
    (differentiable_deningerMeyerStrongLogMellin
      ((-1 : ℂ) ^ k • deningerMeyerXiCausalSource (xiZeroReflectEquiv rho) k hkr).property).continuous
  intro s hs
  apply mul_left_cancel₀ (pow_ne_zero k (sub_ne_zero.mpr hs))
  rw [deningerMeyerStrongLogMellin_J]
  change (s - (xiZeroReflectEquiv rho : ℂ)) ^ k *
      deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) (1 - s) =
    (s - (xiZeroReflectEquiv rho : ℂ)) ^ k * deningerMeyerStrongLogMellinLM s
      ((-1 : ℂ) ^ k • deningerMeyerXiCausalSource (xiZeroReflectEquiv rho) k hkr)
  rw [map_smul]
  calc
    (s - (xiZeroReflectEquiv rho : ℂ)) ^ k *
        deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) (1 - s) =
      (-1 : ℂ) ^ k * ((1 - s - (rho : ℂ)) ^ k *
        deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) (1 - s)) := by
          rw [← mul_assoc, ← mul_pow]
          congr 2
          rw [xiZeroReflectEquiv_apply]
          ring
    _ = (-1 : ℂ) ^ k * xi (1 - s) := by
      rw [← deningerMeyerXiCausalSource_factor rho k hk]
    _ = (-1 : ℂ) ^ k * xi s := by rw [xi_one_sub]
    _ = (s - (xiZeroReflectEquiv rho : ℂ)) ^ k *
        ((-1 : ℂ) ^ k * deningerMeyerStrongLogMellin
          (deningerMeyerXiCausalSource (xiZeroReflectEquiv rho) k hkr) s) := by
      rw [deningerMeyerXiCausalSource_factor (xiZeroReflectEquiv rho) k hkr]
      ring

theorem deningerMeyerXiJetSource_J (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerStrongLogCohomologyJ (deningerMeyerXiJetSource rho j) =
      (-1 : ℂ) ^ (xiSupportMultiplicity rho - j.val) •
        deningerMeyerXiJetSource (xiZeroReflectEquiv rho)
          ⟨j.val, by rw [xiSupportMultiplicity_reflect]; exact j.isLt⟩ := by
  simp only [deningerMeyerXiJetSource, deningerMeyerXiCausalClass,
    deningerMeyerStrongLogCohomologyJ_mk, deningerMeyerXiCausalSource_J,
    Submodule.Quotient.mk_smul, xiSupportMultiplicity_reflect]

theorem deningerMeyerXiJetSource_mem_finite (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiJetSource rho j ∈ DeningerMeyerFiniteCausalModes := by
  refine ⟨{rho}, Pi.single ⟨⟨rho, Finset.mem_singleton_self rho⟩, j⟩ 1, ?_⟩
  simp

/-- The original finite Hedenmalm causal span is stable under actual Paugam reflection. -/
theorem deningerMeyerFiniteCausalModes_J_mem (u : DeningerMeyerFiniteCausalModes) :
    deningerMeyerStrongLogCohomologyJ u ∈ DeningerMeyerFiniteCausalModes := by
  obtain ⟨S, c, hc⟩ := u.property
  rw [← hc, deningerMeyerFiniteXiCausalSynthesis_apply, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [map_smul, deningerMeyerXiJetSource_J]
  exact DeningerMeyerFiniteCausalModes.smul_mem _
    (DeningerMeyerFiniteCausalModes.smul_mem _ (deningerMeyerXiJetSource_mem_finite _ _))

end
end RHTower
