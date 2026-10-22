import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerCyclicCap
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity
import GaloisForLFunctions.HTGeometry.SchwartzComplete

/-!
# The actual Poisson boundary is a closed cyclic Euler module

The inverse Poisson estimates and Frechet open mapping give forward continuity.
Consequently the cyclic Xi cap generates every actual Poisson boundary in the
natural strong source topology.
-/

open Complex Polynomial Set Topology TopologicalSpace
open scoped SchwartzMap
open GaloisForLFunctions

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

theorem deningerPoissonMeyerLM_continuous : Continuous deningerPoissonMeyerLM := by
  haveI : IsUniformAddGroup DeningerMeyerCap :=
    inferInstanceAs (IsUniformAddGroup DeningerMeyerCap.toAddSubgroup)
  haveI : IsCompletelyPseudoMetrizableSpace DeningerMeyerCap :=
    deningerMeyerCap_isClosed.isCompletelyPseudoMetrizableSpace
  haveI : IsUniformAddGroup (LinearMap.range deningerPoissonMeyerLM) :=
    inferInstanceAs (IsUniformAddGroup (LinearMap.range deningerPoissonMeyerLM).toAddSubgroup)
  haveI : IsCompletelyPseudoMetrizableSpace (LinearMap.range deningerPoissonMeyerLM) :=
    deningerPoissonMeyer_range_isClosed.isCompletelyPseudoMetrizableSpace
  haveI : CompleteSpace (LinearMap.range deningerPoissonMeyerLM) :=
    deningerPoissonMeyer_range_isClosed.completeSpace_coe
  have hc := GaloisForLFunctions.continuous_symm_of_continuous
    deningerPoissonMeyerRangeEquiv.symm deningerPoissonMeyerRangeEquiv_symm_continuous
  exact continuous_subtype_val.comp hc

theorem deningerMeyerStrongLogSumLM_continuous :
    Continuous deningerMeyerStrongLogSumLM := by
  have he : (deningerMeyerStrongLogSumLM : DeningerMeyerCap → _) =
      fun f => deningerMeyerStrongLogSourceEquiv.symm (deningerPoissonMeyerLM f) := by
    funext f
    apply deningerMeyerStrongLogSourceEquiv.injective
    exact (deningerMeyerStrongLogSourceEquiv_boundary f).trans
      (deningerMeyerStrongLogSourceEquiv.apply_symm_apply _).symm
  rw [he]
  exact deningerMeyerStrongLogSourceContinuousEquiv.symm.continuous.comp
    deningerPoissonMeyerLM_continuous

/-- The one-generator polynomial boundary module, in the literal source. -/
def deningerMeyerXiBoundaryPolynomial : ℂ[X] →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogSumLM.comp deningerMeyerXiCapPolynomial

theorem deningerMeyerXiBoundaryPolynomial_X_mul (p : ℂ[X]) :
    deningerMeyerXiBoundaryPolynomial (X * p) =
      deningerMeyerStrongLogGenerator (deningerMeyerXiBoundaryPolynomial p) := by
  change deningerMeyerStrongLogSumLM (deningerMeyerXiCapPolynomial (X * p)) = _
  rw [deningerMeyerXiCapPolynomial_X_mul, ← deningerMeyerStrongLogGenerator_boundary]
  rfl

theorem deningerMeyerXiBoundaryPolynomial_mellin (p : ℂ[X]) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerXiBoundaryPolynomial p) s = p.eval s * xi s := by
  induction p using Polynomial.induction_on with
  | C a =>
    have he : deningerMeyerXiBoundaryPolynomial (C a) =
        a • deningerMeyerStrongLogSumLM deningerMeyerXiCapSource := by
      simp [deningerMeyerXiBoundaryPolynomial, deningerMeyerXiCapPolynomial]
    rw [he]
    change deningerMeyerStrongLogMellinLM s (a • _) = _
    rw [map_smul]
    change a * deningerMeyerBoundaryMellin deningerMeyerXiCapSource s = _
    rw [deningerMeyerXiCapSource_mellin, Polynomial.eval_C]
  | add p q hp hq =>
    rw [map_add]
    change deningerMeyerStrongLogMellinLM s (_ + _) = _
    rw [map_add]
    change deningerMeyerStrongLogMellin (deningerMeyerXiBoundaryPolynomial p) s +
      deningerMeyerStrongLogMellin (deningerMeyerXiBoundaryPolynomial q) s = _
    rw [hp, hq, Polynomial.eval_add, add_mul]
  | monomial n a ih =>
    rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring,
      deningerMeyerXiBoundaryPolynomial_X_mul, deningerMeyerStrongLogGenerator_mellin, ih]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]

/-- No extra boundary directions are needed beyond the closed Euler orbit of Xi. -/
theorem deningerMeyerXiBoundaryPolynomial_closure :
    (LinearMap.range deningerMeyerXiBoundaryPolynomial).topologicalClosure =
      LinearMap.range deningerMeyerStrongLogSumLM := by
  let H := LinearMap.range deningerMeyerXiBoundaryPolynomial
  apply le_antisymm
  · exact H.topologicalClosure_minimal
      (by rintro g ⟨p, rfl⟩; exact ⟨deningerMeyerXiCapPolynomial p, rfl⟩)
      deningerMeyerStrongLogSum_range_isClosed
  · rintro g ⟨f, rfl⟩
    have h : closure (Set.range deningerMeyerXiCapPolynomial) ⊆
        deningerMeyerStrongLogSumLM ⁻¹' (H.topologicalClosure : Set _) := by
      apply closure_minimal
      · rintro g ⟨p, rfl⟩
        exact H.le_topologicalClosure ⟨p, rfl⟩
      · exact H.isClosed_topologicalClosure.preimage deningerMeyerStrongLogSumLM_continuous
    exact h (deningerMeyerXiCapPolynomial_dense f)

end
end RHTower
