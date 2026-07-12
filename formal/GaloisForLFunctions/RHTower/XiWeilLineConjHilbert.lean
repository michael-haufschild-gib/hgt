import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.HilbertSchmidtMatrix

/-!
# Unconditional Hilbert realization of the Xi Weil form

Critical-line reflection permutes the multiplicity-exact Xi divisor.  Reindexing an `ell^2`
evaluation vector by this permutation realizes the Weil polarization as an ordinary Hilbert inner
product without assuming RH.  The reindexing preserves the norm, so the zero-side Weil form is a
bounded Hermitian form on its complete square-summable evaluation carrier.

This is the continuity bridge needed to pass positivity from an algebraic source-generated core to
its Hilbert closure.  It does not assert that the regular Cauchy core is dense in every divisor
evaluation vector; detecting the finite off-real sign vectors remains the top-down density problem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Critical-line reflection acting on the multiplicity-exact Xi `ell^2` carrier. -/
def xiWeilLineConjLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨fun q => v (xiZeroCopyLineConjEquiv q),
    HilbertSchmidt.memℓp_of_sq
      (xiZeroCopyLineConjEquiv.summable_iff.mpr
        (HilbertSchmidt.summable_coe_sq v))⟩

@[simp] theorem xiWeilLineConjLp_apply
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiWeilLineConjLp v q = v (xiZeroCopyLineConjEquiv q) := rfl

/-- Critical-line reflection preserves the `ell^2` norm unconditionally. -/
theorem norm_xiWeilLineConjLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    ‖xiWeilLineConjLp v‖ = ‖v‖ := by
  have hsq : ‖xiWeilLineConjLp v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    exact xiZeroCopyLineConjEquiv.tsum_eq (fun q => ‖v q‖ ^ 2)
  nlinarith [norm_nonneg (xiWeilLineConjLp v), norm_nonneg v]

/-- Critical-line reflection as a linear isometry of the Xi `ell^2` carrier. -/
def xiWeilLineConjLinearIsometry :
    lp (fun _ : XiZeroCopy => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 where
  toFun := xiWeilLineConjLp
  map_add' v w := by
    apply Subtype.ext
    funext q
    rfl
  map_smul' c v := by
    apply Subtype.ext
    funext q
    rfl
  norm_map' := norm_xiWeilLineConjLp

@[simp] theorem xiWeilLineConjLinearIsometry_apply
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilLineConjLinearIsometry v = xiWeilLineConjLp v := rfl

/-- The real quadratic form carried by critical-line reflection on the Xi `ell^2` space. -/
def xiWeilHilbertQuadratic (v : lp (fun _ : XiZeroCopy => ℂ) 2) : ℝ :=
  (inner ℂ (xiWeilLineConjLinearIsometry v) v).re

/-- The unconditional Xi Hilbert quadratic form is continuous. -/
theorem continuous_xiWeilHilbertQuadratic : Continuous xiWeilHilbertQuadratic := by
  unfold xiWeilHilbertQuadratic
  fun_prop

/-- Positivity on the algebraic regular-Cauchy core automatically extends to its Hilbert closure. -/
theorem xiWeilHilbertQuadratic_nonneg_on_cauchyHilbertSubspace
    (hpos : ∀ v ∈ xiWeilCauchyAlgebraicSubspace, 0 ≤ xiWeilHilbertQuadratic v) :
    ∀ v ∈ xiWeilCauchyHilbertSubspace, 0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  have hclosed : IsClosed {w | 0 ≤ xiWeilHilbertQuadratic w} :=
    isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
  have hv' : v ∈ closure (↑xiWeilCauchyAlgebraicSubspace : Set _) := by
    change v ∈ closure (↑xiWeilCauchyAlgebraicSubspace : Set _) at hv
    exact hv
  exact (closure_minimal hpos hclosed) hv'

/-- The Xi Weil polarization is the Hilbert product after critical-line-reflection reindexing.
No zero-location hypothesis is used. -/
theorem inner_xiWeilLineConjLp_evaluation_eq_polarization
    (F G : ℂ → ℂ) (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    inner ℂ (xiWeilLineConjLp (xiWeilEvaluationLp G hG))
      (xiWeilEvaluationLp F hF) = xiWeilPolarization F G := by
  rw [lp.inner_eq_tsum, xiWeilPolarization]
  apply tsum_congr
  intro q
  rw [xiWeilLineConjLp_apply, xiWeilEvaluationLp_apply,
    xiWeilEvaluationLp_apply, xiSpectralPoint_lineConj]
  simp [xiWeilSharp, RCLike.inner_apply]

/-- Evaluation identifies the continuous Hilbert quadratic form with the diagonal Weil value. -/
theorem xiWeilHilbertQuadratic_evaluation_eq_polarization_re
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilHilbertQuadratic (xiWeilEvaluationLp F hF) =
      (xiWeilPolarization F F).re := by
  rw [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry_apply,
    inner_xiWeilLineConjLp_evaluation_eq_polarization]

/-- Unconditional Cauchy--Schwarz bound for the Xi Weil polarization on square-summable tests. -/
theorem norm_xiWeilPolarization_le
    (F G : ℂ → ℂ) (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    ‖xiWeilPolarization F G‖ ≤
      ‖xiWeilEvaluationLp F hF‖ * ‖xiWeilEvaluationLp G hG‖ := by
  rw [← inner_xiWeilLineConjLp_evaluation_eq_polarization F G hF hG]
  calc
    ‖inner ℂ (xiWeilLineConjLp (xiWeilEvaluationLp G hG))
        (xiWeilEvaluationLp F hF)‖ ≤
        ‖xiWeilLineConjLp (xiWeilEvaluationLp G hG)‖ *
          ‖xiWeilEvaluationLp F hF‖ := norm_inner_le_norm _ _
    _ = ‖xiWeilEvaluationLp F hF‖ * ‖xiWeilEvaluationLp G hG‖ := by
      rw [norm_xiWeilLineConjLp]
      exact mul_comm _ _

end

end RHTower
