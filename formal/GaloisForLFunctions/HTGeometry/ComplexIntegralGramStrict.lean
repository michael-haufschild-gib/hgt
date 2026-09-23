import GaloisForLFunctions.HTGeometry.ComplexIntegralGram

/-!
# Strict positivity of complex integral Gram matrices

Pairwise integrability makes a complex feature Gram positive semidefinite.  If every nonzero
coefficient combination is nonzero on a set of positive measure, the quadratic integral is
strictly positive and the Gram matrix is positive definite.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Matrix
open scoped ComplexOrder BigOperators

noncomputable section

variable {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]

/-- Positive-measure separation upgrades a complex integral Gram matrix to positive definite. -/
theorem complexFeatureGram_posDef_of_support
    (mu : Measure Omega) (f : iota → Omega → ℂ)
    (hprod : ∀ l m, Integrable (fun omega => f l omega * (starRingEnd ℂ) (f m omega)) mu)
    (hseparate : ∀ x : iota → ℂ, x ≠ 0 →
      0 < mu (Function.support (complexFeatureCombination f x))) :
    (complexFeatureGram mu f).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (complexFeatureGram_isHermitian mu f) fun x hx => ?_
  rw [complexFeatureGram_quadratic mu f hprod x]
  have hcast : ∀ omega, complexFeatureCombination f x omega *
      (starRingEnd ℂ) (complexFeatureCombination f x omega) =
      ((‖complexFeatureCombination f x omega‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro omega
    rw [Complex.mul_conj, ← Complex.sq_norm]
  have hint : Integrable (fun omega => complexFeatureCombination f x omega *
      (starRingEnd ℂ) (complexFeatureCombination f x omega)) mu := by
    refine Integrable.congr
      (integrable_finsetSum (Finset.univ : Finset iota) fun l _ =>
        integrable_finsetSum (Finset.univ : Finset iota) fun m _ =>
          (hprod l m).const_mul ((starRingEnd ℂ) (x l) * x m)) ?_
    exact Filter.Eventually.of_forall fun omega =>
      (complexFeatureCombination_mul_conj f x omega).symm
  have hnormInt : Integrable (fun omega => ‖complexFeatureCombination f x omega‖ ^ (2 : ℕ)) mu := by
    have hre : Integrable (fun omega => (complexFeatureCombination f x omega *
        (starRingEnd ℂ) (complexFeatureCombination f x omega)).re) mu := hint.re
    refine hre.congr (Filter.Eventually.of_forall fun omega => ?_)
    dsimp only
    rw [hcast omega, Complex.ofReal_re]
  have hval : (∫ omega, complexFeatureCombination f x omega *
      (starRingEnd ℂ) (complexFeatureCombination f x omega) ∂mu) =
      ((∫ omega, ‖complexFeatureCombination f x omega‖ ^ (2 : ℕ) ∂mu : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hcast)]
    exact Complex.ofRealCLM.integral_comp_comm hnormInt
  rw [hval]
  apply Complex.zero_lt_real.mpr
  rw [integral_pos_iff_support_of_nonneg (fun omega => by positivity)]
  · simpa [Function.support] using hseparate x hx
  · exact hnormInt

end

end GaloisForLFunctions.HTGeometry
