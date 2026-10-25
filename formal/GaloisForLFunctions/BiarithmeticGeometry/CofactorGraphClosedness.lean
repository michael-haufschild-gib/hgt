import GaloisForLFunctions.BiarithmeticGeometry.CofactorGraphDomain
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Ambient closedness is a uniform cofactor-energy estimate

The complete graph has its product maximum norm. Its injective input map
has closed range precisely when the output norm is uniformly controlled
by the input Wiener norm. The Banach inverse theorem supplies necessity;
the same estimate makes the input map bounded below and supplies sufficiency.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The complete graph carries the maximum of its input and output norms. -/
theorem norm_cofactorGraphDomain (v : ℕ → ℂ) (p : cofactorGraphDomain v) :
    ‖p‖ = max ‖cofactorGraphInput v p‖ ‖cofactorGraphOutput v p‖ := rfl

/-- Ambient closedness is exactly a uniform total-energy bound on the graph domain. -/
theorem isClosed_range_cofactorGraphInput_iff (v : ℕ → ℂ) :
    IsClosed (Set.range (cofactorGraphInput v)) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p : cofactorGraphDomain v,
        ‖cofactorGraphOutput v p‖ ≤ C * ‖cofactorGraphInput v p‖ := by
  rw [(cofactorGraphInput v).isClosed_range_iff_antilipschitz_of_injective
    (cofactorGraphInput_injective v)]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, K.property, fun p => ?_⟩
    have h := (cofactorGraphInput v).bound_of_antilipschitz hK p
    rw [norm_cofactorGraphDomain] at h
    exact (le_max_right _ _).trans h
  · rintro ⟨C, hC0, hC⟩
    let K : NNReal := ⟨max 1 C, le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)⟩
    refine ⟨K, (cofactorGraphInput v).antilipschitz_of_bound fun p => ?_⟩
    rw [norm_cofactorGraphDomain]
    change max ‖cofactorGraphInput v p‖ ‖cofactorGraphOutput v p‖ ≤
      max 1 C * ‖cofactorGraphInput v p‖
    apply max_le
    · calc
        _ = 1 * ‖cofactorGraphInput v p‖ := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · exact (hC p).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end GaloisForLFunctions.BiarithmeticGeometry
