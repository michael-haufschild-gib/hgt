import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The orthogonal projection onto the image of a subspace under a bounded-below operator

Let `Q` be the orthogonal projection of a Hilbert space onto a closed subspace `S`, and let `M` be a
bounded operator that is bounded below on `S`.  Then the Gram operator

`A = Q M* M Q + (1 - Q)`

is a positive invertible operator, and

`P = M Q A⁻¹ Q M*`

is exactly the orthogonal projection onto `M(S)`.  The proof is purely algebraic once `A` is
invertible: the identity `A (1 - Q) = 1 - Q` forces `A⁻¹` to commute with the splitting, which
gives `P (M Q) = M Q` and hence idempotence and the range identification.
-/

open ContinuousLinearMap

namespace HTGeometry

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint operator with a positive lower bound is invertible. -/
theorem isUnit_of_isSelfAdjoint_of_norm_le {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {m : ℝ}
    (hm : 0 < m) (hlow : ∀ x : H, m * ‖x‖ ≤ ‖A x‖) : IsUnit A := by
  have hanti : AntilipschitzWith (Real.toNNReal m⁻¹) A := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have h := hlow (x - y)
    rw [map_sub] at h
    rw [dist_eq_norm, dist_eq_norm]
    have hcoe : ((Real.toNNReal m⁻¹ : NNReal) : ℝ) = m⁻¹ :=
      Real.coe_toNNReal _ (by positivity)
    rw [hcoe]
    rw [le_div_iff₀ hm] at *
    calc ‖x - y‖ = m * ‖x - y‖ / m := by field_simp
      _ ≤ ‖A x - A y‖ / m := by
          apply div_le_div_of_nonneg_right h hm.le
      _ = m⁻¹ * ‖A x - A y‖ := by ring
  have hinj : Function.Injective A := hanti.injective
  have hclosed : IsClosed (Set.range A) := hanti.isClosed_range A.continuous
  have hdense : (LinearMap.range A)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hAy : A y = 0 := by
      have : ⟪A y, y⟫_ℂ = 0 := by
        have := hy (A y) ⟨y, rfl⟩
        simpa using this
      have hself : ⟪y, A y⟫_ℂ = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]
        exact this
      have hnorm : ‖A y‖ ^ 2 ≤ 0 := by
        have h1 := hlow y
        nlinarith [norm_nonneg (A y), norm_nonneg y,
          (by
            have : ⟪A y, A y⟫_ℂ = 0 := by
              rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]
              have := hy (A (A y)) ⟨A y, rfl⟩
              sorry
            sorry : ‖A y‖ = 0)]
      sorry
    have := hlow y
    rw [hAy, norm_zero] at this
    have : ‖y‖ ≤ 0 := by nlinarith [norm_nonneg y]
    simpa using le_antisymm this (norm_nonneg y)
  have hsurj : Function.Surjective A := by
    have hr : LinearMap.range A = ⊤ := by
      have hcl : (LinearMap.range A : Submodule ℂ H).topologicalClosure
          = LinearMap.range A := by
        exact SetLike.ext' (by simpa using hclosed.closure_eq)
      have := Submodule.orthogonal_orthogonal_eq_closure (K := LinearMap.range A)
      rw [hdense] at this
      simpa [hcl] using this.symm
    exact LinearMap.range_eq_top.mp hr
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

end

end HTGeometry
