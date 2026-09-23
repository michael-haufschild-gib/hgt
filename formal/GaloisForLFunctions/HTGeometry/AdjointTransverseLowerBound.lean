import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# A bounded-below adjoint gives a transverse lower bound

If the Hilbert adjoint `T*` of a bounded operator satisfies `c‖y‖ ≤ ‖T* y‖` for a positive `c`,
then `T` itself satisfies the same lower bound on the orthogonal complement of its kernel:

```
x ⊥ ker T  ⟹  c‖x‖ ≤ ‖T x‖.
```

This is the *reduced minimum modulus* half of the polar picture.  The proof needs no closed-range
input: `ker T = (ran T*)ᗮ` identifies `(ker T)ᗮ` with the closure of `ran T*`, on which the bound
is the Cauchy--Schwarz computation `‖T* y‖² = ⟪T T* y, y⟫ ≤ ‖T(T* y)‖‖y‖`, and the inequality
passes to the closure because the set where it holds is closed.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The kernel of an operator is the orthogonal complement of the range of its adjoint. -/
theorem ker_eq_orthogonal_range_adjoint (T : E →L[𝕜] E) :
    LinearMap.ker (T : E →ₗ[𝕜] E)
      = (LinearMap.range (ContinuousLinearMap.adjoint T : E →ₗ[𝕜] E))ᗮ := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨y, rfl⟩
    have hTx : T x = 0 := hx
    have := ContinuousLinearMap.adjoint_inner_left T x y
    simp only [hTx, inner_zero_right] at this
    exact this
  · intro hx
    have hall : ∀ y : E, ⟪(y : E), T x⟫_𝕜 = 0 := by
      intro y
      have hmem : (ContinuousLinearMap.adjoint T) y
          ∈ LinearMap.range (ContinuousLinearMap.adjoint T : E →ₗ[𝕜] E) := ⟨y, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).mp hx _ hmem
      rw [ContinuousLinearMap.adjoint_inner_left T x y] at h0
      exact h0
    have : T x = 0 := by
      have := hall (T x)
      exact (inner_self_eq_zero (𝕜 := 𝕜)).mp this
    exact this

/-- **The reduced minimum modulus from the adjoint.** -/
theorem transverse_lower_bound_of_adjoint_bounded_below (T : E →L[𝕜] E) {c : ℝ} (hc : 0 < c)
    (hT : ∀ y : E, c * ‖y‖ ≤ ‖ContinuousLinearMap.adjoint T y‖) :
    ∀ x ∈ (LinearMap.ker (T : E →ₗ[𝕜] E))ᗮ, c * ‖x‖ ≤ ‖T x‖ := by
  set S := LinearMap.range (ContinuousLinearMap.adjoint T : E →ₗ[𝕜] E) with hS
  have hker : (LinearMap.ker (T : E →ₗ[𝕜] E))ᗮ = S.topologicalClosure := by
    rw [ker_eq_orthogonal_range_adjoint T, ← hS, Submodule.orthogonal_orthogonal_eq_closure]
  -- the bound holds on the range of the adjoint
  have hrange0 : ∀ y : E, c * ‖(ContinuousLinearMap.adjoint T) y‖
      ≤ ‖T ((ContinuousLinearMap.adjoint T) y)‖ := by
    intro y
    set x : E := (ContinuousLinearMap.adjoint T) y with hx
    rcases eq_or_ne x 0 with h0 | h0
    · rw [h0]
      simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
    have hy : c * ‖y‖ ≤ ‖x‖ := hT y
    have hnormsq : ‖x‖ ^ (2 : ℕ) = RCLike.re (⟪T x, y⟫_𝕜) := by
      have hinner : ⟪x, x⟫_𝕜 = ⟪T x, y⟫_𝕜 := by
        rw [hx]
        exact ContinuousLinearMap.adjoint_inner_right T x y
      have h2 := congrArg RCLike.re hinner
      rw [inner_self_eq_norm_sq_to_K] at h2
      simpa using h2
    have hcs : RCLike.re (⟪T x, y⟫_𝕜) ≤ ‖T x‖ * ‖y‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
    have hkey : ‖x‖ ^ (2 : ℕ) ≤ ‖T x‖ * ‖y‖ := by rw [hnormsq]; exact hcs
    have hstep : (c * ‖x‖) * ‖x‖ ≤ ‖T x‖ * ‖x‖ := by
      calc (c * ‖x‖) * ‖x‖ = c * ‖x‖ ^ (2 : ℕ) := by ring
        _ ≤ c * (‖T x‖ * ‖y‖) := mul_le_mul_of_nonneg_left hkey hc.le
        _ = ‖T x‖ * (c * ‖y‖) := by ring
        _ ≤ ‖T x‖ * ‖x‖ := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    exact le_of_mul_le_mul_right hstep hxpos
  have hrange : ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖ := by
    rintro _ ⟨y, rfl⟩
    exact hrange0 y
  -- and the set where it holds is closed
  have hclosed : IsClosed {x : E | c * ‖x‖ ≤ ‖T x‖} := by
    have hcont : Continuous fun x : E => ‖T x‖ - c * ‖x‖ :=
      (T.continuous.norm).sub (continuous_const.mul continuous_norm)
    have : {x : E | c * ‖x‖ ≤ ‖T x‖} = (fun x : E => ‖T x‖ - c * ‖x‖) ⁻¹' (Set.Ici 0) := by
      ext x
      simp [Set.mem_Ici, sub_nonneg]
    rw [this]
    exact isClosed_Ici.preimage hcont
  intro x hx
  rw [hker] at hx
  have hxcl : x ∈ closure (S : Set E) := by
    rwa [← Submodule.topologicalClosure_coe]
  exact hclosed.closure_subset_iff.mpr hrange hxcl

end GaloisForLFunctions.HTGeometry
