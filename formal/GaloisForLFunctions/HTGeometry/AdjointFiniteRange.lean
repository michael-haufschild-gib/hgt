import GaloisForLFunctions.HTGeometry.HilbertClosedRange

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Finite algebraic rank is preserved when passing to a Hilbert-space adjoint. -/
theorem finiteDimensional_range_adjoint_of_range
    (T : E →L[ℂ] F) [FiniteDimensional ℂ T.range] :
    FiniteDimensional ℂ T.adjoint.range := by
  let K : Submodule ℂ E := LinearMap.ker (T : E →ₗ[ℂ] F)
  let L : (Kᗮ : Submodule ℂ E) →ₗ[ℂ] T.range := {
    toFun x := ⟨T x, ⟨x, rfl⟩⟩
    map_add' x y := by
      ext
      exact map_add T (x : E) (y : E)
    map_smul' c x := by
      ext
      exact map_smul T c (x : E) }
  have hLinj : Function.Injective L := by
    intro x y hxy
    have hval : T (x : E) = T (y : E) := congrArg Subtype.val hxy
    have hker : (x : E) - (y : E) ∈ K := by
      change T ((x : E) - (y : E)) = 0
      rw [map_sub, hval, sub_self]
    have horth : (x : E) - (y : E) ∈ Kᗮ := sub_mem x.property y.property
    have hinner : inner ℂ ((x : E) - (y : E)) ((x : E) - (y : E)) = 0 :=
      ((K.mem_orthogonal _).1 horth) _ hker
    apply Subtype.ext
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)
  letI : FiniteDimensional ℂ (Kᗮ : Submodule ℂ E) :=
    FiniteDimensional.of_injective L hLinj
  have hclosedRange : IsClosed (Set.range T) := by
    rw [show Set.range T = (T.range : Set F) by
      ext y
      simp [LinearMap.mem_range, Set.mem_range]]
    exact Submodule.closed_of_finiteDimensional T.range
  have hrange := ContinuousLinearMap.range_adjoint_eq_ker_orthogonal_of_isClosed_range
    T hclosedRange
  change FiniteDimensional ℂ
    (LinearMap.range ((T.adjoint : F →L[ℂ] E) : F →ₗ[ℂ] E))
  rw [hrange]
  exact inferInstance

/-- If an adjoint has infinite algebraic rank, then so does the original operator. -/
theorem not_finiteDimensional_range_of_adjoint
    (T : E →L[ℂ] F) (h : ¬ FiniteDimensional ℂ T.adjoint.range) :
    ¬ FiniteDimensional ℂ T.range := by
  intro hT
  letI : FiniteDimensional ℂ T.range := hT
  exact h (finiteDimensional_range_adjoint_of_range T)

end

end GaloisForLFunctions.HTGeometry
