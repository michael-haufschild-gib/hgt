import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue

/-!
# The compact commutant of a unitary without eigenvectors

If a unitary `U` on a complex Hilbert space has no eigenvector, then every compact operator
commuting with `U` vanishes.  If `K ≠ 0` commutes with `U`, so does the positive compact operator
`K* K ≠ 0`; it has an eigenvalue `μ ≠ 0` whose eigenspace is nonzero, finite dimensional and
`U`-invariant, and a unitary on a nonzero finite-dimensional complex space has an eigenvector.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary **has no eigenvectors** when `U x = μ x` forces `x = 0`. -/
def HasNoEigenvectors (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ (x : H) (μ : ℂ), U x = μ • x → x = 0

omit [CompleteSpace H] in
theorem inner_map_symm (U : H ≃ₗᵢ[ℂ] H) (x y : H) : ⟪U x, y⟫_ℂ = ⟪x, U.symm y⟫_ℂ := by
  conv_lhs => rw [← U.apply_symm_apply y]
  exact U.inner_map_map _ _

/-- The adjoint of an operator commuting with a unitary also commutes with it. -/
theorem adjoint_comm_of_comm (U : H ≃ₗᵢ[ℂ] H) {K : H →L[ℂ] H}
    (hcomm : ∀ x, K (U x) = U (K x)) (x : H) :
    ContinuousLinearMap.adjoint K (U x) = U (ContinuousLinearMap.adjoint K x) := by
  have hsymm := symm_comm_of_comm U K hcomm
  refine ext_inner_right ℂ fun y => ?_
  rw [inner_map_symm, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left, hsymm y, ← inner_map_symm]

/-- **Compact commutant.**  A compact operator commuting with a unitary that has no eigenvectors
is zero. -/
theorem eq_zero_of_isCompactOperator_of_comm {U : H ≃ₗᵢ[ℂ] H} (hU : HasNoEigenvectors U)
    {K : H →L[ℂ] H} (hK : IsCompactOperator K) (hcomm : ∀ x, K (U x) = U (K x)) : K = 0 := by
  by_contra hK0
  set S : H →L[ℂ] H := ContinuousLinearMap.adjoint K ∘L K with hSdef
  have hScpt : IsCompactOperator S := hK.clm_comp (ContinuousLinearMap.adjoint K)
  have hSsym : S.IsSymmetric := fun x y => by
    show ⟪ContinuousLinearMap.adjoint K (K x), y⟫_ℂ = ⟪x, ContinuousLinearMap.adjoint K (K y)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  have hSne : S ≠ 0 := by
    intro h
    have hn := ContinuousLinearMap.norm_adjoint_comp_self K
    rw [← hSdef, h, norm_zero] at hn
    exact hK0 (norm_eq_zero.mp (mul_self_eq_zero.mp hn.symm))
  obtain ⟨μ, x, hμ, hx, hSx⟩ := ContinuousLinearMap.exists_unit_eigenvector_norm hScpt hSsym hSne
  have hμ0 : (μ : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    intro h
    rw [h, abs_zero] at hμ
    exact hSne (norm_eq_zero.mp hμ.symm)
  have hcommS : ∀ y, S (U y) = U (S y) := by
    intro y
    show ContinuousLinearMap.adjoint K (K (U y)) = U (ContinuousLinearMap.adjoint K (K y))
    rw [hcomm, adjoint_comm_of_comm U hcomm]
  haveI : FiniteDimensional ℂ (Module.End.eigenspace S.toLinearMap (μ : ℂ)) :=
    finiteDimensional_eigenspace_of_isCompactOperator hScpt hμ0
  have hxmem : x ∈ Module.End.eigenspace S.toLinearMap (μ : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr hSx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  haveI : Nontrivial (Module.End.eigenspace S.toLinearMap (μ : ℂ)) :=
    ⟨⟨⟨x, hxmem⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨y, c, hy0, hyc, -⟩ :=
    exists_unimodular_eigenvector (unitaryEigenspaceRestrict U S hcommS (μ : ℂ))
  have hUy : U (y : H) = c • (y : H) := by
    have := congrArg Subtype.val hyc
    simpa using this
  exact hy0 (Subtype.ext (hU _ _ hUy))

end GaloisForLFunctions.HTGeometry
