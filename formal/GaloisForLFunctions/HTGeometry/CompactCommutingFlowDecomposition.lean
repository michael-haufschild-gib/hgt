import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-!
# Eigenspaces of a commuting compact operator are flow-invariant

A unitary commuting with a compact operator preserves each of its eigenspaces, and its inverse
does too, so it restricts to a unitary of the eigenspace.  Since the eigenspaces of a compact
operator attached to a nonzero eigenvalue are finite dimensional, a flow commuting with a compact
smoothing operator decomposes into finite-dimensional unitary blocks.

This is the assembly step for discreteness of the spectrum of a flow whose smoothings are
compact: the block structure comes from the compact operator, and the flow acts inside each block.
-/

namespace GaloisForLFunctions.HTGeometry

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- An endomorphism commuting with another preserves its eigenspaces. -/
theorem mapsTo_eigenspace_of_commute {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    (S T : Module.End 𝕜 M) (hcomm : ∀ x, S (T x) = T (S x)) (mu : 𝕜) :
    ∀ x ∈ eigenspace S mu, T x ∈ eigenspace S mu := by
  intro x hx
  have hSx : S x = mu • x := mem_eigenspace_iff.mp hx
  rw [mem_eigenspace_iff, hcomm x, hSx, map_smul]

/-- A unitary commuting with a continuous linear operator has an inverse commuting with it. -/
theorem symm_comm_of_comm (U : H ≃ₗᵢ[𝕜] H) (K : H →L[𝕜] H)
    (hcomm : ∀ x, K (U x) = U (K x)) (y : H) :
    K (U.symm y) = U.symm (K y) := by
  have h := hcomm (U.symm y)
  rw [U.apply_symm_apply] at h
  rw [h, U.symm_apply_apply]

/-- A unitary commuting with `K` preserves every eigenspace of `K`. -/
theorem mapsTo_eigenspace_of_unitary_comm (U : H ≃ₗᵢ[𝕜] H) (K : H →L[𝕜] H)
    (hcomm : ∀ x, K (U x) = U (K x)) (mu : 𝕜) :
    ∀ x ∈ eigenspace K.toLinearMap mu, U x ∈ eigenspace K.toLinearMap mu :=
  mapsTo_eigenspace_of_commute K.toLinearMap U.toLinearEquiv.toLinearMap hcomm mu

/-- Its inverse preserves the same eigenspace. -/
theorem mapsTo_eigenspace_of_unitary_symm_comm (U : H ≃ₗᵢ[𝕜] H) (K : H →L[𝕜] H)
    (hcomm : ∀ x, K (U x) = U (K x)) (mu : 𝕜) :
    ∀ x ∈ eigenspace K.toLinearMap mu, U.symm x ∈ eigenspace K.toLinearMap mu :=
  mapsTo_eigenspace_of_commute K.toLinearMap U.symm.toLinearEquiv.toLinearMap
    (symm_comm_of_comm U K hcomm) mu

/-- **The flow restricts to a unitary of each eigenspace.**  A unitary commuting with `K` induces a
linear isometry equivalence of every eigenspace of `K`. -/
noncomputable def unitaryEigenspaceRestrict (U : H ≃ₗᵢ[𝕜] H) (K : H →L[𝕜] H)
    (hcomm : ∀ x, K (U x) = U (K x)) (mu : 𝕜) :
    (eigenspace K.toLinearMap mu) ≃ₗᵢ[𝕜] (eigenspace K.toLinearMap mu) where
  toFun x := ⟨U (x : H), mapsTo_eigenspace_of_unitary_comm U K hcomm mu (x : H) x.2⟩
  invFun x := ⟨U.symm (x : H), mapsTo_eigenspace_of_unitary_symm_comm U K hcomm mu (x : H) x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact U.symm_apply_apply (x : H)
  right_inv x := by
    apply Subtype.ext
    exact U.apply_symm_apply (x : H)
  map_add' x y := by
    apply Subtype.ext
    exact map_add U (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul U c (x : H)
  norm_map' x := U.norm_map (x : H)

@[simp]
theorem unitaryEigenspaceRestrict_coe (U : H ≃ₗᵢ[𝕜] H) (K : H →L[𝕜] H)
    (hcomm : ∀ x, K (U x) = U (K x)) (mu : 𝕜)
    (x : eigenspace K.toLinearMap mu) :
    ((unitaryEigenspaceRestrict U K hcomm mu x : eigenspace K.toLinearMap mu) : H)
      = U (x : H) := rfl

/-- **Finite-dimensional flow blocks.**  For a compact `K` and a nonzero eigenvalue, the eigenspace
is finite dimensional and carries the restricted unitary. -/
theorem finiteDimensional_eigenspace_of_isCompactOperator [CompleteSpace H]
    {K : H →L[𝕜] H} (hK : IsCompactOperator K) {mu : 𝕜} (hmu : mu ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace K.toLinearMap mu) :=
  K.finite_dimensional_eigenspace hK mu hmu

end GaloisForLFunctions.HTGeometry
