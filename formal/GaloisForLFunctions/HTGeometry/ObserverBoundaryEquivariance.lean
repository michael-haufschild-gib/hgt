import GaloisForLFunctions.HTGeometry.ObserverBoundaryBuilding
import GaloisForLFunctions.HTGeometry.HermitianFlagEquivariance

/-!
# Equivariance of the boundary–building correspondence

An isometry of the observer space conjugates directions, and the correspondence between asymptote
classes of rays and flags of the horizon building intertwines that action with the action of the
isometry on subspaces:

```text
Asymptotic (ray (g T g⁻¹)) (ray (g S g⁻¹))  ↔  Asymptotic (ray T) (ray S),
eigenSum (g T g⁻¹) c = (eigenSum T c).map g.
```

So the boundary point of a conjugated ray is the conjugated flag: the dictionary of the card is
equivariant for the stabiliser of the reference metric.  Conjugation by a nonzero scalar multiple
of an isometry is conjugation by the isometry, so the action is projective.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The conjugate of a direction by an isometry. -/
noncomputable def conjOp (g : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  ((g.toLinearEquiv : E →ₗ[ℂ] E)) ∘ₗ T ∘ₗ ((g.toLinearEquiv.symm : E →ₗ[ℂ] E))

omit [FiniteDimensional ℂ E] in
/-- **Conjugating by an isometry preserves Hermitian symmetry.** -/
theorem isSymmetric_conjOp (g : E ≃ₗᵢ[ℂ] E) {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) :
    (conjOp g T).IsSymmetric := by
  intro x y
  show inner ℂ (g (T (g.symm x))) y = inner ℂ x (g (T (g.symm y)))
  rw [show (inner ℂ (g (T (g.symm x))) y : ℂ) = inner ℂ (T (g.symm x)) (g.symm y) from by
      rw [← g.inner_map_map (T (g.symm x)) (g.symm y), g.apply_symm_apply],
    hT (g.symm x) (g.symm y),
    show (inner ℂ (g.symm x) (T (g.symm y)) : ℂ) = inner ℂ x (g (T (g.symm y))) from by
      rw [← g.inner_map_map (g.symm x) (T (g.symm y)), g.apply_symm_apply]]

omit [FiniteDimensional ℂ E] in
/-- **Conjugating by an isometry preserves the trace.** -/
theorem trace_conjOp (g : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (conjOp g T) = LinearMap.trace ℂ E T := by
  rw [conjOp]
  exact LinearMap.trace_conj' T g.toLinearEquiv

omit [FiniteDimensional ℂ E] in
/-- **The flag of a conjugated direction is the conjugated flag.** -/
theorem eigenSum_conjOp (g : E ≃ₗᵢ[ℂ] E) (T : E →ₗ[ℂ] E) (c : ℝ) :
    eigenSum (conjOp g T) c = (eigenSum T c).map (g.toLinearEquiv : E →ₗ[ℂ] E) :=
  eigenSum_conj g.toLinearEquiv T c

/-- **The boundary–building correspondence is equivariant.**  Two rays are asymptotic exactly when
their conjugates by an isometry are, and the flags transform by the same isometry. -/
theorem asymptotic_conjOp_iff (g : E ≃ₗᵢ[ℂ] E) {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (htr : LinearMap.trace ℂ E (S - T) = 0) :
    Asymptotic (observerRay (isSymmetric_conjOp g hT)) (observerRay (isSymmetric_conjOp g hS))
      ↔ Asymptotic (observerRay hT) (observerRay hS) := by
  have htr' : LinearMap.trace ℂ E (conjOp g S - conjOp g T) = 0 := by
    rw [map_sub, trace_conjOp, trace_conjOp, ← map_sub]
    exact htr
  rw [asymptotic_iff_eigenSum_eq (isSymmetric_conjOp g hT) (isSymmetric_conjOp g hS) htr',
    asymptotic_iff_eigenSum_eq hT hS htr]
  constructor
  · intro h c
    have hc := h c
    rw [eigenSum_conjOp, eigenSum_conjOp] at hc
    have hinj : Function.Injective
        (fun p : Submodule ℂ E => p.map (g.toLinearEquiv : E →ₗ[ℂ] E)) := by
      intro p q hpq
      have h1 := congrArg
        (fun p : Submodule ℂ E => p.comap (g.toLinearEquiv : E →ₗ[ℂ] E)) hpq
      simpa [Submodule.comap_map_eq_of_injective g.toLinearEquiv.injective] using h1
    exact hinj hc
  · intro h c
    rw [eigenSum_conjOp, eigenSum_conjOp, h c]

omit [FiniteDimensional ℂ E] in
/-- **Scalars act trivially.**  Conjugation by a nonzero multiple of an isometry is conjugation by
the isometry, so the action on the boundary is that of the projective observer group. -/
theorem conjOp_smul_eq (g : E ≃ₗᵢ[ℂ] E) {a : ℂ} (ha : a ≠ 0) (T : E →ₗ[ℂ] E) :
    ((a • (g.toLinearEquiv : E →ₗ[ℂ] E)) ∘ₗ T ∘ₗ (a⁻¹ • (g.toLinearEquiv.symm : E →ₗ[ℂ] E)))
      = conjOp g T :=
  conj_smul_eq g.toLinearEquiv ha T

end GaloisForLFunctions.HTGeometry
