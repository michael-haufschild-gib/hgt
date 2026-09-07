import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactKAction

/-!
# Harish-Chandra operators on compact-picture finite K-types

This file realizes the explicit spherical Harish-Chandra model as the finite even-Fourier
subspace of the normalized compact principal series.  It transports the raising, lowering,
weight, and Casimir operators to that concrete function space and proves the `sl₂` relations
and Casimir scalar there.

The normalization uses Borel exponent `s + 1`, matching the coefficients
`(s - 1 ∓ 2m) / 2` in the explicit Harish-Chandra model.  The compact rotation derivative is
identified with the weight operator in `RealPrincipalSeriesCompactKDerivative`; identifying the
raising and lowering operators with noncompact infinitesimal translations remains analytic work.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Finite even-Fourier subspace of the normalized compact principal series. -/
abbrev normalizedRealCompactKFiniteSubmodule (s : ℝ) :
    Submodule ℂ (realCompactPictureSpace (s + 1)) :=
  LinearMap.range (realCompactKFiniteEmbedding (s + 1))

/-- The explicit spherical Harish-Chandra model is linearly equivalent to the finite
even-Fourier compact-picture subspace. -/
def sphericalModelCompactKFiniteEquiv (s : ℝ) :
    SphericalKFiniteModel ≃ₗ[ℂ] normalizedRealCompactKFiniteSubmodule s :=
  LinearEquiv.ofInjective (realCompactKFiniteEmbedding (s + 1))
    (realCompactKFiniteEmbedding_injective (s + 1))

/-- Finite normalized compact-picture K-types are stable under the actual principal-series
action restricted to `K`. -/
theorem normalizedRealCompactKFiniteSubmodule_K_invariant (s : ℝ)
    (q : upperHalfPlaneStabilizer) :
    normalizedRealCompactKFiniteSubmodule s ≤
      (normalizedRealCompactKFiniteSubmodule s).comap
        (compactRealPrincipalSeries (s + 1) (q : SL2R)) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨sphericalKTypeRepresentation q v, ?_⟩
  exact LinearMap.congr_fun
    (realCompactKFiniteEmbedding_intertwines_K (s + 1) q) v

/-- Actual restricted K-representation on the finite compact-picture subspace. -/
def normalizedRealCompactKFiniteRepresentation (s : ℝ) :
    Representation ℂ upperHalfPlaneStabilizer
      (normalizedRealCompactKFiniteSubmodule s) :=
  Representation.subrepresentation
    ((compactRealPrincipalSeries (s + 1)).comp upperHalfPlaneStabilizer.subtype)
    (normalizedRealCompactKFiniteSubmodule s)
    (normalizedRealCompactKFiniteSubmodule_K_invariant s)

/-- The explicit finite-support K-representation and compact-picture K-representation are
intertwined by Fourier expansion. -/
theorem sphericalModelCompactKFiniteEquiv_intertwines_K (s : ℝ)
    (q : upperHalfPlaneStabilizer) (v : SphericalKFiniteModel) :
    normalizedRealCompactKFiniteRepresentation s q
        (sphericalModelCompactKFiniteEquiv s v) =
      sphericalModelCompactKFiniteEquiv s (sphericalKTypeRepresentation q v) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun
    (realCompactKFiniteEmbedding_intertwines_K (s + 1) q) v).symm

@[simp]
theorem sphericalModelCompactKFiniteEquiv_apply_coe (s : ℝ)
    (v : SphericalKFiniteModel) :
    ((sphericalModelCompactKFiniteEquiv s v : normalizedRealCompactKFiniteSubmodule s) :
      realCompactPictureSpace (s + 1)) = realCompactKFiniteEmbedding (s + 1) v :=
  rfl

@[simp]
theorem sphericalModelCompactKFiniteEquiv_single_apply (s : ℝ) (m : ℤ) (z : ℂ)
    (k : upperHalfPlaneStabilizer) :
    ((((sphericalModelCompactKFiniteEquiv s) (Finsupp.single m z) :
        normalizedRealCompactKFiniteSubmodule s) :
      realCompactPictureSpace (s + 1)) : upperHalfPlaneStabilizer → ℂ) k =
      z * realSphericalKTypeCharacter m k := by
  rw [sphericalModelCompactKFiniteEquiv_apply_coe,
    realCompactKFiniteEmbedding_single]
  rfl

/-- Conjugating endomorphisms across a linear equivalence preserves composition. -/
theorem linearEquiv_conj_comp {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (A B : Module.End ℂ V) :
    e.conj (A.comp B) = (e.conj A).comp (e.conj B) := by
  ext w
  rcases e.surjective w with ⟨v, rfl⟩
  simp [LinearEquiv.conj_apply]

/-- Conjugating the identity endomorphism gives the identity. -/
theorem linearEquiv_conj_id {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    e.conj LinearMap.id = LinearMap.id := by
  ext w
  rcases e.surjective w with ⟨v, rfl⟩
  simp [LinearEquiv.conj_apply]

/-- Weight operator on finite compact-picture K-types. -/
def compactSphericalPrincipalH (s : ℝ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH

/-- Raising operator on finite compact-picture K-types. -/
def compactSphericalPrincipalE (s : ℝ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalE (s : ℂ))

/-- Lowering operator on finite compact-picture K-types. -/
def compactSphericalPrincipalF (s : ℝ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalF (s : ℂ))

@[simp]
theorem compactSphericalPrincipalH_equiv_apply (s : ℝ) (v : SphericalKFiniteModel) :
    compactSphericalPrincipalH s (sphericalModelCompactKFiniteEquiv s v) =
      sphericalModelCompactKFiniteEquiv s (sphericalPrincipalH v) := by
  simp [compactSphericalPrincipalH, LinearEquiv.conj_apply]

@[simp]
theorem compactSphericalPrincipalE_equiv_apply (s : ℝ) (v : SphericalKFiniteModel) :
    compactSphericalPrincipalE s (sphericalModelCompactKFiniteEquiv s v) =
      sphericalModelCompactKFiniteEquiv s (sphericalPrincipalE (s : ℂ) v) := by
  simp [compactSphericalPrincipalE, LinearEquiv.conj_apply]

@[simp]
theorem compactSphericalPrincipalF_equiv_apply (s : ℝ) (v : SphericalKFiniteModel) :
    compactSphericalPrincipalF s (sphericalModelCompactKFiniteEquiv s v) =
      sphericalModelCompactKFiniteEquiv s (sphericalPrincipalF (s : ℂ) v) := by
  simp [compactSphericalPrincipalF, LinearEquiv.conj_apply]

@[simp]
theorem compactSphericalPrincipalH_single (s : ℝ) (m : ℤ) (z : ℂ) :
    compactSphericalPrincipalH s
        (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z)) =
      sphericalModelCompactKFiniteEquiv s
        (Finsupp.single m ((2 * (m : ℂ)) * z)) := by
  simp

@[simp]
theorem compactSphericalPrincipalE_single (s : ℝ) (m : ℤ) (z : ℂ) :
    compactSphericalPrincipalE s
        (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z)) =
      sphericalModelCompactKFiniteEquiv s
        (Finsupp.single (m + 1) (((s - 1 : ℝ) - 2 * m : ℝ) / 2 * z)) := by
  simp

@[simp]
theorem compactSphericalPrincipalF_single (s : ℝ) (m : ℤ) (z : ℂ) :
    compactSphericalPrincipalF s
        (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z)) =
      sphericalModelCompactKFiniteEquiv s
        (Finsupp.single (m - 1) (((s - 1 : ℝ) + 2 * m : ℝ) / 2 * z)) := by
  simp

private theorem sphericalPrincipalH_comp_E_eq (s : ℂ) :
    sphericalPrincipalH.comp (sphericalPrincipalE s) =
      (2 : ℂ) • sphericalPrincipalE s +
        (sphericalPrincipalE s).comp sphericalPrincipalH := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun T : Module.End ℂ SphericalKFiniteModel ↦ T v)
    (sphericalPrincipalH_comm_E s)
  have hv : sphericalPrincipalH (sphericalPrincipalE s v) -
      sphericalPrincipalE s (sphericalPrincipalH v) =
        (2 : ℂ) • sphericalPrincipalE s v := by
    simpa [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, two_smul] using h
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using
    (sub_eq_iff_eq_add.mp hv)

private theorem sphericalPrincipalH_comp_F_eq (s : ℂ) :
    sphericalPrincipalH.comp (sphericalPrincipalF s) =
      (-2 : ℂ) • sphericalPrincipalF s +
        (sphericalPrincipalF s).comp sphericalPrincipalH := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun T : Module.End ℂ SphericalKFiniteModel ↦ T v)
    (sphericalPrincipalH_comm_F s)
  have hv : sphericalPrincipalH (sphericalPrincipalF s v) -
      sphericalPrincipalF s (sphericalPrincipalH v) =
        (-2 : ℂ) • sphericalPrincipalF s v := by
    simpa [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, two_smul] using h
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using
    (sub_eq_iff_eq_add.mp hv)

private theorem sphericalPrincipalE_comp_F_eq (s : ℂ) :
    (sphericalPrincipalE s).comp (sphericalPrincipalF s) =
      sphericalPrincipalH + (sphericalPrincipalF s).comp (sphericalPrincipalE s) := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun T : Module.End ℂ SphericalKFiniteModel ↦ T v)
    (sphericalPrincipalE_comm_F s)
  have hv : sphericalPrincipalE s (sphericalPrincipalF s v) -
      sphericalPrincipalF s (sphericalPrincipalE s v) = sphericalPrincipalH v := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using h
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using (sub_eq_iff_eq_add.mp hv)

theorem compactSphericalPrincipalH_comm_E (s : ℝ) :
    (compactSphericalPrincipalH s).comp (compactSphericalPrincipalE s) =
      (2 : ℂ) • compactSphericalPrincipalE s +
        (compactSphericalPrincipalE s).comp (compactSphericalPrincipalH s) := by
  change
    ((sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH).comp
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalE (s : ℂ))) =
      (2 : ℂ) • (sphericalModelCompactKFiniteEquiv s).conj
          (sphericalPrincipalE (s : ℂ)) +
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalE (s : ℂ))).comp
          ((sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH)
  rw [← linearEquiv_conj_comp, ← map_smul, ← linearEquiv_conj_comp, ← map_add]
  congr 1
  exact sphericalPrincipalH_comp_E_eq (s : ℂ)

theorem compactSphericalPrincipalH_comm_F (s : ℝ) :
    (compactSphericalPrincipalH s).comp (compactSphericalPrincipalF s) =
      (-2 : ℂ) • compactSphericalPrincipalF s +
        (compactSphericalPrincipalF s).comp (compactSphericalPrincipalH s) := by
  change
    ((sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH).comp
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalF (s : ℂ))) =
      (-2 : ℂ) • (sphericalModelCompactKFiniteEquiv s).conj
          (sphericalPrincipalF (s : ℂ)) +
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalF (s : ℂ))).comp
          ((sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH)
  rw [← linearEquiv_conj_comp, ← map_smul, ← linearEquiv_conj_comp, ← map_add]
  congr 1
  exact sphericalPrincipalH_comp_F_eq (s : ℂ)

theorem compactSphericalPrincipalE_comm_F (s : ℝ) :
    (compactSphericalPrincipalE s).comp (compactSphericalPrincipalF s) =
      compactSphericalPrincipalH s +
        (compactSphericalPrincipalF s).comp (compactSphericalPrincipalE s) := by
  change
    ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalE (s : ℂ))).comp
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalF (s : ℂ))) =
      (sphericalModelCompactKFiniteEquiv s).conj sphericalPrincipalH +
        ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalF (s : ℂ))).comp
          ((sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalE (s : ℂ)))
  rw [← linearEquiv_conj_comp, ← linearEquiv_conj_comp, ← map_add]
  congr 1
  exact sphericalPrincipalE_comp_F_eq (s : ℂ)

/-- Casimir operator on finite compact-picture K-types. -/
def compactSphericalPrincipalCasimir (s : ℝ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj (sphericalPrincipalCasimir (s : ℂ))

/-- Compact-picture Casimir acts by scalar `s²/4`. -/
theorem compactSphericalPrincipalCasimir_eq_smul_id (s : ℝ) :
    compactSphericalPrincipalCasimir s = (((s : ℂ) ^ 2) / 4) • LinearMap.id := by
  rw [compactSphericalPrincipalCasimir, sphericalPrincipalCasimir_eq_smul_id,
    map_smul, linearEquiv_conj_id]

/-- Positive-Laplacian normalization on finite compact-picture K-types. -/
def compactSphericalPrincipalLaplacian (s : ℝ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj
    (sphericalPrincipalLaplacian (s : ℂ))

/-- Compact-picture shifted Casimir acts by `(1-s²)/4`. -/
theorem compactSphericalPrincipalLaplacian_eq_smul_id (s : ℝ) :
    compactSphericalPrincipalLaplacian s = ((1 - (s : ℂ) ^ 2) / 4) • LinearMap.id := by
  rw [compactSphericalPrincipalLaplacian, sphericalPrincipalLaplacian_eq_smul_id,
    map_smul, linearEquiv_conj_id]

end
end GaloisForLFunctions.RHTower
