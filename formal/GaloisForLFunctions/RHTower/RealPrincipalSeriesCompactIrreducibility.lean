import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactHarishChandra
import GaloisForLFunctions.RHTower.RealSphericalIrreducibility

/-!
# Irreducibility in the compact principal-series picture

The complementary-series irreducibility theorem is transferred to the normalized finite
compact-picture subspace.  Compact K-type projections are defined on the actual Fourier-function
model, and closure under those projections and the transported raising/lowering operators admits
no proper nonzero submodule for `|s| < 1`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Projection onto one spherical weight in the finite-support model. -/
def sphericalKTypeProjection (m : ℤ) : Module.End ℂ SphericalKFiniteModel where
  toFun v := Finsupp.single m (v m)
  map_add' v w := by
    ext j
    by_cases h : m = j <;> simp [h]
  map_smul' c v := by
    ext j
    by_cases h : m = j <;> simp [h]

/-- Projection onto one even Fourier K-type in the normalized compact picture. -/
def compactSphericalKTypeProjection (s : ℝ) (m : ℤ) :
    Module.End ℂ (normalizedRealCompactKFiniteSubmodule s) :=
  (sphericalModelCompactKFiniteEquiv s).conj (sphericalKTypeProjection m)

@[simp]
theorem compactSphericalKTypeProjection_equiv_apply (s : ℝ) (m : ℤ)
    (v : SphericalKFiniteModel) :
    compactSphericalKTypeProjection s m (sphericalModelCompactKFiniteEquiv s v) =
      sphericalModelCompactKFiniteEquiv s (Finsupp.single m (v m)) := by
  simp [compactSphericalKTypeProjection, sphericalKTypeProjection,
    LinearEquiv.conj_apply]

/-- A `(g,K)`-submodule inside the finite compact-picture principal series. -/
def IsCompactSphericalHarishChandraSubmodule (s : ℝ)
    (W : Submodule ℂ (normalizedRealCompactKFiniteSubmodule s)) : Prop :=
  (∀ v ∈ W, ∀ m : ℤ, compactSphericalKTypeProjection s m v ∈ W) ∧
    (∀ v ∈ W, compactSphericalPrincipalE s v ∈ W) ∧
      ∀ v ∈ W, compactSphericalPrincipalF s v ∈ W

theorem isSphericalHarishChandraSubmodule_comap_compact
    (s : ℝ) (W : Submodule ℂ (normalizedRealCompactKFiniteSubmodule s))
    (hW : IsCompactSphericalHarishChandraSubmodule s W) :
    IsSphericalHarishChandraSubmodule s
      (W.comap (sphericalModelCompactKFiniteEquiv s).toLinearMap) := by
  constructor
  · intro v hv m
    change sphericalModelCompactKFiniteEquiv s (Finsupp.single m (v m)) ∈ W
    simpa using hW.1 (sphericalModelCompactKFiniteEquiv s v) hv m
  constructor
  · intro v hv
    change sphericalModelCompactKFiniteEquiv s (sphericalPrincipalE (s : ℂ) v) ∈ W
    simpa using hW.2.1 (sphericalModelCompactKFiniteEquiv s v) hv
  · intro v hv
    change sphericalModelCompactKFiniteEquiv s (sphericalPrincipalF (s : ℂ) v) ∈ W
    simpa using hW.2.2 (sphericalModelCompactKFiniteEquiv s v) hv

/-- The normalized finite compact-picture Harish-Chandra module is irreducible throughout the
complementary interval. -/
theorem compactSphericalPrincipal_irreducible_of_abs_lt_one (s : ℝ) (hs : |s| < 1) :
    ∀ W : Submodule ℂ (normalizedRealCompactKFiniteSubmodule s),
      IsCompactSphericalHarishChandraSubmodule s W → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  rcases sphericalPrincipal_irreducible_of_abs_lt_one s hs
      (W.comap (sphericalModelCompactKFiniteEquiv s).toLinearMap)
      (isSphericalHarishChandraSubmodule_comap_compact s W hW) with hbot | htop
  · left
    calc
      W = (Submodule.orderIsoMapComap (sphericalModelCompactKFiniteEquiv s))
          (W.comap (sphericalModelCompactKFiniteEquiv s).toLinearMap) := by
        exact (Submodule.map_comap_eq_of_surjective
          (sphericalModelCompactKFiniteEquiv s).surjective W).symm
      _ = (Submodule.orderIsoMapComap (sphericalModelCompactKFiniteEquiv s)) ⊥ := by
        rw [hbot]
      _ = ⊥ := by simp
  · right
    calc
      W = (Submodule.orderIsoMapComap (sphericalModelCompactKFiniteEquiv s))
          (W.comap (sphericalModelCompactKFiniteEquiv s).toLinearMap) := by
        exact (Submodule.map_comap_eq_of_surjective
          (sphericalModelCompactKFiniteEquiv s).surjective W).symm
      _ = (Submodule.orderIsoMapComap (sphericalModelCompactKFiniteEquiv s)) ⊤ := by
        rw [htop]
      _ = ⊤ := by simp

end
end GaloisForLFunctions.RHTower
