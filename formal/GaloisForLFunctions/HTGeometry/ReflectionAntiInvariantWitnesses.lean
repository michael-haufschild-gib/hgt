import GaloisForLFunctions.HTGeometry.ReflectionTateAnomaly

/-!
# Realizations of the reflection anti-invariance interface

Anti-invariance is realized by the zero vector, by every vector of the total reflection `-id`, and —
for any involution — by the anti-symmetric part `v - C v` of an arbitrary vector.  It is a linear
condition, so anti-invariant vectors form the kernel of `C + id` and are closed under sums and
scalars.

Consequently the characteristic-zero averaging firewall applies to the anti-symmetric part of every
vector with no interface premise.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## Realizations -/

theorem linearReflectionAntiInvariant_zero (C : V →ₗ[K] V) :
    LinearReflectionAntiInvariant C (0 : V) := by
  simp [LinearReflectionAntiInvariant]

/-- Every vector is anti-invariant for the total reflection. -/
theorem linearReflectionAntiInvariant_neg_id (v : V) :
    LinearReflectionAntiInvariant (-LinearMap.id : V →ₗ[K] V) v := by
  simp [LinearReflectionAntiInvariant]

/-- **Anti-symmetric part.**  For an involution the displacement `v - C v` is anti-invariant. -/
theorem linearReflectionAntiInvariant_sub_apply (C : V →ₗ[K] V)
    (hC : ∀ x, C (C x) = x) (v : V) :
    LinearReflectionAntiInvariant C (v - C v) := by
  unfold LinearReflectionAntiInvariant
  rw [map_sub, hC]
  abel

theorem linearReflectionAntiInvariant_smul (C : V →ₗ[K] V) {v : V}
    (hv : LinearReflectionAntiInvariant C v) (c : K) :
    LinearReflectionAntiInvariant C (c • v) := by
  unfold LinearReflectionAntiInvariant at hv ⊢
  rw [map_smul, hv, smul_neg]

theorem linearReflectionAntiInvariant_add (C : V →ₗ[K] V) {v w : V}
    (hv : LinearReflectionAntiInvariant C v) (hw : LinearReflectionAntiInvariant C w) :
    LinearReflectionAntiInvariant C (v + w) := by
  unfold LinearReflectionAntiInvariant at hv hw ⊢
  rw [map_add, hv, hw, neg_add]

/-- Anti-invariance is membership in the kernel of `C + id`. -/
theorem linearReflectionAntiInvariant_iff_mem_ker (C : V →ₗ[K] V) (v : V) :
    LinearReflectionAntiInvariant C v ↔ v ∈ LinearMap.ker (C + LinearMap.id) := by
  unfold LinearReflectionAntiInvariant
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    simp [h]
  · intro h
    have h' : C v + v = 0 := by simpa using h
    linear_combination (norm := module) h'

/-! ## The firewall with no interface premise -/

section CharZero

variable [CharZero K]

/-- **Averaging firewall on anti-symmetric parts.**  For an involution the anti-symmetric part of
every vector is an unrestricted reflection boundary. -/
theorem exists_relativeReflectionBoundary_sub_apply (C : V →ₗ[K] V)
    (hC : ∀ x, C (C x) = x) (v : V) :
    ∃ g : V, relativeReflectionBoundary C g = v - C v :=
  linearReflectionAntiInvariant_is_boundary C
    (linearReflectionAntiInvariant_sub_apply C hC v)

/-- The canonical primitive of an anti-symmetric part, explicitly. -/
theorem relativeReflectionBoundary_canonical_sub_apply (C : V →ₗ[K] V)
    (hC : ∀ x, C (C x) = x) (v : V) :
    relativeReflectionBoundary C
        (canonicalReflectionPrimitive (K := K) (v - C v)) = v - C v :=
  relativeReflectionBoundary_canonical (K := K) C
    (linearReflectionAntiInvariant_sub_apply C hC v)

/-- **Restricted-gauge criterion on anti-symmetric parts.**  For a reflection-stable admissible
subspace the anti-symmetric part of a vector has an admissible primitive exactly when it is itself
admissible. -/
theorem relativeReflectionBoundary_sub_apply_iff_mem (C : V →ₗ[K] V)
    (hC : ∀ x, C (C x) = x) (D : Submodule K V)
    (hstable : ∀ g ∈ D, C g ∈ D) (v : V) :
    (∃ g : V, g ∈ D ∧ relativeReflectionBoundary C g = v - C v) ↔ v - C v ∈ D :=
  linearReflectionAntiInvariant_relativeBoundary_iff_mem C D hstable
    (linearReflectionAntiInvariant_sub_apply C hC v)

end CharZero

end GaloisForLFunctions.HTGeometry
