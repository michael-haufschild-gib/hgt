import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient

/-!
# Hasse classification of cyclic degree-two cohomology

For a finite cyclic Galois extension, every degree-two unit-cohomology class is represented by a
base-field unit, and two representatives agree exactly when their difference is a field norm.
This is the norm-quotient classification underlying cyclic algebras and local Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- The cyclic norm-quotient equivalence is induced by the base-unit cohomology projection. -/
@[simp] theorem cyclicGaloisH2BaseNormQuotientEquiv_hasse_mk (a : Additive Kˣ) :
    cyclicGaloisH2BaseNormQuotientEquiv K L (QuotientAddGroup.mk a) =
      cyclicGaloisH2BaseProjection K L a := by
  rfl

/-- Two base units represent the same cyclic degree-two class exactly when their difference is a
norm from the extension. -/
theorem cyclicGaloisH2BaseProjection_congr_hasse_iff (a b : Additive Kˣ) :
    a - b ∈ cyclicGaloisH2BaseNormImage K L ↔
      cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b := by
  rw [cyclicGaloisH2BaseNormImage_eq_ker K L]
  change cyclicGaloisH2BaseProjection K L (a - b) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every cyclic degree-two class has a base-unit representative, unique modulo field norms. -/
theorem cyclicGaloisH2_exists_unique_mod_norm (z : cyclicGaloisH2 K L) :
    ∃ a : Additive Kˣ,
      cyclicGaloisH2BaseProjection K L a = z ∧
      ∀ b : Additive Kˣ,
        cyclicGaloisH2BaseProjection K L b = z ↔
          b - a ∈ cyclicGaloisH2BaseNormImage K L := by
  obtain ⟨a, ha⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  refine ⟨a, ha, fun b => ?_⟩
  simpa only [ha] using (cyclicGaloisH2BaseProjection_congr_hasse_iff K L b a).symm

end GaloisForLFunctions.HTGeometry.ABHN
