import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PrimeRadialExcessDiscriminant

/-!
# Hasse reconstruction for the prime-radial Smith staircase

The prime-radial observer cokernel is a product of cyclic height-local quotients `R/(c^j)`.
Choosing the proved Smith equivalence turns this decomposition into a Hasse interface: every local
height packet has one global cokernel class, and vector representatives are unique modulo the
global Vandermonde range.
-/

namespace HTGeometry.ConstraintRelativity

open GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- Chosen Smith/Hasse equivalence from the global prime-radial cokernel to all height-local cyclic
quotients. -/
noncomputable def primeRadialHasseEquiv {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) :
    (((Fin N → R) ⧸ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin)
      ≃ₗ[R] ∀ j : Fin N, R ⧸ (Ideal.span {c ^ (j : ℕ)} : Submodule R R)) :=
  Classical.choice (primeRadial_cokernel_equiv c u hu)

/-- A global prime-radial cokernel class vanishes exactly when every height-local cyclic coordinate
vanishes. -/
theorem primeRadialHasseClass_eq_zero_iff {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i))
    (q : (Fin N → R) ⧸ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin) :
    q = 0 ↔ ∀ j, primeRadialHasseEquiv c u hu q j = 0 := by
  constructor
  · rintro rfl
    simp
  · intro hlocal
    apply (primeRadialHasseEquiv c u hu).injective
    rw [map_zero]
    funext j
    exact hlocal j

/-- Two global vectors represent the same prime-radial class exactly when all height-local cyclic
coordinates agree. -/
theorem primeRadial_congr_hasse_iff {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i)) (x y : Fin N → R) :
    (∀ j, primeRadialHasseEquiv c u hu (Submodule.Quotient.mk x) j =
        primeRadialHasseEquiv c u hu (Submodule.Quotient.mk y) j) ↔
      x - y ∈ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin := by
  let S := LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin
  constructor
  · intro hlocal
    have heq : primeRadialHasseEquiv c u hu (Submodule.Quotient.mk x) =
        primeRadialHasseEquiv c u hu (Submodule.Quotient.mk y) := funext hlocal
    have hquot : (Submodule.Quotient.mk x : (Fin N → R) ⧸ S) =
        Submodule.Quotient.mk y := (primeRadialHasseEquiv c u hu).injective heq
    exact (Submodule.Quotient.eq S).mp hquot
  · intro hxy
    have hquot : (Submodule.Quotient.mk x : (Fin N → R) ⧸ S) =
        Submodule.Quotient.mk y := (Submodule.Quotient.eq S).mpr hxy
    intro j
    rw [hquot]

/-- Every complete family of height-local cyclic classes has one unique global prime-radial
cokernel class. -/
theorem primeRadialHasse_existsUnique_globalClass {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i))
    (packet : ∀ j : Fin N, R ⧸ (Ideal.span {c ^ (j : ℕ)} : Submodule R R)) :
    ∃! q : (Fin N → R) ⧸ LinearMap.range
        (Matrix.vandermonde (contactSheets c u)).mulVecLin,
      primeRadialHasseEquiv c u hu q = packet := by
  refine ⟨(primeRadialHasseEquiv c u hu).symm packet, ?_, ?_⟩
  · exact (primeRadialHasseEquiv c u hu).apply_symm_apply packet
  · intro q hq
    apply (primeRadialHasseEquiv c u hu).injective
    rw [hq]
    exact ((primeRadialHasseEquiv c u hu).apply_symm_apply packet).symm

/-- Every height-local packet has a global vector representative, unique modulo the global
Vandermonde range. -/
theorem primeRadialHasse_exists_globalVector_unique_mod_range
    {N : ℕ} (c : R) (u : Fin N → R)
    (hu : ∀ i j : Fin N, i ≠ j → IsUnit (u j - u i))
    (packet : ∀ j : Fin N, R ⧸ (Ideal.span {c ^ (j : ℕ)} : Submodule R R)) :
    ∃ x : Fin N → R,
      primeRadialHasseEquiv c u hu (Submodule.Quotient.mk x) = packet ∧
      ∀ y : Fin N → R,
        primeRadialHasseEquiv c u hu (Submodule.Quotient.mk y) = packet ↔
          y - x ∈ LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin := by
  let S := LinearMap.range (Matrix.vandermonde (contactSheets c u)).mulVecLin
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective S
    ((primeRadialHasseEquiv c u hu).symm packet)
  refine ⟨x, ?_, fun y => ?_⟩
  · rw [hx]
    exact (primeRadialHasseEquiv c u hu).apply_symm_apply packet
  · constructor
    · intro hy
      have hq : (Submodule.Quotient.mk y : (Fin N → R) ⧸ S) =
          Submodule.Quotient.mk x := by
        apply (primeRadialHasseEquiv c u hu).injective
        rw [hy, hx]
        exact ((primeRadialHasseEquiv c u hu).apply_symm_apply packet).symm
      exact (Submodule.Quotient.eq S).mp hq
    · intro hyx
      have hq : (Submodule.Quotient.mk y : (Fin N → R) ⧸ S) =
          Submodule.Quotient.mk x := (Submodule.Quotient.eq S).mpr hyx
      rw [hq, hx]
      exact (primeRadialHasseEquiv c u hu).apply_symm_apply packet

end HTGeometry.ConstraintRelativity
