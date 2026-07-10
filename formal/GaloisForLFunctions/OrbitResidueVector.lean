import GaloisForLFunctions.OrbitBalance
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# Orbit-residue vectors for finite principal-part data

For a translation by `q` on an additive group `G`, the orbit space is
`G / ℤq`.  Pushing a finitely supported coefficient field to this quotient records the sum of its
coefficients on every translation orbit.  Translation preserves this vector, so every finite
translation coboundary has zero orbit-residue vector.  A lone nonzero coefficient, or two opposite
coefficients on distinct orbits, is therefore not a coboundary.

This is the coefficient-valued multi-orbit strengthening of `OrbitBalance`.  Taking the
coefficients to be a fixed Laurent principal-part coefficient gives the algebraic obstruction used
in elliptic rational summability.
-/

namespace GaloisForLFunctions
noncomputable section

/-- The sum of finite coefficient data on every orbit of translation by `q`. -/
def orbitResidueVector
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q : G) (D : G →₀ A) : (G ⧸ AddSubgroup.zmultiples q) →₀ A :=
  Finsupp.mapDomain (fun x : G => (x : G ⧸ AddSubgroup.zmultiples q)) D

/-- Translation of finitely supported coefficient data. -/
def translateFiniteSupport
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q : G) (D : G →₀ A) : G →₀ A :=
  Finsupp.mapDomain (fun x => x + q) D

/-- Orbit-residue vectors are invariant under translation. -/
theorem orbitResidueVector_translate
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q : G) (D : G →₀ A) :
    orbitResidueVector q (translateFiniteSupport q D) = orbitResidueVector q D := by
  rw [orbitResidueVector, translateFiniteSupport, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro x _
  change ((x + q : G) : G ⧸ AddSubgroup.zmultiples q) =
    (x : G ⧸ AddSubgroup.zmultiples q)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp

/-- The finite coefficient coboundary for translation by `q`. -/
def finiteOrbitCoboundary
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q : G) (D : G →₀ A) : G →₀ A :=
  translateFiniteSupport q D - D

/-- Every finite translation coboundary has zero residue on every orbit. -/
theorem orbitResidueVector_finiteOrbitCoboundary
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q : G) (D : G →₀ A) :
    orbitResidueVector q (finiteOrbitCoboundary q D) = 0 := by
  rw [finiteOrbitCoboundary, orbitResidueVector, Finsupp.mapDomain_sub,
    ← orbitResidueVector, ← orbitResidueVector, orbitResidueVector_translate, sub_self]

@[simp] theorem orbitResidueVector_single
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q x : G) (c : A) :
    orbitResidueVector q (Finsupp.single x c) =
      Finsupp.single (x : G ⧸ AddSubgroup.zmultiples q) c := by
  simp [orbitResidueVector]

/-- A lone nonzero principal-part coefficient on one orbit cannot be a finite translation
coboundary. -/
theorem single_ne_finiteOrbitCoboundary
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q x : G) {c : A} (hc : c ≠ 0) (E : G →₀ A) :
    Finsupp.single x c ≠ finiteOrbitCoboundary q E := by
  intro h
  have hv := congrArg (orbitResidueVector q) h
  rw [orbitResidueVector_single, orbitResidueVector_finiteOrbitCoboundary] at hv
  exact (Finsupp.single_ne_zero.mpr hc) hv

theorem orbitResidueVector_single_sub_single
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q x y : G) (c : A) :
    orbitResidueVector q (Finsupp.single x c - Finsupp.single y c) =
      Finsupp.single (x : G ⧸ AddSubgroup.zmultiples q) c -
        Finsupp.single (y : G ⧸ AddSubgroup.zmultiples q) c := by
  simp [orbitResidueVector, Finsupp.mapDomain_sub]

/-- Two opposite nonzero principal-part coefficients on distinct translation orbits cannot form a
finite translation coboundary. -/
theorem single_sub_single_ne_finiteOrbitCoboundary_of_orbit_ne
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (q x y : G) {c : A} (hc : c ≠ 0)
    (hxy : (x : G ⧸ AddSubgroup.zmultiples q) ≠
      (y : G ⧸ AddSubgroup.zmultiples q))
    (E : G →₀ A) :
    Finsupp.single x c - Finsupp.single y c ≠ finiteOrbitCoboundary q E := by
  classical
  intro h
  have hv := congrArg (orbitResidueVector q) h
  rw [orbitResidueVector_single_sub_single,
    orbitResidueVector_finiteOrbitCoboundary] at hv
  have heval := congrArg
    (fun D : (G ⧸ AddSubgroup.zmultiples q) →₀ A =>
      D (x : G ⧸ AddSubgroup.zmultiples q)) hv
  simp [hxy, hc] at heval

end
end GaloisForLFunctions
