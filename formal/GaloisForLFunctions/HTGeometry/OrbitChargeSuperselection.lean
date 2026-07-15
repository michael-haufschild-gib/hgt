import GaloisForLFunctions.HTGeometry.OrbitChargeExactSequence

/-!
# Multi-orbit topological superselection

A rational difference constraint may have defects on several disjoint translation orbits.  This
file takes the direct sum of the one-orbit exact sequences from `OrbitChargeExactSequence`.

For a finitely supported family of finite orbit data, `orbitwiseCharge` is the finitely supported
vector of component charges.  The theorem says that this vector is a complete invariant modulo
finite local shift boundaries: every datum is its charge vector concentrated at chosen origins,
plus an explicit boundary.  Thus the quotient by local gauges is the direct sum of the coefficient
group over orbit components.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Componentwise total charge of a finite family of finite translation-orbit data. -/
def orbitwiseCharge {ι A : Type*} [AddCommGroup A]
    (D : ι →₀ (ℤ →₀ A)) : ι →₀ A :=
  D.mapRange additiveOrbitSum (by simp)

/-- Componentwise cellular boundary.  It is the finite local gauge action on a disjoint union of
integer translation orbits. -/
def orbitwiseBoundary {ι A : Type*} [AddCommGroup A]
    (E : ι →₀ (ℤ →₀ A)) : ι →₀ (ℤ →₀ A) :=
  E.mapRange intOrbitCellularBoundary (by simp)

/-- Componentwise explicit path primitive. -/
def orbitwisePrimitive {ι A : Type*} [AddCommGroup A]
    (D : ι →₀ (ℤ →₀ A)) : ι →₀ (ℤ →₀ A) :=
  D.mapRange intOrbitPrimitive (by simp [intOrbitPrimitive])

/-- The canonical representative that concentrates each component charge at site `0`. -/
def orbitwiseChargeNormalForm {ι A : Type*} [AddCommGroup A]
    (D : ι →₀ (ℤ →₀ A)) : ι →₀ (ℤ →₀ A) :=
  (orbitwiseCharge D).mapRange (Finsupp.single 0) (by simp)

/-- Direct-sum chain contraction: the boundary of the componentwise primitive is the original
datum minus its canonical charge representative. -/
theorem orbitwiseBoundary_primitive
    {ι A : Type*} [AddCommGroup A] (D : ι →₀ (ℤ →₀ A)) :
    orbitwiseBoundary (orbitwisePrimitive D) =
      D - orbitwiseChargeNormalForm D := by
  ext i z
  simp [orbitwiseBoundary, orbitwisePrimitive, orbitwiseChargeNormalForm,
    orbitwiseCharge, intOrbitCellularBoundary_orbitPrimitive]

/-- Every finite local boundary has zero charge on every orbit component. -/
theorem orbitwiseCharge_boundary
    {ι A : Type*} [AddCommGroup A] (E : ι →₀ (ℤ →₀ A)) :
    orbitwiseCharge (orbitwiseBoundary E) = 0 := by
  ext i
  simp [orbitwiseCharge, orbitwiseBoundary, intOrbitCellularBoundary,
    additiveOrbitSum_sub, additiveOrbitSum_embDomain]

/-- Exactness for a disjoint finite family of translation orbits. -/
theorem orbitwiseCharge_eq_zero_iff_exists_boundary
    {ι A : Type*} [AddCommGroup A] (D : ι →₀ (ℤ →₀ A)) :
    orbitwiseCharge D = 0 ↔ ∃ E, D = orbitwiseBoundary E := by
  constructor
  · intro h
    refine ⟨orbitwisePrimitive D, ?_⟩
    have hnormal : orbitwiseChargeNormalForm D = 0 := by
      simp [orbitwiseChargeNormalForm, h]
    rw [orbitwiseBoundary_primitive, hnormal, sub_zero]
  · rintro ⟨E, rfl⟩
    exact orbitwiseCharge_boundary E

/-- Positive global normal form: every multi-orbit defect is its full charge vector plus a finite
local gauge boundary. -/
theorem orbitwiseData_charge_normalForm
    {ι A : Type*} [AddCommGroup A] (D : ι →₀ (ℤ →₀ A)) :
    ∃ E, D = orbitwiseChargeNormalForm D + orbitwiseBoundary E := by
  refine ⟨orbitwisePrimitive D, ?_⟩
  rw [orbitwiseBoundary_primitive]
  abel

/-- Componentwise charge respects subtraction of finite defect data. -/
theorem orbitwiseCharge_sub
    {ι A : Type*} [AddCommGroup A] (D F : ι →₀ (ℤ →₀ A)) :
    orbitwiseCharge (D - F) = orbitwiseCharge D - orbitwiseCharge F := by
  ext i
  simp [orbitwiseCharge, additiveOrbitSum_sub]

/-- Complete multi-orbit superselection law: two finite data are related by local shift gauges
exactly when their entire finitely supported charge vectors agree. -/
theorem orbitwiseData_sameCharge_iff_boundary
    {ι A : Type*} [AddCommGroup A] (D F : ι →₀ (ℤ →₀ A)) :
    orbitwiseCharge D = orbitwiseCharge F ↔
      ∃ E, D - F = orbitwiseBoundary E := by
  rw [← sub_eq_zero, ← orbitwiseCharge_sub]
  exact orbitwiseCharge_eq_zero_iff_exists_boundary (D - F)

end

end GaloisForLFunctions
