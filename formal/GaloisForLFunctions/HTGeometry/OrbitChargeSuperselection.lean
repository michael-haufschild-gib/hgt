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

/-- Total orbit charge as an additive homomorphism. -/
def additiveOrbitSumHom {ι A : Type*} [AddCommGroup A] : (ι →₀ A) →+ A where
  toFun := additiveOrbitSum
  map_zero' := additiveOrbitSum_zero
  map_add' := additiveOrbitSum_add

@[simp]
theorem additiveOrbitSumHom_apply {ι A : Type*} [AddCommGroup A] (D : ι →₀ A) :
    additiveOrbitSumHom D = additiveOrbitSum D := rfl

/-- Componentwise charge as a surjective additive homomorphism. -/
def orbitwiseChargeHom {ι A : Type*} [AddCommGroup A] :
    (ι →₀ (ℤ →₀ A)) →+ (ι →₀ A) :=
  Finsupp.mapRange.addMonoidHom additiveOrbitSumHom

@[simp]
theorem orbitwiseChargeHom_apply {ι A : Type*} [AddCommGroup A]
    (D : ι →₀ (ℤ →₀ A)) : orbitwiseChargeHom D = orbitwiseCharge D := rfl

/-- Componentwise cellular boundary as an additive endomorphism. -/
def orbitwiseBoundaryHom {ι A : Type*} [AddCommGroup A] :
    (ι →₀ (ℤ →₀ A)) →+ (ι →₀ (ℤ →₀ A)) :=
  Finsupp.mapRange.addMonoidHom intOrbitCellularBoundary

@[simp]
theorem orbitwiseBoundaryHom_apply {ι A : Type*} [AddCommGroup A]
    (E : ι →₀ (ℤ →₀ A)) : orbitwiseBoundaryHom E = orbitwiseBoundary E := rfl

/-- The subgroup of finite local shift boundaries. -/
def orbitwiseBoundaries {ι A : Type*} [AddCommGroup A] :
    AddSubgroup (ι →₀ (ℤ →₀ A)) :=
  (orbitwiseBoundaryHom (ι := ι) (A := A)).range

/-- Exactness packaged as equality between boundaries and the charge kernel. -/
theorem orbitwiseBoundaries_eq_chargeKer {ι A : Type*} [AddCommGroup A] :
    orbitwiseBoundaries (ι := ι) (A := A) =
      (orbitwiseChargeHom (ι := ι) (A := A)).ker := by
  ext D
  constructor
  · rintro ⟨E, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact orbitwiseCharge_boundary E
  · intro hD
    rw [AddMonoidHom.mem_ker] at hD
    obtain ⟨E, hE⟩ := (orbitwiseCharge_eq_zero_iff_exists_boundary D).mp hD
    exact ⟨E, hE.symm⟩

/-- Every finitely supported charge vector has a canonical origin-supported representative. -/
theorem orbitwiseChargeHom_surjective {ι A : Type*} [AddCommGroup A] :
    Function.Surjective (orbitwiseChargeHom (ι := ι) (A := A)) := by
  intro q
  refine ⟨q.mapRange (Finsupp.single (0 : ℤ)) (by simp), ?_⟩
  ext i
  simp [orbitwiseChargeHom, additiveOrbitSumHom]

/-- Multi-orbit defect data modulo finite local gauges. -/
abbrev OrbitChargeQuotient (ι A : Type*) [AddCommGroup A] :=
  (ι →₀ (ℤ →₀ A)) ⧸ orbitwiseBoundaries (ι := ι) (A := A)

/-- The literal quotient by local gauges is the direct sum of component charges. -/
noncomputable def orbitChargeQuotientEquiv {ι A : Type*} [AddCommGroup A] :
    OrbitChargeQuotient ι A ≃+ (ι →₀ A) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (orbitwiseBoundaries_eq_chargeKer (ι := ι) (A := A))).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (orbitwiseChargeHom (ι := ι) (A := A))
      (orbitwiseChargeHom_surjective (ι := ι) (A := A)))

end

end GaloisForLFunctions
