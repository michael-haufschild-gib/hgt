import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners

/-!
# Hasse detection of zero divisors in central simple algebras

Left and right zero-divisor conditions are nonzero-kernel statements for multiplication.  They are
therefore reflected by field scalar extension, and over the supported global fields they are
detected at every completion.  This concerns a fixed global element; it does not construct a
global element from independently specified local zero divisors.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A nonzero left annihilator exists exactly when one exists after field scalar extension. -/
theorem scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∃ z, z ≠ 0 ∧
      scalarExtensionMap (L := L) A a * z = 0 := by
  simpa using scalarExtensionMap_exists_nonzero_intertwiner_iff (L := L) A a 0

/-- A nonzero right annihilator exists exactly when one exists after field scalar extension. -/
theorem scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∃ z, z ≠ 0 ∧
      z * scalarExtensionMap (L := L) A a = 0 := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨z, hz0, hz⟩ :=
      (scalarExtensionMap_exists_nonzero_intertwiner_iff (L := L) A 0 a).mp
        ⟨x, hx0, by simpa using hx.symm⟩
    exact ⟨z, hz0, by simpa using hz.symm⟩
  · rintro ⟨z, hz0, hz⟩
    obtain ⟨x, hx0, hx⟩ :=
      (scalarExtensionMap_exists_nonzero_intertwiner_iff (L := L) A 0 a).mpr
        ⟨z, hz0, by simpa using hz.symm⟩
    exact ⟨x, hx0, by simpa using hx.symm⟩

/-- A global element of a number-field central simple algebra has a nonzero left annihilator
exactly when every completed scalar extension has one. -/
theorem numberField_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p A a * z = 0 := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := completion K (witnessPlace K)) A a).mpr (h (witnessPlace K))

/-- A global element of a number-field central simple algebra has a nonzero right annihilator
exactly when every completed scalar extension has one. -/
theorem numberField_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p A a = 0 := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := completion K (witnessPlace K)) A a).mpr (h (witnessPlace K))

/-- A global element of an `F(t)` central simple algebra has a nonzero left annihilator exactly
when every finite and infinite completed scalar extension has one. -/
theorem rationalFunction_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p A a * z = 0 := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := rationalFunctionCompletion F .infinite) A a).mpr (h .infinite)

/-- A global element of an `F(t)` central simple algebra has a nonzero right annihilator exactly
when every finite and infinite completed scalar extension has one. -/
theorem rationalFunction_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p A a = 0 := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := rationalFunctionCompletion F .infinite) A a).mpr (h .infinite)

/-- A nonzero left annihilator of a number-field CSA element is detected at one completion. -/
theorem numberField_exists_nonzero_mulLeft_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∃ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p A a * z = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
        (L := completion K (witnessPlace K)) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := completion K p) A a).mpr hp

/-- A nonzero right annihilator of a number-field CSA element is detected at one completion. -/
theorem numberField_exists_nonzero_mulRight_eq_zero_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∃ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p A a = 0 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
        (L := completion K (witnessPlace K)) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := completion K p) A a).mpr hp

/-- A nonzero left annihilator of a rational-function-field CSA element is detected at one finite
or infinite completion. -/
theorem rationalFunction_exists_nonzero_mulLeft_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = 0) ↔ ∃ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p A a * z = 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
        (L := rationalFunctionCompletion F .infinite) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
      (L := rationalFunctionCompletion F p) A a).mpr hp

/-- A nonzero right annihilator of a rational-function-field CSA element is detected at one
finite or infinite completion. -/
theorem rationalFunction_exists_nonzero_mulRight_eq_zero_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (∃ x, x ≠ 0 ∧ x * a = 0) ↔ ∃ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p A a = 0 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
        (L := rationalFunctionCompletion F .infinite) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
      (L := rationalFunctionCompletion F p) A a).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
