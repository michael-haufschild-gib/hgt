/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Hasse detection for quadratic forms over number fields

When two is invertible, nondegeneracy of a finite-dimensional quadratic form is invariant under
field scalar extension. Thus it is detected at all completions of a number field and, in odd
characteristic, of a rational function field. Equality of fixed forms is likewise detected at
number-field completions. This is not a local-global classification theorem for quadratic forms up
to isometry.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The scalar extension of a quadratic form to a number-field completion. -/
noncomputable def numberFieldQuadraticFormBaseChange (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (p : NumberFieldPlace K) :
    QuadraticForm (completion K p) (completion K p ⊗[K] M) := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  exact Q.baseChange (completion K p)

/-- Field scalar extension reflects equality of quadratic forms when two is invertible. -/
theorem quadraticForm_eq_iff_baseChange_eq {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q₁ Q₂ : QuadraticForm K M) :
    Q₁ = Q₂ ↔ Q₁.baseChange L = Q₂.baseChange L := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext x
    apply FaithfulSMul.algebraMap_injective K L
    simpa [Algebra.smul_def] using congrArg (fun Q => Q (1 ⊗ₜ[K] x)) h

/-- Nondegeneracy of a quadratic form descends through field scalar extension when two is
invertible. -/
theorem quadraticForm_nondegenerate_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (h : (Q.baseChange L).Nondegenerate) : Q.Nondegenerate := by
  letI : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply QuadraticMap.nondegenerate_polar_iff.mp
  apply bilinForm_nondegenerate_of_baseChange (L := L) Q.polarBilin
  rw [← QuadraticForm.polarBilin_baseChange]
  exact QuadraticMap.nondegenerate_polar_iff.mpr h

/-- Nondegeneracy of a finite-dimensional quadratic form is preserved by field scalar extension
when two is invertible. -/
theorem quadraticForm_nondegenerate_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (h : Q.Nondegenerate) :
    (Q.baseChange L).Nondegenerate := by
  letI : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply QuadraticMap.nondegenerate_polar_iff.mp
  rw [QuadraticForm.polarBilin_baseChange]
  apply bilinForm_nondegenerate_baseChange Q.polarBilin
  exact QuadraticMap.nondegenerate_polar_iff.mpr h

/-- Nondegeneracy of a finite-dimensional quadratic form is detected by field scalar extension
when two is invertible. -/
theorem quadraticForm_nondegenerate_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    [FiniteDimensional K M] (Q : QuadraticForm K M) :
    Q.Nondegenerate ↔ (Q.baseChange L).Nondegenerate := by
  constructor
  · exact quadraticForm_nondegenerate_baseChange Q
  · exact quadraticForm_nondegenerate_of_baseChange Q

/-- Equality of quadratic forms over a number field is detected at every completed place. -/
theorem numberField_quadraticForm_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (Q₁ Q₂ : QuadraticForm K M) :
    Q₁ = Q₂ ↔ ∀ p : NumberFieldPlace K,
      numberFieldQuadraticFormBaseChange K Q₁ p = numberFieldQuadraticFormBaseChange K Q₂ p := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · intro h p
    rw [h]
  · intro h
    apply (quadraticForm_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) Q₁ Q₂).mpr
    simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- Equality of quadratic forms over `F(t)` is detected at every finite and infinite completed
place.  As for the number-field statement, this reflects equality of fixed forms rather than
local-global classification up to isometry. -/
theorem rationalFunction_quadraticForm_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q₁ Q₂ : QuadraticForm (RatFunc F) M) :
    Q₁ = Q₂ ↔ ∀ p : RationalFunctionPlace F,
      Q₁.baseChange (rationalFunctionCompletion F p) =
        Q₂.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (quadraticForm_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F p) Q₁ Q₂).mp h
  · intro h
    exact (quadraticForm_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) Q₁ Q₂).mpr (h .infinite)

/-- Nondegeneracy of a quadratic form over a number field follows when every completed base
change is nondegenerate. -/
theorem numberField_quadraticForm_nondegenerate_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    (h : ∀ p : NumberFieldPlace K, (numberFieldQuadraticFormBaseChange K Q p).Nondegenerate) :
    Q.Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  apply quadraticForm_nondegenerate_of_baseChange (L := completion K (witnessPlace K)) Q
  simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- Nondegeneracy of a finite-dimensional quadratic form over a number field is detected at every
completed place. -/
theorem numberField_quadraticForm_nondegenerate_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) :
    Q.Nondegenerate ↔ ∀ p : NumberFieldPlace K,
      (numberFieldQuadraticFormBaseChange K Q p).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · intro h p
    simpa only [numberFieldQuadraticFormBaseChange] using
      (quadraticForm_nondegenerate_iff_baseChange (L := completion K p) Q).mp h
  · intro h
    apply (quadraticForm_nondegenerate_iff_baseChange
      (L := completion K (witnessPlace K)) Q).mpr
    simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- The scalar extension of a quadratic form to a rational-function completion, when two is
invertible. -/
noncomputable def rationalFunctionQuadraticFormBaseChange (F : Type u) [Field F] [Finite F]
    [Invertible (2 : RatFunc F)] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (p : RationalFunctionPlace F) :
    QuadraticForm (rationalFunctionCompletion F p)
      (rationalFunctionCompletion F p ⊗[RatFunc F] M) :=
  Q.baseChange (rationalFunctionCompletion F p)

/-- Nondegeneracy of a finite-dimensional quadratic form over `F(t)` is detected at every finite
and infinite completed place whenever two is invertible in `F(t)`. -/
theorem rationalFunction_quadraticForm_nondegenerate_iff_forall_place (F : Type u)
    [Field F] [Finite F] [Invertible (2 : RatFunc F)] {M : Type w} [AddCommGroup M]
    [Module (RatFunc F) M] [FiniteDimensional (RatFunc F) M] (Q : QuadraticForm (RatFunc F) M) :
    Q.Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      (rationalFunctionQuadraticFormBaseChange F Q p).Nondegenerate := by
  constructor
  · intro h p
    simpa only [rationalFunctionQuadraticFormBaseChange] using
      (quadraticForm_nondegenerate_iff_baseChange
        (L := rationalFunctionCompletion F p) Q).mp h
  · intro h
    apply (quadraticForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) Q).mpr
    simpa only [rationalFunctionQuadraticFormBaseChange] using h .infinite

/-- Anisotropy of a quadratic form descends through field scalar extension when two is
invertible. -/
theorem quadraticForm_anisotropic_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (h : (Q.baseChange L).Anisotropic) : Q.Anisotropic := by
  intro x hx
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
  simp only [TensorProduct.mk_apply, TensorProduct.tmul_zero]
  apply h
  simp [QuadraticForm.baseChange_tmul, hx]

/-- A specified quadratic-form value vanishes exactly when its scalar extension at the pure
tensor `1 ⊗ x` vanishes. -/
theorem quadraticForm_apply_eq_zero_iff_baseChange_tmul
    {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (x : M) :
    Q x = 0 ↔ (Q.baseChange L) (1 ⊗ₜ[K] x) = 0 := by
  constructor
  · intro hx
    simp [QuadraticForm.baseChange_tmul, hx]
  · intro hx
    apply FaithfulSMul.algebraMap_injective K L
    simpa [QuadraticForm.baseChange_tmul] using hx

/-- The canonical pure-tensor image of a vector is nonzero exactly when the vector is nonzero. -/
theorem quadraticForm_tmul_ne_zero_iff
    {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] (x : M) :
    (1 ⊗ₜ[K] x : L ⊗[K] M) ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h hx
    apply h
    simp [hx]
  · intro h hzero
    apply h
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hzero

/-- A specified nonzero isotropic vector remains, and is reflected, after field scalar extension. -/
theorem quadraticForm_isotropicVector_iff_baseChange_tmul
    {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (x : M) :
    x ≠ 0 ∧ Q x = 0 ↔
      (1 ⊗ₜ[K] x : L ⊗[K] M) ≠ 0 ∧ (Q.baseChange L) (1 ⊗ₜ[K] x) = 0 := by
  rw [quadraticForm_tmul_ne_zero_iff (L := L),
    quadraticForm_apply_eq_zero_iff_baseChange_tmul (L := L)]

/-- Nonanisotropy persists under field scalar extension.  Equivalently, an isotropic vector over
the base field remains one after extension. -/
theorem quadraticForm_not_anisotropic_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) : ¬ Q.Anisotropic → ¬ (Q.baseChange L).Anisotropic := by
  intro h hL
  exact h (quadraticForm_anisotropic_of_baseChange Q hL)

/-- A prescribed quadratic-form value over a number field vanishes exactly when its images at all
completed places vanish. -/
theorem numberField_quadraticForm_apply_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (x : M) : Q x = 0 ↔
      ∀ p : NumberFieldPlace K, numberFieldQuadraticFormBaseChange K Q p
        (1 ⊗ₜ[K] x) = 0 := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · intro hx p
    exact (quadraticForm_apply_eq_zero_iff_baseChange_tmul
      (L := completion K p) Q x).mp hx
  · intro h
    exact (quadraticForm_apply_eq_zero_iff_baseChange_tmul
      (L := completion K (witnessPlace K)) Q x).mpr (by
        simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K))

/-- A fixed nonzero isotropic vector over a number field is exactly a vector whose image is
nonzero and isotropic at every completed place. -/
theorem numberField_quadraticForm_isotropicVector_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (x : M) : x ≠ 0 ∧ Q x = 0 ↔
      ∀ p : NumberFieldPlace K,
        (1 ⊗ₜ[K] x : completion K p ⊗[K] M) ≠ 0 ∧
          numberFieldQuadraticFormBaseChange K Q p (1 ⊗ₜ[K] x) = 0 := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · intro hx p
    exact (quadraticForm_isotropicVector_iff_baseChange_tmul
      (L := completion K p) Q x).mp hx
  · intro h
    exact (quadraticForm_isotropicVector_iff_baseChange_tmul
      (L := completion K (witnessPlace K)) Q x).mpr (by
        simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K))

/-- A quadratic form over a number field is anisotropic when every completed base change is
anisotropic.  In fact the proof uses one selected completion. -/
theorem numberField_quadraticForm_anisotropic_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    (h : ∀ p : NumberFieldPlace K, (numberFieldQuadraticFormBaseChange K Q p).Anisotropic) :
    Q.Anisotropic := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  apply quadraticForm_anisotropic_of_baseChange (L := completion K (witnessPlace K)) Q
  simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- A nonanisotropic quadratic form over a number field stays nonanisotropic at every completed
place.  This is the scalar-extension half of the local isotropy direction; its converse is the
substantive Hasse--Minkowski theorem. -/
theorem numberField_quadraticForm_not_anisotropic_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (h : ¬ Q.Anisotropic) :
    ∀ p : NumberFieldPlace K, ¬ (numberFieldQuadraticFormBaseChange K Q p).Anisotropic := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  intro p hp
  exact h (quadraticForm_anisotropic_of_baseChange Q (by
    simpa only [numberFieldQuadraticFormBaseChange] using hp))

/-- A prescribed quadratic-form value over `F(t)` vanishes exactly when it vanishes at every
finite and infinite completed place. -/
theorem rationalFunction_quadraticForm_apply_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) : Q x = 0 ↔
      ∀ p : RationalFunctionPlace F, rationalFunctionQuadraticFormBaseChange F Q p
        (1 ⊗ₜ[RatFunc F] x) = 0 := by
  constructor
  · intro hx p
    exact (quadraticForm_apply_eq_zero_iff_baseChange_tmul
      (L := rationalFunctionCompletion F p) Q x).mp hx
  · intro h
    exact (quadraticForm_apply_eq_zero_iff_baseChange_tmul
      (L := rationalFunctionCompletion F .infinite) Q x).mpr (by
        simpa only [rationalFunctionQuadraticFormBaseChange] using h .infinite)

/-- A fixed nonzero isotropic vector over `F(t)` is exactly a vector whose image is nonzero and
isotropic at every finite and infinite completed place. -/
theorem rationalFunction_quadraticForm_isotropicVector_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) : x ≠ 0 ∧ Q x = 0 ↔
      ∀ p : RationalFunctionPlace F,
        (1 ⊗ₜ[RatFunc F] x : rationalFunctionCompletion F p ⊗[RatFunc F] M) ≠ 0 ∧
          rationalFunctionQuadraticFormBaseChange F Q p (1 ⊗ₜ[RatFunc F] x) = 0 := by
  constructor
  · intro hx p
    exact (quadraticForm_isotropicVector_iff_baseChange_tmul
      (L := rationalFunctionCompletion F p) Q x).mp hx
  · intro h
    exact (quadraticForm_isotropicVector_iff_baseChange_tmul
      (L := rationalFunctionCompletion F .infinite) Q x).mpr (by
        simpa only [rationalFunctionQuadraticFormBaseChange] using h .infinite)

/-- A quadratic form over `F(t)` is anisotropic when every finite and infinite completed base
change is anisotropic.  The reverse implication is not asserted: scalar extension can create
isotropic vectors. -/
theorem rationalFunction_quadraticForm_anisotropic_of_forall_place (F : Type u)
    [Field F] [Finite F] [Invertible (2 : RatFunc F)] {M : Type w} [AddCommGroup M]
    [Module (RatFunc F) M] (Q : QuadraticForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (rationalFunctionQuadraticFormBaseChange F Q p).Anisotropic) : Q.Anisotropic := by
  apply quadraticForm_anisotropic_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) Q
  simpa only [rationalFunctionQuadraticFormBaseChange] using h RationalFunctionPlace.infinite

/-- A nonanisotropic quadratic form over `F(t)` stays nonanisotropic at every finite and infinite
completed place.  The converse is the global local-to-global isotropy question. -/
theorem rationalFunction_quadraticForm_not_anisotropic_of_forall_place (F : Type u)
    [Field F] [Finite F] [Invertible (2 : RatFunc F)] {M : Type w} [AddCommGroup M]
    [Module (RatFunc F) M] (Q : QuadraticForm (RatFunc F) M) (h : ¬ Q.Anisotropic) :
    ∀ p : RationalFunctionPlace F,
      ¬ (rationalFunctionQuadraticFormBaseChange F Q p).Anisotropic := by
  intro p hp
  exact h (quadraticForm_anisotropic_of_baseChange Q (by
    simpa only [rationalFunctionQuadraticFormBaseChange] using hp))

end GaloisForLFunctions.HTGeometry.ABHN
