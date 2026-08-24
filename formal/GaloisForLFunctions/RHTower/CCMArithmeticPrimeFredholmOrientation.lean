import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.HTGeometry.ConstitutiveBalancedDefectZeroIndex
import GaloisForLFunctions.HTGeometry.UnboundedFredholm
import GaloisForLFunctions.RHTower.CCMConnesConsaniArithmeticJacobianPrimeFibre

/-!
# Arithmetic-prime Fredholm orientation

The literal Connes--Consani prime fibre has cyclic deck generator
`(Frob_p, log p)`.  A nonzero character of this deck direction supplies an
integer grade before any zeta or Xi datum is mentioned.  Hardy polarization
sends that grade to a signed unilateral Toeplitz operator on the complete
space `ℓ²(ℕ)`.

This module proves that the resulting full-domain operator is Fredholm, its
actual kernel-minus-cokernel index is the negative character grade, deck
duality is Hilbert adjoint and reverses both index and horizontal orientation,
and no compact perturbation can erase a nonzero class by making the operator
invertible.  Thus the signed distinction survives infinite completion without
using a zero location.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open Module

noncomputable section

/-! ## Signed Toeplitz Fredholm infrastructure -/

/-- Hardy-polarized Toeplitz operator of integer character grade `m`.
Nonnegative grades use the forward shift; negative grades use its adjoint. -/
def signedToeplitzOp (m : ℤ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  if 0 ≤ m then shiftOp m.natAbs else backOp m.natAbs

/-- Full-domain partial-map presentation used by the unbounded Fredholm API. -/
def signedToeplitzPMap (m : ℤ) : ToeplitzSpace →ₗ.[ℂ] ToeplitzSpace :=
  (signedToeplitzOp m).toLinearMap.toPMap ⊤

/-- Kernel of an everywhere-defined partial map is the ordinary kernel. -/
theorem kernel_toPMap_top
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ[ℂ] F) :
    LinearPMap.kernel (T.toPMap ⊤) = LinearMap.ker T := by
  ext x
  rw [LinearPMap.mem_kernel_iff]
  constructor
  · rintro ⟨_, hx⟩
    simpa using hx
  · intro hx
    exact ⟨Submodule.mem_top, by simpa using hx⟩

/-- Range of an everywhere-defined partial map is the ordinary range. -/
theorem rangeSubmodule_toPMap_top
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ[ℂ] F) :
    LinearPMap.rangeSubmodule (T.toPMap ⊤) = LinearMap.range T := by
  ext y
  rw [LinearPMap.mem_rangeSubmodule_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, Submodule.mem_top⟩, by simp⟩

/-- The shift range is closed because it is the kernel of its bounded defect
projection. -/
theorem isClosed_range_shiftOp (n : ℕ) :
    IsClosed ((LinearMap.range (shiftOp n).toLinearMap :
      Submodule ℂ ToeplitzSpace) : Set ToeplitzSpace) := by
  have hker : LinearMap.ker (defectMap n) =
      LinearMap.ker (defectOp n).toLinearMap := by
    ext f
    constructor <;> intro hf
    · simpa [defectMap] using congrArg Subtype.val hf
    · apply Subtype.ext
      simpa [defectMap] using hf
  rw [range_shiftOp, hker]
  exact (defectOp n).isClosed_ker

/-- Every forward shift is Fredholm on the actual infinite Hardy completion. -/
theorem shiftPMap_isFredholm (n : ℕ) :
    ((shiftOp n).toLinearMap.toPMap ⊤).IsFredholm where
  finiteDimensional_kernel := by
    rw [kernel_toPMap_top, ker_shiftOp]
    infer_instance
  isClosed_range := by
    rw [rangeSubmodule_toPMap_top]
    exact isClosed_range_shiftOp n
  finiteDimensional_cokernel := by
    rw [rangeSubmodule_toPMap_top]
    letI : FiniteDimensional ℂ (defectSubmodule n) :=
      (defectCoordEquiv n).symm.finiteDimensional
    exact (cokerShiftEquiv n).symm.finiteDimensional

/-- Every backward shift is Fredholm; its kernel is the finite Hardy defect
and its range is all of the completed space. -/
theorem backPMap_isFredholm (n : ℕ) :
    ((backOp n).toLinearMap.toPMap ⊤).IsFredholm where
  finiteDimensional_kernel := by
    rw [kernel_toPMap_top, ker_backOp]
    exact (defectCoordEquiv n).symm.finiteDimensional
  isClosed_range := by
    rw [rangeSubmodule_toPMap_top,
      LinearMap.range_eq_top.mpr (backOp_surjective n)]
    exact isClosed_univ
  finiteDimensional_cokernel := by
    rw [rangeSubmodule_toPMap_top,
      LinearMap.range_eq_top.mpr (backOp_surjective n)]
    infer_instance

/-- Forward-shift index computed through the actual `LinearPMap` Fredholm
definition. -/
theorem index_shiftPMap (n : ℕ) :
    LinearPMap.index ((shiftOp n).toLinearMap.toPMap ⊤) = -(n : ℤ) := by
  rw [LinearPMap.index_eq, kernel_toPMap_top, rangeSubmodule_toPMap_top,
    finrank_ker_shiftOp, finrank_coker_shiftOp]
  simp

/-- Backward-shift index computed through the actual `LinearPMap` Fredholm
definition. -/
theorem index_backPMap (n : ℕ) :
    LinearPMap.index ((backOp n).toLinearMap.toPMap ⊤) = (n : ℤ) := by
  rw [LinearPMap.index_eq, kernel_toPMap_top, rangeSubmodule_toPMap_top,
    ker_backOp, finrank_defectSubmodule,
    LinearMap.range_eq_top.mpr (backOp_surjective n)]
  rw [Module.finrank_zero_of_subsingleton]
  simp

/-- The integer-graded Toeplitz operator is Fredholm for every grade. -/
theorem signedToeplitzPMap_isFredholm (m : ℤ) :
    (signedToeplitzPMap m).IsFredholm := by
  by_cases hm : 0 ≤ m
  · simpa [signedToeplitzPMap, signedToeplitzOp, hm] using
      shiftPMap_isFredholm m.natAbs
  · simpa [signedToeplitzPMap, signedToeplitzOp, hm] using
      backPMap_isFredholm m.natAbs

/-- Literal Fredholm index of the signed Hardy-polarized character. -/
def signedToeplitzIndex (m : ℤ) : ℤ :=
  LinearPMap.index (signedToeplitzPMap m)

/-- Polarization converts character grade `m` into Fredholm index `-m`. -/
theorem signedToeplitzIndex_eq (m : ℤ) : signedToeplitzIndex m = -m := by
  by_cases hm : 0 ≤ m
  · rw [signedToeplitzIndex, signedToeplitzPMap, signedToeplitzOp, if_pos hm,
      index_shiftPMap]
    simp [Int.natAbs_of_nonneg hm]
  · have hm' : m ≤ 0 := le_of_not_ge hm
    rw [signedToeplitzIndex, signedToeplitzPMap, signedToeplitzOp, if_neg hm,
      index_backPMap]
    exact Int.ofNat_natAbs_of_nonpos hm'

/-- Character duality is exactly Hilbert adjoint after Hardy polarization. -/
theorem signedToeplitzOp_neg (m : ℤ) :
    signedToeplitzOp (-m) = ContinuousLinearMap.adjoint (signedToeplitzOp m) := by
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hmn : ¬ 0 ≤ m := not_le.mpr hm
    have hneg : 0 ≤ -m := neg_nonneg.mpr hm.le
    rw [signedToeplitzOp, signedToeplitzOp, if_neg hmn, if_pos hneg,
      adjoint_backOp]
    simp
  · rw [signedToeplitzOp, signedToeplitzOp, if_pos (le_refl 0),
      adjoint_shiftOp]
    rfl
  · have hm0 : 0 ≤ m := hm.le
    have hneg : ¬ 0 ≤ -m := not_le.mpr (neg_neg_of_pos hm)
    rw [signedToeplitzOp, signedToeplitzOp, if_pos hm0, if_neg hneg,
      adjoint_shiftOp]
    simp

/-- No invertible bounded operator is compactly equivalent to a nonzero
signed Toeplitz character.  This is the required infinite-completion index
stability statement. -/
theorem signedToeplitz_no_invertible_compact_perturbation
    (m : {m : ℤ // m ≠ 0})
    (U : ToeplitzSpace →L[ℂ] ToeplitzSpace)
    (hU : Function.Bijective U) :
    ¬ IsCompactOperator (U - signedToeplitzOp m) := by
  intro hcomp
  rcases lt_or_gt_of_ne m.property with hm | hm
  · have hdef : signedToeplitzOp (m : ℤ) = backOp m.val.natAbs := by
      rw [signedToeplitzOp, if_neg (not_le.mpr hm)]
    rw [hdef] at hcomp
    have hcompAdj : IsCompactOperator
        (ContinuousLinearMap.adjoint U - shiftOp m.val.natAbs) := by
      have h := isCompactOperator_adjoint_rectangular (U - backOp m.val.natAbs) hcomp
      simpa only [map_sub, adjoint_backOp] using h
    have hUunit : IsUnit U :=
      (ContinuousLinearMap.isUnit_iff_bijective).2 hU
    have hUadj : Function.Bijective (ContinuousLinearMap.adjoint U) :=
      (ContinuousLinearMap.isUnit_iff_bijective).1 hUunit.star
    exact no_invertible_compact_perturbation (Int.natAbs_pos.mpr m.property)
      (ContinuousLinearMap.adjoint U) hUadj hcompAdj
  · have hdef : signedToeplitzOp (m : ℤ) = shiftOp m.val.natAbs := by
      rw [signedToeplitzOp, if_pos hm.le]
    rw [hdef] at hcomp
    exact no_invertible_compact_perturbation (Int.natAbs_pos.mpr m.property)
      U hU hcomp

/-- Premise-free unit form of compact index stability. -/
theorem signedToeplitz_no_unit_compact_perturbation
    (m : {m : ℤ // m ≠ 0})
    (U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ) :
    ¬ IsCompactOperator
      ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) - signedToeplitzOp m) :=
  signedToeplitz_no_invertible_compact_perturbation m U
    ((ContinuousLinearMap.isUnit_iff_bijective).1 U.isUnit)

/-! ## Literal prime source and its reflected Fredholm cycle -/

/-- Nonzero deck character on one literal arithmetic-Jacobian prime orbit. -/
structure CCMArithmeticPrimeFredholmCycle where
  prime : Nat.Primes
  grade : {m : ℤ // m ≠ 0}

namespace CCMArithmeticPrimeFredholmCycle

/-- Canonical source orientation: the fundamental positive character of the
directed arithmetic deck generator `(Frob_p, log p)`. -/
def canonical (p : Nat.Primes) : CCMArithmeticPrimeFredholmCycle where
  prime := p
  grade := ⟨1, one_ne_zero⟩

/-- Arithmetic deck generator from which the horizontal period is read. -/
def deck (X : CCMArithmeticPrimeFredholmCycle) :=
  ccmArithmeticJacobianPrimeDeck X.prime

/-- Positive horizontal period, literally the second deck coordinate. -/
def period (X : CCMArithmeticPrimeFredholmCycle) : {L : ℝ // 0 < L} :=
  ⟨Real.log (X.prime : ℝ), ccmArithmeticJacobianPrimePeriod_pos X.prime⟩

@[simp] theorem deck_second (X : CCMArithmeticPrimeFredholmCycle) :
    (X.deck).2 = (X.period : ℝ) := rfl

/-- Completed Hardy-space Fredholm operator selected by the deck character. -/
def operator (X : CCMArithmeticPrimeFredholmCycle) :
    ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  signedToeplitzOp X.grade

/-- Full-domain Fredholm presentation of the source operator. -/
def fredholmOperator (X : CCMArithmeticPrimeFredholmCycle) :
    ToeplitzSpace →ₗ.[ℂ] ToeplitzSpace :=
  signedToeplitzPMap X.grade

/-- Reflection/duality reverses the deck character and changes no source
prime. -/
def dual (X : CCMArithmeticPrimeFredholmCycle) :
    CCMArithmeticPrimeFredholmCycle where
  prime := X.prime
  grade := ⟨-X.grade, neg_ne_zero.mpr X.grade.property⟩

@[simp] theorem dual_prime (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.prime = X.prime := rfl

@[simp] theorem dual_grade (X : CCMArithmeticPrimeFredholmCycle) :
    (X.dual.grade : ℤ) = -X.grade := rfl

@[simp] theorem dual_dual (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.dual = X := by
  cases X with
  | mk p m =>
      apply congrArg (CCMArithmeticPrimeFredholmCycle.mk p)
      apply Subtype.ext
      exact neg_neg m.val

/-- Source operator is genuinely Fredholm on the completed infinite carrier. -/
theorem isFredholm (X : CCMArithmeticPrimeFredholmCycle) :
    X.fredholmOperator.IsFredholm :=
  signedToeplitzPMap_isFredholm X.grade

/-- Signed index carried by the source object. -/
def index (X : CCMArithmeticPrimeFredholmCycle) : ℤ :=
  LinearPMap.index X.fredholmOperator

/-- Index is literal negative deck-character grade. -/
theorem index_eq_neg_grade (X : CCMArithmeticPrimeFredholmCycle) :
    X.index = -X.grade :=
  signedToeplitzIndex_eq X.grade

/-- Reflection follows from duality: reflected operator is Hilbert adjoint. -/
theorem operator_dual (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.operator = ContinuousLinearMap.adjoint X.operator :=
  signedToeplitzOp_neg X.grade

/-- Fredholm index is an odd function under source duality. -/
theorem index_dual (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.index = -X.index := by
  rw [index_eq_neg_grade, index_eq_neg_grade]
  simp

/-- Horizontal polarization orientation of the prime-orbit character. -/
def horizontalOrientation (X : CCMArithmeticPrimeFredholmCycle) : ℝ :=
  -2 * Real.pi * (X.grade : ℝ) / (X.period : ℝ)

/-- Horizontal orientation is normalized Fredholm index density. -/
theorem horizontalOrientation_eq_index_density
    (X : CCMArithmeticPrimeFredholmCycle) :
    X.horizontalOrientation =
      2 * Real.pi * (X.index : ℝ) / (X.period : ℝ) := by
  rw [horizontalOrientation, index_eq_neg_grade]
  push_cast
  ring

/-- Horizontal orientation reverses under source duality. -/
theorem horizontalOrientation_dual (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.horizontalOrientation = -X.horizontalOrientation := by
  simp [horizontalOrientation, period]
  ring

/-- Infinite completion preserves the signed distinction: compact
perturbation cannot turn the source operator into an invertible operator. -/
theorem no_invertible_compact_completion
    (X : CCMArithmeticPrimeFredholmCycle)
    (U : ToeplitzSpace →L[ℂ] ToeplitzSpace)
    (hU : Function.Bijective U) :
    ¬ IsCompactOperator (U - X.operator) :=
  signedToeplitz_no_invertible_compact_perturbation X.grade U hU

/-- Premise-free unit form of infinite-completion stability. -/
theorem no_unit_compact_completion
    (X : CCMArithmeticPrimeFredholmCycle)
    (U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ) :
    ¬ IsCompactOperator
      ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) - X.operator) :=
  signedToeplitz_no_unit_compact_perturbation X.grade U

/-- Literal arithmetic produces a canonical reflected signed pair: the
directed fundamental character has index `-1`, its dual has index `+1`, their
operators are adjoints, and neither class can be erased by compact completion. -/
theorem canonical_reflected_signed_pair (p : Nat.Primes) :
    (canonical p).index = -1 ∧
      (canonical p).dual.index = 1 ∧
      (canonical p).dual.operator =
        ContinuousLinearMap.adjoint (canonical p).operator ∧
      (canonical p).dual.horizontalOrientation =
        -(canonical p).horizontalOrientation ∧
      (∀ U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ,
        ¬ IsCompactOperator
          ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) -
            (canonical p).operator)) ∧
      ∀ U : (ToeplitzSpace →L[ℂ] ToeplitzSpace)ˣ,
        ¬ IsCompactOperator
          ((U : ToeplitzSpace →L[ℂ] ToeplitzSpace) -
            (canonical p).dual.operator) := by
  refine ⟨?_, ?_, operator_dual (canonical p),
    horizontalOrientation_dual (canonical p),
    no_unit_compact_completion (canonical p),
    no_unit_compact_completion (canonical p).dual⟩
  · simp [index_eq_neg_grade, canonical]
  · simp [index_eq_neg_grade, canonical]

/-- Closed source-first package: literal deck period, Fredholmness, dual
reflection, odd index/orientation, and compact-stable infinite completion. -/
theorem source_fredholm_orientation
    (X : CCMArithmeticPrimeFredholmCycle) :
    (X.deck).2 = (X.period : ℝ) ∧
      X.fredholmOperator.IsFredholm ∧
      X.dual.operator = ContinuousLinearMap.adjoint X.operator ∧
      X.dual.index = -X.index ∧
      X.dual.horizontalOrientation = -X.horizontalOrientation ∧
      ∀ U : ToeplitzSpace →L[ℂ] ToeplitzSpace,
        Function.Bijective U → ¬ IsCompactOperator (U - X.operator) :=
  ⟨deck_second X, isFredholm X, operator_dual X, index_dual X,
    horizontalOrientation_dual X, no_invertible_compact_completion X⟩

end CCMArithmeticPrimeFredholmCycle

end

end RHTower
