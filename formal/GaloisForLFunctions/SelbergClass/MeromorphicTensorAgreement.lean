import GaloisForLFunctions.SelbergClass.MeromorphicTensor

/-!
# Agreement of globally presented meromorphic tensors

Two quotient presentations of entire functions describe the same global
meromorphic tensor precisely when their classes agree in the fraction field of
entire functions.  This module transports that algebraic equality to equality
of their displayed quotient functions wherever both displayed denominators are
nonzero.

`candidatePolarSet` records only the zero locus of a *chosen* denominator.  It
does not assert that any such point is an actual pole: a numerator can cancel a
displayed denominator zero.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

namespace MeromorphicTensorPresentation

variable {N : ℕ}

/-- Two presentations denote the same global meromorphic tensor when they
agree in the fraction field of entire functions. -/
noncomputable def sameMeromorphicFunction
    (S T : MeromorphicTensorPresentation N) : Prop :=
  S.toEntireField = T.toEntireField

/-- The complement of a presentation's displayed regular locus.  This is a
candidate polar set of the presentation, rather than an assertion about actual
poles of its fraction-field class. -/
def candidatePolarSet (T : MeromorphicTensorPresentation N) : Set (Fin N → ℂ) :=
  T.regularSetᶜ

/-- The candidate polar set is exactly the zero locus of the displayed
denominator. -/
theorem candidatePolarSet_eq_denominator_zeroSet (T : MeromorphicTensorPresentation N) :
    T.candidatePolarSet = {s | (T.denominator : (Fin N → ℂ) → ℂ) s = 0} := by
  ext s
  simp only [candidatePolarSet, Set.mem_compl_iff, regularSet, Set.mem_setOf_eq,
    not_ne_iff]

/-- The displayed regular locus is the complement of the candidate polar set. -/
theorem regularSet_eq_compl_candidatePolarSet (T : MeromorphicTensorPresentation N) :
    T.regularSet = T.candidatePolarSetᶜ := by
  simp only [candidatePolarSet, compl_compl]

/-- Membership in the candidate polar set means exactly that the displayed
denominator vanishes.  This is not a claim that the fraction-field class has a
pole there. -/
theorem mem_candidatePolarSet_iff (T : MeromorphicTensorPresentation N)
    (s : Fin N → ℂ) :
    s ∈ T.candidatePolarSet ↔ (T.denominator : (Fin N → ℂ) → ℂ) s = 0 := by
  rw [candidatePolarSet_eq_denominator_zeroSet]
  rfl

/-- Equality in the entire fraction field is reflexive. -/
theorem sameMeromorphicFunction_refl (S : MeromorphicTensorPresentation N) :
    S.sameMeromorphicFunction S := rfl

/-- Equality in the entire fraction field is symmetric. -/
theorem sameMeromorphicFunction_symm {S T : MeromorphicTensorPresentation N}
    (h : S.sameMeromorphicFunction T) : T.sameMeromorphicFunction S := h.symm

/-- Equality in the entire fraction field is transitive. -/
theorem sameMeromorphicFunction_trans {S T U : MeromorphicTensorPresentation N}
    (hST : S.sameMeromorphicFunction T) (hTU : T.sameMeromorphicFunction U) :
    S.sameMeromorphicFunction U := hST.trans hTU

/-- Two equal fraction-field presentations satisfy the cross-multiplied
identity between their entire numerators and denominators. -/
theorem numerator_mul_denominator_eq_of_sameMeromorphicFunction
    {S T : MeromorphicTensorPresentation N} (h : S.sameMeromorphicFunction T) :
    S.numerator * T.denominator = T.numerator * S.denominator := by
  have hcrossField := (div_eq_div_iff S.denominator_toEntireField_ne_zero
    T.denominator_toEntireField_ne_zero).mp h
  apply IsFractionRing.injective (entireSubring (Fin N → ℂ)) (EntireField (Fin N → ℂ))
  simpa only [map_mul] using hcrossField

/-- Equal fraction-field presentations have equal displayed quotient values at
every point where both displayed denominators are nonzero. -/
theorem value_eq_of_sameMeromorphicFunction
    {S T : MeromorphicTensorPresentation N} (h : S.sameMeromorphicFunction T)
    {s : Fin N → ℂ} (hs : s ∈ S.regularSet ∩ T.regularSet) : S.value s = T.value s := by
  have hcross := numerator_mul_denominator_eq_of_sameMeromorphicFunction h
  have hcrossEval := congrArg (fun f : entireSubring (Fin N → ℂ) =>
    (f : (Fin N → ℂ) → ℂ) s) hcross
  change
    (S.numerator : (Fin N → ℂ) → ℂ) s * (T.denominator : (Fin N → ℂ) → ℂ) s =
      (T.numerator : (Fin N → ℂ) → ℂ) s * (S.denominator : (Fin N → ℂ) → ℂ) s at hcrossEval
  apply (div_eq_div_iff hs.1 hs.2).mpr
  exact hcrossEval

end MeromorphicTensorPresentation

end GaloisForLFunctions.SelbergClass
