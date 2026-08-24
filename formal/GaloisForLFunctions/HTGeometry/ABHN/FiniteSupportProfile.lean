import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality

/-!
# Packaging finite-support functions as reciprocity profiles

This file turns a function with finite support into a literal `Finsupp`, preserving coordinates and
identifying its `Finsupp.sum` with `finsum`.  It is the common bridge from analytically constructed
local terms to finite-support Hasse and reciprocity lemmas.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Function

/-- Package any finitely supported function as a `Finsupp`. -/
noncomputable def finsuppOfFiniteSupport
    {ι M : Type*} [Zero M] (f : ι → M) (hf : HasFiniteSupport f) : ι →₀ M := by
  classical
  exact
    { toFun := f
      support := hf.toFinset
      mem_support_toFun := by
        intro i
        rw [hf.mem_toFinset]
        rfl }

@[simp]
theorem finsuppOfFiniteSupport_apply
    {ι M : Type*} [Zero M] (f : ι → M) (hf : HasFiniteSupport f) (i : ι) :
    finsuppOfFiniteSupport f hf i = f i := rfl

/-- The coordinate sum of the packaged profile is the unrestricted finite sum of the function. -/
theorem finsuppOfFiniteSupport_sum_eq_finsum
    {ι M : Type*} [AddCommMonoid M] (f : ι → M) (hf : HasFiniteSupport f) :
    (finsuppOfFiniteSupport f hf).sum (fun _ z => z) = ∑ᶠ i, f i := by
  classical
  change (finsuppOfFiniteSupport f hf).support.sum f = ∑ᶠ i, f i
  symm
  apply finsum_eq_finsetSum_of_support_subset
  intro i hi
  exact Finsupp.mem_support_iff.mpr hi

end GaloisForLFunctions.HTGeometry.ABHN
