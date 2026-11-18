import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinate arrangements restricted to a linear code

On a subspace, coordinate choices need not be independent. Intersecting
coordinate hyperplanes restricts the code to a linear kernel instead.
Expanding the multivariate zero-coordinate enumerator gives the exact
coordinate-rank transform and its inclusion–exclusion specialization.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section

variable {ι F : Type*} [Fintype ι] [Field F] [Fintype F]

/-- Coordinate restriction of a code to the indicated sites. -/
def punctureAt (C : Submodule F (ι → F)) (s : Finset ι) : C →ₗ[F] (s → F) where
  toFun x i := x.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate hyperplanes containing a word. -/
def codeZeroSites (x : ι → F) : Finset ι := univ.filter fun i => x i = 0

/-- All codewords on the intersection of the indicated coordinate hyperplanes. -/
def codeSlice (C : Submodule F (ι → F)) (s : Finset ι) : Finset C :=
  univ.filter fun x => s ⊆ codeZeroSites x.val

private theorem slice_ker (C : Submodule F (ι → F)) (s : Finset ι) (x : C) :
    x ∈ codeSlice C s ↔ x ∈ (punctureAt C s).ker := by
  simp only [codeSlice, mem_filter, mem_univ, true_and, LinearMap.mem_ker]
  constructor
  · intro h
    funext i
    exact (mem_filter.mp (h i.property)).2
  · intro h i hi
    exact mem_filter.mpr ⟨mem_univ _, congrFun h ⟨i,hi⟩⟩

/-- Each hyperplane intersection has exactly the power of the field order
predicted by its projection nullity. -/
theorem card_codeSlice (C : Submodule F (ι → F)) (s : Finset ι) :
    (codeSlice C s).card = Fintype.card F ^ Module.finrank F (punctureAt C s).ker := by
  let e : ↥(codeSlice C s) ≃ ↥(punctureAt C s).ker := Equiv.subtypeEquivRight (slice_ker C s)
  calc
    _ = Fintype.card (punctureAt C s).ker := by simpa using Fintype.card_congr e
    _ = _ := Module.card_eq_pow_finrank

variable {R : Type*} [CommSemiring R]

/-- The complete multivariate transform, with independently chosen test sites
and a prescribed set of forced zeros. Coordinate dependence enters only
through the dimensions of the restricted kernels. -/
theorem code_arrangement_transform (C : Submodule F (ι → F)) (S U : Finset ι) (z : ι → R) :
    (∑ x ∈ codeSlice C S, ∏ i ∈ U ∩ codeZeroSites x.val, (z i + 1)) =
      ∑ T ∈ U.powerset, (Fintype.card F : R) ^ Module.finrank F (punctureAt C (S ∪ T)).ker *
        ∏ i ∈ T, z i := by
  have row (x : C) : (∏ i ∈ U ∩ codeZeroSites x.val, (z i + 1)) =
      ∑ T ∈ U.powerset, if T ⊆ codeZeroSites x.val then ∏ i ∈ T, z i else 0 := by
    rw [← sum_filter, Finset.prod_add]
    have he : U.powerset.filter (fun T => T ⊆ codeZeroSites x.val) =
        (U ∩ codeZeroSites x.val).powerset := by ext T; simp [Finset.subset_inter_iff]
    simp [he]
  simp_rw [row]
  rw [sum_comm]
  refine sum_congr rfl fun T _ => ?_
  rw [← sum_filter]
  have he : (codeSlice C S).filter (fun x => T ⊆ codeZeroSites x.val) = codeSlice C (S ∪ T) := by
    ext x
    simp [codeSlice,union_subset_iff]
  rw [he, sum_const, nsmul_eq_mul, card_codeSlice, Nat.cast_pow]

/-- Evaluating every test variable at minus one extracts the count on an
intersection avoiding every other designated hyperplane. -/
theorem code_avoid_hyperplanes (C : Submodule F (ι → F)) (S U : Finset ι) :
    (((codeSlice C S).filter (fun x => U ∩ codeZeroSites x.val = ∅)).card : ℤ) =
      ∑ T ∈ U.powerset, (Fintype.card F : ℤ) ^ Module.finrank F (punctureAt C (S ∪ T)).ker *
        (-1 : ℤ) ^ T.card := by
  have h := code_arrangement_transform C S U (fun _ => (-1:ℤ))
  have he (s : Finset ι) : (∏ _i ∈ s, ((-1:ℤ)+1)) = if s = ∅ then 1 else 0 := by
    by_cases hs : s = ∅
    · simp [hs]
    · simp [hs, Finset.card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hs)]
  simp only [he, prod_const] at h
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- The number of full-support words of an arbitrary code is the signed
nullity sum over its coordinate subsets. -/
theorem full_weight_count_of_coordinate_ranks (C : Submodule F (ι → F)) :
    ((univ.filter (fun x : C => weight x.val = Fintype.card ι)).card : ℤ) =
      ∑ T : Finset ι, (Fintype.card F : ℤ) ^ Module.finrank F (punctureAt C T).ker *
        (-1 : ℤ) ^ T.card := by
  have he (x : C) : weight x.val = Fintype.card ι ↔ codeZeroSites x.val = ∅ := by
    change (univ.filter _).card = (univ : Finset ι).card ↔ _
    simp [card_filter_eq_iff, codeZeroSites, Finset.filter_eq_empty_iff]
  simpa [codeSlice,he] using code_avoid_hyperplanes C ∅ univ

#print axioms card_codeSlice
#print axioms code_arrangement_transform
#print axioms code_avoid_hyperplanes
#print axioms full_weight_count_of_coordinate_ranks

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
