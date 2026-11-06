import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.BoundaryTateTrace

/-!
# Kloosterman moments and the compactified reciprocal locus

The homogeneous reciprocal zero locus splits into its torus and coordinate
boundary. Counting scalar representatives identifies its projective torus with
the normalized double-zero locus. The moment identity then separates the
compactified point count from an explicit signed Tate trace.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

section Homogeneity

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Clearing reciprocal denominators gives a homogeneous equation of degree `n−1`. -/
theorem reciprocalClearedValue_scale (a : F) (x : ι → F) :
    reciprocalClearedValue (fun i => a * x i) =
      a ^ (Fintype.card ι - 1) * reciprocalClearedValue x := by
  rw [reciprocalClearedValue, reciprocalClearedValue, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ]

/-- The homogeneous zero locus is invariant under nonzero scalar multiplication. -/
theorem reciprocalClearedValue_scale_zero_iff (u : Fˣ) (x : ι → F) :
    reciprocalClearedValue (fun i => (u : F) * x i) = 0 ↔ reciprocalClearedValue x = 0 := by
  rw [reciprocalClearedValue_scale, mul_eq_zero]
  exact or_iff_right (pow_ne_zero _ u.ne_zero)

/-- On the torus, the cleared value is the coordinate product times the reciprocal sum. -/
theorem reciprocalClearedValue_eq (x : ι → F) (hx : ∀ i, x i ≠ 0) :
    reciprocalClearedValue x = (∏ i, x i) * ∑ i, (x i)⁻¹ := by
  rw [reciprocalClearedValue, mul_sum]
  apply sum_congr rfl
  intro i _
  symm
  rw [← prod_erase_mul univ x (mem_univ i), mul_assoc, mul_inv_cancel₀ (hx i), mul_one]

/-- Denominator clearing preserves the zero equation on the torus. -/
theorem reciprocalClearedValue_zero_iff (x : ι → F) (hx : ∀ i, x i ≠ 0) :
    reciprocalClearedValue x = 0 ↔ (∑ i, (x i)⁻¹) = 0 := by
  rw [reciprocalClearedValue_eq x hx, mul_eq_zero]
  exact or_iff_right (prod_ne_zero_iff.mpr (fun i _ => hx i))

end Homogeneity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Nonzero vectors in the coordinate-sum hyperplane. -/
abbrev FullZeroCone (n : ℕ) := ↥(boundedSupportZeroSum (F := F) (ι := Fin n) n)

theorem mem_fullZeroCone_iff (n : ℕ) (x : Fin n → F) :
    x ∈ boundedSupportZeroSum n ↔ (∃ i, x i ≠ 0) ∧ ∑ i, x i = 0 := by
  simp only [boundedSupportZeroSum, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hp, _, hs⟩
    obtain ⟨i, hi⟩ := card_pos.mp hp
    exact ⟨⟨i, HTGeometry.mem_configSupport.mp hi⟩, hs⟩
  · rintro ⟨⟨i, hi⟩, hs⟩
    refine ⟨card_pos.mpr ⟨i, HTGeometry.mem_configSupport.mpr hi⟩, ?_, hs⟩
    simpa only [Fintype.card_fin] using card_le_univ (HTGeometry.configSupport 0 x)

/-- The nonzero affine cone of the compactified reciprocal locus. -/
def reciprocalCone (n : ℕ) : Finset (FullZeroCone (F := F) n) :=
  univ.filter (fun x => reciprocalClearedValue x.val = 0)

/-- The homogeneous reciprocal zero locus inside the actual projective hyperplane. -/
def projectiveReciprocalLocus (n : ℕ) :
    Finset (ProjectiveSupportZeroSum (F := F) (ι := Fin n) n) :=
  univ.filter (fun q => reciprocalClearedValue q.out.val = 0)

/-- The projective equation is independent of the representative. -/
theorem mem_projectiveReciprocalLocus_iff (n : ℕ) (x : FullZeroCone (F := F) n) :
    Quotient.mk (supportScalarSetoid n) x ∈ projectiveReciprocalLocus n ↔
      reciprocalClearedValue x.val = 0 := by
  obtain ⟨u, hu⟩ := Quotient.mk_out (s := supportScalarSetoid n) x
  have heq : (Quotient.mk (supportScalarSetoid n) x).out.val =
      fun i => (u : F) * x.val i := funext hu
  simp only [projectiveReciprocalLocus, mem_filter, mem_univ, true_and]
  rw [heq, reciprocalClearedValue_scale_zero_iff]

/-- Every projective point of the compactification has exactly `q−1` scalar representatives. -/
theorem reciprocalCone_card_orbits (n : ℕ) :
    (reciprocalCone (F := F) n).card =
      (projectiveReciprocalLocus (F := F) n).card * (Fintype.card F - 1) := by
  classical
  let π : FullZeroCone (F := F) n → ProjectiveSupportZeroSum (F := F) (ι := Fin n) n :=
    Quotient.mk (supportScalarSetoid n)
  have hsplit : reciprocalCone (F := F) n = (projectiveReciprocalLocus n).biUnion
      (fun q => univ.filter (fun x : FullZeroCone (F := F) n => π x = q)) := by
    ext x
    simp only [reciprocalCone, mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hx
      exact ⟨π x, (mem_projectiveReciprocalLocus_iff n x).mpr hx, rfl⟩
    · rintro ⟨q, hq, hx⟩
      apply (mem_projectiveReciprocalLocus_iff n x).mp
      change π x ∈ projectiveReciprocalLocus n
      rwa [hx]
  rw [hsplit, card_biUnion]
  · have hf : ∀ q : ProjectiveSupportZeroSum (F := F) (ι := Fin n) n,
        (univ.filter (fun x : FullZeroCone (F := F) n => π x = q)).card =
          Fintype.card F - 1 := by
      intro q
      rw [← Fintype.card_subtype, ← Fintype.card_units F]
      convert (Fintype.card_congr (projectiveSupportFiberEquiv n q)).symm <;> rfl
    rw [sum_congr rfl (fun q _ => hf q), sum_const, nsmul_eq_mul, Nat.cast_id]
  · intro q _ q' _ hne
    apply disjoint_left.mpr
    intro x hx hy
    exact hne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
