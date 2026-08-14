import GaloisForLFunctions.HTGeometry.MilnorKGrading
import GaloisForLFunctions.HTGeometry.MilnorKFunctoriality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Graded functoriality of Milnor `K`-theory, and reduction to finite subextensions

A field homomorphism maps a symbol to the symbol of the entrywise image; it carries multilinearity
to multilinearity and the Steinberg relation to the Steinberg relation, so it descends to the
graded pieces.  Since the symbol classes generate, a subgroup containing all of them is everything;
and since two units of an algebraic extension of the rationals generate a finite subextension, the
torsion of `K_2^M` of every algebraic extension of the rationals follows from the torsion of
`K_2^M` of every number field.

* `milnorKDegMap` : **the induced map on the graded pieces.**
* `milnorKDeg_mem_of_gen` : the symbol classes generate.
* `milnorKDegTwo_torsion_of_finiteSubextension` : **reduction of degree two to finite
  subextensions.**
-/

namespace GaloisForLFunctions.HTGeometry

section GradedFunctoriality

variable {F E : Type*} [Field F] [Field E]

/-- The entrywise image of a symbol under a field homomorphism. -/
def milnorSymbolDegMap (f : F →+* E) (n : ℕ) (s : MilnorSymbolDeg F n) : MilnorSymbolDeg E n :=
  ⟨s.val.map (milnorUnitMap f), by rw [List.length_map, s.property]⟩

@[simp]
theorem milnorSymbolDegMap_val (f : F →+* E) (n : ℕ) (s : MilnorSymbolDeg F n) :
    (milnorSymbolDegMap f n s).val = s.val.map (milnorUnitMap f) := rfl

/-- The induced map on formal sums of symbols. -/
def milnorKDegPreMap (f : F →+* E) (n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg F n) →+ MilnorKDeg E n :=
  FreeAbelianGroup.lift fun s => milnorClassDeg E n (milnorSymbolDegMap f n s)

@[simp]
theorem milnorKDegPreMap_of (f : F →+* E) (n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorKDegPreMap f n (FreeAbelianGroup.of s)
      = milnorClassDeg E n (milnorSymbolDegMap f n s) := by
  simp [milnorKDegPreMap]

/-- **The relations are preserved**: multilinearity goes to multilinearity and Steinberg to
Steinberg. -/
theorem milnorKDegPreMap_rel (f : F →+* E) (n : ℕ) :
    ∀ x ∈ milnorRelSubgroupDeg F n, milnorKDegPreMap f n x = 0 := by
  intro x hx
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
    · rw [map_sub, map_sub, milnorKDegPreMap_of, milnorKDegPreMap_of, milnorKDegPreMap_of,
        sub_sub, sub_eq_zero]
      exact milnorClassDeg_mul_of_eq E (n := n) (milnorUnitMap f a) (milnorUnitMap f b)
        (l₁.map (milnorUnitMap f)) (l₂.map (milnorUnitMap f))
        (by simp) (by simp) (by simp) _ _ _
    · rw [milnorKDegPreMap_of]
      exact milnorClassDeg_steinberg_of_eq E (milnorUnitMap_ne_one f ha)
        (l₁.map (milnorUnitMap f)) (l₂.map (milnorUnitMap f))
        (by simp [milnorUnitMap_oneSubUnit]) _
  · exact map_zero _
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, add_zero]
  · intro y _ hy
    rw [map_neg, hy, neg_zero]

/-- **The map induced on the graded pieces of Milnor `K`-theory.** -/
def milnorKDegMap (f : F →+* E) (n : ℕ) : MilnorKDeg F n →+ MilnorKDeg E n :=
  QuotientAddGroup.lift _ (milnorKDegPreMap f n) (milnorKDegPreMap_rel f n)

@[simp]
theorem milnorKDegMap_class (f : F →+* E) (n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorKDegMap f n (milnorClassDeg F n s) = milnorClassDeg E n (milnorSymbolDegMap f n s) :=
  milnorKDegPreMap_of f n s

end GradedFunctoriality

section Generation

variable {F : Type*} [Field F]

/-- **The symbol classes generate**: a subgroup containing all of them is everything. -/
theorem milnorKDeg_mem_of_gen {n : ℕ} (S : AddSubgroup (MilnorKDeg F n))
    (h : ∀ s : MilnorSymbolDeg F n, milnorClassDeg F n s ∈ S) (x : MilnorKDeg F n) : x ∈ S := by
  refine QuotientAddGroup.induction_on x fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero => exact S.zero_mem
  | of s => exact h s
  | neg s ih =>
      have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (-FreeAbelianGroup.of s))
          = -(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n)
            (FreeAbelianGroup.of s)) := rfl
      rw [hmk]
      exact S.neg_mem (h s)
  | add u v hu hv =>
      have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (u + v))
          = QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u
            + QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v := rfl
      rw [hmk]
      exact S.add_mem hu hv

end Generation

section Reduction

open IntermediateField

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **Reduction of degree two to finite subextensions.**  Every degree-two class of an algebraic
extension of the rationals is the image of a degree-two class of a finite subextension, so it is
torsion as soon as every finite subextension has torsion degree two. -/
theorem milnorKDegTwo_torsion_of_finiteSubextension
    (hNF : ∀ K : IntermediateField ℚ F, FiniteDimensional ℚ K →
      ∀ x : MilnorKDeg K 2, x ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (x : MilnorKDeg F 2) : x ∈ torsionAddSubgroup (MilnorKDeg F 2) := by
  classical
  refine milnorKDeg_mem_of_gen _ (fun s => ?_) x
  obtain ⟨a, b, hs⟩ : ∃ a b : Fˣ, s.val = [a, b] := by
    rcases s with ⟨l, hl⟩
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)
    · exact ⟨a, b, rfl⟩
    · exact absurd hl (by simp)
  have hint : ∀ y ∈ ({(a : F), (b : F)} : Set F), IsIntegral ℚ y := by
    intro y _
    exact (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  set K : IntermediateField ℚ F := IntermediateField.adjoin ℚ ({(a : F), (b : F)} : Set F) with hK
  haveI hfd : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hint
  have haK : (a : F) ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hbK : (b : F) ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hane : (⟨(a : F), haK⟩ : K) ≠ 0 := fun hzero => a.ne_zero (congrArg Subtype.val hzero)
  have hbne : (⟨(b : F), hbK⟩ : K) ≠ 0 := fun hzero => b.ne_zero (congrArg Subtype.val hzero)
  set sK : MilnorSymbolDeg K 2 := ⟨[Units.mk0 _ hane, Units.mk0 _ hbne], rfl⟩ with hsK
  obtain ⟨n, hn, hnz⟩ := hNF K hfd (milnorClassDeg K 2 sK)
  refine ⟨n, hn, ?_⟩
  have himg := congrArg (milnorKDegMap (K.val : K →+* F) 2) hnz
  rw [map_zsmul, milnorKDegMap_class, map_zero] at himg
  have hval : milnorSymbolDegMap (K.val : K →+* F) 2 sK = s := by
    refine Subtype.ext ?_
    rw [milnorSymbolDegMap_val, hs]
    show [milnorUnitMap (K.val : K →+* F) (Units.mk0 _ hane),
        milnorUnitMap (K.val : K →+* F) (Units.mk0 _ hbne)] = [a, b]
    rw [show milnorUnitMap (K.val : K →+* F) (Units.mk0 _ hane) = a from Units.ext rfl,
      show milnorUnitMap (K.val : K →+* F) (Units.mk0 _ hbne) = b from Units.ext rfl]
  rwa [hval] at himg

end Reduction

end GaloisForLFunctions.HTGeometry
