import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionSeparableSubfield
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# Maximal commutative subfields of finite central division algebras

Finite-dimensionality lets us maximize the dimension of a commutative subalgebra containing a
given commutative seed.  Every such subalgebra is a field because it lies in a division algebra
and is integral over the base.  Maximality then identifies its centralizer with itself.

For a nonsplit Brauer class, the construction starts from the separable Jacobson--Noether seed.
Thus the remaining local-Brauer structural step is no longer existence of maximal commutative
subfields; it is the local theorem that an appropriate maximal subfield can be chosen unramified,
together with the double-centralizer splitting identification.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped IsMulCommutative

noncomputable section

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]

/-- Every commutative subalgebra of a finite division algebra over a field is a field. -/
theorem commutativeSubalgebra_isField_of_finiteDivisionRing
    (S : Subalgebra K D) [IsMulCommutative S] : IsField S := by
  haveI : Algebra.IsIntegral K D := Algebra.IsIntegral.of_finite K D
  refine
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := ?_ }
  intro a ha
  have haD : (a : D) ≠ 0 := by
    intro hzero
    apply ha
    exact Subtype.ext hzero
  have hinv : (a : D)⁻¹ ∈ S :=
    (Algebra.IsIntegral.isIntegral (R := K) (a : D)).inv_mem a.property
  exact ⟨⟨(a : D)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ haD)⟩

/-- A finite division algebra has a dimension-maximal commutative subalgebra containing any given
commutative subalgebra. -/
theorem exists_maximalCommutativeSubalgebra_containing
    (S₀ : Subalgebra K D) [IsMulCommutative S₀] :
    ∃ S : Subalgebra K D, S₀ ≤ S ∧ IsMulCommutative S ∧
      ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Subalgebra K D,
    S₀ ≤ S ∧ IsMulCommutative S ∧ Module.finrank K S = n
  let N := Module.finrank K D
  have hP₀ : P (Module.finrank K S₀) := ⟨S₀, le_rfl, inferInstance, rfl⟩
  have hbound₀ : Module.finrank K S₀ ≤ N := Submodule.finrank_le S₀.toSubmodule
  have hPmax : P (Nat.findGreatest P N) := Nat.findGreatest_spec hbound₀ hP₀
  obtain ⟨S, hS₀, hcommS, hfinS⟩ := hPmax
  refine ⟨S, hS₀, hcommS, ?_⟩
  intro T hST hcommT
  have hboundT : Module.finrank K T ≤ N := Submodule.finrank_le T.toSubmodule
  have hPT : P (Module.finrank K T) :=
    ⟨T, hS₀.trans hST, hcommT, rfl⟩
  have hTmax : Module.finrank K T ≤ Nat.findGreatest P N :=
    Nat.le_findGreatest hboundT hPT
  apply (Subalgebra.eq_of_le_of_finrank_le hST ?_).symm
  rwa [hfinS]

/-- Every element of a finite division algebra is contained in a maximal commutative subfield. -/
theorem exists_maximalCommutativeSubfield_containing_element
    (x : D) :
    ∃ S : Subalgebra K D,
      Algebra.adjoin K ({x} : Set D) ≤ S ∧ IsMulCommutative S ∧ IsField S ∧
        (∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) := by
  obtain ⟨S, hxS, hcommS, hmaxS⟩ :=
    exists_maximalCommutativeSubalgebra_containing K D (Algebra.adjoin K ({x} : Set D))
  letI : IsMulCommutative S := hcommS
  exact ⟨S, hxS, hcommS,
    commutativeSubalgebra_isField_of_finiteDivisionRing K D S, hmaxS⟩

omit [Module.Finite K D] in
/-- A maximal commutative subalgebra of a division algebra is its own centralizer. -/
theorem maximalCommutativeSubalgebra_centralizer_eq
    (S : Subalgebra K D) (hcommS : IsMulCommutative S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    Subalgebra.centralizer K (S : Set D) = S := by
  letI : IsMulCommutative S := hcommS
  apply le_antisymm
  · intro z hz
    let U := Algebra.adjoin K ((S : Set D) ∪ {z})
    have hpair : ∀ a ∈ ((S : Set D) ∪ {z}), ∀ b ∈ ((S : Set D) ∪ {z}),
        a * b = b * a := by
      intro a ha b hb
      rcases ha with haS | haz
      · rcases hb with hbS | hbz
        · exact setLike_mul_comm haS hbS
        · rw [Set.mem_singleton_iff] at hbz
          subst b
          exact hz a haS
      · rw [Set.mem_singleton_iff] at haz
        subst a
        rcases hb with hbS | hbz
        · exact (hz b hbS).symm
        · rw [Set.mem_singleton_iff] at hbz
          subst b
          rfl
    letI : IsMulCommutative U := Algebra.isMulCommutative_adjoin K hpair
    have hSU : S ≤ U := fun s hs => Algebra.subset_adjoin (Set.mem_union_left _ hs)
    have hUS : U = S := hmaxS U hSU inferInstance
    have hzU : z ∈ U :=
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton z))
    rwa [hUS] at hzU
  · intro z hz
    rw [Subalgebra.mem_centralizer_iff]
    intro s hs
    exact setLike_mul_comm hs hz

/-- Every nonsplit Brauer class has a central division representative containing a nontrivial
maximal commutative subfield generated from a separable seed; this subfield is self-centralizing. -/
theorem brauerGroup_ne_split_exists_maximalCommutativeSubfield
    (K : Type u) [Field K] (x : BrauerGroup K) (hx : x ≠ brauerSplitClass K) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D) (y : D)
      (S : Subalgebra K D),
      x = brauerClass (centralDivisionCSA K D) ∧
        y ∉ (⊥ : Subalgebra K D) ∧ IsSeparable K y ∧
          Algebra.adjoin K ({y} : Set D) ≤ S ∧ IsMulCommutative S ∧ IsField S ∧
            1 < Module.finrank K S ∧
              (∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) ∧
                Subalgebra.centralizer K (S : Set D) = S := by
  obtain ⟨D, hD, aD, finD, centralD, y, hclass, hybase, hysep⟩ :=
    brauerGroup_ne_split_exists_centralDivision_separable K x hx
  obtain ⟨S, hyS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element K D y
  letI : IsMulCommutative S := hcommS
  have hseed : 1 < Module.finrank K (Algebra.adjoin K ({y} : Set D)) :=
    one_lt_finrank_algebraAdjoinSingleton_of_not_mem_base K D y hybase
  have hyS' : (Algebra.adjoin K ({y} : Set D)).toSubmodule ≤ S.toSubmodule := hyS
  have hle : Module.finrank K (Algebra.adjoin K ({y} : Set D)) ≤ Module.finrank K S :=
    by simpa only [Subalgebra.finrank_toSubmodule] using Submodule.finrank_mono hyS'
  have hdegree : 1 < Module.finrank K S := hseed.trans_le hle
  have hcentralizer : Subalgebra.centralizer K (S : Set D) = S :=
    maximalCommutativeSubalgebra_centralizer_eq K D S hcommS hmaxS
  exact ⟨D, hD, aD, finD, centralD, y, S, hclass, hybase, hysep, hyS, hcommS,
    hfieldS, hdegree, hmaxS, hcentralizer⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
