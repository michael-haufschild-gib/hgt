import GaloisForLFunctions.RHTower.RelativeShellCommonCurrentHypertranscendence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableFactorization
import GaloisForLFunctions.HTGeometry.DifferentialMatroidClosure

/-!
# Exact common differential core of the high-exponent shell tests

The shell factorization `S_m = ζ H_m` gives many divisor-sharing tests.  Hypertranscendence of
the common zeta current over the complete transverse frame says that the frame cannot manufacture
the current.  This file proves the complementary exact statement: arbitrary sets of shell
labels embed faithfully into the differential-field lattice, preserving nonempty arbitrary
intersections and composita exactly, while private extensions are linearly disjoint over their
common shell field.  Every field observable has finite shell support, so no infinitary ghost
observable appears in all resolutions without belonging to their common source labels.  The
pairwise and complete common-core theorems are immediate boundary cases.

The first theorem is source-independent.  It is the differential-field form of the elementary
fact that two free extensions with disjoint private coordinates meet in their common coordinate
field.
-/

open Set
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Differential common-core law.**  If a common family and two private families are jointly
differentially independent, then the two differential fields obtained by adjoining the common
family with either private family intersect in exactly the common differential field. -/
theorem differentialIndependent_threeBlock_differentialAdjoin_inf
    {F E A B C : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (a : A → E) (b : B → E) (c : C → E)
    (habc : DifferentialIndependent F (Sum.elim a (Sum.elim b c))) :
    differentialAdjoin F (Set.range (Sum.elim a b)) ⊓
        differentialAdjoin F (Set.range (Sum.elim a c)) =
      differentialAdjoin F (Set.range a) :=
  _root_.GaloisForLFunctions.differentialIndependent_threeBlock_differentialAdjoin_inf a b c habc

/-- **Private-sector tensor law.**  Under the same joint differential independence hypothesis,
the two private differential extensions are linearly disjoint over the common differential
field.  Thus the multiplication map from their tensor product has no kernel. -/
theorem differentialIndependent_threeBlock_private_linearDisjoint
    {F E A B C : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (a : A → E) (b : B → E) (c : C → E)
    (habc : DifferentialIndependent F (Sum.elim a (Sum.elim b c))) :
    (differentialAdjoin (differentialAdjoin F (Set.range a))
        (Set.range b)).LinearDisjoint
      (differentialAdjoin (differentialAdjoin F (Set.range a))
        (Set.range c)) := by
  let K0 := differentialAdjoin F (Set.range a)
  let bj : B × ℕ → E := fun p => differentialJet p.2 (b p.1)
  let cj : C × ℕ → E := fun p => differentialJet p.2 (c p.1)
  have hbc :
      DifferentialIndependent K0 (Sum.elim b c) :=
    GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
      a (Sum.elim b c) habc
  unfold DifferentialIndependent at hbc
  let e := Equiv.sumProdDistrib B C ℕ
  have hbcJets :
      AlgebraicIndependent K0 (Sum.elim bj cj) := by
    have hcomp := hbc.comp e.symm e.symm.injective
    convert hcomp using 1
    funext p
    rcases p with ⟨i, n⟩ | ⟨j, n⟩ <;> rfl
  have hld :=
    algebraicIndependent_sum_adjoin_linearDisjoint bj cj hbcJets
  have hb :
      differentialJetSet (Set.range b) = Set.range bj :=
    differentialJetSet_range_eq b
  have hc :
      differentialJetSet (Set.range c) = Set.range cj :=
    differentialJetSet_range_eq c
  unfold differentialAdjoin
  rw [hb, hc]
  exact hld

/-- An arbitrary compositum of derivation-closed intermediate fields is derivation-closed. -/
theorem derivationClosed_iSup_intermediateField
    {F K ι : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (L : ι → IntermediateField F K)
    (hL : ∀ i, DerivationClosed (L i)) :
    DerivationClosed (⨆ i, L i) := by
  rw [IntermediateField.iSup_eq_adjoin]
  intro x hx
  apply IntermediateField.adjoin_induction F
      (s := ⋃ i, (L i : Set K))
      (p := fun y _ => y′ ∈ IntermediateField.adjoin F (⋃ i, (L i : Set K)))
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hy⟩ := hy
    exact IntermediateField.subset_adjoin F _
      (Set.mem_iUnion.mpr ⟨i, hL i hy⟩)
  · intro c
    rw [deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  · intro a b ha hb hda hdb
    rw [map_add]
    exact IntermediateField.add_mem _ hda hdb
  · intro a ha hda
    rw [Derivation.leibniz_inv]
    have hainv :
        a⁻¹ ∈ IntermediateField.adjoin F (⋃ i, (L i : Set K)) :=
      IntermediateField.inv_mem _ ha
    have hasq :
        a⁻¹ ^ (2 : ℕ) ∈ IntermediateField.adjoin F (⋃ i, (L i : Set K)) := by
      simpa [pow_two] using IntermediateField.mul_mem _ hainv hainv
    exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ hasq) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ ha hdb)
      (IntermediateField.mul_mem _ hb hda)
  exact hx

/-- Differential field generated by the common zeta mode. -/
abbrev relativeShellCommonModeDifferentialField :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  differentialAdjoin upperEndRationalCoordinateField
    (Set.range (fun _ : Unit => zetaUpperEndMero))

/-- Differential field of one shell test: the common zeta mode together with its private
zero-free multiplier.  Since `S_m = ζ H_m`, this is equally the differential field of the
actual shell channel and its transverse multiplier. -/
abbrev relativeShellTestDifferentialField
    (m : {m : ℕ // 12 ≤ m}) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  differentialAdjoin upperEndRationalCoordinateField
    (Set.range
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun _ : Unit => relativeShellMultiplierUpperEndCarrier m.1)))

/-- Differential field generated by the common zeta mode and an arbitrary set of private
high-exponent shell multipliers. -/
abbrev relativeShellSubsetDifferentialField
    (S : Set {m : ℕ // 12 ≤ m}) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  differentialAdjoin upperEndRationalCoordinateField
    (Set.range
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun m : S => relativeShellMultiplierUpperEndCarrier m.1.1)))

/-- Private shell extension over a pre-existing common shell field. -/
abbrev relativeShellPrivateDifferentialField
    (A P : Set {m : ℕ // 12 ≤ m}) :
    IntermediateField (relativeShellSubsetDifferentialField A)
      upperEndMeroField :=
  differentialAdjoin (relativeShellSubsetDifferentialField A)
    (Set.range
      (fun m : P => relativeShellMultiplierUpperEndCarrier m.1.1))

/-- **Exact shell-field lattice law.**  The Riemann shell frame preserves arbitrary binary
source intersections exactly: adjoining two collections of shell tests and intersecting the
resulting differential fields retains precisely their common shell labels, together with the
common zeta mode.  Thus the shell subsets form a faithful distributive sublattice of the
differential-field lattice. -/
theorem relativeShellSubsetDifferentialField_inf
    (S T : Set {m : ℕ // 12 ≤ m}) :
    relativeShellSubsetDifferentialField S ⊓
        relativeShellSubsetDifferentialField T =
      relativeShellSubsetDifferentialField (S ∩ T) := by
  let a : Unit ⊕ ↥(S ∩ T) → upperEndMeroField :=
    Sum.elim (fun _ : Unit => zetaUpperEndMero)
      (fun m : ↥(S ∩ T) => relativeShellMultiplierUpperEndCarrier m.1.1)
  let b : ↥(S \ T) → upperEndMeroField :=
    fun m => relativeShellMultiplierUpperEndCarrier m.1.1
  let c : ↥(T \ S) → upperEndMeroField :=
    fun m => relativeShellMultiplierUpperEndCarrier m.1.1
  let select :
      (Unit ⊕ ↥(S ∩ T)) ⊕ (↥(S \ T) ⊕ ↥(T \ S)) →
        Unit ⊕ {m : ℕ // 12 ≤ m}
    | Sum.inl (Sum.inl u) => Sum.inl u
    | Sum.inl (Sum.inr m) => Sum.inr m.1
    | Sum.inr (Sum.inl m) => Sum.inr m.1
    | Sum.inr (Sum.inr m) => Sum.inr m.1
  have hselect : Function.Injective select := by
    intro x y hxy
    rcases x with (u | m) | (m | m) <;>
      rcases y with (v | n) | (n | n)
    · exact congrArg (Sum.inl ∘ Sum.inl) (Subsingleton.elim u v)
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
      exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext hxy)
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact n.2.2 (hmn ▸ m.2.2)
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact n.2.2 (hmn ▸ m.2.1)
    · simp [select] at hxy
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact m.2.2 (hmn ▸ n.2.2)
    · simp [select] at hxy
      exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext hxy)
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact n.2.2 (hmn ▸ m.2.1)
    · simp [select] at hxy
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact m.2.2 (hmn ▸ n.2.1)
    · exfalso
      simp [select] at hxy
      have hmn : (m.1 : {m : ℕ // 12 ≤ m}) = n.1 := hxy
      exact m.2.2 (hmn ▸ n.2.1)
    · simp [select] at hxy
      exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hxy)
  have habc :
      DifferentialIndependent upperEndRationalCoordinateField
        (Sum.elim a (Sum.elim b c)) := by
    have hcomp :=
      zetaRelativeShellMultiplierUpperEnd_differentialIndependent.comp
        select hselect
    convert hcomp using 1
    funext i
    rcases i with (u | m) | (m | m) <;> rfl
  have hmeet :=
    differentialIndependent_threeBlock_differentialAdjoin_inf a b c habc
  have hS :
      Set.range (Sum.elim a b) =
        Set.range
          (Sum.elim (fun _ : Unit => zetaUpperEndMero)
            (fun m : S => relativeShellMultiplierUpperEndCarrier m.1.1)) := by
    ext z
    constructor
    · rintro ⟨(u | m) | m, rfl⟩
      · exact ⟨Sum.inl u, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, m.2.1⟩, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, m.2.1⟩, rfl⟩
    · rintro ⟨u | m, rfl⟩
      · exact ⟨Sum.inl (Sum.inl u), rfl⟩
      · by_cases hmT : m.1 ∈ T
        · exact ⟨Sum.inl (Sum.inr ⟨m.1, m.2, hmT⟩), rfl⟩
        · exact ⟨Sum.inr ⟨m.1, m.2, hmT⟩, rfl⟩
  have hT :
      Set.range (Sum.elim a c) =
        Set.range
          (Sum.elim (fun _ : Unit => zetaUpperEndMero)
            (fun m : T => relativeShellMultiplierUpperEndCarrier m.1.1)) := by
    ext z
    constructor
    · rintro ⟨(u | m) | m, rfl⟩
      · exact ⟨Sum.inl u, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, m.2.2⟩, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, m.2.1⟩, rfl⟩
    · rintro ⟨u | m, rfl⟩
      · exact ⟨Sum.inl (Sum.inl u), rfl⟩
      · by_cases hmS : m.1 ∈ S
        · exact ⟨Sum.inl (Sum.inr ⟨m.1, hmS, m.2⟩), rfl⟩
        · exact ⟨Sum.inr ⟨m.1, m.2, hmS⟩, rfl⟩
  have hST :
      Set.range a =
        Set.range
          (Sum.elim (fun _ : Unit => zetaUpperEndMero)
            (fun m : ↥(S ∩ T) =>
              relativeShellMultiplierUpperEndCarrier m.1.1)) := by
    rfl
  rw [hS, hT, hST] at hmeet
  exact hmeet

/-- The actual private shell extensions for arbitrary source subsets are linearly disjoint over
their exact common shell field. -/
theorem relativeShellPrivateDifferentialField_linearDisjoint
    (S T : Set {m : ℕ // 12 ≤ m}) :
    (relativeShellPrivateDifferentialField (S ∩ T) (S \ T)).LinearDisjoint
      (relativeShellPrivateDifferentialField (S ∩ T) (T \ S)) := by
  let a : Unit ⊕ ↥(S ∩ T) → upperEndMeroField :=
    Sum.elim (fun _ : Unit => zetaUpperEndMero)
      (fun m : ↥(S ∩ T) => relativeShellMultiplierUpperEndCarrier m.1.1)
  let b : ↥(S \ T) → upperEndMeroField :=
    fun m => relativeShellMultiplierUpperEndCarrier m.1.1
  let c : ↥(T \ S) → upperEndMeroField :=
    fun m => relativeShellMultiplierUpperEndCarrier m.1.1
  let select :
      (Unit ⊕ ↥(S ∩ T)) ⊕ (↥(S \ T) ⊕ ↥(T \ S)) →
        Unit ⊕ {m : ℕ // 12 ≤ m}
    | Sum.inl (Sum.inl u) => Sum.inl u
    | Sum.inl (Sum.inr m) => Sum.inr m.1
    | Sum.inr (Sum.inl m) => Sum.inr m.1
    | Sum.inr (Sum.inr m) => Sum.inr m.1
  have hselect : Function.Injective select := by
    intro x y hxy
    rcases x with (u | m) | (m | m) <;>
      rcases y with (v | n) | (n | n)
    · exact congrArg (Sum.inl ∘ Sum.inl) (Subsingleton.elim u v)
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
    · simp [select] at hxy
      exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext hxy)
    · exfalso
      simp [select] at hxy
      exact n.2.2 (hxy ▸ m.2.2)
    · exfalso
      simp [select] at hxy
      exact n.2.2 (hxy ▸ m.2.1)
    · simp [select] at hxy
    · exfalso
      simp [select] at hxy
      exact m.2.2 (hxy ▸ n.2.2)
    · simp [select] at hxy
      exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext hxy)
    · exfalso
      simp [select] at hxy
      exact n.2.2 (hxy ▸ m.2.1)
    · simp [select] at hxy
    · exfalso
      simp [select] at hxy
      exact m.2.2 (hxy ▸ n.2.1)
    · exfalso
      simp [select] at hxy
      exact m.2.2 (hxy ▸ n.2.1)
    · simp [select] at hxy
      exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hxy)
  have habc :
      DifferentialIndependent upperEndRationalCoordinateField
        (Sum.elim a (Sum.elim b c)) := by
    have hcomp :=
      zetaRelativeShellMultiplierUpperEnd_differentialIndependent.comp
        select hselect
    convert hcomp using 1
    funext i
    rcases i with (u | m) | (m | m) <;> rfl
  exact
    differentialIndependent_threeBlock_private_linearDisjoint a b c habc

/-- Shell-field composition is exactly source union. -/
theorem relativeShellSubsetDifferentialField_sup
    (S T : Set {m : ℕ // 12 ≤ m}) :
    relativeShellSubsetDifferentialField S ⊔
        relativeShellSubsetDifferentialField T =
      relativeShellSubsetDifferentialField (S ∪ T) := by
  let gS : Unit ⊕ S → upperEndMeroField :=
    Sum.elim (fun _ : Unit => zetaUpperEndMero)
      (fun m : S => relativeShellMultiplierUpperEndCarrier m.1.1)
  let gT : Unit ⊕ T → upperEndMeroField :=
    Sum.elim (fun _ : Unit => zetaUpperEndMero)
      (fun m : T => relativeShellMultiplierUpperEndCarrier m.1.1)
  let gST : Unit ⊕ ↥(S ∪ T) → upperEndMeroField :=
    Sum.elim (fun _ : Unit => zetaUpperEndMero)
      (fun m : ↥(S ∪ T) =>
        relativeShellMultiplierUpperEndCarrier m.1.1)
  have hgen : Set.range gST = Set.range gS ∪ Set.range gT := by
    ext z
    constructor
    · rintro ⟨u | m, rfl⟩
      · exact Set.mem_union_left _ ⟨Sum.inl u, rfl⟩
      · rcases m.2 with hmS | hmT
        · exact Set.mem_union_left _
            ⟨Sum.inr ⟨m.1, hmS⟩, rfl⟩
        · exact Set.mem_union_right _
            ⟨Sum.inr ⟨m.1, hmT⟩, rfl⟩
    · rintro (⟨u | m, rfl⟩ | ⟨u | m, rfl⟩)
      · exact ⟨Sum.inl u, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, Set.mem_union_left _ m.2⟩, rfl⟩
      · exact ⟨Sum.inl u, rfl⟩
      · exact ⟨Sum.inr ⟨m.1, Set.mem_union_right _ m.2⟩, rfl⟩
  have hjet :
      differentialJetSet (Set.range gS ∪ Set.range gT) =
        differentialJetSet (Set.range gS) ∪
          differentialJetSet (Set.range gT) := by
    ext z
    constructor
    · rintro ⟨w, hwS | hwT, n, rfl⟩
      · exact Set.mem_union_left _ ⟨w, hwS, n, rfl⟩
      · exact Set.mem_union_right _ ⟨w, hwT, n, rfl⟩
    · rintro (⟨w, hwS, n, rfl⟩ | ⟨w, hwT, n, rfl⟩)
      · exact ⟨w, Set.mem_union_left _ hwS, n, rfl⟩
      · exact ⟨w, Set.mem_union_right _ hwT, n, rfl⟩
  unfold relativeShellSubsetDifferentialField differentialAdjoin
  change IntermediateField.adjoin upperEndRationalCoordinateField
      (differentialJetSet (Set.range gS)) ⊔
        IntermediateField.adjoin upperEndRationalCoordinateField
          (differentialJetSet (Set.range gT)) =
    IntermediateField.adjoin upperEndRationalCoordinateField
      (differentialJetSet (Set.range gST))
  rw [hgen, hjet, IntermediateField.adjoin_union]

/-- The shell-field realization reflects inclusion exactly.  No shell label can be reconstructed
from zeta and any collection not containing that label. -/
theorem relativeShellSubsetDifferentialField_le_iff
    (S T : Set {m : ℕ // 12 ≤ m}) :
    relativeShellSubsetDifferentialField S ≤
        relativeShellSubsetDifferentialField T ↔
      S ⊆ T := by
  constructor
  · intro hST m hmS
    by_contra hmT
    let x : Unit ⊕ T → upperEndMeroField :=
      Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun n : T => relativeShellMultiplierUpperEndCarrier n.1.1)
    let y : Unit → upperEndMeroField :=
      fun _ => relativeShellMultiplierUpperEndCarrier m.1
    let select :
        (Unit ⊕ T) ⊕ Unit → Unit ⊕ {m : ℕ // 12 ≤ m}
      | Sum.inl (Sum.inl u) => Sum.inl u
      | Sum.inl (Sum.inr n) => Sum.inr n.1
      | Sum.inr _ => Sum.inr m
    have hselect : Function.Injective select := by
      intro i j hij
      rcases i with (u | n) | w <;> rcases j with (v | q) | z
      · exact congrArg (Sum.inl ∘ Sum.inl) (Subsingleton.elim u v)
      · simp [select] at hij
      · simp [select] at hij
      · simp [select] at hij
      · simp [select] at hij
        exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext hij)
      · exfalso
        simp [select] at hij
        exact hmT (hij ▸ n.2)
      · simp [select] at hij
      · exfalso
        simp [select] at hij
        exact hmT (hij.symm ▸ q.2)
      · exact congrArg Sum.inr (Subsingleton.elim w z)
    have hxy :
        DifferentialIndependent upperEndRationalCoordinateField
          (Sum.elim x y) := by
      have hcomp :=
        zetaRelativeShellMultiplierUpperEnd_differentialIndependent.comp
          select hselect
      convert hcomp using 1
      funext i
      rcases i with (u | n) | w <;> rfl
    have hnot :=
      GaloisForLFunctions.differentialIndependent_sum_right_not_mem_left_differentialAdjoin
        x y hxy ()
    apply hnot
    exact hST
      (subset_differentialAdjoin upperEndRationalCoordinateField _
        ⟨Sum.inr ⟨m, hmS⟩, rfl⟩)
  · intro hST
    apply differentialAdjoin_le upperEndRationalCoordinateField
    · rintro z ⟨u | m, rfl⟩
      · exact subset_differentialAdjoin upperEndRationalCoordinateField _
          ⟨Sum.inl u, rfl⟩
      · exact subset_differentialAdjoin upperEndRationalCoordinateField _
          ⟨Sum.inr ⟨m.1, hST m.2⟩, rfl⟩
    · exact derivationClosed_differentialAdjoin
        upperEndRationalCoordinateField _

/-- Equality of shell differential fields is equality of the underlying shell sets. -/
theorem relativeShellSubsetDifferentialField_eq_iff
    (S T : Set {m : ℕ // 12 ≤ m}) :
    relativeShellSubsetDifferentialField S =
        relativeShellSubsetDifferentialField T ↔
      S = T := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · exact
        (relativeShellSubsetDifferentialField_le_iff S T).mp
          h.le
    · exact
        (relativeShellSubsetDifferentialField_le_iff T S).mp
          h.ge
  · rintro rfl
    rfl

/-- The complete power-set family of shell labels embeds injectively into the differential-field
lattice. -/
theorem relativeShellSubsetDifferentialField_injective :
    Function.Injective relativeShellSubsetDifferentialField := by
  intro S T hST
  exact (relativeShellSubsetDifferentialField_eq_iff S T).mp hST

/-- **Arbitrary compositum law.**  Every nonempty family of shell fields composes to the field
whose source set is the union of the family. -/
theorem relativeShellSubsetDifferentialField_iSup
    {ι : Type*} [Nonempty ι]
    (S : ι → Set {m : ℕ // 12 ≤ m}) :
    (⨆ i, relativeShellSubsetDifferentialField (S i)) =
      relativeShellSubsetDifferentialField (⋃ i, S i) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact
      (relativeShellSubsetDifferentialField_le_iff (S i) (⋃ i, S i)).mpr
        (Set.subset_iUnion S i)
  · apply differentialAdjoin_le upperEndRationalCoordinateField
    · rintro z ⟨u | m, rfl⟩
      · let i : ι := Classical.choice inferInstance
        exact (le_iSup (fun j => relativeShellSubsetDifferentialField (S j)) i)
          (subset_differentialAdjoin upperEndRationalCoordinateField _
            ⟨Sum.inl u, rfl⟩)
      · have hm := m.2
        rw [Set.mem_iUnion] at hm
        obtain ⟨i, hi⟩ := hm
        exact (le_iSup (fun j => relativeShellSubsetDifferentialField (S j)) i)
          (subset_differentialAdjoin upperEndRationalCoordinateField _
            ⟨Sum.inr ⟨m.1, hi⟩, rfl⟩)
    · exact derivationClosed_iSup_intermediateField _
        (fun i => derivationClosed_differentialAdjoin
          upperEndRationalCoordinateField _)

/-- **Finite-support law.**  Every observable in an arbitrary shell-set field already belongs
to the field generated by a finite subset of those shell labels. -/
theorem relativeShellSubsetDifferentialField_exists_finset_support
    (S : Set {m : ℕ // 12 ≤ m}) {x : upperEndMeroField}
    (hx : x ∈ relativeShellSubsetDifferentialField S) :
    ∃ C : Finset {m : ℕ // 12 ≤ m},
      (C : Set {m : ℕ // 12 ≤ m}) ⊆ S ∧
        x ∈ relativeShellSubsetDifferentialField
          (C : Set {m : ℕ // 12 ≤ m}) := by
  let atom : Option S → Set {m : ℕ // 12 ≤ m}
    | none => ∅
    | some m => {m.1}
  have hunion : (⋃ i, atom i) = S := by
    ext m
    constructor
    · intro hm
      rw [Set.mem_iUnion] at hm
      obtain ⟨i, hi⟩ := hm
      rcases i with _ | i
      · simp [atom] at hi
      · have hmi : m = i.1 := by simpa [atom] using hi
        exact hmi ▸ i.2
    · intro hm
      rw [Set.mem_iUnion]
      exact ⟨some ⟨m, hm⟩, by simp [atom]⟩
  have hsup :=
    relativeShellSubsetDifferentialField_iSup atom
  rw [hunion] at hsup
  have hxi :
      x ∈ ⨆ i, relativeShellSubsetDifferentialField (atom i) := by
    rw [hsup]
    exact hx
  obtain ⟨t, ht⟩ :=
    IntermediateField.exists_finset_of_mem_iSup hxi
  let atomFinset : Option S → Finset {m : ℕ // 12 ≤ m}
    | none => ∅
    | some m => {m.1}
  let C : Finset {m : ℕ // 12 ≤ m} :=
    t.biUnion atomFinset
  refine ⟨C, ?_, ?_⟩
  · intro m hmC
    change m ∈ C at hmC
    simp only [C, Finset.mem_biUnion] at hmC
    obtain ⟨i, hit, hmi⟩ := hmC
    rcases i with _ | i
    · simp [atomFinset] at hmi
    · have hmeq : m = i.1 := by simpa [atomFinset] using hmi
      exact hmeq ▸ i.2
  · apply SetLike.le_def.mp ?_ ht
    apply iSup_le
    intro i
    apply iSup_le
    intro hit
    apply
      (relativeShellSubsetDifferentialField_le_iff
        (atom i) (C : Set {m : ℕ // 12 ≤ m})).mpr
    intro m hm
    rcases i with _ | i
    · simp [atom] at hm
    · have hmi : m = i.1 := by simpa [atom] using hm
      subst m
      change i.1 ∈ C
      simp only [C, Finset.mem_biUnion]
      exact ⟨some i, hit, by simp [atomFinset]⟩

/-- **No infinitary ghost law.**  A nonempty arbitrary intersection of shell fields is exactly
the field generated by the shell labels common to every member.  Finite support of field
expressions rules out an observable that survives all resolutions without source support in
their intersection. -/
theorem relativeShellSubsetDifferentialField_iInf
    {ι : Type*} [Nonempty ι]
    (S : ι → Set {m : ℕ // 12 ≤ m}) :
    (⨅ i, relativeShellSubsetDifferentialField (S i)) =
      relativeShellSubsetDifferentialField (⋂ i, S i) := by
  classical
  apply le_antisymm
  · intro x hx
    let i₀ : ι := Classical.choice inferInstance
    have hx₀ :
        x ∈ relativeShellSubsetDifferentialField (S i₀) :=
      (iInf_le
        (fun i => relativeShellSubsetDifferentialField (S i)) i₀) hx
    obtain ⟨C, -, hxC⟩ :=
      relativeShellSubsetDifferentialField_exists_finset_support
        (S i₀) hx₀
    let B : Set {m : ℕ // 12 ≤ m} := ⋂ i, S i
    have hexclude :
        ∀ m : {m : ℕ // 12 ≤ m}, m ∉ B → ∃ i, m ∉ S i := by
      intro m hm
      by_contra h
      apply hm
      rw [Set.mem_iInter]
      intro i
      by_contra hmi
      exact h ⟨i, hmi⟩
    let pick : {m : ℕ // 12 ≤ m} → ι :=
      fun m =>
        if hm : m ∈ B then i₀
        else Classical.choose (hexclude m hm)
    have hpick :
        ∀ m : {m : ℕ // 12 ≤ m}, m ∉ B → m ∉ S (pick m) := by
      intro m hm
      simp only [pick, dif_neg hm]
      exact Classical.choose_spec (hexclude m hm)
    let Bad : Finset {m : ℕ // 12 ≤ m} :=
      C.filter (fun m => m ∉ B)
    have hfinite :
        ∀ J : Finset {m : ℕ // 12 ≤ m},
          x ∈ relativeShellSubsetDifferentialField
            ((C : Set {m : ℕ // 12 ≤ m}) ∩
              ⋂ m ∈ J, S (pick m)) := by
      intro J
      induction J using Finset.induction_on with
      | empty =>
          simpa using hxC
      | @insert m J hm ih =>
          have hxm :
              x ∈ relativeShellSubsetDifferentialField (S (pick m)) :=
            (iInf_le
              (fun i => relativeShellSubsetDifferentialField (S i))
              (pick m)) hx
          have hboth :
              x ∈
                relativeShellSubsetDifferentialField
                    ((C : Set {m : ℕ // 12 ≤ m}) ∩
                      ⋂ n ∈ J, S (pick n)) ⊓
                  relativeShellSubsetDifferentialField (S (pick m)) :=
            ⟨ih, hxm⟩
          rw [relativeShellSubsetDifferentialField_inf] at hboth
          simpa [hm, Set.inter_assoc, Set.inter_left_comm,
            Set.inter_comm] using hboth
    have hxBad := hfinite Bad
    have hDB :
        ((C : Set {m : ℕ // 12 ≤ m}) ∩
            ⋂ m ∈ Bad, S (pick m)) ⊆ B := by
      intro m hm
      by_contra hmB
      have hmBad : m ∈ Bad := by
        simp only [Bad, Finset.mem_filter]
        exact ⟨hm.1, hmB⟩
      have hmAll := hm.2
      rw [Set.mem_iInter] at hmAll
      have hmAt := hmAll m
      rw [Set.mem_iInter] at hmAt
      exact (hpick m hmB) (hmAt hmBad)
    have hle :=
      (relativeShellSubsetDifferentialField_le_iff
        ((C : Set {m : ℕ // 12 ≤ m}) ∩
          ⋂ m ∈ Bad, S (pick m)) B).mpr hDB
    change x ∈ relativeShellSubsetDifferentialField (⋂ i, S i)
    change x ∈ relativeShellSubsetDifferentialField B
    exact hle hxBad
  · apply le_iInf
    intro i
    exact
      (relativeShellSubsetDifferentialField_le_iff (⋂ j, S j) (S i)).mpr
        (Set.iInter_subset S i)

/-- Source complements become exact relative complements between the common-zeta bottom field
and the full shell-frame top field. -/
theorem relativeShellSubsetDifferentialField_compl
    (S : Set {m : ℕ // 12 ≤ m}) :
    relativeShellSubsetDifferentialField S ⊓
        relativeShellSubsetDifferentialField Sᶜ =
      relativeShellSubsetDifferentialField ∅ ∧
    relativeShellSubsetDifferentialField S ⊔
        relativeShellSubsetDifferentialField Sᶜ =
      relativeShellSubsetDifferentialField Set.univ := by
  constructor
  · rw [relativeShellSubsetDifferentialField_inf]
    simp
  · rw [relativeShellSubsetDifferentialField_sup]
    simp

/-- Two distinct zero-free high-exponent shell tests have exactly the zeta differential field as
their common observable field. -/
theorem relativeShellTestDifferentialField_inf
    {m n : {m : ℕ // 12 ≤ m}} (hmn : m ≠ n) :
    relativeShellTestDifferentialField m ⊓
        relativeShellTestDifferentialField n =
      relativeShellCommonModeDifferentialField := by
  let select :
      Unit ⊕ (Unit ⊕ Unit) →
        Unit ⊕ {m : ℕ // 12 ≤ m}
    | Sum.inl u => Sum.inl u
    | Sum.inr (Sum.inl _) => Sum.inr m
    | Sum.inr (Sum.inr _) => Sum.inr n
  have hselect : Function.Injective select := by
    rintro (u | u) (v | v) huv
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · rcases v with v | v <;> simp [select] at huv
    · rcases u with u | u <;> simp [select] at huv
    · rcases u with u | u <;> rcases v with v | v
      · exact congrArg (Sum.inr ∘ Sum.inl) (Subsingleton.elim u v)
      · simp [select] at huv
        exact (hmn huv).elim
      · simp [select] at huv
        exact (hmn huv.symm).elim
      · exact congrArg (Sum.inr ∘ Sum.inr) (Subsingleton.elim u v)
  have hthree :
      DifferentialIndependent upperEndRationalCoordinateField
        (Sum.elim (fun _ : Unit => zetaUpperEndMero)
          (Sum.elim
            (fun _ : Unit => relativeShellMultiplierUpperEndCarrier m.1)
            (fun _ : Unit => relativeShellMultiplierUpperEndCarrier n.1))) := by
    have hcomp :=
      zetaRelativeShellMultiplierUpperEnd_differentialIndependent.comp
        select hselect
    convert hcomp using 1
    funext i
    rcases i with u | u
    · rfl
    · rcases u with u | u <;> rfl
  exact
    differentialIndependent_threeBlock_differentialAdjoin_inf
      (fun _ : Unit => zetaUpperEndMero)
      (fun _ : Unit => relativeShellMultiplierUpperEndCarrier m.1)
      (fun _ : Unit => relativeShellMultiplierUpperEndCarrier n.1)
      hthree

/-- The intersection of the complete countable shell-test family is exactly the zeta
differential field.  No additional common observable survives the infinite family. -/
theorem iInf_relativeShellTestDifferentialField :
    (⨅ m : {m : ℕ // 12 ≤ m}, relativeShellTestDifferentialField m) =
      relativeShellCommonModeDifferentialField := by
  let m₀ : {m : ℕ // 12 ≤ m} := ⟨12, by omega⟩
  let m₁ : {m : ℕ // 12 ≤ m} := ⟨13, by omega⟩
  apply le_antisymm
  · calc
      (⨅ m : {m : ℕ // 12 ≤ m}, relativeShellTestDifferentialField m) ≤
          relativeShellTestDifferentialField m₀ ⊓
            relativeShellTestDifferentialField m₁ :=
        le_inf (iInf_le _ m₀) (iInf_le _ m₁)
      _ = relativeShellCommonModeDifferentialField :=
        relativeShellTestDifferentialField_inf (by
          intro h
          have := congrArg Subtype.val h
          norm_num [m₀, m₁] at this)
  · apply le_iInf
    intro m
    unfold relativeShellCommonModeDifferentialField
      relativeShellTestDifferentialField differentialAdjoin
    rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨x, ⟨u, rfl⟩, k, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨zetaUpperEndMero, ⟨Sum.inl u, rfl⟩, k, rfl⟩

end

end RHTower
