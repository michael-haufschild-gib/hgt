/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.MilnorGlobalReciprocity
import GaloisForLFunctions.HTGeometry.MilnorKFiniteDegreeOne

/-!
# A degree-two Milnor Hasse principle over finite constant fields

Projective-line Milnor reciprocity identifies the kernel of all degree-two residues on `F(t)`
with the constant-field image of `K₂ᴹ(F)`.  When `F` is finite that constant group vanishes.
Thus a degree-two Milnor class over `F(t)` is determined by its residues at all finite places and
at infinity.  This is the Milnor-symbol local-global statement adjacent to the degree-two Brauer
Hasse principle; no comparison between Milnor `K₂` and Brauer classes is assumed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable {F : Type*} [Field F] [Finite F]

/-- The second Milnor `K`-group of a finite field is trivial. -/
theorem finiteField_milnorKTwo_eq_zero (x : MilnorKDeg F 2) : x = 0 := by
  letI : Fintype F := Fintype.ofFinite F
  exact milnorKDeg_eq_zero_of_finite 0 x

/-- Degree-two projective-line residues over a finite field detect the zero global Milnor class.
This is the kernel, or Hasse-principle, half of the degree-two residue sequence. -/
theorem finiteField_rationalFunctionMilnorKTwo_allResidue_eq_zero_iff
    (x : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialAllResidue (F := F) 1 x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ :=
      (rationalFunctionMilnorKTwo_allResidue_eq_zero_iff_constant (F := F) x).mp hx
    rw [hc, finiteField_milnorKTwo_eq_zero c, map_zero]
  · intro hx
    rw [hx, map_zero]

/-- All degree-two projective-line residues jointly determine a Milnor class over a finite
constant field. -/
theorem finiteField_rationalFunctionMilnorKTwo_allResidue_injective :
    Function.Injective (milnorPolynomialAllResidue (F := F) 1) := by
  intro x y hxy
  have hzero : milnorPolynomialAllResidue (F := F) 1 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdiff : x - y = 0 :=
    (finiteField_rationalFunctionMilnorKTwo_allResidue_eq_zero_iff (F := F) (x - y)).mp hzero
  exact sub_eq_zero.mp hdiff

/-- Two degree-two Milnor classes over a finite constant field have the same complete residue
profile exactly when they are equal. -/
theorem finiteField_rationalFunctionMilnorKTwo_allResidue_eq_iff
    (x y : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialAllResidue (F := F) 1 x = milnorPolynomialAllResidue (F := F) 1 y ↔
      x = y :=
  ⟨fun hxy ↦ finiteField_rationalFunctionMilnorKTwo_allResidue_injective (F := F) hxy, fun hxy ↦
    congrArg (milnorPolynomialAllResidue (F := F) 1) hxy⟩

/-- The full degree-two residue profile of a global class automatically satisfies the projective
line reciprocity relation. -/
noncomputable def finiteField_rationalFunctionMilnorKTwoGlobalResidueAddHom :
    MilnorKDeg (RatFunc F) 2 →+
      (milnorPolynomialGlobalSum (F := F) 1).ker := by
  let hExact := (rationalFunctionMilnorKTwo_projectiveLine_exact (F := F)).2.2.1
  refine
    { toFun := fun x ↦ ⟨milnorPolynomialAllResidue (F := F) 1 x,
        hExact _ |>.mpr ⟨x, rfl⟩⟩
      map_zero' := ?_
      map_add' := ?_ }
  · apply Subtype.ext
    exact map_zero _
  · intro x y
    apply Subtype.ext
    exact map_add _ _ _

/-- Global degree-two Milnor classes over a finite constant field are additively equivalent to
all residue profiles satisfying the one reciprocity relation.  This packages both the Hasse
injectivity statement and the global-reciprocity surjectivity statement. -/
noncomputable def finiteField_rationalFunctionMilnorKTwoGlobalResidueEquiv :
    MilnorKDeg (RatFunc F) 2 ≃+
      (milnorPolynomialGlobalSum (F := F) 1).ker :=
  AddEquiv.ofBijective (finiteField_rationalFunctionMilnorKTwoGlobalResidueAddHom (F := F))
    ⟨(by
      intro x y hxy
      apply finiteField_rationalFunctionMilnorKTwo_allResidue_injective (F := F)
      exact congrArg Subtype.val hxy),
      (by
        intro z
        obtain ⟨x, hx⟩ := rationalFunctionMilnor_exists_of_globalSum_eq_zero (F := F) 1 z
        exact ⟨x, Subtype.ext hx⟩)⟩

/-- The finite-field global residue equivalence is represented by the usual complete residue
profile. -/
theorem finiteField_rationalFunctionMilnorKTwoGlobalResidueEquiv_apply
    (x : MilnorKDeg (RatFunc F) 2) :
    (finiteField_rationalFunctionMilnorKTwoGlobalResidueEquiv (F := F) x).1 =
      milnorPolynomialAllResidue (F := F) 1 x :=
  rfl

/-- Every full degree-two residue profile satisfying global reciprocity has a unique global
Milnor class over a finite constant field.  This is the exact Hasse-principle form of the
projective-line sequence, before identifying Milnor classes with Brauer classes. -/
theorem finiteField_rationalFunctionMilnorKTwo_existsUnique_of_globalSum_eq_zero
    (z : (milnorPolynomialGlobalSum (F := F) 1).ker) :
    ∃! x : MilnorKDeg (RatFunc F) 2,
      milnorPolynomialAllResidue (F := F) 1 x = z := by
  obtain ⟨x, hx⟩ :=
    (finiteField_rationalFunctionMilnorKTwoGlobalResidueEquiv (F := F)).surjective z
  refine ⟨x, ?_, ?_⟩
  · exact congrArg Subtype.val hx
  · intro y hy
    apply finiteField_rationalFunctionMilnorKTwo_allResidue_injective (F := F)
    exact hy.trans (congrArg Subtype.val hx).symm

/-- Every finite degree-two residue profile over a finite constant field has one and only one
global realization once reciprocity supplies its forced infinity residue. -/
theorem finiteField_rationalFunctionMilnorKTwo_existsUnique_with_finiteResidues
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    ∃! x : MilnorKDeg (RatFunc F) 2,
      milnorPolynomialAllResidue (F := F) 1 x =
        (z, -milnorPolynomialTotalNorm (F := F) 1 z) := by
  obtain ⟨x, hx⟩ := rationalFunctionMilnorKTwo_exists_with_finiteResidues (F := F) z
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply finiteField_rationalFunctionMilnorKTwo_allResidue_injective (F := F)
  exact hy.trans hx.symm

/-- In every Milnor degree at least two, all projective-line residues over a finite constant field
detect the zero global class. -/
theorem finiteField_rationalFunctionMilnor_allResidue_eq_zero_iff
    (n : ℕ) (x : MilnorKDeg (RatFunc F) (n + 2)) :
    milnorPolynomialAllResidue (F := F) (n + 1) x = 0 ↔ x = 0 := by
  letI : Fintype F := Fintype.ofFinite F
  constructor
  · intro hx
    obtain ⟨c, hc⟩ :=
      (rationalFunctionMilnor_allResidue_eq_iff_sub_eq_constant (F := F) (n + 1) x 0).mp
        (by simpa using hx)
    rw [sub_zero] at hc
    have hc0 : c = 0 := by
      clear hc
      have hdeg : n + 1 + 1 = 2 + n := by
        calc
          n + 1 + 1 = n + (1 + 1) := Nat.add_assoc n 1 1
          _ = n + 2 := rfl
          _ = 2 + n := Nat.add_comm n 2
      revert c
      rw [hdeg]
      intro c
      exact milnorKDeg_eq_zero_of_finite n c
    rw [hc, hc0, map_zero]
  · intro hx
    rw [hx, map_zero]

/-- In every Milnor degree at least two, the full projective-line residue map over a finite
constant field is injective. -/
theorem finiteField_rationalFunctionMilnor_allResidue_injective
    (n : ℕ) :
    Function.Injective (milnorPolynomialAllResidue (F := F) (n + 1)) := by
  intro x y hxy
  have hzero : milnorPolynomialAllResidue (F := F) (n + 1) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdiff : x - y = 0 :=
    (finiteField_rationalFunctionMilnor_allResidue_eq_zero_iff (F := F) n (x - y)).mp hzero
  exact sub_eq_zero.mp hdiff

/-- Every reciprocity-compatible full projective-line residue profile in Milnor degree at least
two has a unique global realization over a finite constant field. -/
theorem finiteField_rationalFunctionMilnor_existsUnique_of_globalSum_eq_zero
    (n : ℕ) (z : (milnorPolynomialGlobalSum (F := F) (n + 1)).ker) :
    ∃! x : MilnorKDeg (RatFunc F) (n + 2),
      milnorPolynomialAllResidue (F := F) (n + 1) x = z := by
  obtain ⟨x, hx⟩ :=
    rationalFunctionMilnor_exists_of_globalSum_eq_zero (F := F) (n + 1) z
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply finiteField_rationalFunctionMilnor_allResidue_injective (F := F) n
  exact hy.trans hx.symm

/-- Finite residue data in every Milnor degree at least two have a unique global realization;
global reciprocity supplies its infinity residue. -/
theorem finiteField_rationalFunctionMilnor_existsUnique_with_finiteResidues
    (n : ℕ) (z : MilnorPolynomialTotalResidueTarget (F := F) (n + 1)) :
    ∃! x : MilnorKDeg (RatFunc F) (n + 2),
      milnorPolynomialAllResidue (F := F) (n + 1) x =
        (z, -milnorPolynomialTotalNorm (F := F) (n + 1) z) := by
  obtain ⟨x, hx⟩ :=
    rationalFunctionMilnor_exists_with_finiteResidues (F := F) (n + 1) z
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply finiteField_rationalFunctionMilnor_allResidue_injective (F := F) n
  exact hy.trans hx.symm

/-- In every Milnor degree at least two, two global classes over a finite constant field have
the same complete projective-line residue profile exactly when they are equal. -/
theorem finiteField_rationalFunctionMilnor_allResidue_eq_iff
    (n : ℕ) (x y : MilnorKDeg (RatFunc F) (n + 2)) :
    milnorPolynomialAllResidue (F := F) (n + 1) x =
      milnorPolynomialAllResidue (F := F) (n + 1) y ↔ x = y :=
  ⟨fun hxy ↦ finiteField_rationalFunctionMilnor_allResidue_injective (F := F) n hxy,
    fun hxy ↦ congrArg (milnorPolynomialAllResidue (F := F) (n + 1)) hxy⟩

/-- The complete residue profile in every Milnor degree at least two, with its reciprocity proof
attached. -/
noncomputable def finiteField_rationalFunctionMilnorGlobalResidueAddHom
    (n : ℕ) :
    MilnorKDeg (RatFunc F) (n + 2) →+
      (milnorPolynomialGlobalSum (F := F) (n + 1)).ker := by
  refine
    { toFun := fun x ↦ ⟨milnorPolynomialAllResidue (F := F) (n + 1) x,
        ?_⟩
      map_zero' := ?_
      map_add' := ?_ }
  · exact (milnorPolynomialProjectiveLine_exact (F := F) (n + 1)).2.2.1 _ |>.mpr ⟨x, rfl⟩
  · apply Subtype.ext
    exact map_zero _
  · intro x y
    apply Subtype.ext
    exact map_add _ _ _

/-- The full finite-field projective-line Hasse sequence in every Milnor degree at least two:
global classes are additively equivalent to residue profiles satisfying global reciprocity. -/
noncomputable def finiteField_rationalFunctionMilnorGlobalResidueEquiv
    (n : ℕ) :
    MilnorKDeg (RatFunc F) (n + 2) ≃+
      (milnorPolynomialGlobalSum (F := F) (n + 1)).ker :=
  AddEquiv.ofBijective (finiteField_rationalFunctionMilnorGlobalResidueAddHom (F := F) n)
    ⟨(by
      intro x y hxy
      apply finiteField_rationalFunctionMilnor_allResidue_injective (F := F) n
      exact congrArg Subtype.val hxy),
      fun z ↦ by
        obtain ⟨x, hx⟩ :=
          rationalFunctionMilnor_exists_of_globalSum_eq_zero (F := F) (n + 1) z
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The all-degree finite-field Hasse equivalence is represented by the usual complete residue
profile. -/
theorem finiteField_rationalFunctionMilnorGlobalResidueEquiv_apply
    (n : ℕ) (x : MilnorKDeg (RatFunc F) (n + 2)) :
    (finiteField_rationalFunctionMilnorGlobalResidueEquiv (F := F) n x).1 =
      milnorPolynomialAllResidue (F := F) (n + 1) x :=
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
