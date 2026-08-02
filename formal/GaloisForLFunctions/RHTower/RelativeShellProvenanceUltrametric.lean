import GaloisForLFunctions.RHTower.RelativeShellCanonicalComplexityFiltration
import Mathlib.Analysis.Normed.Group.Seminorm

/-!
# Source-native ultrametric on transverse shell observables

Canonical provenance grade produces a non-Archimedean source seminorm:
common-field observables have size zero, while an observable with nonempty
private support has size `2 ^ grade`.  Its kernel is exactly the common
differential field.  Quotienting by that kernel gives an honest
non-Archimedean norm on transverse shell observables.

Private shell `m` has exact norm `2 ^ m`, so cofinal labels cannot disappear
in this source-native topology.  Unlike arbitrary target damping, this norm is
forced by the unique least support and its initial-shell filtration.

The same lower bound that prevents cofinal escape forces the quotient topology
to be discrete.  Thus this norm is an exact provenance invariant but cannot be
the missing mixed nuclear/complex topology in Deninger's comparison.
-/

open Set
open scoped Classical
open scoped Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Zero has empty private-shell provenance. -/
theorem relativeShellObservableSupport_zero :
    relativeShellObservableSupport
        (0 : RelativeShellFullObservable) = ∅ := by
  rw [relativeShellObservableSupport_eq_empty_iff]
  exact IntermediateField.zero_mem _

/-- Adding a common-field observable preserves canonical private support exactly. -/
theorem relativeShellObservableSupport_add_of_common
    (x c : RelativeShellFullObservable)
    (hc :
      (c : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)) :
    relativeShellObservableSupport (x + c) =
      relativeShellObservableSupport x := by
  have hcSupport :
      relativeShellObservableSupport c = ∅ :=
    (relativeShellObservableSupport_eq_empty_iff c).2 hc
  apply Set.Subset.antisymm
  · exact
      (relativeShellObservableSupport_add_subset x c).trans
        (by simp [hcSupport])
  · have hback :=
      relativeShellObservableSupport_add_subset
        (x + c) (-c)
    have hneg :
        relativeShellObservableSupport (-c) = ∅ := by
      rw [relativeShellObservableSupport_neg, hcSupport]
    have hxEq : x = (x + c) + (-c) := by ring
    rw [← hxEq] at hback
    exact hback.trans (by simp [hneg])

/--
Source-native size: zero on the common field and exponential in the largest
indispensable private label otherwise.
-/
def relativeShellProvenanceSize
    (x : RelativeShellFullObservable) : ℝ :=
  if relativeShellObservableSupport x = ∅ then 0
  else (2 : ℝ) ^ relativeShellObservableGrade x

theorem relativeShellProvenanceSize_nonneg
    (x : RelativeShellFullObservable) :
    0 ≤ relativeShellProvenanceSize x := by
  rw [relativeShellProvenanceSize]
  split_ifs
  · exact le_rfl
  · positivity

@[simp] theorem relativeShellProvenanceSize_zero :
    relativeShellProvenanceSize
        (0 : RelativeShellFullObservable) = 0 := by
  simp [relativeShellProvenanceSize,
    relativeShellObservableSupport_zero]

/-- Exact kernel of provenance size. -/
theorem relativeShellProvenanceSize_eq_zero_iff
    (x : RelativeShellFullObservable) :
    relativeShellProvenanceSize x = 0 ↔
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel) := by
  rw [relativeShellProvenanceSize]
  by_cases hx : relativeShellObservableSupport x = ∅
  · simp [hx,
      (relativeShellObservableSupport_eq_empty_iff x).1 hx]
  · have hpow :
        (2 : ℝ) ^ relativeShellObservableGrade x ≠ 0 := by
      positivity
    simp [hx, hpow,
      ← relativeShellObservableSupport_eq_empty_iff]

theorem relativeShellProvenanceSize_neg
    (x : RelativeShellFullObservable) :
    relativeShellProvenanceSize (-x) =
      relativeShellProvenanceSize x := by
  simp only [relativeShellProvenanceSize,
    relativeShellObservableSupport_neg,
    relativeShellObservableGrade_neg]

theorem relativeShellProvenanceSize_add_of_common
    (x c : RelativeShellFullObservable)
    (hc :
      (c : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)) :
    relativeShellProvenanceSize (x + c) =
      relativeShellProvenanceSize x := by
  have hs :=
    relativeShellObservableSupport_add_of_common x c hc
  have hg :
      relativeShellObservableGrade (x + c) =
        relativeShellObservableGrade x := by
    apply le_antisymm
    · exact
        relativeShellObservableGrade_le_of_support_subset hs.le
    · exact
        relativeShellObservableGrade_le_of_support_subset hs.ge
  simp only [relativeShellProvenanceSize, hs, hg]

/-- Provenance size satisfies the strong triangle inequality. -/
theorem relativeShellProvenanceSize_add_le_max
    (x y : RelativeShellFullObservable) :
    relativeShellProvenanceSize (x + y) ≤
      max (relativeShellProvenanceSize x)
        (relativeShellProvenanceSize y) := by
  by_cases hx : relativeShellObservableSupport x = ∅
  · have hxc :
        (x : upperEndMeroField) ∈
          relativeShellSubsetDifferentialField
            (∅ : Set RelativeShellLabel) :=
      (relativeShellObservableSupport_eq_empty_iff x).1 hx
    have hcomm : x + y = y + x := add_comm _ _
    rw [hcomm,
      relativeShellProvenanceSize_add_of_common y x hxc]
    exact le_max_right _ _
  by_cases hy : relativeShellObservableSupport y = ∅
  · have hyc :
        (y : upperEndMeroField) ∈
          relativeShellSubsetDifferentialField
            (∅ : Set RelativeShellLabel) :=
      (relativeShellObservableSupport_eq_empty_iff y).1 hy
    rw [relativeShellProvenanceSize_add_of_common x y hyc]
    exact le_max_left _ _
  by_cases hxy :
      relativeShellObservableSupport (x + y) = ∅
  · rw [relativeShellProvenanceSize, if_pos hxy]
    exact
      (relativeShellProvenanceSize_nonneg x).trans
        (le_max_left _ _)
  · rw [relativeShellProvenanceSize, if_neg hxy,
      relativeShellProvenanceSize, if_neg hx,
      relativeShellProvenanceSize, if_neg hy]
    have hgrade :=
      relativeShellObservableGrade_add_le x y
    by_cases hle :
        relativeShellObservableGrade x ≤
          relativeShellObservableGrade y
    · rw [max_eq_right hle] at hgrade
      have hp :
          (2 : ℝ) ^ relativeShellObservableGrade x ≤
            (2 : ℝ) ^ relativeShellObservableGrade y :=
        pow_le_pow_right₀ (by norm_num) hle
      rw [max_eq_right hp]
      exact
        pow_le_pow_right₀ (by norm_num) hgrade
    · have hle' :
          relativeShellObservableGrade y ≤
            relativeShellObservableGrade x :=
        le_of_not_ge hle
      rw [max_eq_left hle'] at hgrade
      have hp :
          (2 : ℝ) ^ relativeShellObservableGrade y ≤
            (2 : ℝ) ^ relativeShellObservableGrade x :=
        pow_le_pow_right₀ (by norm_num) hle'
      rw [max_eq_left hp]
      exact
        pow_le_pow_right₀ (by norm_num) hgrade

/-- Non-Archimedean provenance seminorm on the full shell field. -/
def relativeShellProvenanceNonarchSeminorm :
    NonarchAddGroupSeminorm RelativeShellFullObservable where
  toFun := relativeShellProvenanceSize
  map_zero' := relativeShellProvenanceSize_zero
  add_le_max' := relativeShellProvenanceSize_add_le_max
  neg' := relativeShellProvenanceSize_neg

@[simp] theorem relativeShellProvenanceNonarchSeminorm_apply
    (x : RelativeShellFullObservable) :
    relativeShellProvenanceNonarchSeminorm x =
      relativeShellProvenanceSize x := rfl

/-- Seminorm radical is exactly the common bottom differential field. -/
theorem relativeShellProvenanceNonarchSeminorm_kernel
    (x : RelativeShellFullObservable) :
    relativeShellProvenanceNonarchSeminorm x = 0 ↔
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel) :=
  relativeShellProvenanceSize_eq_zero_iff x

theorem relativeShellProvenanceSize_common :
    relativeShellProvenanceSize
        relativeShellCommonObservable = 0 := by
  rw [relativeShellProvenanceSize_eq_zero_iff]
  exact
    (relativeShellObservableSupport_eq_empty_iff _).1
      relativeShellCommonObservable_support

/-- Private shell `m` has exact provenance size `2 ^ m`. -/
theorem relativeShellProvenanceSize_multiplier
    (m : RelativeShellLabel) :
    relativeShellProvenanceSize
        (relativeShellMultiplierObservable m) =
      (2 : ℝ) ^ m.1 := by
  rw [relativeShellProvenanceSize,
    relativeShellMultiplierObservable_support,
    if_neg (Set.singleton_ne_empty m),
    relativeShellMultiplierObservable_grade]

/-- Additive subgroup given by the common bottom differential field. -/
def relativeShellCommonAddSubgroup :
    AddSubgroup RelativeShellFullObservable where
  carrier :=
    {x |
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)}
  zero_mem' := by
    change
      (0 : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)
    exact IntermediateField.zero_mem _
  add_mem' := by
    intro x y hx hy
    change
      ((x + y : RelativeShellFullObservable) :
        upperEndMeroField) ∈
          relativeShellSubsetDifferentialField
            (∅ : Set RelativeShellLabel)
    exact IntermediateField.add_mem _ hx hy
  neg_mem' := by
    intro x hx
    change
      (-(x : upperEndMeroField)) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)
    exact IntermediateField.neg_mem _ hx

@[simp] theorem mem_relativeShellCommonAddSubgroup
    (x : RelativeShellFullObservable) :
    x ∈ relativeShellCommonAddSubgroup ↔
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel) :=
  Iff.rfl

/-- Transverse shell observables modulo the common zeta differential field. -/
abbrev RelativeShellTransverseQuotient :=
  RelativeShellFullObservable ⧸ relativeShellCommonAddSubgroup

theorem relativeShellProvenanceSize_eq_of_sub_mem_common
    {x y : RelativeShellFullObservable}
    (hxy : x - y ∈ relativeShellCommonAddSubgroup) :
    relativeShellProvenanceSize x =
      relativeShellProvenanceSize y := by
  have hx : x = y + (x - y) := by ring
  rw [hx]
  rw [mem_relativeShellCommonAddSubgroup] at hxy
  exact
    relativeShellProvenanceSize_add_of_common
      y (x - y) hxy

/-- Quotient value induced by provenance size. -/
def relativeShellTransverseNormValue
    (q : RelativeShellTransverseQuotient) : ℝ :=
  Quotient.liftOn q relativeShellProvenanceSize
    (fun x y hxy => by
      have hclasses :
          (x : RelativeShellTransverseQuotient) = y :=
        Quot.sound hxy
      exact
        relativeShellProvenanceSize_eq_of_sub_mem_common
          ((QuotientAddGroup.eq_iff_sub_mem).mp hclasses))

@[simp] theorem relativeShellTransverseNormValue_mk
    (x : RelativeShellFullObservable) :
    relativeShellTransverseNormValue
        (x : RelativeShellTransverseQuotient) =
      relativeShellProvenanceSize x := rfl

theorem relativeShellTransverseNormValue_nonneg
    (q : RelativeShellTransverseQuotient) :
    0 ≤ relativeShellTransverseNormValue q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact relativeShellProvenanceSize_nonneg x

/-- Honest non-Archimedean norm after quotienting the exact common radical. -/
def relativeShellTransverseNonarchNorm :
    NonarchAddGroupNorm RelativeShellTransverseQuotient where
  toFun := relativeShellTransverseNormValue
  map_zero' := by
    change relativeShellProvenanceSize 0 = 0
    exact relativeShellProvenanceSize_zero
  add_le_max' := by
    intro q r
    refine Quotient.inductionOn q ?_
    intro x
    refine Quotient.inductionOn r ?_
    intro y
    exact relativeShellProvenanceSize_add_le_max x y
  neg' := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact relativeShellProvenanceSize_neg x
  eq_zero_of_map_eq_zero' := by
    intro q hq
    refine Quotient.inductionOn q ?_ hq
    intro x hx
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    rw [sub_zero, mem_relativeShellCommonAddSubgroup]
    exact
      (relativeShellProvenanceSize_eq_zero_iff x).mp hx

@[simp] theorem relativeShellTransverseNonarchNorm_apply
    (q : RelativeShellTransverseQuotient) :
    relativeShellTransverseNonarchNorm q =
      relativeShellTransverseNormValue q := rfl

/-- Cofinal private labels have exponentially growing exact transverse norm. -/
theorem relativeShellTransverseNonarchNorm_multiplier
    (m : RelativeShellLabel) :
    relativeShellTransverseNonarchNorm
        (relativeShellMultiplierObservable m :
          RelativeShellTransverseQuotient) =
      (2 : ℝ) ^ m.1 := by
  rw [relativeShellTransverseNonarchNorm_apply,
    relativeShellTransverseNormValue_mk,
    relativeShellProvenanceSize_multiplier]

/-- Additive norm underlying the transverse non-Archimedean norm. -/
def relativeShellTransverseAddGroupNorm :
    AddGroupNorm RelativeShellTransverseQuotient where
  toFun := relativeShellTransverseNormValue
  map_zero' := relativeShellTransverseNonarchNorm.map_zero'
  add_le' := by
    intro q r
    exact
      (relativeShellTransverseNonarchNorm.add_le_max' q r).trans
        (max_le
          (le_add_of_nonneg_right
            (relativeShellTransverseNormValue_nonneg r))
          (le_add_of_nonneg_left
            (relativeShellTransverseNormValue_nonneg q)))
  neg' := relativeShellTransverseNonarchNorm.neg'
  eq_zero_of_map_eq_zero' :=
    relativeShellTransverseNonarchNorm.eq_zero_of_map_eq_zero'

/--
Canonical normed additive-group structure on transverse shell observables,
obtained by quotienting out the common field.
-/
@[reducible] noncomputable def relativeShellTransverseNormedAddCommGroup :
    NormedAddCommGroup RelativeShellTransverseQuotient :=
  relativeShellTransverseAddGroupNorm.toNormedAddCommGroup

/--
Every nonzero transverse class has provenance norm at least one.  This is the
sharp obstruction behind the topology below: increasing maximum-label weights
cannot admit small nonzero transverse classes.
-/
theorem relativeShellTransverseNormValue_nonzero_lower_bound
    (q : RelativeShellTransverseQuotient)
    (hq : q ≠ 0) :
    1 ≤ relativeShellTransverseNormValue q := by
  refine Quotient.inductionOn q ?_ hq
  intro x hx
  have hs : relativeShellObservableSupport x ≠ ∅ := by
    intro hs
    apply hx
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    rw [sub_zero, mem_relativeShellCommonAddSubgroup]
    exact
      (relativeShellObservableSupport_eq_empty_iff x).1 hs
  rw [relativeShellTransverseNormValue_mk,
    relativeShellProvenanceSize, if_neg hs]
  exact one_le_pow₀ (by norm_num)

/--
The canonical maximum-grade norm induces the discrete topology.  Consequently
it records exact finite provenance but is too strong to model a mixed
nuclear/complex completion.
-/
theorem relativeShellTransverseNormedAddCommGroup_discrete :
    let _ : NormedAddCommGroup RelativeShellTransverseQuotient :=
      relativeShellTransverseNormedAddCommGroup
    DiscreteTopology RelativeShellTransverseQuotient := by
  letI : NormedAddCommGroup RelativeShellTransverseQuotient :=
    relativeShellTransverseNormedAddCommGroup
  apply DiscreteTopology.of_forall_le_norm (r := 1)
  · norm_num
  · intro q hq
    exact
      relativeShellTransverseNormValue_nonzero_lower_bound
        q hq

end

end RHTower
