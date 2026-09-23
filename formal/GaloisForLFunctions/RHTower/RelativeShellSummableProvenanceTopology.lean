import GaloisForLFunctions.RHTower.RelativeShellProvenanceUltrametric
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summable provenance topology and the cofinal-escape boundary

The increasing maximum-grade provenance norm is exact but discrete.  This file
constructs the opposite canonical model: give private label `m` dyadic weight
`2⁻ᵐ` and sum the weights in the unique least finite support.

The resulting seminorm still has the common zeta differential field as its
exact kernel.  After quotienting, it is an honest additive norm and its
topology is non-discrete.  However, the class of the cofinal private generator
at label `n + 12` converges to zero.

Thus exact common-kernel separation and non-discreteness are compatible, but
only here at the cost of cofinal private-shell escape.  Together with the
discreteness theorem for increasing maximum grade, this gives a precise
topological design constraint for any missing mixed Deninger/Meyer comparison:
it must use more structure than one provenance norm if it is to be both
non-discrete and uniformly faithful to cofinal private labels.
-/

open Set Filter
open scoped Classical BigOperators Topology
open scoped Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Dyadic weight assigned to private shell label `m`. -/
def relativeShellInverseLabelWeight
    (m : RelativeShellLabel) : ℝ :=
  ((2 : ℝ)⁻¹) ^ m.1

theorem relativeShellInverseLabelWeight_pos
    (m : RelativeShellLabel) :
    0 < relativeShellInverseLabelWeight m := by
  exact pow_pos (by norm_num) _

/--
Dyadic mass of the unique least finite private-shell support of an observable.
-/
def relativeShellSummableProvenanceMass
    (x : RelativeShellFullObservable) : ℝ :=
  ∑ m ∈ relativeShellObservableSupportFinset x,
    relativeShellInverseLabelWeight m

private theorem relativeShellInverseLabelWeight_sum_union_le
    (s t : Finset RelativeShellLabel) :
    ∑ m ∈ s ∪ t, relativeShellInverseLabelWeight m ≤
      (∑ m ∈ s, relativeShellInverseLabelWeight m) +
        ∑ m ∈ t, relativeShellInverseLabelWeight m := by
  calc
    ∑ m ∈ s ∪ t, relativeShellInverseLabelWeight m =
        (∑ m ∈ s, relativeShellInverseLabelWeight m) +
          ∑ m ∈ t \ s,
            relativeShellInverseLabelWeight m := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union]
    _ ≤ (∑ m ∈ s, relativeShellInverseLabelWeight m) +
          ∑ m ∈ t, relativeShellInverseLabelWeight m := by
      simpa [add_comm] using add_le_add_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          Finset.sdiff_subset
          (fun m _ _ =>
            (relativeShellInverseLabelWeight_pos m).le))
        (∑ m ∈ s, relativeShellInverseLabelWeight m)

theorem relativeShellObservableSupportFinset_add_subset
    (x y : RelativeShellFullObservable) :
    relativeShellObservableSupportFinset (x + y) ⊆
      relativeShellObservableSupportFinset x ∪
        relativeShellObservableSupportFinset y := by
  intro m hm
  have hmSupport :
      m ∈ relativeShellObservableSupport (x + y) := by
    have hmSet :
        m ∈
          (relativeShellObservableSupportFinset (x + y) :
            Set RelativeShellLabel) := hm
    rwa [coe_relativeShellObservableSupportFinset] at hmSet
  have hmUnion :=
    relativeShellObservableSupport_add_subset x y hmSupport
  rcases hmUnion with hmx | hmy
  · apply Finset.mem_union_left
    have hmSet :
        m ∈
          (relativeShellObservableSupportFinset x :
            Set RelativeShellLabel) := by
      rwa [coe_relativeShellObservableSupportFinset]
    exact hmSet
  · apply Finset.mem_union_right
    have hmSet :
        m ∈
          (relativeShellObservableSupportFinset y :
            Set RelativeShellLabel) := by
      rwa [coe_relativeShellObservableSupportFinset]
    exact hmSet

theorem relativeShellSummableProvenanceMass_nonneg
    (x : RelativeShellFullObservable) :
    0 ≤ relativeShellSummableProvenanceMass x := by
  exact Finset.sum_nonneg fun _ _ =>
    (relativeShellInverseLabelWeight_pos _).le

theorem relativeShellSummableProvenanceMass_add_le
    (x y : RelativeShellFullObservable) :
    relativeShellSummableProvenanceMass (x + y) ≤
      relativeShellSummableProvenanceMass x +
        relativeShellSummableProvenanceMass y := by
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg
      (relativeShellObservableSupportFinset_add_subset x y)
      (fun m _ _ =>
        (relativeShellInverseLabelWeight_pos m).le)).trans
      (relativeShellInverseLabelWeight_sum_union_le
        (relativeShellObservableSupportFinset x)
        (relativeShellObservableSupportFinset y))

/-- Exact kernel of dyadic support mass. -/
theorem relativeShellSummableProvenanceMass_eq_zero_iff
    (x : RelativeShellFullObservable) :
    relativeShellSummableProvenanceMass x = 0 ↔
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel) := by
  rw [← relativeShellObservableSupport_eq_empty_iff]
  constructor
  · intro hx
    by_contra hs
    have hfin :
        (relativeShellObservableSupportFinset x).Nonempty := by
      have hsnon :
          (relativeShellObservableSupport x).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hs
      obtain ⟨m, hm⟩ := hsnon
      refine ⟨m, ?_⟩
      have hmSet :
          m ∈
            (relativeShellObservableSupportFinset x :
              Set RelativeShellLabel) := by
        rwa [coe_relativeShellObservableSupportFinset]
      exact hmSet
    have hpos :
        0 < relativeShellSummableProvenanceMass x :=
      Finset.sum_pos
        (fun m _ => relativeShellInverseLabelWeight_pos m)
        hfin
    exact hpos.ne' hx
  · intro hs
    have hfin :
        relativeShellObservableSupportFinset x = ∅ := by
      apply Finset.ext
      intro m
      change
        m ∈
            (relativeShellObservableSupportFinset x :
              Set RelativeShellLabel) ↔
          m ∈ (∅ : Finset RelativeShellLabel)
      rw [coe_relativeShellObservableSupportFinset, hs]
      simp
    simp [relativeShellSummableProvenanceMass, hfin]

theorem relativeShellSummableProvenanceMass_neg
    (x : RelativeShellFullObservable) :
    relativeShellSummableProvenanceMass (-x) =
      relativeShellSummableProvenanceMass x := by
  have hfin :
      relativeShellObservableSupportFinset (-x) =
        relativeShellObservableSupportFinset x := by
    apply Finset.ext
    intro m
    change
      m ∈
          (relativeShellObservableSupportFinset (-x) :
            Set RelativeShellLabel) ↔
        m ∈
          (relativeShellObservableSupportFinset x :
            Set RelativeShellLabel)
    rw [coe_relativeShellObservableSupportFinset,
      coe_relativeShellObservableSupportFinset,
      relativeShellObservableSupport_neg]
  simp [relativeShellSummableProvenanceMass, hfin]

theorem relativeShellSummableProvenanceMass_add_of_common
    (x c : RelativeShellFullObservable)
    (hc :
      (c : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel)) :
    relativeShellSummableProvenanceMass (x + c) =
      relativeShellSummableProvenanceMass x := by
  have hfin :
      relativeShellObservableSupportFinset (x + c) =
        relativeShellObservableSupportFinset x := by
    apply Finset.ext
    intro m
    change
      m ∈
          (relativeShellObservableSupportFinset (x + c) :
            Set RelativeShellLabel) ↔
        m ∈
          (relativeShellObservableSupportFinset x :
            Set RelativeShellLabel)
    rw [coe_relativeShellObservableSupportFinset,
      coe_relativeShellObservableSupportFinset,
      relativeShellObservableSupport_add_of_common x c hc]
  simp [relativeShellSummableProvenanceMass, hfin]

theorem relativeShellSummableProvenanceMass_eq_of_sub_mem_common
    {x y : RelativeShellFullObservable}
    (hxy : x - y ∈ relativeShellCommonAddSubgroup) :
    relativeShellSummableProvenanceMass x =
      relativeShellSummableProvenanceMass y := by
  have hx : x = y + (x - y) := by ring
  rw [hx]
  rw [mem_relativeShellCommonAddSubgroup] at hxy
  exact
    relativeShellSummableProvenanceMass_add_of_common
      y (x - y) hxy

/-- Quotient value induced by dyadic provenance mass. -/
def relativeShellSummableTransverseNormValue
    (q : RelativeShellTransverseQuotient) : ℝ :=
  Quotient.liftOn q relativeShellSummableProvenanceMass
    (fun x y hxy => by
      have hclasses :
          (x : RelativeShellTransverseQuotient) = y :=
        Quot.sound hxy
      exact
        relativeShellSummableProvenanceMass_eq_of_sub_mem_common
          ((QuotientAddGroup.eq_iff_sub_mem).mp hclasses))

@[simp] theorem relativeShellSummableTransverseNormValue_mk
    (x : RelativeShellFullObservable) :
    relativeShellSummableTransverseNormValue
        (x : RelativeShellTransverseQuotient) =
      relativeShellSummableProvenanceMass x := rfl

/-- Honest additive norm after quotienting the exact common radical. -/
def relativeShellSummableTransverseAddGroupNorm :
    AddGroupNorm RelativeShellTransverseQuotient where
  toFun := relativeShellSummableTransverseNormValue
  map_zero' := by
    change relativeShellSummableProvenanceMass 0 = 0
    rw [relativeShellSummableProvenanceMass_eq_zero_iff]
    exact IntermediateField.zero_mem _
  add_le' := by
    intro q r
    refine Quotient.inductionOn q ?_
    intro x
    refine Quotient.inductionOn r ?_
    intro y
    exact relativeShellSummableProvenanceMass_add_le x y
  neg' := by
    intro q
    refine Quotient.inductionOn q ?_
    exact relativeShellSummableProvenanceMass_neg
  eq_zero_of_map_eq_zero' := by
    intro q hq
    refine Quotient.inductionOn q ?_ hq
    intro x hx
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    rw [sub_zero, mem_relativeShellCommonAddSubgroup]
    exact
      (relativeShellSummableProvenanceMass_eq_zero_iff x).mp hx

/-- Normed additive group induced by dyadic provenance mass. -/
@[reducible] noncomputable def
    relativeShellSummableTransverseNormedAddCommGroup :
    NormedAddCommGroup RelativeShellTransverseQuotient :=
  relativeShellSummableTransverseAddGroupNorm.toNormedAddCommGroup

theorem relativeShellObservableSupportFinset_multiplier
    (m : RelativeShellLabel) :
    relativeShellObservableSupportFinset
        (relativeShellMultiplierObservable m) = {m} := by
  apply Finset.ext
  intro n
  change
    n ∈
        (relativeShellObservableSupportFinset
          (relativeShellMultiplierObservable m) :
            Set RelativeShellLabel) ↔
      n ∈ ({m} : Finset RelativeShellLabel)
  rw [coe_relativeShellObservableSupportFinset,
    relativeShellMultiplierObservable_support]
  simp

/-- Private shell `m` has exact dyadic transverse mass `2⁻ᵐ`. -/
theorem relativeShellSummableProvenanceMass_multiplier
    (m : RelativeShellLabel) :
    relativeShellSummableProvenanceMass
        (relativeShellMultiplierObservable m) =
      ((2 : ℝ)⁻¹) ^ m.1 := by
  simp [relativeShellSummableProvenanceMass,
    relativeShellObservableSupportFinset_multiplier,
    relativeShellInverseLabelWeight]

/-- Explicit cofinal shell sequence, beginning at the first admissible label. -/
def relativeShellCofinalLabel
    (n : ℕ) : RelativeShellLabel :=
  ⟨n + 12, by omega⟩

/-- Exact dyadic norm values along the cofinal private-shell sequence tend to zero. -/
theorem relativeShellSummableTransverseNormValue_cofinal_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        relativeShellSummableTransverseNormValue
          (relativeShellMultiplierObservable
            (relativeShellCofinalLabel n) :
              RelativeShellTransverseQuotient))
      atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity) (by norm_num)
  have hscaled :=
    hpow.const_mul (((2 : ℝ)⁻¹) ^ (12 : ℕ))
  simpa [relativeShellSummableTransverseNormValue_mk,
    relativeShellSummableProvenanceMass_multiplier,
    relativeShellCofinalLabel, pow_add, mul_comm] using hscaled

/-- Cofinal private-shell classes converge to zero in the dyadic norm topology. -/
theorem relativeShellCofinalMultiplier_tendsto_zero :
    let _ : NormedAddCommGroup RelativeShellTransverseQuotient :=
      relativeShellSummableTransverseNormedAddCommGroup
    Tendsto
      (fun n : ℕ =>
        (relativeShellMultiplierObservable
          (relativeShellCofinalLabel n) :
            RelativeShellTransverseQuotient))
      atTop (𝓝 0) := by
  letI : NormedAddCommGroup RelativeShellTransverseQuotient :=
    relativeShellSummableTransverseNormedAddCommGroup
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact
    relativeShellSummableTransverseNormValue_cofinal_tendsto_zero

theorem relativeShellMultiplier_transverse_ne_zero
    (m : RelativeShellLabel) :
    (relativeShellMultiplierObservable m :
      RelativeShellTransverseQuotient) ≠ 0 := by
  intro hm
  have hmem :
      relativeShellMultiplierObservable m -
          (0 : RelativeShellFullObservable) ∈
        relativeShellCommonAddSubgroup :=
    (QuotientAddGroup.eq_iff_sub_mem).mp hm
  rw [sub_zero, mem_relativeShellCommonAddSubgroup] at hmem
  exact
    relativeShellMultiplierUpperEndCarrier_not_mem_common m hmem

/--
The dyadic provenance norm topology is non-discrete: it has an explicit
sequence of nonzero private-shell classes converging to zero.
-/
theorem relativeShellSummableTransverseNormedAddCommGroup_not_discrete :
    let _ : NormedAddCommGroup RelativeShellTransverseQuotient :=
      relativeShellSummableTransverseNormedAddCommGroup
    ¬ DiscreteTopology RelativeShellTransverseQuotient := by
  letI : NormedAddCommGroup RelativeShellTransverseQuotient :=
    relativeShellSummableTransverseNormedAddCommGroup
  change ¬ DiscreteTopology RelativeShellTransverseQuotient
  intro hdisc
  letI : DiscreteTopology RelativeShellTransverseQuotient := hdisc
  have hzeroNhds :
      ({0} : Set RelativeShellTransverseQuotient) ∈
        𝓝 (0 : RelativeShellTransverseQuotient) :=
    (isOpen_discrete {0}).mem_nhds (by simp)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (relativeShellMultiplierObservable
          (relativeShellCofinalLabel n) :
            RelativeShellTransverseQuotient) ∈
              ({0} : Set RelativeShellTransverseQuotient) :=
    relativeShellCofinalMultiplier_tendsto_zero hzeroNhds
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  exact
    relativeShellMultiplier_transverse_ne_zero
      (relativeShellCofinalLabel N)
      (by simpa using hN N le_rfl)

/--
The increasing grade norm cannot be uniformly controlled by the dyadic
non-discrete norm.  On shell `m` such a bound would read
`2^m ≤ C 2⁻ᵐ`, hence `4^m ≤ C`; cofinal labels contradict every fixed `C`.

This is an exact singularity statement between the two canonical provenance
topologies, stronger than merely observing different behavior of one sequence.
-/
theorem no_uniform_increasingGrade_le_dyadicProvenance :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : RelativeShellTransverseQuotient,
        relativeShellTransverseNormValue q ≤
          C * relativeShellSummableTransverseNormValue q := by
  rintro ⟨C, hC, hbound⟩
  have hpow :
      Tendsto (fun n : ℕ => (4 : ℝ) ^ n)
        atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent :
      ∀ᶠ n : ℕ in atTop, C < (4 : ℝ) ^ n := by
    filter_upwards [(tendsto_atTop.1 hpow (C + 1))]
      with n hn
    linarith
  obtain ⟨n, hn⟩ := hevent.exists
  let m : RelativeShellLabel := relativeShellCofinalLabel n
  have hmBound :=
    hbound
      (relativeShellMultiplierObservable m :
        RelativeShellTransverseQuotient)
  rw [relativeShellTransverseNormValue_mk,
    relativeShellProvenanceSize_multiplier,
    relativeShellSummableTransverseNormValue_mk,
    relativeShellSummableProvenanceMass_multiplier] at hmBound
  have htwo : 0 < (2 : ℝ) ^ m.1 := by positivity
  have hmProduct :
      (2 : ℝ) ^ m.1 * (2 : ℝ) ^ m.1 ≤ C := by
    apply (le_div_iff₀ htwo).mp
    simpa [div_eq_mul_inv, inv_pow] using hmBound
  have hfour :
      (4 : ℝ) ^ m.1 ≤ C := by
    simpa [show (4 : ℝ) = 2 * 2 by norm_num,
      mul_pow] using hmProduct
  have hnToM :
      (4 : ℝ) ^ n ≤ (4 : ℝ) ^ m.1 := by
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [m, relativeShellCofinalLabel]
    omega
  exact (not_lt_of_ge hfour) (hn.trans_le hnToM)

end

end RHTower
