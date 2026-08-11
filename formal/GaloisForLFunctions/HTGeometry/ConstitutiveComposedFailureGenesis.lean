import GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantArityGenesis
import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw

/-!
# Composed-failure genesis

A finite family of independent unoriented failures is the signed face cube
`I → Option (ZMod 2)`.  Any contextwise-resolving equivariant reporter must retain different
supports and at least two values on every nonempty support.  This forces an exact
`2^(|I|+1)-1` lower bound.  The mixed channels across two blocks are counted by the product of
their nonempty-support palettes.

The declarations are source-independent.  No RH or route premise occurs.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A composed failure record: inactive, or one of two unoriented active states, at every slot. -/
abbrev ComposedFailureConfig (I : Type*) := I → Option (ZMod 2)

/-- Flip one active failure coordinate and leave inactive coordinates fixed. -/
def composedFailureFlip {I : Type*} [DecidableEq I]
    (i : I) (x : ComposedFailureConfig I) : ComposedFailureConfig I :=
  fun j => if j = i then (x j).map (fun b => b + 1) else x j

/-- Active support of a composed failure record. -/
def composedFailureSupport {I : Type*} [Fintype I] [DecidableEq I]
    (x : ComposedFailureConfig I) : Finset I :=
  Finset.univ.filter fun i => x i ≠ none

/-- A coordinate flip preserves active support. -/
theorem composedFailureSupport_flip {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (x : ComposedFailureConfig I) :
    composedFailureSupport (composedFailureFlip i x) = composedFailureSupport x := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    cases hxi : x i <;> simp [composedFailureSupport, composedFailureFlip, hxi]
  · simp [composedFailureSupport, composedFailureFlip, hji]

/-- Flipping an inactive coordinate changes nothing. -/
theorem composedFailureFlip_eq_self_of_inactive {I : Type*} [DecidableEq I]
    {i : I} {x : ComposedFailureConfig I} (hxi : x i = none) :
    composedFailureFlip i x = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [composedFailureFlip, hxi]
  · simp [composedFailureFlip, hji]

/-- A legal deterministic reporter transports every elementary flip and detects it in every
active context. -/
structure ComposedFailureReporter (I Y : Type*) [DecidableEq I] where
  q : ComposedFailureConfig I → Y
  targetFlip : I → Y → Y
  equivariant : ∀ i x, q (composedFailureFlip i x) = targetFlip i (q x)
  resolves : ∀ i x, x i ≠ none → q (composedFailureFlip i x) ≠ q x

/-- Equal reported values must have equal active support. -/
theorem ComposedFailureReporter.support_eq_of_q_eq
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (R : ComposedFailureReporter I Y) {x z : ComposedFailureConfig I}
    (hq : R.q x = R.q z) :
    composedFailureSupport x = composedFailureSupport z := by
  classical
  ext i
  simp only [composedFailureSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxi
    by_contra hzi
    have hznone : z i = none := by simpa using hzi
    have hzflip : composedFailureFlip i z = z :=
      composedFailureFlip_eq_self_of_inactive hznone
    apply R.resolves i x hxi
    calc
      R.q (composedFailureFlip i x) = R.targetFlip i (R.q x) := R.equivariant i x
      _ = R.targetFlip i (R.q z) := congrArg (R.targetFlip i) hq
      _ = R.q (composedFailureFlip i z) := (R.equivariant i z).symm
      _ = R.q z := congrArg R.q hzflip
      _ = R.q x := hq.symm
  · intro hzi
    by_contra hxi
    have hxnone : x i = none := by simpa using hxi
    have hxflip : composedFailureFlip i x = x :=
      composedFailureFlip_eq_self_of_inactive hxnone
    apply R.resolves i z hzi
    calc
      R.q (composedFailureFlip i z) = R.targetFlip i (R.q z) := R.equivariant i z
      _ = R.targetFlip i (R.q x) := congrArg (R.targetFlip i) hq.symm
      _ = R.q (composedFailureFlip i x) := (R.equivariant i x).symm
      _ = R.q x := congrArg R.q hxflip
      _ = R.q z := hq

/-- Nonempty support labels used by the sharp lower-bound injection. -/
abbrev NonemptyComposedFailureSupport (I : Type*) [DecidableEq I] :=
  {S : Finset I // S.Nonempty}

/-- One background label and a Boolean pair over every nonempty support. -/
abbrev ComposedFailureResponseLabel (I : Type*) [DecidableEq I] :=
  Unit ⊕ (NonemptyComposedFailureSupport I × Bool)

/-- Canonical inactive configuration. -/
def composedFailureInactive (I : Type*) : ComposedFailureConfig I := fun _ => none

/-- Canonical all-zero active configuration on one support. -/
def composedFailureBase {I : Type*} [DecidableEq I]
    (S : Finset I) : ComposedFailureConfig I :=
  fun i => if i ∈ S then some 0 else none

/-- Distinguished active coordinate of a nonempty support. -/
noncomputable def composedFailureChosen {I : Type*} [DecidableEq I]
    (S : NonemptyComposedFailureSupport I) : I :=
  Classical.choose S.property

theorem composedFailureChosen_mem {I : Type*} [DecidableEq I]
    (S : NonemptyComposedFailureSupport I) : composedFailureChosen S ∈ S.1 :=
  Classical.choose_spec S.property

/-- Two canonical configurations over each nonempty support. -/
noncomputable def composedFailureConfigOfLabel
    {I : Type*} [DecidableEq I] :
    ComposedFailureResponseLabel I → ComposedFailureConfig I
  | Sum.inl _ => composedFailureInactive I
  | Sum.inr (S, false) => composedFailureBase S.1
  | Sum.inr (S, true) =>
      composedFailureFlip (composedFailureChosen S) (composedFailureBase S.1)

theorem composedFailureSupport_inactive {I : Type*} [Fintype I] [DecidableEq I] :
    composedFailureSupport (composedFailureInactive I) = ∅ := by
  ext i
  simp [composedFailureSupport, composedFailureInactive]

theorem composedFailureSupport_base {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) :
    composedFailureSupport (composedFailureBase S) = S := by
  ext i
  simp [composedFailureSupport, composedFailureBase]

theorem composedFailureSupport_configOfLabel
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ComposedFailureResponseLabel I) :
    composedFailureSupport (composedFailureConfigOfLabel a) =
      match a with
      | Sum.inl _ => ∅
      | Sum.inr (S, _) => S.1 := by
  rcases a with (_ | ⟨S, b⟩)
  · exact composedFailureSupport_inactive
  · cases b
    · exact composedFailureSupport_base S.1
    · simp [composedFailureConfigOfLabel, composedFailureSupport_flip,
        composedFailureSupport_base]

/-- The exact cardinal of the forced deterministic label palette. -/
theorem card_composedFailureResponseLabel_closed
    (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card (ComposedFailureResponseLabel I) =
      2 ^ (Fintype.card I + 1) - 1 := by
  classical
  rw [Fintype.card_sum, Fintype.card_prod]
  have hs := card_nonemptyLBitSupports (I := I)
  simp only [Fintype.card_unit, Fintype.card_bool]
  rw [hs, pow_succ]
  have hpow : 1 ≤ 2 ^ Fintype.card I := Nat.one_le_pow' _ 1
  omega

/-- Reporter image as a finite type. -/
abbrev ComposedFailureReporterImage
    {I Y : Type*} [DecidableEq I] (R : ComposedFailureReporter I Y) :=
  {y : Y // y ∈ Set.range R.q}

/-- Every forced support/pair label has a reported representative. -/
noncomputable def composedFailureLabelToImage
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (R : ComposedFailureReporter I Y) :
    ComposedFailureResponseLabel I → ComposedFailureReporterImage R :=
  fun a => ⟨R.q (composedFailureConfigOfLabel a), ⟨_, rfl⟩⟩

/-- The forced label representatives are pairwise distinct. -/
theorem composedFailureLabelToImage_injective
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (R : ComposedFailureReporter I Y) :
    Function.Injective (composedFailureLabelToImage R) := by
  classical
  intro a b hab
  have hq : R.q (composedFailureConfigOfLabel a) =
      R.q (composedFailureConfigOfLabel b) := congrArg Subtype.val hab
  have hs := R.support_eq_of_q_eq hq
  rw [composedFailureSupport_configOfLabel, composedFailureSupport_configOfLabel] at hs
  rcases a with (_ | ⟨S, p⟩)
  · rcases b with (_ | ⟨T, q⟩)
    · rfl
    · exfalso
      exact T.property.ne_empty hs.symm
  · rcases b with (_ | ⟨T, q⟩)
    · exfalso
      exact S.property.ne_empty hs
    · have hST : S = T := Subtype.ext hs
      subst T
      cases p <;> cases q
      · rfl
      · exfalso
        exact (R.resolves (composedFailureChosen S) (composedFailureBase S.1)
          (by simp [composedFailureBase, composedFailureChosen_mem S])) hq.symm
      · exfalso
        exact (R.resolves (composedFailureChosen S) (composedFailureBase S.1)
          (by simp [composedFailureBase, composedFailureChosen_mem S])) hq
      · rfl

/-- **Sharp composed-failure lower bound.** Every finite legal deterministic reporter has at least
`2^(|I|+1)-1` attained response values. -/
theorem composedFailureReporter_card_lower_bound_closed
    (I Y : Type*) [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (R : ComposedFailureReporter I Y) :
    2 ^ (Fintype.card I + 1) - 1 ≤
      Fintype.card (ComposedFailureReporterImage R) := by
  classical
  rw [← card_composedFailureResponseLabel_closed I]
  exact Fintype.card_le_of_injective
    (composedFailureLabelToImage R) (composedFailureLabelToImage_injective R)

/-- Sign parity retained by the sharp reporter. Inactive coordinates contribute zero. -/
def composedFailureParity {I : Type*} [Fintype I]
    (x : ComposedFailureConfig I) : ZMod 2 :=
  ∑ i : I, (x i).getD 0

/-- Inactive support has zero parity. -/
theorem composedFailureParity_eq_zero_of_support_empty
    {I : Type*} [Fintype I] [DecidableEq I]
    {x : ComposedFailureConfig I} (hx : composedFailureSupport x = ∅) :
    composedFailureParity x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hnone : x i = none := by
    by_contra hactive
    have himem : i ∈ composedFailureSupport x := by
      simp [composedFailureSupport, hactive]
    rw [hx] at himem
    simp at himem
  simp [hnone]

/-- Flipping an active coordinate adds the nonzero parity bit. -/
theorem composedFailureParity_flip_of_active
    {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (x : ComposedFailureConfig I) (hactive : x i ≠ none) :
    composedFailureParity (composedFailureFlip i x) = composedFailureParity x + 1 := by
  classical
  cases hxi : x i with
  | none => exact (hactive hxi).elim
  | some b =>
      have hoff :
          ∑ j ∈ Finset.univ.erase i, (composedFailureFlip i x j).getD 0 =
            ∑ j ∈ Finset.univ.erase i, (x j).getD 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [composedFailureFlip, hji]
      calc
        composedFailureParity (composedFailureFlip i x) =
            (∑ j ∈ Finset.univ.erase i, (composedFailureFlip i x j).getD 0) +
              (composedFailureFlip i x i).getD 0 :=
          (Finset.sum_erase_add Finset.univ
            (fun j => (composedFailureFlip i x j).getD 0) (Finset.mem_univ i)).symm
        _ = (∑ j ∈ Finset.univ.erase i, (x j).getD 0) + (b + 1) := by
          rw [hoff]
          simp [composedFailureFlip, hxi]
        _ = ((∑ j ∈ Finset.univ.erase i, (x j).getD 0) + b) + 1 := by abel
        _ = composedFailureParity x + 1 := by
          congr 1
          unfold composedFailureParity
          rw [← Finset.sum_erase_add Finset.univ (fun j => (x j).getD 0)
            (Finset.mem_univ i)]
          simp [hxi]

/-- In `ZMod 2` distinct elements differ by one. -/
theorem zmodTwo_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : b = a + 1 := by
  revert h
  revert a b
  decide

/-! ## Flipping a whole coordinate set -/

/-- Flip every coordinate in a set, leaving inactive coordinates inactive. -/
def composedFailureFlipSet {I : Type*} [DecidableEq I] (T : Finset I)
    (x : ComposedFailureConfig I) : ComposedFailureConfig I :=
  fun j => if j ∈ T then (x j).map (fun b => b + 1) else x j

@[simp] theorem composedFailureFlipSet_empty {I : Type*} [DecidableEq I]
    (x : ComposedFailureConfig I) : composedFailureFlipSet ∅ x = x := by
  funext j
  simp [composedFailureFlipSet]

theorem composedFailureFlipSet_insert {I : Type*} [DecidableEq I]
    {i : I} {T : Finset I} (hi : i ∉ T) (x : ComposedFailureConfig I) :
    composedFailureFlipSet (insert i T) x =
      composedFailureFlip i (composedFailureFlipSet T x) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [composedFailureFlipSet, composedFailureFlip, hi]
  · simp [composedFailureFlipSet, composedFailureFlip, hji, Finset.mem_insert]

theorem composedFailureSupport_flipSet {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (x : ComposedFailureConfig I) :
    composedFailureSupport (composedFailureFlipSet T x) = composedFailureSupport x := by
  classical
  ext j
  by_cases hjT : j ∈ T <;>
    cases hxj : x j <;>
      simp [composedFailureSupport, composedFailureFlipSet, hjT, hxj]

theorem composedFailureParity_flipSet {I : Type*} [Fintype I] [DecidableEq I]
    {x : ComposedFailureConfig I} {T : Finset I}
    (hT : T ⊆ composedFailureSupport x) :
    composedFailureParity (composedFailureFlipSet T x) =
      composedFailureParity x + (T.card : ZMod 2) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | @insert i T hi ih =>
      have hTsub : T ⊆ composedFailureSupport x :=
        fun j hj => hT (Finset.mem_insert_of_mem hj)
      have hiS : i ∈ composedFailureSupport x := hT (Finset.mem_insert_self i T)
      have hactive : composedFailureFlipSet T x i ≠ none := by
        have : i ∈ composedFailureSupport (composedFailureFlipSet T x) := by
          rw [composedFailureSupport_flipSet]; exact hiS
        simpa [composedFailureSupport] using this
      rw [composedFailureFlipSet_insert hi,
        composedFailureParity_flip_of_active i _ hactive, ih hTsub,
        Finset.card_insert_of_notMem hi]
      push_cast
      ring

/-- Two records with the same support differ by flipping a subset of that support. -/
theorem exists_flipSet_of_support_eq {I : Type*} [Fintype I] [DecidableEq I]
    {x z : ComposedFailureConfig I}
    (hsupp : composedFailureSupport x = composedFailureSupport z) :
    ∃ T : Finset I, T ⊆ composedFailureSupport x ∧ composedFailureFlipSet T x = z := by
  classical
  refine ⟨Finset.univ.filter fun i => x i ≠ z i ∧ x i ≠ none, ?_, ?_⟩
  · intro i hi
    have := (Finset.mem_filter.mp hi).2.2
    simpa [composedFailureSupport] using this
  · funext j
    by_cases hj : x j ≠ z j ∧ x j ≠ none
    · obtain ⟨hne, hnone⟩ := hj
      have hjS : j ∈ composedFailureSupport x := by simpa [composedFailureSupport] using hnone
      have hjT : j ∈ composedFailureSupport z := by rwa [hsupp] at hjS
      have hznone : z j ≠ none := by simpa [composedFailureSupport] using hjT
      cases hxj : x j with
      | none => exact absurd hxj hnone
      | some a =>
          cases hzj : z j with
          | none => exact absurd hzj hznone
          | some b =>
              have hab : a ≠ b := by
                intro h
                rw [hxj, hzj, h] at hne
                exact hne rfl
              have hb : b = a + 1 := zmodTwo_eq_add_one_of_ne hab
              simp [composedFailureFlipSet, hxj, hzj, hb]
    · have hj' : ¬ (x j ≠ z j ∧ x j ≠ none) := hj
      by_cases heq : x j = z j
      · simp [composedFailureFlipSet, heq]
      · have hnone : x j = none := by
          by_contra hc
          exact hj' ⟨heq, hc⟩
        have hzn : z j = none := by
          by_contra hc
          have hjT : j ∈ composedFailureSupport z := by
            simpa [composedFailureSupport] using hc
          rw [← hsupp] at hjT
          have : x j ≠ none := by simpa [composedFailureSupport] using hjT
          exact this hnone
        simp [composedFailureFlipSet, hnone, hzn]

/-! ## Equality rigidity of a sharp reporter -/

/-- A minimal-image legal reporter takes exactly the two canonical values on each nonempty
support stratum. -/
theorem composedFailureReporter_stratum_two_valued
    {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (R : ComposedFailureReporter I Y)
    (hmin : Fintype.card (ComposedFailureReporterImage R) =
      2 ^ (Fintype.card I + 1) - 1)
    (S : NonemptyComposedFailureSupport I) {y : ComposedFailureConfig I}
    (hy : composedFailureSupport y = S.1) :
    R.q y = R.q (composedFailureBase S.1) ∨
      R.q y = R.q (composedFailureFlip (composedFailureChosen S)
        (composedFailureBase S.1)) := by
  classical
  have hcard : Fintype.card (ComposedFailureResponseLabel I) =
      Fintype.card (ComposedFailureReporterImage R) := by
    rw [card_composedFailureResponseLabel_closed I, hmin]
  have hbij : Function.Bijective (composedFailureLabelToImage R) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨composedFailureLabelToImage_injective R, hcard⟩
  obtain ⟨a, ha⟩ := hbij.surjective ⟨R.q y, ⟨y, rfl⟩⟩
  have hqa : R.q (composedFailureConfigOfLabel a) = R.q y := congrArg Subtype.val ha
  have hsa := R.support_eq_of_q_eq hqa
  rw [composedFailureSupport_configOfLabel, hy] at hsa
  rcases a with (_ | ⟨T, p⟩)
  · exact absurd hsa.symm S.property.ne_empty
  · have hTS : T = S := Subtype.ext hsa
    subst T
    cases p
    · exact Or.inl hqa.symm
    · exact Or.inr hqa.symm

/-- On a nonempty stratum, a single active flip toggles between the two canonical values. -/
theorem composedFailureReporter_flipSet_eq_iff_even
    {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (R : ComposedFailureReporter I Y)
    (hmin : Fintype.card (ComposedFailureReporterImage R) =
      2 ^ (Fintype.card I + 1) - 1)
    (S : NonemptyComposedFailureSupport I) {x : ComposedFailureConfig I}
    (hx : composedFailureSupport x = S.1) {T : Finset I} (hT : T ⊆ S.1) :
    (R.q (composedFailureFlipSet T x) = R.q x) ↔ Even T.card := by
  classical
  set a := R.q (composedFailureBase S.1) with ha
  set b := R.q (composedFailureFlip (composedFailureChosen S)
    (composedFailureBase S.1)) with hb
  have hab : a ≠ b := by
    intro h
    exact (R.resolves (composedFailureChosen S) (composedFailureBase S.1)
      (by simp [composedFailureBase, composedFailureChosen_mem S])) h.symm
  induction T using Finset.induction with
  | empty => simp
  | @insert i T hi ih =>
      have hTsub : T ⊆ S.1 := fun j hj => hT (Finset.mem_insert_of_mem hj)
      have hiS : i ∈ S.1 := hT (Finset.mem_insert_self i T)
      have hsuppT : composedFailureSupport (composedFailureFlipSet T x) = S.1 := by
        rw [composedFailureSupport_flipSet, hx]
      have hactive : composedFailureFlipSet T x i ≠ none := by
        have : i ∈ composedFailureSupport (composedFailureFlipSet T x) := by
          rw [hsuppT]; exact hiS
        simpa [composedFailureSupport] using this
      have hstep : R.q (composedFailureFlipSet (insert i T) x) ≠
          R.q (composedFailureFlipSet T x) := by
        rw [composedFailureFlipSet_insert hi]
        exact R.resolves i _ hactive
      have hvalT := composedFailureReporter_stratum_two_valued R hmin S hsuppT
      have hsuppI : composedFailureSupport (composedFailureFlipSet (insert i T) x) = S.1 := by
        rw [composedFailureSupport_flipSet, hx]
      have hvalI := composedFailureReporter_stratum_two_valued R hmin S hsuppI
      have hvalx : R.q x = a ∨ R.q x = b :=
        composedFailureReporter_stratum_two_valued R hmin S hx
      rw [Finset.card_insert_of_notMem hi, Nat.even_add_one]
      constructor
      · intro hEq hEven
        have hTeq : R.q (composedFailureFlipSet T x) = R.q x := ih hTsub |>.mpr hEven
        exact hstep (hEq.trans hTeq.symm)
      · intro hOdd
        have hTne : R.q (composedFailureFlipSet T x) ≠ R.q x := by
          intro hc
          exact hOdd ((ih hTsub).mp hc)
        rcases hvalx with hx' | hx' <;> rcases hvalT with hT' | hT' <;>
          rcases hvalI with hI' | hI'
        · exact absurd (hT'.trans hx'.symm) hTne
        · exact absurd (hT'.trans hx'.symm) hTne
        · rw [hI', hx']
        · exact absurd (hI'.trans hT'.symm) hstep
        · exact absurd (hI'.trans hT'.symm) hstep
        · rw [hI', hx']
        · exact absurd (hT'.trans hx'.symm) hTne
        · exact absurd (hT'.trans hx'.symm) hTne

/-- **Equality rigidity.**  A legal reporter attaining the sharp bound identifies exactly the
support/parity classes: its image is the canonical Walsh chart. -/
theorem composedFailureReporter_sharp_eq_iff
    {I Y : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (R : ComposedFailureReporter I Y)
    (hmin : Fintype.card (ComposedFailureReporterImage R) =
      2 ^ (Fintype.card I + 1) - 1)
    (x z : ComposedFailureConfig I) :
    R.q x = R.q z ↔
      composedFailureSupport x = composedFailureSupport z ∧
        composedFailureParity x = composedFailureParity z := by
  classical
  constructor
  · intro hq
    have hsupp := R.support_eq_of_q_eq hq
    refine ⟨hsupp, ?_⟩
    obtain ⟨T, hTsub, hTz⟩ := exists_flipSet_of_support_eq hsupp
    by_cases hempty : composedFailureSupport x = ∅
    · have hzempty : composedFailureSupport z = ∅ := by rw [← hsupp]; exact hempty
      rw [composedFailureParity_eq_zero_of_support_empty hempty,
        composedFailureParity_eq_zero_of_support_empty hzempty]
    · have hne : (composedFailureSupport x).Nonempty := Finset.nonempty_of_ne_empty hempty
      have heven : Even T.card := by
        refine (composedFailureReporter_flipSet_eq_iff_even R hmin
          ⟨composedFailureSupport x, hne⟩ rfl hTsub).mp ?_
        rw [hTz]
        exact hq.symm
      have hpar := composedFailureParity_flipSet (x := x) (T := T) hTsub
      rw [hTz] at hpar
      rw [hpar, ZMod.natCast_eq_zero_iff_even.mpr heven, add_zero]
  · rintro ⟨hsupp, hpar⟩
    obtain ⟨T, hTsub, hTz⟩ := exists_flipSet_of_support_eq hsupp
    by_cases hempty : composedFailureSupport x = ∅
    · have hxall : ∀ j, x j = none := by
        intro j
        by_contra hc
        have hj : j ∈ composedFailureSupport x := by
          simp only [composedFailureSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hc
        rw [hempty] at hj
        simp at hj
      have hzall : ∀ j, z j = none := by
        intro j
        by_contra hc
        have hj : j ∈ composedFailureSupport z := by
          simp only [composedFailureSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hc
        rw [← hsupp, hempty] at hj
        simp at hj
      have hxz : x = z := by
        funext j
        rw [hxall j, hzall j]
      rw [hxz]
    · have hne : (composedFailureSupport x).Nonempty := Finset.nonempty_of_ne_empty hempty
      have hparT := composedFailureParity_flipSet (x := x) (T := T) hTsub
      rw [hTz, ← hpar] at hparT
      have hzero : (T.card : ZMod 2) = 0 := by
        have := hparT.symm
        exact (add_eq_left).mp this
      have heven : Even T.card := ZMod.natCast_eq_zero_iff_even.mp hzero
      have hval := (composedFailureReporter_flipSet_eq_iff_even R hmin
        ⟨composedFailureSupport x, hne⟩ rfl hTsub).mpr heven
      rw [hTz] at hval
      exact hval.symm

/-! ## Convex doctrine exchange: a linear pure-outcome realization -/

/-- Pure outcome doctrine of the convex repair: two atoms over every failure coordinate. -/
abbrev ComposedFailureOutcome (I : Type*) := I × ZMod 2

theorem sum_zmodTwo (f : ZMod 2 → ℚ) : ∑ c : ZMod 2, f c = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

theorem zmodTwo_add_one_eq_iff (a b : ZMod 2) : a + 1 = b ↔ a = b + 1 := by
  revert a b
  decide

theorem zmodTwo_add_one_ne (a : ZMod 2) : a + 1 ≠ a := by
  revert a
  decide

/-- Weight placed on one atom by one coordinate state. -/
noncomputable def composedFailureAtomWeight {I : Type*} [Fintype I]
    (o : Option (ZMod 2)) (c : ZMod 2) : ℚ :=
  1 / (2 * (Fintype.card I : ℚ)) +
    (if o = some c then 1 / (4 * (Fintype.card I : ℚ))
      else if o = none then 0 else -(1 / (4 * (Fintype.card I : ℚ))))

/-- The convex composed-failure reporter: a strictly positive probability vector on `2n` atoms. -/
noncomputable def composedFailureConvexReporter {I : Type*} [Fintype I]
    (x : ComposedFailureConfig I) (z : ComposedFailureOutcome I) : ℚ :=
  composedFailureAtomWeight (I := I) (x z.1) z.2

theorem composedFailureAtomWeight_pair_sum {I : Type*} [Fintype I]
    (hI : 0 < Fintype.card I) (o : Option (ZMod 2)) :
    ∑ c : ZMod 2, composedFailureAtomWeight (I := I) o c = 1 / (Fintype.card I : ℚ) := by
  have hn : (0 : ℚ) < (Fintype.card I : ℚ) := by exact_mod_cast hI
  rw [sum_zmodTwo]
  cases o with
  | none =>
      simp [composedFailureAtomWeight]
      ring
  | some b =>
      have hb : b = 0 ∨ b = 1 := by revert b; decide
      rcases hb with rfl | rfl <;>
        · simp [composedFailureAtomWeight]
          ring

/-- **Convex doctrine exchange, mass.**  The convex reporter is a probability vector on the `2n`
pure outcomes. -/
theorem composedFailureConvexReporter_sum {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (x : ComposedFailureConfig I) :
    ∑ z : ComposedFailureOutcome I, composedFailureConvexReporter x z = 1 := by
  classical
  have hn : (0 : ℚ) < (Fintype.card I : ℚ) := by exact_mod_cast hI
  have hrow : ∀ i : I,
      ∑ c : ZMod 2, composedFailureConvexReporter x (i, c) = 1 / (Fintype.card I : ℚ) :=
    fun i => composedFailureAtomWeight_pair_sum (I := I) hI (x i)
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun i _ => hrow i,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Convex doctrine exchange, positivity.**  Every pure outcome receives strictly positive
weight. -/
theorem composedFailureConvexReporter_pos {I : Type*} [Fintype I]
    (hI : 0 < Fintype.card I) (x : ComposedFailureConfig I)
    (z : ComposedFailureOutcome I) : 0 < composedFailureConvexReporter x z := by
  have hn : (0 : ℚ) < (Fintype.card I : ℚ) := by exact_mod_cast hI
  have hquarter : (0 : ℚ) < 1 / (4 * (Fintype.card I : ℚ)) := by positivity
  have hhalf : 1 / (2 * (Fintype.card I : ℚ)) = 2 * (1 / (4 * (Fintype.card I : ℚ))) := by
    field_simp
    ring
  rw [composedFailureConvexReporter, composedFailureAtomWeight]
  by_cases h1 : x z.1 = some z.2
  · rw [if_pos h1]
    positivity
  · rw [if_neg h1]
    by_cases h2 : x z.1 = none
    · rw [if_pos h2, add_zero]
      positivity
    · rw [if_neg h2, hhalf]
      linarith

/-- **Convex doctrine exchange, equivariance.**  Flipping a coordinate permutes exactly the two
atoms over that coordinate. -/
theorem composedFailureConvexReporter_equivariant {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (x : ComposedFailureConfig I) (j : I) (c : ZMod 2) :
    composedFailureConvexReporter (composedFailureFlip i x) (j, c) =
      composedFailureConvexReporter x (j, if j = i then c + 1 else c) := by
  classical
  by_cases hji : j = i
  · subst j
    cases hx : x i with
    | none =>
        simp [composedFailureConvexReporter, composedFailureAtomWeight,
          composedFailureFlip, hx]
    | some b =>
        have hxflip : composedFailureFlip i x i = some (b + 1) := by
          simp [composedFailureFlip, hx]
        have hidx : (if (i : I) = i then c + 1 else c) = c + 1 := if_pos rfl
        show composedFailureAtomWeight (composedFailureFlip i x i) c
            = composedFailureAtomWeight (x i) (if (i : I) = i then c + 1 else c)
        rw [hidx, hxflip, hx, composedFailureAtomWeight, composedFailureAtomWeight]
        have hiff : (some (b + 1) = (some c : Option (ZMod 2))) ↔
            (some b = (some (c + 1) : Option (ZMod 2))) := by
          simp only [Option.some.injEq]
          exact zmodTwo_add_one_eq_iff b c
        by_cases hcb : some (b + 1) = (some c : Option (ZMod 2))
        · rw [if_pos hcb, if_pos (hiff.mp hcb)]
        · rw [if_neg hcb, if_neg (fun h => hcb (hiff.mpr h)), if_neg (by simp),
            if_neg (by simp)]
  · simp [composedFailureConvexReporter, composedFailureAtomWeight,
      composedFailureFlip, hji]

/-- **Convex doctrine exchange, contextwise resolution.**  Flipping an active coordinate changes
the mixture. -/
theorem composedFailureConvexReporter_resolves {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 0 < Fintype.card I) (i : I) (x : ComposedFailureConfig I) (hx : x i ≠ none) :
    composedFailureConvexReporter (composedFailureFlip i x) ≠
      composedFailureConvexReporter x := by
  classical
  intro hEq
  have hn : (0 : ℚ) < (Fintype.card I : ℚ) := by exact_mod_cast hI
  have hquarter : (0 : ℚ) < 1 / (4 * (Fintype.card I : ℚ)) := by positivity
  cases hxi : x i with
  | none => exact hx hxi
  | some b =>
      have hxflip : composedFailureFlip i x i = some (b + 1) := by
        simp [composedFailureFlip, hxi]
      have h := congrFun hEq (i, b)
      simp only [composedFailureConvexReporter, composedFailureAtomWeight,
        hxflip, hxi, Option.some.injEq, zmodTwo_add_one_ne, if_false, if_true] at h
      rw [if_neg (Option.some_ne_none (b + 1))] at h
      linarith

/-- **Exact pure-outcome count.**  The convex realization uses exactly `2n` pure outcomes. -/
theorem card_composedFailureOutcome {I : Type*} [Fintype I] :
    Fintype.card (ComposedFailureOutcome I) = 2 * Fintype.card I := by
  rw [Fintype.card_prod, ZMod.card]
  ring

/-- Target flip on the marked support/parity chart. -/
def composedFailureCanonicalTargetFlip
    {I : Type*} [DecidableEq I]
    (i : I) : (Finset I × ZMod 2) → (Finset I × ZMod 2)
  | (S, p) => if i ∈ S then (S, p + 1) else (S, p)

/-- Sharp support/parity reporter. -/
def composedFailureCanonicalQ
    {I : Type*} [Fintype I] [DecidableEq I]
  (x : ComposedFailureConfig I) : Finset I × ZMod 2 :=
  (composedFailureSupport x, composedFailureParity x)

/-- The canonical reporter identifies exactly equal support/parity classes. -/
theorem composedFailureCanonicalQ_eq_iff_closed
    {I : Type*} [Fintype I] [DecidableEq I]
    (x z : ComposedFailureConfig I) :
    composedFailureCanonicalQ x = composedFailureCanonicalQ z ↔
      composedFailureSupport x = composedFailureSupport z ∧
        composedFailureParity x = composedFailureParity z := by
  simp [composedFailureCanonicalQ, Prod.ext_iff]

/-- The support/parity reporter is legal. -/
def composedFailureCanonicalReporter
    (I : Type*) [Fintype I] [DecidableEq I] :
    ComposedFailureReporter I (Finset I × ZMod 2) where
  q := composedFailureCanonicalQ
  targetFlip := composedFailureCanonicalTargetFlip
  equivariant := by
    intro i x
    by_cases hactive : x i ≠ none
    · have himem : i ∈ composedFailureSupport x := by
        simp [composedFailureSupport, hactive]
      simp only [composedFailureCanonicalQ, composedFailureCanonicalTargetFlip]
      rw [composedFailureSupport_flip,
        composedFailureParity_flip_of_active i x hactive]
      simp [himem]
    · have hnone : x i = none := by simpa using hactive
      have hnotmem : i ∉ composedFailureSupport x := by
        simp [composedFailureSupport, hnone]
      rw [composedFailureFlip_eq_self_of_inactive hnone]
      simp [composedFailureCanonicalQ, composedFailureCanonicalTargetFlip, hnotmem]
  resolves := by
    intro i x hactive hq
    have hp := congrArg Prod.snd hq
    simp only [composedFailureCanonicalQ] at hp
    rw [composedFailureParity_flip_of_active i x hactive] at hp
    have hone : (1 : ZMod 2) = 0 := by
      calc
        1 = -composedFailureParity x + (composedFailureParity x + 1) := by abel
        _ = -composedFailureParity x + composedFailureParity x :=
          congrArg (fun z => -composedFailureParity x + z) hp
        _ = 0 := by abel
    exact one_ne_zero hone

/-- Sharp labels using the actual parity group. -/
abbrev ComposedFailureSharpLabel (I : Type*) [DecidableEq I] :=
  Unit ⊕ (NonemptyComposedFailureSupport I × ZMod 2)

theorem card_composedFailureSharpLabel_closed
    (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card (ComposedFailureSharpLabel I) =
      2 ^ (Fintype.card I + 1) - 1 := by
  classical
  rw [Fintype.card_sum, Fintype.card_prod,
    card_nonemptyLBitSupports (I := I), ZMod.card, pow_succ]
  have hpow : 1 ≤ 2 ^ Fintype.card I := Nat.one_le_pow' _ 1
  simp only [Fintype.card_unit]
  omega

/-- Every attained canonical value embeds back into its sharp support/parity label. -/
noncomputable def composedFailureCanonicalImageToSharpLabel
    {I : Type*} [Fintype I] [DecidableEq I] :
    ComposedFailureReporterImage (composedFailureCanonicalReporter I) →
      ComposedFailureSharpLabel I :=
  fun y => if hS : y.1.1.Nonempty then Sum.inr (⟨y.1.1, hS⟩, y.1.2) else Sum.inl ()

theorem composedFailureCanonicalImage_empty_parity
    {I : Type*} [Fintype I] [DecidableEq I]
    (y : ComposedFailureReporterImage (composedFailureCanonicalReporter I))
    (hy : y.1.1 = ∅) : y.1.2 = 0 := by
  rcases y.2 with ⟨x, hx⟩
  change composedFailureCanonicalQ x = y.1 at hx
  have hs : composedFailureSupport x = ∅ := by
    exact (congrArg Prod.fst hx).trans hy
  have hp := composedFailureParity_eq_zero_of_support_empty hs
  exact (congrArg Prod.snd hx).symm.trans hp

theorem composedFailureCanonicalImageToSharpLabel_injective
    {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (composedFailureCanonicalImageToSharpLabel (I := I)) := by
  classical
  intro y z hyz
  by_cases hy : y.1.1.Nonempty
  · by_cases hz : z.1.1.Nonempty
    · simp [composedFailureCanonicalImageToSharpLabel, hy, hz] at hyz
      rcases hyz with ⟨hS, hp⟩
      exact Subtype.ext (Prod.ext hS hp)
    · simp [composedFailureCanonicalImageToSharpLabel, hy, hz] at hyz
  · by_cases hz : z.1.1.Nonempty
    · simp [composedFailureCanonicalImageToSharpLabel, hy, hz] at hyz
    · have hyempty : y.1.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hy
      have hzempty : z.1.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz
      have hyp := composedFailureCanonicalImage_empty_parity y hyempty
      have hzp := composedFailureCanonicalImage_empty_parity z hzempty
      apply Subtype.ext
      apply Prod.ext
      · exact hyempty.trans hzempty.symm
      · exact hyp.trans hzp.symm

/-- The canonical reporter attains the lower bound exactly. -/
theorem composedFailureCanonicalReporter_card_exact_closed
    (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card
        (ComposedFailureReporterImage (composedFailureCanonicalReporter I)) =
      2 ^ (Fintype.card I + 1) - 1 := by
  classical
  apply Nat.le_antisymm
  · rw [← card_composedFailureSharpLabel_closed I]
    exact Fintype.card_le_of_injective
      (composedFailureCanonicalImageToSharpLabel (I := I))
      composedFailureCanonicalImageToSharpLabel_injective
  · exact composedFailureReporter_card_lower_bound_closed I
      (Finset I × ZMod 2) (composedFailureCanonicalReporter I)

/-- Mixed failure supports across two blocks are the product of their nonempty support palettes. -/
theorem card_composedFailureMixedChannels_closed
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Fintype.card
        {S : Finset (A ⊕ B) // S.toLeft.Nonempty ∧ S.toRight.Nonempty} =
      (2 ^ Fintype.card A - 1) * (2 ^ Fintype.card B - 1) := by
  exact card_mixedLBitSupports A B

/-- Closed conjunction of the support-separation, sharp lower-bound, and mixed-channel laws. -/
theorem composedFailureGenesisMechanism_closed :
    (∀ (I Y : Type) (_ : Fintype I) (_ : DecidableEq I)
        (_ : Fintype Y) (_ : DecidableEq Y) (R : ComposedFailureReporter I Y),
      2 ^ (Fintype.card I + 1) - 1 ≤
        Fintype.card (ComposedFailureReporterImage R)) ∧
    (∀ (I : Type) (_ : Fintype I) (_ : DecidableEq I),
      Fintype.card
          (ComposedFailureReporterImage (composedFailureCanonicalReporter I)) =
        2 ^ (Fintype.card I + 1) - 1) ∧
    (∀ (A B : Type) (_ : Fintype A) (_ : Fintype B)
        (_ : DecidableEq A) (_ : DecidableEq B),
      Fintype.card
          {S : Finset (A ⊕ B) // S.toLeft.Nonempty ∧ S.toRight.Nonempty} =
        (2 ^ Fintype.card A - 1) * (2 ^ Fintype.card B - 1)) := by
  constructor
  · intro I Y _ _ _ _ R
    exact composedFailureReporter_card_lower_bound_closed I Y R
  constructor
  · intro I _ _
    exact composedFailureCanonicalReporter_card_exact_closed I
  · intro A B _ _ _ _
    exact card_composedFailureMixedChannels_closed A B

end GaloisForLFunctions.HTGeometry
