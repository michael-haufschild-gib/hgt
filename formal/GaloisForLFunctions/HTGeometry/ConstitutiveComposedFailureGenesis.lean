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
