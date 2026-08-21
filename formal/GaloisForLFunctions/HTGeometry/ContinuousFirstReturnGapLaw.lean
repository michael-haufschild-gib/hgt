import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous first-return gaps from closed capture sets

A closed set of capture times that is visited on both sides of one avoided closed interval has a
last visit before that interval and a first visit after it.  These two visits are consecutive and
their separation is at least the avoided interval's width.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Consecutive-capture extraction law.**  A closed capture-time set, one visit on either side,
and avoidance throughout `[A, A + W]` produce two consecutive visits separated by at least `W`.
The endpoints are selected intrinsically as the last pre-block and first post-block visits. -/
theorem exists_consecutive_mem_separated_by_avoided_Icc
    {S : Set ℝ} (hS : IsClosed S)
    {a A W b : ℝ} (hW : 0 ≤ W)
    (hpre : ∃ t ∈ Icc a A, t ∈ S)
    (hpost : ∃ t ∈ Icc (A + W) b, t ∈ S)
    (havoid : ∀ t ∈ Icc A (A + W), t ∉ S) :
    ∃ tExit tReturn : ℝ,
      tExit ∈ Icc a A ∧ tReturn ∈ Icc (A + W) b ∧
        tExit ∈ S ∧ tReturn ∈ S ∧ tExit < tReturn ∧
        W ≤ tReturn - tExit ∧
        ∀ t ∈ Ioo tExit tReturn, t ∉ S := by
  let Kpre : Set ℝ := Icc a A ∩ S
  let Kpost : Set ℝ := Icc (A + W) b ∩ S
  have hKpre : IsCompact Kpre := isCompact_Icc.inter_right hS
  have hKpost : IsCompact Kpost := isCompact_Icc.inter_right hS
  have hKpre_ne : Kpre.Nonempty := by
    obtain ⟨t, ht, htS⟩ := hpre
    exact ⟨t, ht, htS⟩
  have hKpost_ne : Kpost.Nonempty := by
    obtain ⟨t, ht, htS⟩ := hpost
    exact ⟨t, ht, htS⟩
  obtain ⟨tExit, htExitK, htExitMax⟩ :=
    hKpre.exists_isMaxOn hKpre_ne continuous_id.continuousOn
  obtain ⟨tReturn, htReturnK, htReturnMin⟩ :=
    hKpost.exists_isMinOn hKpost_ne continuous_id.continuousOn
  have htExit_mem : tExit ∈ S := htExitK.2
  have htReturn_mem : tReturn ∈ S := htReturnK.2
  have htExit_ge : a ≤ tExit := htExitK.1.1
  have htReturn_le : tReturn ≤ b := htReturnK.1.2
  have htExit_lt : tExit < A := by
    have hle : tExit ≤ A := htExitK.1.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact havoid A ⟨le_rfl, by linarith⟩ (heq ▸ htExit_mem)
  have htReturn_gt : A + W < tReturn := by
    have hle : A + W ≤ tReturn := htReturnK.1.1
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact havoid (A + W) ⟨by linarith, le_rfl⟩ (heq ▸ htReturn_mem)
  refine ⟨tExit, tReturn, htExitK.1, htReturnK.1,
    htExit_mem, htReturn_mem, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro t ht htSmem
    rcases lt_or_ge t A with htA | hAt
    · have htK : t ∈ Kpre :=
        ⟨⟨htExit_ge.trans ht.1.le, htA.le⟩, htSmem⟩
      have hle := htExitMax htK
      exact (not_le_of_gt ht.1) (by simpa using hle)
    · rcases le_or_gt t (A + W) with htW | hWt
      · exact havoid t ⟨hAt, htW⟩ htSmem
      · have htK : t ∈ Kpost :=
          ⟨⟨hWt.le, ht.2.le.trans htReturn_le⟩, htSmem⟩
        have hle := htReturnMin htK
        exact (not_le_of_gt ht.2) (by simpa using hle)

end GaloisForLFunctions.HTGeometry
