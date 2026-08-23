import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw

/-!
# Complete-resolution shared-gauge reflection atlas

The complete positive Riemann resolution supplies a nonzero source packet at every point of the
open critical strip and at its functional-equation reflection. A local countercharacter can make
either orientation look norm-conservative and equivariant away from the critical line. The two
local normalizations cannot both descend from one shared gauge.

This module packages that obstruction as a source-defined three-chart cover of the off-line strip:
forward local descent fails, reflected local descent fails, or the gauges split on the overlap.
The candidate structure stores only data. No faithfulness, conservation, covariance, gauge law,
Xi-zero condition, or Riemann-hypothesis premise is assumed. Three explicit complete-source models
show sharp minimality: every two-obligation face is inhabited off line.
-/

open Complex

namespace RHTower

noncomputable section

/-- Open critical-strip points away from the reflection fixed line. -/
abbrev CompleteResolutionOffLineStrip :=
  {s : CompleteResolutionOpenCriticalStrip // s.1.re ≠ 1 / 2}

/-- Signed horizontal source rate relative to the critical line. -/
def completeResolutionHorizontalRate
    (s : CompleteResolutionOpenCriticalStrip) : ℝ :=
  s.1.re - 1 / 2

/-- Complete source packet in the displayed orientation. -/
def completeResolutionForwardSourcePacket
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K ⟨s.1, s.2.1⟩

/-- Complete source packet in the functional-equation-reflected orientation. -/
def completeResolutionReflectedSourcePacket
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K
    ⟨1 - star s.1, by
      have hstarRe : (star s.1).re = s.1.re := by simp
      simp only [sub_re, one_re]
      rw [hstarRe]
      linarith [s.2.2]⟩

/-- The displayed complete source packet is never zero. -/
theorem completeResolutionForwardSourcePacket_ne_zero
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionForwardSourcePacket K s ≠ 0 := by
  simpa [completeResolutionForwardSourcePacket,
    completeResolutionSourceEmbedding] using
      completeResolutionSourceVector_ne_zero K s.2.1

/-- The reflected complete source packet is never zero. -/
theorem completeResolutionReflectedSourcePacket_ne_zero
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    completeResolutionReflectedSourcePacket K s ≠ 0 := by
  have hreflectedPos : 0 < (1 - star s.1).re := by
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re]
    rw [hstarRe]
    linarith [s.2.2]
  simpa [completeResolutionReflectedSourcePacket,
    completeResolutionSourceEmbedding] using
      completeResolutionSourceVector_ne_zero K hreflectedPos

/-- Data of one observer fixed on the whole strip. No conservation, faithfulness, covariance, or
gauge compatibility law is stored in the structure. -/
structure SharedGaugeReflectionDescentCandidate where
  observe : CompleteResolutionSourceSpace → ℝ
  transport : ℝ → ℝ
  forwardGauge : CompleteResolutionOpenCriticalStrip → ℝ
  reflectedGauge : CompleteResolutionOpenCriticalStrip → ℝ

/-- A local non-erasing, absolute-norm-conservative, character-equivariant descent package. -/
def LocalCharacterDescentGood
    (rate observed transported : ℝ) : Prop :=
  observed ≠ 0 ∧
    |transported| = |observed| ∧
    transported = Real.exp rate * observed

def completeResolutionForwardObserved
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOpenCriticalStrip) : ℝ :=
  C.observe (completeResolutionForwardSourcePacket K s)

def completeResolutionReflectedObserved
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOpenCriticalStrip) : ℝ :=
  C.observe (completeResolutionReflectedSourcePacket K s)

def CompleteResolutionForwardGood
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOpenCriticalStrip) : Prop :=
  let m := completeResolutionForwardObserved K C s
  LocalCharacterDescentGood
    (C.forwardGauge s + completeResolutionHorizontalRate s)
    m (C.transport m)

def CompleteResolutionReflectedGood
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOpenCriticalStrip) : Prop :=
  let m := completeResolutionReflectedObserved K C s
  LocalCharacterDescentGood
    (C.reflectedGauge s - completeResolutionHorizontalRate s)
    m (C.transport m)

/-- Overlap compatibility: the two local countercharacters descend from one shared gauge. -/
def CompleteResolutionSharedGauge
    (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOpenCriticalStrip) : Prop :=
  C.forwardGauge s = C.reflectedGauge s

def completeResolutionForwardFailureChart
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate) :
    Set CompleteResolutionOffLineStrip :=
  {s | ¬ CompleteResolutionForwardGood K C s.1}

def completeResolutionReflectedFailureChart
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate) :
    Set CompleteResolutionOffLineStrip :=
  {s | ¬ CompleteResolutionReflectedGood K C s.1}

def completeResolutionGaugeSplitChart
    (C : SharedGaugeReflectionDescentCandidate) :
    Set CompleteResolutionOffLineStrip :=
  {s | ¬ CompleteResolutionSharedGauge C s.1}

/-- **Shared-gauge reflection descent obstruction.** Every off-line source pair fails forward
descent, reflected descent, or overlap gauge compatibility. -/
theorem completeResolution_sharedGaugeReflection_failure_at
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOffLineStrip) :
    ¬ CompleteResolutionForwardGood K C s.1 ∨
      ¬ CompleteResolutionReflectedGood K C s.1 ∨
      ¬ CompleteResolutionSharedGauge C s.1 := by
  by_contra hfailure
  push Not at hfailure
  rcases hfailure with ⟨hforward, hreflected, hshared⟩
  have rate_zero_of_good :
      ∀ rate observed transported : ℝ,
        LocalCharacterDescentGood rate observed transported → rate = 0 := by
    intro rate observed transported hgood
    rcases hgood with ⟨hobserved, hnorm, hintertwine⟩
    rw [hintertwine, abs_mul,
      abs_of_pos (Real.exp_pos rate)] at hnorm
    have habs : |observed| ≠ 0 := abs_ne_zero.mpr hobserved
    have hproduct : (Real.exp rate - 1) * |observed| = 0 := by
      nlinarith
    have hexpSub : Real.exp rate - 1 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right habs
    exact (Real.exp_eq_one_iff rate).mp (sub_eq_zero.mp hexpSub)
  have hforwardRate :
      C.forwardGauge s.1 + completeResolutionHorizontalRate s.1 = 0 :=
    rate_zero_of_good _ _ _ hforward
  have hreflectedRate :
      C.reflectedGauge s.1 - completeResolutionHorizontalRate s.1 = 0 :=
    rate_zero_of_good _ _ _ hreflected
  have hrate : completeResolutionHorizontalRate s.1 = 0 := by
    rw [CompleteResolutionSharedGauge] at hshared
    linarith
  exact s.2 (sub_eq_zero.mp hrate)

/-- Literal three-chart cover of the full off-line strip. -/
theorem completeResolution_sharedGaugeReflection_failure_cover
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate) :
    completeResolutionForwardFailureChart K C ∪
        (completeResolutionReflectedFailureChart K C ∪
          completeResolutionGaugeSplitChart C) = Set.univ := by
  ext s
  simp only [completeResolutionForwardFailureChart,
    completeResolutionReflectedFailureChart,
    completeResolutionGaugeSplitChart, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact completeResolution_sharedGaugeReflection_failure_at K C s

/-- Expanded seven-way form: erasure, norm failure, covariance failure in either orientation, or
failure of overlap descent. -/
theorem completeResolution_sharedGaugeReflection_sevenFailure_at
    (K : ℕ) (C : SharedGaugeReflectionDescentCandidate)
    (s : CompleteResolutionOffLineStrip) :
    completeResolutionForwardObserved K C s.1 = 0 ∨
    |C.transport (completeResolutionForwardObserved K C s.1)| ≠
      |completeResolutionForwardObserved K C s.1| ∨
    C.transport (completeResolutionForwardObserved K C s.1) ≠
      Real.exp (C.forwardGauge s.1 + completeResolutionHorizontalRate s.1) *
        completeResolutionForwardObserved K C s.1 ∨
    completeResolutionReflectedObserved K C s.1 = 0 ∨
    |C.transport (completeResolutionReflectedObserved K C s.1)| ≠
      |completeResolutionReflectedObserved K C s.1| ∨
    C.transport (completeResolutionReflectedObserved K C s.1) ≠
      Real.exp (C.reflectedGauge s.1 - completeResolutionHorizontalRate s.1) *
        completeResolutionReflectedObserved K C s.1 ∨
    C.forwardGauge s.1 ≠ C.reflectedGauge s.1 := by
  classical
  rcases completeResolution_sharedGaugeReflection_failure_at K C s with
      hforward | hreflected | hshared
  · by_cases herased : completeResolutionForwardObserved K C s.1 = 0
    · exact Or.inl herased
    · by_cases hnorm :
        |C.transport (completeResolutionForwardObserved K C s.1)| ≠
          |completeResolutionForwardObserved K C s.1|
      · exact Or.inr (Or.inl hnorm)
      · exact Or.inr (Or.inr (Or.inl (by
          intro hintertwine
          exact hforward ⟨herased, not_ne_iff.mp hnorm, hintertwine⟩)))
  · by_cases herased : completeResolutionReflectedObserved K C s.1 = 0
    · exact Or.inr (Or.inr (Or.inr (Or.inl herased)))
    · by_cases hnorm :
        |C.transport (completeResolutionReflectedObserved K C s.1)| ≠
          |completeResolutionReflectedObserved K C s.1|
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hnorm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          intro hintertwine
          exact hreflected ⟨herased, not_ne_iff.mp hnorm, hintertwine⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hshared)))))

/-- Common source observer used by the sharpness models: read source norm and transport it by the
identity. -/
def completeResolutionNormIdentityCandidate
    (forwardGauge reflectedGauge : CompleteResolutionOpenCriticalStrip → ℝ) :
    SharedGaugeReflectionDescentCandidate where
  observe := fun x => ‖x‖
  transport := id
  forwardGauge := forwardGauge
  reflectedGauge := reflectedGauge

/-- Both local descents are perfect when each orientation receives its own co-moving gauge. -/
def completeResolutionSplitGaugeCandidate :
    SharedGaugeReflectionDescentCandidate :=
  completeResolutionNormIdentityCandidate
    (fun s => -completeResolutionHorizontalRate s)
    completeResolutionHorizontalRate

/-- Forward descent and shared gauge are perfect; the reflected local law is left exposed. -/
def completeResolutionForwardSharedCandidate :
    SharedGaugeReflectionDescentCandidate :=
  completeResolutionNormIdentityCandidate
    (fun s => -completeResolutionHorizontalRate s)
    (fun s => -completeResolutionHorizontalRate s)

/-- Reflected descent and shared gauge are perfect; the forward local law is left exposed. -/
def completeResolutionReflectedSharedCandidate :
    SharedGaugeReflectionDescentCandidate :=
  completeResolutionNormIdentityCandidate
    completeResolutionHorizontalRate
    completeResolutionHorizontalRate

theorem completeResolutionSplitGaugeCandidate_forwardGood
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionForwardGood K completeResolutionSplitGaugeCandidate s := by
  refine ⟨?_, rfl, ?_⟩
  · exact norm_ne_zero_iff.mpr
      (completeResolutionForwardSourcePacket_ne_zero K s)
  · simp [completeResolutionSplitGaugeCandidate,
      completeResolutionNormIdentityCandidate,
      completeResolutionForwardObserved]

theorem completeResolutionSplitGaugeCandidate_reflectedGood
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionReflectedGood K completeResolutionSplitGaugeCandidate s := by
  refine ⟨?_, rfl, ?_⟩
  · exact norm_ne_zero_iff.mpr
      (completeResolutionReflectedSourcePacket_ne_zero K s)
  · simp [completeResolutionSplitGaugeCandidate,
      completeResolutionNormIdentityCandidate,
      completeResolutionReflectedObserved]

theorem completeResolutionForwardSharedCandidate_forwardGood
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionForwardGood K completeResolutionForwardSharedCandidate s := by
  refine ⟨?_, rfl, ?_⟩
  · exact norm_ne_zero_iff.mpr
      (completeResolutionForwardSourcePacket_ne_zero K s)
  · simp [completeResolutionForwardSharedCandidate,
      completeResolutionNormIdentityCandidate,
      completeResolutionForwardObserved]

theorem completeResolutionReflectedSharedCandidate_reflectedGood
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionReflectedGood K completeResolutionReflectedSharedCandidate s := by
  refine ⟨?_, rfl, ?_⟩
  · exact norm_ne_zero_iff.mpr
      (completeResolutionReflectedSourcePacket_ne_zero K s)
  · simp [completeResolutionReflectedSharedCandidate,
      completeResolutionNormIdentityCandidate,
      completeResolutionReflectedObserved]

theorem completeResolutionForwardSharedCandidate_sharedGauge
    (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionSharedGauge completeResolutionForwardSharedCandidate s := by
  rfl

theorem completeResolutionReflectedSharedCandidate_sharedGauge
    (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionSharedGauge completeResolutionReflectedSharedCandidate s := by
  rfl

/-- Pairwise sharpness, first face: both local laws coexist off line by splitting the gauge. -/
theorem completeResolution_splitGauge_pairwiseSharp
    (K : ℕ) (s : CompleteResolutionOffLineStrip) :
    CompleteResolutionForwardGood K completeResolutionSplitGaugeCandidate s.1 ∧
    CompleteResolutionReflectedGood K completeResolutionSplitGaugeCandidate s.1 ∧
    ¬ CompleteResolutionSharedGauge completeResolutionSplitGaugeCandidate s.1 := by
  refine ⟨completeResolutionSplitGaugeCandidate_forwardGood K s.1,
    completeResolutionSplitGaugeCandidate_reflectedGood K s.1, ?_⟩
  intro hshared
  rw [CompleteResolutionSharedGauge, completeResolutionSplitGaugeCandidate,
    completeResolutionNormIdentityCandidate] at hshared
  have hrate : completeResolutionHorizontalRate s.1 = 0 := by
    linarith
  exact s.2 (sub_eq_zero.mp hrate)

/-- Pairwise sharpness, second face: forward law and overlap descent coexist off line. -/
theorem completeResolution_forwardShared_pairwiseSharp
    (K : ℕ) (s : CompleteResolutionOffLineStrip) :
    CompleteResolutionForwardGood K completeResolutionForwardSharedCandidate s.1 ∧
    CompleteResolutionSharedGauge completeResolutionForwardSharedCandidate s.1 ∧
    ¬ CompleteResolutionReflectedGood K completeResolutionForwardSharedCandidate s.1 := by
  refine ⟨completeResolutionForwardSharedCandidate_forwardGood K s.1,
    completeResolutionForwardSharedCandidate_sharedGauge s.1, ?_⟩
  rcases completeResolution_sharedGaugeReflection_failure_at
      K completeResolutionForwardSharedCandidate s with hforward | hreflected | hshared
  · exact False.elim (hforward
      (completeResolutionForwardSharedCandidate_forwardGood K s.1))
  · exact hreflected
  · exact False.elim (hshared
      (completeResolutionForwardSharedCandidate_sharedGauge s.1))

/-- Pairwise sharpness, third face: reflected law and overlap descent coexist off line. -/
theorem completeResolution_reflectedShared_pairwiseSharp
    (K : ℕ) (s : CompleteResolutionOffLineStrip) :
    CompleteResolutionReflectedGood K completeResolutionReflectedSharedCandidate s.1 ∧
    CompleteResolutionSharedGauge completeResolutionReflectedSharedCandidate s.1 ∧
    ¬ CompleteResolutionForwardGood K completeResolutionReflectedSharedCandidate s.1 := by
  refine ⟨completeResolutionReflectedSharedCandidate_reflectedGood K s.1,
    completeResolutionReflectedSharedCandidate_sharedGauge s.1, ?_⟩
  rcases completeResolution_sharedGaugeReflection_failure_at
      K completeResolutionReflectedSharedCandidate s with hforward | hreflected | hshared
  · exact hforward
  · exact False.elim (hreflected
      (completeResolutionReflectedSharedCandidate_reflectedGood K s.1))
  · exact False.elim (hshared
      (completeResolutionReflectedSharedCandidate_sharedGauge s.1))

/-- Closed capstone: the source-defined failure charts cover the off-line strip and all three
two-obligation faces are inhabited there. -/
theorem completeResolution_sharedGaugeReflection_atlas_minimal
    (K : ℕ) (s : CompleteResolutionOffLineStrip) :
    (∀ C : SharedGaugeReflectionDescentCandidate,
      ¬ CompleteResolutionForwardGood K C s.1 ∨
      ¬ CompleteResolutionReflectedGood K C s.1 ∨
      ¬ CompleteResolutionSharedGauge C s.1) ∧
    (CompleteResolutionForwardGood K completeResolutionSplitGaugeCandidate s.1 ∧
      CompleteResolutionReflectedGood K completeResolutionSplitGaugeCandidate s.1 ∧
      ¬ CompleteResolutionSharedGauge completeResolutionSplitGaugeCandidate s.1) ∧
    (CompleteResolutionForwardGood K completeResolutionForwardSharedCandidate s.1 ∧
      CompleteResolutionSharedGauge completeResolutionForwardSharedCandidate s.1 ∧
      ¬ CompleteResolutionReflectedGood K completeResolutionForwardSharedCandidate s.1) ∧
    (CompleteResolutionReflectedGood K completeResolutionReflectedSharedCandidate s.1 ∧
      CompleteResolutionSharedGauge completeResolutionReflectedSharedCandidate s.1 ∧
      ¬ CompleteResolutionForwardGood K completeResolutionReflectedSharedCandidate s.1) := by
  refine ⟨fun C => completeResolution_sharedGaugeReflection_failure_at K C s,
    completeResolution_splitGauge_pairwiseSharp K s,
    completeResolution_forwardShared_pairwiseSharp K s,
    completeResolution_reflectedShared_pairwiseSharp K s⟩

end

end RHTower
