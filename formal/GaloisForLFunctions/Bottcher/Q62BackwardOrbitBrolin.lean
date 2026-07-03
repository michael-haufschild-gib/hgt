/-
# q62 backward-orbit density from the Brolin finite-measure stack

`Q62OneSidedPullback` isolates `BackwardOrbitDense` as the dynamical input needed to
spread one local one-sided point across the Julia frontier.  This file connects that
input to the existing arbitrary-target Brolin stack.

The algebraic and weak-convergence parts are discharged here:

* positive finite arbitrary-target pre-Brolin mass in a ball gives an actual
  `f_c^[n]`-preimage in that ball;
* positive mass of the selected arbitrary-target Brolin cluster on a Julia ball
  gives such a finite level by portmanteau;
* a target avoiding the positive critical orbit upgrades ordinary preimage
  density to the non-critical form `BackwardOrbitDense`.

What remains for the full classical statement is exactly the support theorem
`BrolinJuliaBallPositiveAt`: every ball centered at a Julia-frontier point has
positive mass for the arbitrary-target limiting Brolin measure.
-/
import GaloisForLFunctions.Bottcher.Q62OneSidedPullback
import GaloisForLFunctions.Bottcher.OneSidedCofinal
import GaloisForLFunctions.Bottcher.Brolin.TargetLimit
import GaloisForLFunctions.Bottcher.CrossRatioSelectorBridge
import GaloisForLFunctions.Bottcher.Q62PhiMeroConditional
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional
import GaloisForLFunctions.Bottcher.BottcherArcExtension
import Mathlib.MeasureTheory.Measure.Support

open Set Metric Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

noncomputable section

/-- Ordinary backward-preimage density on the Julia frontier, without the
critical-orbit avoidance clause carried by `BackwardOrbitDense`. -/
def PreimagesDenseInJulia (c a : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0, ∃ (n : ℕ) (z : ℂ),
    (quadratic c)^[n] z = a ∧ dist p z < ε

/-- The exact support-positivity residue needed from Brolin: every Julia ball
has positive mass for the selected arbitrary-target limiting measure. -/
def BrolinJuliaBallPositiveAt (c a : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0,
    0 < limitingBrolinMeasureAt c a (Metric.ball p ε)

/-- A target is not on the positive critical orbit.  This sufficient condition
turns an arbitrary pullback root of `a` into a non-critical pullback root. -/
def CriticalOrbitAvoidingTarget (c a : ℂ) : Prop :=
  ∀ m : ℕ, 0 < m → (quadratic c)^[m] (0 : ℂ) ≠ a

/-- Membership in the arbitrary-target root multiset is the same as being an
`n`-fold preimage of the target. -/
theorem iterate_eq_target_of_mem_roots_quadraticPolyIterate_sub_C
    {c a z : ℂ} {n : ℕ}
    (hz : z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots) :
    (quadratic c)^[n] z = a := by
  have hp : quadraticPolyIterate c n - Polynomial.C a ≠ 0 :=
    (quadraticPolyIterate_sub_C_monic c a n).ne_zero
  have hisroot : (quadraticPolyIterate c n - Polynomial.C a).IsRoot z :=
    (Polynomial.mem_roots hp).mp hz
  rwa [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
    quadraticPolyIterate_eval, sub_eq_zero] at hisroot

/-- Positive finite arbitrary-target pre-Brolin mass in a metric ball contains
an actual level-`n` pullback root in that ball. -/
theorem exists_mem_roots_ball_of_preBrolinMeasureAt_ball_pos
    {c a p : ℂ} {ε : ℝ} {n : ℕ}
    (hpos : 0 < preBrolinMeasureAt c a n (Metric.ball p ε)) :
    ∃ z : ℂ, z ∈ (quadraticPolyIterate c n - Polynomial.C a).roots ∧
      dist p z < ε := by
  classical
  by_contra hnone
  push Not at hnone
  have hcard :
      (((quadraticPolyIterate c n - Polynomial.C a).roots).filter
        fun z => z ∈ Metric.ball p ε).card = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hcardpos
    obtain ⟨z, hzfilter⟩ :=
      Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hcardpos)
    rcases Multiset.mem_filter.mp hzfilter with ⟨hzroot, hzball⟩
    exact not_lt_of_ge (hnone z hzroot)
      (by simpa [Metric.mem_ball, dist_comm] using hzball)
  have hzero : preBrolinMeasureAt c a n (Metric.ball p ε) = 0 := by
    rw [preBrolinMeasureAt, Measure.smul_apply,
      rootCountingMeasure_apply_of_measurableSet _ Metric.isOpen_ball.measurableSet]
    rw [hcard]
    simp
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ENNReal)) hpos

/-- Positive finite arbitrary-target pre-Brolin mass in a ball gives a genuine
preimage of the target in that ball. -/
theorem exists_preimage_ball_of_preBrolinMeasureAt_ball_pos
    {c a p : ℂ} {ε : ℝ} {n : ℕ}
    (hpos : 0 < preBrolinMeasureAt c a n (Metric.ball p ε)) :
    ∃ z : ℂ, (quadratic c)^[n] z = a ∧ dist p z < ε := by
  obtain ⟨z, hzroot, hzball⟩ :=
    exists_mem_roots_ball_of_preBrolinMeasureAt_ball_pos (c := c) (a := a)
      (p := p) (ε := ε) (n := n) hpos
  exact ⟨z, iterate_eq_target_of_mem_roots_quadraticPolyIterate_sub_C hzroot, hzball⟩

/-- If the selected arbitrary-target Brolin cluster has positive mass on an
open ball, some finite pullback level in the chosen subsequence already has
positive mass on that ball. -/
theorem exists_preBrolinMeasureAt_subseq_ball_pos_of_limitingBrolinMeasureAt_ball_pos
    {c a p : ℂ} {ε : ℝ}
    (hpos : 0 < limitingBrolinMeasureAt c a (Metric.ball p ε)) :
    ∃ k : ℕ,
      0 < preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
        (Metric.ball p ε) := by
  classical
  let G : Set (targetEscapeDisk c a) :=
    ((fun z : targetEscapeDisk c a => (z : ℂ)) ⁻¹' Metric.ball p ε)
  have hGopen : IsOpen G := by
    dsimp [G]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hposG :
      0 < (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G := by
    have hmeas : MeasurableSet (Metric.ball p ε) := Metric.isOpen_ball.measurableSet
    have hmap :
        limitingBrolinMeasureAt c a (Metric.ball p ε) =
          (brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)) G := by
      rw [limitingBrolinMeasureAt, Measure.map_apply measurable_subtype_coe hmeas]
    rwa [hmap] at hpos
  by_contra hnone
  push Not at hnone
  have hle :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a) hGopen
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k) :
          Measure (targetEscapeDisk c a)) G = 0 := by
    refine Filter.Eventually.of_forall ?_
    intro k
    have hplane_nonpos :
        preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
          (Metric.ball p ε) ≤ 0 := hnone k
    have hplane_zero :
        preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
          (Metric.ball p ε) = 0 :=
      le_antisymm hplane_nonpos bot_le
    have hmeas : MeasurableSet (Metric.ball p ε) := Metric.isOpen_ball.measurableSet
    have hmap :
        preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k)
          (Metric.ball p ε) =
        (preBrolinMeasureAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k)) G := by
      rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk,
        Measure.map_apply measurable_subtype_coe hmeas]
    have hsub_zero :
        (preBrolinMeasureAtOnTargetEscapeDisk c a
          (brolinLimitAtSubsequence c a k)) G = 0 := by
      rw [← hmap, hplane_zero]
    simpa [preBrolinProbabilityAtOnTargetEscapeDisk, G] using hsub_zero
  have htend :
      Tendsto
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G)
        atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hevent] with k hk
    exact hk.symm
  have hliminf :
      atTop.liminf
        (fun k =>
          (preBrolinProbabilityAtOnTargetEscapeDisk c a
            (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)) G) = 0 :=
    htend.liminf_eq
  have hle_zero :
      (brolinLimitAtOnTargetEscapeDisk c a :
        Measure (targetEscapeDisk c a)) G ≤ 0 := by
    rw [← hliminf]
    exact hle
  exact (not_lt_of_ge hle_zero) hposG

/-- Positive limiting Brolin mass on a ball produces an actual finite
arbitrary-target preimage in that ball. -/
theorem exists_preimage_ball_of_limitingBrolinMeasureAt_ball_pos
    {c a p : ℂ} {ε : ℝ}
    (hpos : 0 < limitingBrolinMeasureAt c a (Metric.ball p ε)) :
    ∃ (n : ℕ) (z : ℂ), (quadratic c)^[n] z = a ∧ dist p z < ε := by
  obtain ⟨k, hkpos⟩ :=
    exists_preBrolinMeasureAt_subseq_ball_pos_of_limitingBrolinMeasureAt_ball_pos
      (c := c) (a := a) (p := p) (ε := ε) hpos
  obtain ⟨z, hz, hdist⟩ :=
    exists_preimage_ball_of_preBrolinMeasureAt_ball_pos
      (c := c) (a := a) (p := p) (ε := ε)
      (n := brolinLimitAtSubsequence c a k) hkpos
  exact ⟨brolinLimitAtSubsequence c a k, z, hz, hdist⟩

/-- The support-positive Brolin cluster hypothesis is exactly enough to prove
ordinary preimages are dense in the Julia frontier. -/
theorem preimagesDenseInJulia_of_brolinJuliaBallPositiveAt
    {c a : ℂ} (hpos : BrolinJuliaBallPositiveAt c a) :
    PreimagesDenseInJulia c a := by
  intro p hp ε hε
  exact exists_preimage_ball_of_limitingBrolinMeasureAt_ball_pos
    (c := c) (a := a) (p := p) (ε := ε) (hpos p hp ε hε)

/-- `BackwardOrbitDense` immediately implies ordinary preimage density on the
Julia frontier. -/
theorem PreimagesDenseInJulia.of_backwardOrbitDense
    {c a : ℂ} (hbwd : BackwardOrbitDense c a) :
    PreimagesDenseInJulia c a := by
  intro p hp ε hε
  obtain ⟨n, z, hz, _hcrit, hdist⟩ := hbwd p hp ε hε
  exact ⟨n, z, hz, hdist⟩

/-- If the target avoids the positive critical orbit, every finite preimage of
the target is non-critical along its forward path. -/
theorem critical_avoidance_of_iterate_eq_target
    {c a z : ℂ} {n : ℕ}
    (hcrit : CriticalOrbitAvoidingTarget c a)
    (hz : (quadratic c)^[n] z = a) :
    ∀ i < n, (quadratic c)^[i] z ≠ 0 := by
  intro i hi hzero
  have hle : i ≤ n := le_of_lt hi
  have hhit : (quadratic c)^[n - i] ((quadratic c)^[i] z) = a := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    exact hz
  rw [hzero] at hhit
  exact hcrit (n - i) (Nat.sub_pos_of_lt hi) hhit

/-- The support-positive arbitrary-target Brolin statement, plus critical-orbit
avoidance of the target, discharges the q62 `BackwardOrbitDense` input. -/
theorem backwardOrbitDense_of_brolinJuliaBallPositiveAt
    {c a : ℂ} (hpos : BrolinJuliaBallPositiveAt c a)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    BackwardOrbitDense c a := by
  intro p hp ε hε
  obtain ⟨n, z, hz, hdist⟩ :=
    preimagesDenseInJulia_of_brolinJuliaBallPositiveAt hpos p hp ε hε
  exact ⟨n, z, hz, critical_avoidance_of_iterate_eq_target hcrit hz, hdist⟩

/-- q62-facing wrapper: the Brolin support-positive statement is enough to
spread one base `LocOneSided` point to a dense set of `LocOneSided` points. -/
theorem locOneSidedDense_of_base_brolinJuliaBallPositiveAt
    {c z₀ : ℂ} (hbase : LocOneSided c z₀)
    (hpos : BrolinJuliaBallPositiveAt c z₀)
    (hcrit : CriticalOrbitAvoidingTarget c z₀) :
    LocOneSidedDense c :=
  locOneSidedDense_of_base_backwardDense hbase
    (backwardOrbitDense_of_brolinJuliaBallPositiveAt hpos hcrit)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- The pullback-stable local one-sided notion is strong enough for the
neighbourhood-cofinal q62 interface. -/
theorem oneSidedAtCofinalNbhd_of_locOneSided {c z : ℂ}
    (h : LocOneSided c z) : OneSidedAtCofinalNbhd c z := by
  obtain ⟨hzfront, hbasis⟩ := h
  refine ⟨hzfront, ?_⟩
  intro ε hε
  obtain ⟨V, hVo, hzV, hVsub, hVpre, hVne⟩ := hbasis ε hε
  refine ⟨V, hVo, hzV, hVsub, ?_⟩
  rw [Set.diff_eq]
  exact ⟨hVne, hVpre⟩

/-- Density of neighbourhood-cofinal one-sided points on the Julia frontier. -/
def OneSidedAtCofinalNbhdDense (c : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0,
    ∃ z, OneSidedAtCofinalNbhd c z ∧ dist p z < ε

/-- Dense `LocOneSided` points give dense neighbourhood-cofinal one-sided
points. -/
theorem oneSidedAtCofinalNbhdDense_of_locOneSidedDense
    {c : ℂ} (hd : LocOneSidedDense c) : OneSidedAtCofinalNbhdDense c := by
  intro p hp ε hε
  obtain ⟨z, hz, hdist⟩ := hd p hp ε hε
  exact ⟨z, oneSidedAtCofinalNbhd_of_locOneSided hz, hdist⟩

/-- Set-closure form of neighbourhood-cofinal one-sided density. -/
theorem frontier_subset_closure_oneSidedAtCofinalNbhd_of_dense
    {c : ℂ} (hd : OneSidedAtCofinalNbhdDense c) :
    frontier (filledJulia c) ⊆ closure {z | OneSidedAtCofinalNbhd c z} := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hdist⟩ := hd p hp ε hε
  exact ⟨z, hz, hdist⟩

/-- If the neighbourhood-cofinal one-sided points are dense on both Julia
frontiers, one orientation has such a point outside the other filled Julia set. -/
theorem exists_oneSidedCofinalNbhd_offOther_of_dense
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hd₁ : OneSidedAtCofinalNbhdDense c₁)
    (hd₂ : OneSidedAtCofinalNbhdDense c₂) :
    (∃ x, OneSidedAtCofinalNbhd c₁ x ∧ x ∉ filledJulia c₂) ∨
      (∃ x, OneSidedAtCofinalNbhd c₂ x ∧ x ∉ filledJulia c₁) := by
  have hD₁ : frontier (filledJulia c₁) ⊆ closure {z | OneSidedAtCofinalNbhd c₁ z} :=
    frontier_subset_closure_oneSidedAtCofinalNbhd_of_dense hd₁
  have hD₂ : frontier (filledJulia c₂) ⊆ closure {z | OneSidedAtCofinalNbhd c₂ z} :=
    frontier_subset_closure_oneSidedAtCofinalNbhd_of_dense hd₂
  rcases exists_exposed_of_dense_frontier hne hD₁ hD₂ with ⟨x, hx, hx2⟩ | ⟨x, hx, hx1⟩
  · exact Or.inl ⟨x, hx, hx2⟩
  · exact Or.inr ⟨x, hx, hx1⟩

/-- Version of the exposure dichotomy fed by the pullback-stable local
one-sided density. -/
theorem exists_oneSidedCofinalNbhd_offOther_of_locOneSidedDense
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hd₁ : LocOneSidedDense c₁) (hd₂ : LocOneSidedDense c₂) :
    (∃ x, OneSidedAtCofinalNbhd c₁ x ∧ x ∉ filledJulia c₂) ∨
      (∃ x, OneSidedAtCofinalNbhd c₂ x ∧ x ∉ filledJulia c₁) :=
  exists_oneSidedCofinalNbhd_offOther_of_dense hne
    (oneSidedAtCofinalNbhdDense_of_locOneSidedDense hd₁)
    (oneSidedAtCofinalNbhdDense_of_locOneSidedDense hd₂)

/-- The visibility upgrade still needed after an off-other
neighbourhood-cofinal one-sided point is found. -/
def OffOtherCofinalNbhdVisible (c₁ c₂ : ℂ) : Prop :=
  ∀ x, OneSidedAtCofinalNbhd c₁ x → x ∉ filledJulia c₂ →
    VisibleFromInfinity c₁ c₂ x

/-- Local one-sidedness plus off-other visibility gives the exposed
neighbourhood-cofinal input consumed by the q62 capstone. -/
theorem exposedOneSidedCofinalNbhd_of_locOneSided_visible
    {c₁ c₂ x : ℂ} (hloc : LocOneSided c₁ x)
    (hx2 : x ∉ filledJulia c₂) (hvis : VisibleFromInfinity c₁ c₂ x) :
    ExposedOneSidedCofinalNbhd c₁ c₂ :=
  ⟨x, oneSidedAtCofinalNbhd_of_locOneSided hloc, hx2, hvis⟩

/-- Dense local one-sidedness plus the visibility upgrade gives the exposed
neighbourhood-cofinal disjunction. -/
theorem exposedOneSidedCofinalNbhd_or_swap_of_locOneSidedDense
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hd₁ : LocOneSidedDense c₁) (hd₂ : LocOneSidedDense c₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁) :
    ExposedOneSidedCofinalNbhd c₁ c₂ ∨ ExposedOneSidedCofinalNbhd c₂ c₁ := by
  rcases exists_oneSidedCofinalNbhd_offOther_of_locOneSidedDense hne hd₁ hd₂ with
    ⟨x, hx, hx2⟩ | ⟨x, hx, hx1⟩
  · exact Or.inl ⟨x, hx, hx2, hvis₁₂ x hx hx2⟩
  · exact Or.inr ⟨x, hx, hx1, hvis₂₁ x hx hx1⟩

/-- Brolin support-positivity plus critical-orbit avoidance produces dense
neighbourhood-cofinal one-sided points from one local base point. -/
theorem oneSidedAtCofinalNbhdDense_of_base_brolinJuliaBallPositiveAt
    {c z₀ : ℂ} (hbase : LocOneSided c z₀)
    (hpos : BrolinJuliaBallPositiveAt c z₀)
    (hcrit : CriticalOrbitAvoidingTarget c z₀) :
    OneSidedAtCofinalNbhdDense c :=
  oneSidedAtCofinalNbhdDense_of_locOneSidedDense
    (locOneSidedDense_of_base_brolinJuliaBallPositiveAt hbase hpos hcrit)

/-- Q62-facing Brolin bridge up to the remaining visibility upgrade: from one
local base point on each side, Brolin support-positivity yields the exposed
neighbourhood-cofinal disjunction once off-other witnesses are visible from
infinity. -/
theorem exposedOneSidedCofinalNbhd_or_swap_of_base_brolinJuliaBallPositiveAt
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hbase₂ : LocOneSided c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁) :
    ExposedOneSidedCofinalNbhd c₁ c₂ ∨ ExposedOneSidedCofinalNbhd c₂ c₁ :=
  exposedOneSidedCofinalNbhd_or_swap_of_locOneSidedDense hne
    (locOneSidedDense_of_base_brolinJuliaBallPositiveAt hbase₁ hpos₁ hcrit₁)
    (locOneSidedDense_of_base_brolinJuliaBallPositiveAt hbase₂ hpos₂ hcrit₂)
    hvis₁₂ hvis₂₁

/-- Both-connected q62 from the Brolin backward-orbit bridge, separated into
its remaining residues: Brolin Julia-ball positivity, critical-orbit avoidance,
one local base point on each side, off-other visibility, and smooth-piece
rigidity. -/
theorem q62_phiMero_bothconnected_of_base_brolinJuliaBallPositiveAt_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hpos₁ : BrolinJuliaBallPositiveAt c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hbase₂ : LocOneSided c₂ z₂)
    (hpos₂ : BrolinJuliaBallPositiveAt c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_op6_cofinalNbhd hUo hUc hUne hUinf
    hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (exposedOneSidedCofinalNbhd_or_swap_of_base_brolinJuliaBallPositiveAt hne
      hbase₁ hpos₁ hcrit₁ hbase₂ hpos₂ hcrit₂ hvis₁₂ hvis₂₁)
    hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Standard support-theorem form of the remaining arbitrary-target Brolin gap:
the selected limiting Brolin measure has every Julia-frontier point in its
measure-theoretic support. -/
def LimitingBrolinMeasureAtSupportsJulia (c a : ℂ) : Prop :=
  frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support

/-- The standard support statement implies the ball-positivity form used by the
backward-orbit bridge. -/
theorem brolinJuliaBallPositiveAt_of_limitingBrolinMeasureAtSupportsJulia
    {c a : ℂ} (hsupp : LimitingBrolinMeasureAtSupportsJulia c a) :
    BrolinJuliaBallPositiveAt c a := by
  intro p hp ε hε
  have hpμ : p ∈ (limitingBrolinMeasureAt c a).support := hsupp hp
  rw [Measure.mem_support_iff_forall] at hpμ
  exact hpμ (Metric.ball p ε) (Metric.ball_mem_nhds p hε)

/-- Support-on-Julia plus critical-orbit avoidance discharges
`BackwardOrbitDense`. -/
theorem backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia
    {c a : ℂ} (hsupp : LimitingBrolinMeasureAtSupportsJulia c a)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    BackwardOrbitDense c a :=
  backwardOrbitDense_of_brolinJuliaBallPositiveAt
    (brolinJuliaBallPositiveAt_of_limitingBrolinMeasureAtSupportsJulia hsupp) hcrit

/-- Support-on-Julia is also enough for ordinary density of target preimages in
`J_c`. -/
theorem preimagesDenseInJulia_of_limitingBrolinMeasureAtSupportsJulia
    {c a : ℂ} (hsupp : LimitingBrolinMeasureAtSupportsJulia c a) :
    PreimagesDenseInJulia c a :=
  preimagesDenseInJulia_of_brolinJuliaBallPositiveAt
    (brolinJuliaBallPositiveAt_of_limitingBrolinMeasureAtSupportsJulia hsupp)

/-- Q62-facing local one-sided density from the standard support-theorem form. -/
theorem locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia
    {c z₀ : ℂ} (hbase : LocOneSided c z₀)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c z₀)
    (hcrit : CriticalOrbitAvoidingTarget c z₀) :
    LocOneSidedDense c :=
  locOneSidedDense_of_base_backwardDense hbase
    (backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia hsupp hcrit)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Q62-facing Brolin bridge using the standard support-theorem form instead
of the ball-positivity form. -/
theorem exposedOneSidedCofinalNbhd_or_swap_of_base_limitingBrolinMeasureAtSupportsJulia
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hbase₂ : LocOneSided c₂ z₂)
    (hsupp₂ : LimitingBrolinMeasureAtSupportsJulia c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁) :
    ExposedOneSidedCofinalNbhd c₁ c₂ ∨ ExposedOneSidedCofinalNbhd c₂ c₁ :=
  exposedOneSidedCofinalNbhd_or_swap_of_locOneSidedDense hne
    (locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia hbase₁ hsupp₁ hcrit₁)
    (locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia hbase₂ hsupp₂ hcrit₂)
    hvis₁₂ hvis₂₁

/-- Both-connected q62 from the standard support-theorem form of the Brolin
residue, plus the remaining base, visibility, and smooth-piece inputs. -/
theorem q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hbase₂ : LocOneSided c₂ z₂)
    (hsupp₂ : LimitingBrolinMeasureAtSupportsJulia c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_op6_cofinalNbhd hUo hUc hUne hUinf
    hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (exposedOneSidedCofinalNbhd_or_swap_of_base_limitingBrolinMeasureAtSupportsJulia hne
      hbase₁ hsupp₁ hcrit₁ hbase₂ hsupp₂ hcrit₂ hvis₁₂ hvis₂₁)
    hrig₁₂ hrig₂₁

/-- If two fixed points both fail the critical-orbit avoidance condition, then
they are the same fixed point. -/
theorem fixed_points_eq_of_not_criticalOrbitAvoidingTarget
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β)
    (hαcrit : ¬ CriticalOrbitAvoidingTarget c α)
    (hβcrit : ¬ CriticalOrbitAvoidingTarget c β) :
    α = β := by
  rw [CriticalOrbitAvoidingTarget] at hαcrit hβcrit
  push Not at hαcrit hβcrit
  obtain ⟨i, hi0, hi⟩ := hαcrit
  obtain ⟨j, hj0, hj⟩ := hβcrit
  rcases le_total i j with hij | hji
  · symm
    have hdecomp : j = (j - i) + i := by omega
    calc
      β = (quadratic c)^[j] (0 : ℂ) := hj.symm
      _ = (quadratic c)^[(j - i) + i] (0 : ℂ) := by rw [← hdecomp]
      _ = (quadratic c)^[j - i] ((quadratic c)^[i] (0 : ℂ)) := by
        rw [Function.iterate_add_apply]
      _ = (quadratic c)^[j - i] α := by rw [hi]
      _ = α := Function.iterate_fixed hαfix (j - i)
  · have hdecomp : i = (i - j) + j := by omega
    calc
      α = (quadratic c)^[i] (0 : ℂ) := hi.symm
      _ = (quadratic c)^[(i - j) + j] (0 : ℂ) := by rw [← hdecomp]
      _ = (quadratic c)^[i - j] ((quadratic c)^[j] (0 : ℂ)) := by
        rw [Function.iterate_add_apply]
      _ = (quadratic c)^[i - j] β := by rw [hj]
      _ = β := Function.iterate_fixed hβfix (i - j)

/-- For `c ≠ 1/4`, at least one fixed point avoids the positive critical
orbit, in the `CriticalOrbitAvoidingTarget` form used by the Brolin pullback
bridge. -/
theorem exists_fixed_point_criticalOrbitAvoidingTarget
    (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ α : ℂ, quadratic c α = α ∧ CriticalOrbitAvoidingTarget c α := by
  obtain ⟨α, β, hαfix, hβfix, hαβ⟩ := exists_two_distinct_fixed_points c hc
  by_cases hαcrit : CriticalOrbitAvoidingTarget c α
  · exact ⟨α, hαfix, hαcrit⟩
  · by_cases hβcrit : CriticalOrbitAvoidingTarget c β
    · exact ⟨β, hβfix, hβcrit⟩
    · exact False.elim (hαβ (fixed_points_eq_of_not_criticalOrbitAvoidingTarget
        hαfix hβfix hαcrit hβcrit))

/-- Choosing a fixed target removes the separate critical-orbit-avoidance
residue from the support-form Brolin route to `BackwardOrbitDense`. -/
theorem exists_fixedPoint_backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia
    {c : ℂ} (hc : c ≠ 1 / 4)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget c hc
  exact ⟨a, hfix,
    backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia (hsupp a hfix) hcrit⟩

/-- Fixed-point version of the local one-sided density bridge: the target is
chosen so critical-orbit avoidance is automatic. -/
theorem locOneSidedDense_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia
    {c : ℂ} (hc : c ≠ 1 / 4)
    (hbase : ∀ a : ℂ, quadratic c a = a →
      CriticalOrbitAvoidingTarget c a → LocOneSided c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget c hc
  exact locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Both-connected q62 with fixed targets selected internally.  This removes
explicit target choices and explicit critical-orbit-avoidance hypotheses from
the support-form Brolin bridge. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      CriticalOrbitAvoidingTarget c₁ a → LocOneSided c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      CriticalOrbitAvoidingTarget c₂ a → LocOneSided c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ :=
    exists_fixed_point_criticalOrbitAvoidingTarget c₁ hc₁quarter
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ :=
    exists_fixed_point_criticalOrbitAvoidingTarget c₂ hc₂quarter
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (hbase₁ z₁ hz₁fix hz₁crit) (hsupp₁ z₁ hz₁fix) hz₁crit
    (hbase₂ z₂ hz₂fix hz₂crit) (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- The neighbourhood-cofinal q62 one-sided form is exactly strong enough to
feed the pullback-stable local one-sided interface: connected puncture supplies
both nonempty and preconnected basin part. -/
theorem locOneSided_of_oneSidedAtCofinalNbhd {c z : ℂ}
    (h : OneSidedAtCofinalNbhd c z) : LocOneSided c z := by
  obtain ⟨hzfront, hbasis⟩ := h
  refine ⟨hzfront, ?_⟩
  intro ε hε
  obtain ⟨V, hVo, hzV, hVsub, hVconn⟩ := hbasis ε hε
  refine ⟨V, hVo, hzV, hVsub, ?_, ?_⟩
  · rw [Set.diff_eq] at hVconn
    exact hVconn.2
  · rw [Set.diff_eq] at hVconn
    exact hVconn.1

/-- Support-form Brolin pullback with a neighbourhood-cofinal base point rather
than a `LocOneSided` base point. -/
theorem locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia
    {c z0 : ℂ} (hbase : OneSidedAtCofinalNbhd c z0)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c z0)
    (hcrit : CriticalOrbitAvoidingTarget c z0) :
    LocOneSidedDense c :=
  locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia
    (locOneSided_of_oneSidedAtCofinalNbhd hbase) hsupp hcrit

/-- Fixed-point version of the support-form Brolin pullback when the available
base one-sidedness is the neighbourhood-cofinal q62 form. -/
theorem locOneSidedDense_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia
    {c : ℂ} (hc : c ≠ 1 / 4)
    (hbase : ∀ a : ℂ, quadratic c a = a →
      CriticalOrbitAvoidingTarget c a → OneSidedAtCofinalNbhd c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget c hc
  exact locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Both-connected q62 with fixed targets selected internally and the base
one-sidedness supplied in the neighbourhood-cofinal form. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      CriticalOrbitAvoidingTarget c₁ a → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      CriticalOrbitAvoidingTarget c₂ a → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ :=
    exists_fixed_point_criticalOrbitAvoidingTarget c₁ hc₁quarter
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ :=
    exists_fixed_point_criticalOrbitAvoidingTarget c₂ hc₂quarter
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix) hz₁crit
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₂ z₂ hz₂fix hz₂crit))
    (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- A raw seed for the neighbourhood-cofinal fixed-point transfer: at every
scale there is one open neighbourhood with connected puncture.  The inverse
branch threshold lemma upgrades this to full cofinal neighbourhood
one-sidedness at a repelling fixed point. -/
def ConnectedPunctureSeed (c z : ℂ) : Prop :=
  ∀ r > 0, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Metric.ball z r ∧
    IsConnected (V \ filledJulia c)

/-- The repelling fixed-point threshold engine converts a connected-puncture
seed into the packaged neighbourhood-cofinal one-sided input. -/
theorem oneSidedAtCofinalNbhd_of_repelling_fixed_connectedPunctureSeed
    {c a : ℂ} (hfix : quadratic c a = a) (hrep : 1 < ‖(2 : ℂ) * a‖)
    (hseed : ConnectedPunctureSeed c a) :
    OneSidedAtCofinalNbhd c a := by
  have hfront : a ∈ frontier (filledJulia c) := mem_frontier_of_repelling_fixed hfix hrep
  have hrep' : 1 < 2 * ‖a‖ := by
    simpa [norm_mul] using hrep
  obtain ⟨r₀, hr₀, hthreshold⟩ := exists_threshold_oneSidedAtCofinalNbhd hfront hfix hrep'
  obtain ⟨V₀, hV₀o, haV₀, hV₀sub, hV₀conn⟩ := hseed r₀ hr₀
  exact hthreshold V₀ hV₀o haV₀ hV₀sub hV₀conn

/-- Support-form Brolin pullback from an explicit repelling fixed target and a
raw connected-puncture seed.  This exposes the true remaining local-topology
input instead of requiring a prepackaged `OneSidedAtCofinalNbhd` proof. -/
theorem locOneSidedDense_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia
    {c a : ℂ} (hfix : quadratic c a = a) (hrep : 1 < ‖(2 : ℂ) * a‖)
    (hseed : ConnectedPunctureSeed c a)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c a)
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    LocOneSidedDense c :=
  locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia
    (oneSidedAtCofinalNbhd_of_repelling_fixed_connectedPunctureSeed hfix hrep hseed)
    hsupp hcrit

/-- Both-connected q62 from explicit repelling fixed targets, support-form
Brolin, visibility, smooth-piece rigidity, and the raw local connected-puncture
seeds at those targets. -/
theorem q62_phiMero_bothconnected_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hz₁fix : quadratic c₁ z₁ = z₁) (hz₁rep : 1 < ‖(2 : ℂ) * z₁‖)
    (hseed₁ : ConnectedPunctureSeed c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hz₂fix : quadratic c₂ z₂ = z₂) (hz₂rep : 1 < ‖(2 : ℂ) * z₂‖)
    (hseed₂ : ConnectedPunctureSeed c₂ z₂)
    (hsupp₂ : LimitingBrolinMeasureAtSupportsJulia c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd
      (oneSidedAtCofinalNbhd_of_repelling_fixed_connectedPunctureSeed hz₁fix hz₁rep hseed₁))
    hsupp₁ hcrit₁
    (locOneSided_of_oneSidedAtCofinalNbhd
      (oneSidedAtCofinalNbhd_of_repelling_fixed_connectedPunctureSeed hz₂fix hz₂rep hseed₂))
    hsupp₂ hcrit₂
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- If a point is on `∂K₁` and outside the closed set `K₂`, then it is on the
frontier of the joint compact set `K₁ ∪ K₂`.  Locally near such a point the
second filled Julia set is absent, so the complement side of `∂K₁` is also the
complement side of the union. -/
theorem mem_frontier_filledJulia_union_left_of_frontier_off_right
    {c₁ c₂ x : ℂ} (hx : x ∈ frontier (filledJulia c₁))
    (hx2 : x ∉ filledJulia c₂) :
    x ∈ frontier (filledJulia c₁ ∪ filledJulia c₂) := by
  rw [frontier_eq_closure_inter_closure] at hx ⊢
  refine ⟨closure_mono subset_union_left hx.1, ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl x hx2
  have hxK₁c : x ∈ closure (filledJulia c₁)ᶜ := hx.2
  rw [Metric.mem_closure_iff] at hxK₁c
  obtain ⟨y, hyK₁c, hydist⟩ := hxK₁c (min ε δ) (lt_min hε hδ)
  have hyK₂c : y ∈ (filledJulia c₂)ᶜ := by
    apply hδsub
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hydist (min_le_right _ _)
  refine ⟨y, ?_, lt_of_lt_of_le hydist (min_le_left _ _)⟩
  rw [Set.mem_compl_iff, Set.mem_union]
  intro hy
  rcases hy with hyK₁ | hyK₂
  · exact hyK₁c hyK₁
  · exact hyK₂c hyK₂

/-- Neighbourhood-cofinal one-sidedness plus the off-other condition places the
point on the joint frontier. -/
theorem mem_frontier_union_of_oneSidedAtCofinalNbhd_offOther
    {c₁ c₂ x : ℂ} (hx : OneSidedAtCofinalNbhd c₁ x)
    (hx2 : x ∉ filledJulia c₂) :
    x ∈ frontier (filledJulia c₁ ∪ filledJulia c₂) :=
  mem_frontier_filledJulia_union_left_of_frontier_off_right hx.1 hx2

/-- Visibility residue restricted to the joint frontier; the preceding lemma
shows this is enough for all off-other neighbourhood-cofinal one-sided points. -/
def OffOtherCofinalNbhdJointFrontierVisible (c₁ c₂ : ℂ) : Prop :=
  ∀ x, OneSidedAtCofinalNbhd c₁ x → x ∉ filledJulia c₂ →
    x ∈ frontier (filledJulia c₁ ∪ filledJulia c₂) → VisibleFromInfinity c₁ c₂ x

/-- Joint-frontier visibility implies the older off-other visibility interface. -/
theorem offOtherCofinalNbhdVisible_of_jointFrontierVisible
    {c₁ c₂ : ℂ} (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    OffOtherCofinalNbhdVisible c₁ c₂ := by
  intro x hx hx2
  exact hvis x hx hx2 (mem_frontier_union_of_oneSidedAtCofinalNbhd_offOther hx hx2)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Fixed-target q62 support-form capstone using joint-frontier visibility rather
than the older off-other visibility package. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      CriticalOrbitAvoidingTarget c₁ a → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      CriticalOrbitAvoidingTarget c₂ a → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁quarter hc₂quarter hc₁M hc₂M
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hbase₁ hsupp₁ hbase₂ hsupp₂
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₁₂)
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₂₁)
    hrig₁₂ hrig₂₁

/-- Explicit repelling-fixed q62 support-form capstone using joint-frontier
visibility and raw connected-puncture seeds. -/
theorem q62_phiMero_bothconnected_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hz₁fix : quadratic c₁ z₁ = z₁) (hz₁rep : 1 < ‖(2 : ℂ) * z₁‖)
    (hseed₁ : ConnectedPunctureSeed c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hz₂fix : quadratic c₂ z₂ = z₂) (hz₂rep : 1 < ‖(2 : ℂ) * z₂‖)
    (hseed₂ : ConnectedPunctureSeed c₂ z₂)
    (hsupp₂ : LimitingBrolinMeasureAtSupportsJulia c₂ z₂)
    (hcrit₂ : CriticalOrbitAvoidingTarget c₂ z₂)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    hz₁fix hz₁rep hseed₁ hsupp₁ hcrit₁
    hz₂fix hz₂rep hseed₂ hsupp₂ hcrit₂
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₁₂)
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₂₁)
    hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Ball-positivity on all Julia-centered balls is exactly the support-membership
form of the arbitrary-target Brolin residue. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_brolinJuliaBallPositiveAt
    {c a : ℂ} (hpos : BrolinJuliaBallPositiveAt c a) :
    LimitingBrolinMeasureAtSupportsJulia c a := by
  intro p hp
  rw [Measure.mem_support_iff_forall]
  intro s hs
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hs
  exact lt_of_lt_of_le (hpos p hp ε hε) (measure_mono hεsub)

/-- The two Brolin support residues used in this file are equivalent: support
membership on the Julia frontier and positive mass for every Julia-centered
metric ball. -/
theorem limitingBrolinMeasureAtSupportsJulia_iff_brolinJuliaBallPositiveAt
    (c a : ℂ) :
    LimitingBrolinMeasureAtSupportsJulia c a ↔ BrolinJuliaBallPositiveAt c a :=
  ⟨brolinJuliaBallPositiveAt_of_limitingBrolinMeasureAtSupportsJulia,
    limitingBrolinMeasureAtSupportsJulia_of_brolinJuliaBallPositiveAt⟩

/-- Local support-carrier form used by the q62 bridge.  This is duplicated from
the Brolin target-limit layer so this file checks against the already-built
dependency interface; it uses only the older carrier theorem
`limitingBrolinMeasureAt_filledJulia_compl`. -/
theorem limitingBrolinMeasureAt_support_subset_filledJulia_for_q62 (c a : ℂ) :
    (limitingBrolinMeasureAt c a).support ⊆ filledJulia c := by
  intro z hz
  by_contra hzK
  have hpos : 0 < limitingBrolinMeasureAt c a (filledJulia c)ᶜ := by
    rw [Measure.mem_support_iff_forall] at hz
    exact hz (filledJulia c)ᶜ ((isClosed_filledJulia c).isOpen_compl.mem_nhds hzK)
  rw [limitingBrolinMeasureAt_filledJulia_compl] at hpos
  exact (lt_irrefl _) hpos

/-- Current support localization for the arbitrary-target limiting Brolin
measure once the Julia-frontier positivity residue is supplied: the hard side is
`frontier K_c ⊆ support`; the easy carrier side is already proven in
`Brolin.TargetLimit`. -/
theorem limitingBrolinMeasureAt_support_sandwich_of_brolinJuliaBallPositiveAt
    {c a : ℂ} (hpos : BrolinJuliaBallPositiveAt c a) :
    frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support ∧
      (limitingBrolinMeasureAt c a).support ⊆ filledJulia c :=
  ⟨limitingBrolinMeasureAtSupportsJulia_of_brolinJuliaBallPositiveAt hpos,
    limitingBrolinMeasureAt_support_subset_filledJulia_for_q62 c a⟩

/-- Support-sandwich form from the standard support-theorem statement. -/
theorem limitingBrolinMeasureAt_support_sandwich_of_limitingBrolinMeasureAtSupportsJulia
    {c a : ℂ} (hsupp : LimitingBrolinMeasureAtSupportsJulia c a) :
    frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support ∧
      (limitingBrolinMeasureAt c a).support ⊆ filledJulia c :=
  ⟨hsupp, limitingBrolinMeasureAt_support_subset_filledJulia_for_q62 c a⟩

end

end Bottcher

namespace Bottcher

noncomputable section

/-- The q62 target-avoidance predicate is the pointwise form of being outside
the positive critical orbit used by the repelling-fixed/Newton selector stack. -/
theorem criticalOrbitAvoidingTarget_iff_not_mem_positiveCriticalOrbit
    {c a : ℂ} :
    CriticalOrbitAvoidingTarget c a ↔ a ∉ positiveCriticalOrbit c := by
  constructor
  · intro hcrit hmem
    obtain ⟨j, hj⟩ := hmem
    exact hcrit (j + 1) (Nat.succ_pos j) hj
  · intro hcrit m hm hhit
    apply hcrit
    refine ⟨m - 1, ?_⟩
    simpa [Nat.sub_add_cancel hm] using hhit

/-- Convert the existing positive-critical-orbit avoidance vocabulary into the
q62 Brolin pullback target predicate. -/
theorem criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit
    {c a : ℂ} (hcrit : a ∉ positiveCriticalOrbit c) :
    CriticalOrbitAvoidingTarget c a :=
  criticalOrbitAvoidingTarget_iff_not_mem_positiveCriticalOrbit.mpr hcrit

/-- Convert the q62 target predicate back to the standard positive-critical-orbit
avoidance vocabulary. -/
theorem not_mem_positiveCriticalOrbit_of_criticalOrbitAvoidingTarget
    {c a : ℂ} (hcrit : CriticalOrbitAvoidingTarget c a) :
    a ∉ positiveCriticalOrbit c :=
  criticalOrbitAvoidingTarget_iff_not_mem_positiveCriticalOrbit.mp hcrit

/-- Fixed-point selector in the positive-critical-orbit vocabulary. -/
theorem exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62
    (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ a : ℂ, quadratic c a = a ∧ a ∉ positiveCriticalOrbit c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget c hc
  exact ⟨a, hfix, not_mem_positiveCriticalOrbit_of_criticalOrbitAvoidingTarget hcrit⟩

/-- Support-form Brolin pullback using the standard not-postcritical target
vocabulary. -/
theorem locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    {c z₀ : ℂ} (hbase : LocOneSided c z₀)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c z₀)
    (hcrit : z₀ ∉ positiveCriticalOrbit c) :
    LocOneSidedDense c :=
  locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia hbase hsupp
    (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hcrit)

/-- Repelling-fixed connected-puncture bridge using the standard not-postcritical
target vocabulary. -/
theorem locOneSidedDense_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    {c a : ℂ} (hfix : quadratic c a = a) (hrep : 1 < ‖(2 : ℂ) * a‖)
    (hseed : ConnectedPunctureSeed c a)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c a)
    (hcrit : a ∉ positiveCriticalOrbit c) :
    LocOneSidedDense c :=
  locOneSidedDense_of_repelling_fixed_connectedPunctureSeed_limitingBrolinMeasureAtSupportsJulia
    hfix hrep hseed hsupp
    (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hcrit)

/-- Both-connected q62 support-form bridge using not-postcritical target
hypotheses instead of the q62-local `CriticalOrbitAvoidingTarget` predicate. -/
theorem q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ z₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : z₁ ∉ positiveCriticalOrbit c₁)
    (hbase₂ : LocOneSided c₂ z₂)
    (hsupp₂ : LimitingBrolinMeasureAtSupportsJulia c₂ z₂)
    (hcrit₂ : z₂ ∉ positiveCriticalOrbit c₂)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    hbase₁ hsupp₁ (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hcrit₁)
    hbase₂ hsupp₂ (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hcrit₂)
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Neighbourhood-cofinal support-form Brolin pullback using the standard
not-postcritical target vocabulary. -/
theorem locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    {c z₀ : ℂ} (hbase : OneSidedAtCofinalNbhd c z₀)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c z₀)
    (hcrit : z₀ ∉ positiveCriticalOrbit c) :
    LocOneSidedDense c :=
  locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia hbase hsupp
    (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hcrit)

/-- Fixed-point support-form pullback where the base one-sided input is stated
in the standard positive-critical-orbit vocabulary. -/
theorem locOneSidedDense_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    {c : ℂ} (hc : c ≠ 1 / 4)
    (hbase : ∀ a : ℂ, quadratic c a = a → a ∉ positiveCriticalOrbit c → LocOneSided c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c hc
  exact locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Fixed-point neighbourhood-cofinal support-form pullback where the base
one-sided input is stated in the standard positive-critical-orbit vocabulary. -/
theorem locOneSidedDense_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    {c : ℂ} (hc : c ≠ 1 / 4)
    (hbase : ∀ a : ℂ, quadratic c a = a →
      a ∉ positiveCriticalOrbit c → OneSidedAtCofinalNbhd c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c hc
  exact locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Both-connected q62 with fixed targets selected internally, accepting base
one-sidedness in the standard positive-critical-orbit vocabulary. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a → a ∉ positiveCriticalOrbit c₁ → LocOneSided c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a → a ∉ positiveCriticalOrbit c₂ → LocOneSided c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ :=
    exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c₁ hc₁quarter
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ :=
    exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c₂ hc₂quarter
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (hbase₁ z₁ hz₁fix hz₁crit) (hsupp₁ z₁ hz₁fix) hz₁crit
    (hbase₂ z₂ hz₂fix hz₂crit) (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

/-- Both-connected q62 with fixed targets selected internally and the base
one-sidedness supplied in neighbourhood-cofinal form, using the standard
positive-critical-orbit vocabulary. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ :=
    exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c₁ hc₁quarter
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ :=
    exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62 c₂ hc₂quarter
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix) hz₁crit
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₂ z₂ hz₂fix hz₂crit))
    (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

/-- Joint-frontier visibility version of the fixed-point neighbourhood-cofinal
capstone in the standard positive-critical-orbit vocabulary. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    hUo hUc hUne hUinf hne hc₁quarter hc₂quarter hc₁M hc₂M
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂ hbase₁ hsupp₁ hbase₂ hsupp₂
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₁₂)
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₂₁)
    hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Full q62 case split with the Brolin/not-postcritical bridge as the
both-connected branch.  Disconnected parameters still contribute the usual
Cantor-basin monodromy hypotheses; the connected-connected branch is discharged
by fixed-point Brolin support, neighbourhood-cofinal one-sidedness, joint-frontier
visibility, and smooth-piece rigidity. -/
theorem q62_phiMero_independence_of_monodromy_fixedPoint_cofinalNbhd_brolin_notPostcritical_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁quarter : c₁ ≠ 1 / 4) (hc₂quarter : c₂ ≠ 1 / 4)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine q62_phiMero_independence_conditional hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    (fun c => c ∉ mandelbrot) hmono₁ hmono₂ ?_ ?_ ?_
  · intro h₁M
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h₁M) hc₁0 hc₁m2 hU₁
  · intro h₂M
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h₂M) hc₂0 hc₂m2 hU₂
  · intro h₁M h₂M
    exact q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁quarter hc₂quarter
      (not_not.mp h₁M) (not_not.mp h₂M)
      hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- At the parabolic parameter `c = 1 / 4`, the critical orbit is real and
strictly below the fixed point `1 / 2` at every finite level. -/
theorem quarter_critical_orbit_real_lt_half (m : ℕ) :
    ∃ x : ℝ, (quadratic (1 / 4 : ℂ))^[m] (0 : ℂ) = (x : ℂ) ∧
      0 ≤ x ∧ x < 1 / 2 := by
  induction m with
  | zero =>
      refine ⟨0, ?_, by norm_num, by norm_num⟩
      simp
  | succ m ih =>
      obtain ⟨x, hxeq, hx0, hxlt⟩ := ih
      refine ⟨x ^ 2 + 1 / 4, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        rw [hxeq]
        norm_num [quadratic]
      · nlinarith [sq_nonneg x]
      · nlinarith [sq_nonneg (x - 1 / 2)]

/-- The parabolic fixed point at `c = 1 / 4` avoids the positive critical
orbit. -/
theorem criticalOrbitAvoidingTarget_quarter_half :
    CriticalOrbitAvoidingTarget (1 / 4 : ℂ) (1 / 2 : ℂ) := by
  intro m _hm hhit
  obtain ⟨x, hxeq, _hx0, hxlt⟩ := quarter_critical_orbit_real_lt_half m
  have hxhalfC : (x : ℂ) = (1 / 2 : ℂ) := by
    rw [← hxeq]
    exact hhit
  have hxhalfC' : (x : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    simpa using hxhalfC
  have hxhalf : x = 1 / 2 := Complex.ofReal_injective hxhalfC'
  nlinarith

/-- The parabolic fixed point at `c = 1 / 4`. -/
theorem fixed_quarter_half : quadratic (1 / 4 : ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  norm_num [quadratic]

/-- Every quadratic parameter has a fixed point avoiding the positive critical
orbit, in the q62-local target-avoidance form.  The non-parabolic case uses the
two-distinct-fixed-points selector; `c = 1 / 4` is supplied by the explicit
parabolic fixed point `1 / 2`. -/
theorem exists_fixed_point_criticalOrbitAvoidingTarget_all (c : ℂ) :
    ∃ α : ℂ, quadratic c α = α ∧ CriticalOrbitAvoidingTarget c α := by
  by_cases hc : c = 1 / 4
  · subst c
    exact ⟨1 / 2, fixed_quarter_half, criticalOrbitAvoidingTarget_quarter_half⟩
  · exact exists_fixed_point_criticalOrbitAvoidingTarget c hc

/-- Every quadratic parameter has a fixed point outside the positive critical
orbit, in the standard selector vocabulary. -/
theorem exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all (c : ℂ) :
    ∃ a : ℂ, quadratic c a = a ∧ a ∉ positiveCriticalOrbit c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c
  exact ⟨a, hfix, not_mem_positiveCriticalOrbit_of_criticalOrbitAvoidingTarget hcrit⟩

/-- Both-connected q62 with fixed targets selected internally, without excluding
`c = 1 / 4`.  The parabolic parameter uses the explicit fixed target `1 / 2`;
all other parameters use the two-fixed-point selector. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c₁
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c₂
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix) hz₁crit
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₂ z₂ hz₂fix hz₂crit))
    (hsupp₂ z₂ hz₂fix) hz₂crit
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₁₂)
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis₂₁)
    hrig₁₂ hrig₂₁

/-- Full q62 case split with the Brolin/not-postcritical bridge as the
both-connected branch, with no parabolic fixed-point exclusion. -/
theorem q62_phiMero_independence_of_monodromy_fixedPoint_cofinalNbhd_brolin_notPostcritical_jointFrontierVisibility_all
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine q62_phiMero_independence_conditional hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    (fun c => c ∉ mandelbrot) hmono₁ hmono₂ ?_ ?_ ?_
  · intro h₁M
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h₁M) hc₁0 hc₁m2 hU₁
  · intro h₂M
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h₂M) hc₂0 hc₂m2 hU₂
  · intro h₁M h₂M
    exact q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_jointFrontierVisibility
      hUo hUc hUne hUinf hne (not_not.mp h₁M) (not_not.mp h₂M)
      hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Fixed-point version of the Brolin backward-orbit bridge with no parabolic
exception: the target fixed point is selected internally. -/
theorem exists_fixedPoint_backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia_all
    {c : ℂ}
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c
  exact ⟨a, hfix,
    backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia (hsupp a hfix) hcrit⟩

/-- Fixed-point local one-sided density from Brolin support, with no parabolic
exception. -/
theorem locOneSidedDense_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia_all
    {c : ℂ}
    (hbase : ∀ a : ℂ, quadratic c a = a →
      CriticalOrbitAvoidingTarget c a → LocOneSided c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c
  exact locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Fixed-point neighbourhood-cofinal local one-sided density from Brolin
support, with no parabolic exception. -/
theorem locOneSidedDense_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all
    {c : ℂ}
    (hbase : ∀ a : ℂ, quadratic c a = a →
      CriticalOrbitAvoidingTarget c a → OneSidedAtCofinalNbhd c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c
  exact locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Both-connected q62 with fixed targets selected internally, no parabolic
exception, and base one-sidedness supplied in q62-local critical-orbit form. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      CriticalOrbitAvoidingTarget c₁ a → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      CriticalOrbitAvoidingTarget c₂ a → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c₁
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ := exists_fixed_point_criticalOrbitAvoidingTarget_all c₂
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix) hz₁crit
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₂ z₂ hz₂fix hz₂crit))
    (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

/-- Fixed-point local one-sided density from Brolin support in the standard
positive-critical-orbit vocabulary, with no parabolic exception. -/
theorem locOneSidedDense_of_fixedPoint_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical
    {c : ℂ}
    (hbase : ∀ a : ℂ, quadratic c a = a → a ∉ positiveCriticalOrbit c → LocOneSided c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c
  exact locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Fixed-point neighbourhood-cofinal local one-sided density from Brolin
support in the standard positive-critical-orbit vocabulary, with no parabolic
exception. -/
theorem locOneSidedDense_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical
    {c : ℂ}
    (hbase : ∀ a : ℂ, quadratic c a = a →
      a ∉ positiveCriticalOrbit c → OneSidedAtCofinalNbhd c a)
    (hsupp : ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a) :
    LocOneSidedDense c := by
  obtain ⟨a, hfix, hcrit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c
  exact locOneSidedDense_of_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical
    (hbase a hfix hcrit) (hsupp a hfix) hcrit

/-- Both-connected q62 with fixed targets selected internally, no parabolic
exception, and base one-sidedness supplied in the standard not-postcritical
vocabulary. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c₁
  obtain ⟨z₂, hz₂fix, hz₂crit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c₂
  exact q62_phiMero_bothconnected_of_base_limitingBrolinMeasureAtSupportsJulia_notPostcritical_visibility
    hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix) hz₁crit
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₂ z₂ hz₂fix hz₂crit))
    (hsupp₂ z₂ hz₂fix) hz₂crit
    hvis₁₂ hvis₂₁ hrig₁₂ hrig₂₁

end

end Bottcher

namespace Bottcher

noncomputable section

/-- If the filled Julia set has empty interior, then every filled-Julia point is
on the Julia frontier. -/
theorem filledJulia_subset_frontier_of_emptyInterior
    {c : ℂ} (hempty : interior (filledJulia c) = ∅) :
    filledJulia c ⊆ frontier (filledJulia c) := by
  intro z hzK
  rw [(isClosed_filledJulia c).frontier_eq]
  exact ⟨hzK, by rw [hempty]; simp⟩

/-- In the empty-interior case, the q62 Brolin support theorem identifies the
selected arbitrary-target limiting Brolin support exactly with the Julia
frontier. -/
theorem limitingBrolinMeasureAt_support_eq_frontier_of_limitingBrolinMeasureAtSupportsJulia_emptyInterior
    {c a : ℂ} (hempty : interior (filledJulia c) = ∅)
    (hsupp : LimitingBrolinMeasureAtSupportsJulia c a) :
    (limitingBrolinMeasureAt c a).support = frontier (filledJulia c) := by
  apply subset_antisymm
  · exact (limitingBrolinMeasureAt_support_subset_filledJulia_for_q62 c a).trans
      (filledJulia_subset_frontier_of_emptyInterior hempty)
  · exact hsupp

/-- Empty-interior support equality from the ball-positivity residue. -/
theorem limitingBrolinMeasureAt_support_eq_frontier_of_brolinJuliaBallPositiveAt_emptyInterior
    {c a : ℂ} (hempty : interior (filledJulia c) = ∅)
    (hpos : BrolinJuliaBallPositiveAt c a) :
    (limitingBrolinMeasureAt c a).support = frontier (filledJulia c) :=
  limitingBrolinMeasureAt_support_eq_frontier_of_limitingBrolinMeasureAtSupportsJulia_emptyInterior
    hempty (limitingBrolinMeasureAtSupportsJulia_of_brolinJuliaBallPositiveAt hpos)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- One-sided neighbourhood-cofinal density on `∂K₁` produces an off-`K₂`
witness as soon as some point of `∂K₁` is already outside `K₂`. -/
theorem exists_oneSidedCofinalNbhd_offOther_of_dense_frontier_offOther
    {c₁ c₂ : ℂ} (hd : OneSidedAtCofinalNbhdDense c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂) :
    ∃ x, OneSidedAtCofinalNbhd c₁ x ∧ x ∉ filledJulia c₂ := by
  obtain ⟨p, hpfront, hp2⟩ := hoff
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hp2
  obtain ⟨x, hx, hdist⟩ := hd p hpfront δ hδ
  refine ⟨x, hx, ?_⟩
  exact hδsub (by simpa [Metric.mem_ball, dist_comm] using hdist)

/-- The asymmetric exposure bridge: one dense neighbourhood-cofinal side plus a
known frontier point off the other filled Julia set is enough, provided the
resulting off-other one-sided witnesses are visible from infinity. -/
theorem exposedOneSidedCofinalNbhd_of_dense_frontier_offOther_visible
    {c₁ c₂ : ℂ} (hd : OneSidedAtCofinalNbhdDense c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdVisible c₁ c₂) :
    ExposedOneSidedCofinalNbhd c₁ c₂ := by
  obtain ⟨x, hx, hx2⟩ := exists_oneSidedCofinalNbhd_offOther_of_dense_frontier_offOther hd hoff
  exact ⟨x, hx, hx2, hvis x hx hx2⟩

/-- Asymmetric Brolin support bridge to an exposed one-sided point: only the
`c₁` Brolin/local-one-sided side is used once a `∂K₁ \ K₂` point is supplied. -/
theorem exposedOneSidedCofinalNbhd_of_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visible
    {c₁ c₂ z₁ : ℂ}
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdVisible c₁ c₂) :
    ExposedOneSidedCofinalNbhd c₁ c₂ :=
  exposedOneSidedCofinalNbhd_of_dense_frontier_offOther_visible
    (oneSidedAtCofinalNbhdDense_of_locOneSidedDense
      (locOneSidedDense_of_base_limitingBrolinMeasureAtSupportsJulia hbase₁ hsupp₁ hcrit₁))
    hoff hvis

/-- Asymmetric both-connected q62: a single Brolin-supported local base on
`c₁`, plus a known point of `∂K₁` outside `K₂`, supplies the exposed one-sided
input directly.  No density/support hypothesis on `c₂` is needed. -/
theorem q62_phiMero_bothconnected_of_oneSide_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdVisible c₁ c₂)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_phiMero_independence_of_exposed_oneSidedCofinalNbhd hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hc₁0 hc₁m2 hc₂0 hc₂m2
    (fun h => absurd hc₁M h) (fun h => absurd hc₂M h)
    (fun _ _ =>
      exposedOneSidedCofinalNbhd_of_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visible
        hbase₁ hsupp₁ hcrit₁ hoff hvis)
    (fun _ _ => hrig₁₂)

/-- Asymmetric fixed-target q62 support bridge in the standard not-postcritical
vocabulary, with the fixed target selected internally and no parabolic
exception. -/
theorem q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_visibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdVisible c₁ c₂)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨z₁, hz₁fix, hz₁crit⟩ := exists_fixed_point_not_mem_positiveCriticalOrbit_for_q62_all c₁
  exact q62_phiMero_bothconnected_of_oneSide_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visibility
    hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (locOneSided_of_oneSidedAtCofinalNbhd (hbase₁ z₁ hz₁fix hz₁crit))
    (hsupp₁ z₁ hz₁fix)
    (criticalOrbitAvoidingTarget_of_not_mem_positiveCriticalOrbit hz₁crit)
    hoff hvis hrig₁₂

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Asymmetric exposure bridge using joint-frontier visibility. -/
theorem exposedOneSidedCofinalNbhd_of_dense_frontier_offOther_jointFrontierVisible
    {c₁ c₂ : ℂ} (hd : OneSidedAtCofinalNbhdDense c₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    ExposedOneSidedCofinalNbhd c₁ c₂ :=
  exposedOneSidedCofinalNbhd_of_dense_frontier_offOther_visible hd hoff
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis)

/-- Asymmetric Brolin support bridge to exposure using joint-frontier visibility. -/
theorem exposedOneSidedCofinalNbhd_of_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_jointFrontierVisible
    {c₁ c₂ z₁ : ℂ}
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    ExposedOneSidedCofinalNbhd c₁ c₂ :=
  exposedOneSidedCofinalNbhd_of_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visible
    hbase₁ hsupp₁ hcrit₁ hoff
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis)

/-- Asymmetric both-connected q62 with one Brolin-supported side, using
joint-frontier visibility. -/
theorem q62_phiMero_bothconnected_of_oneSide_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ z₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : LocOneSided c₁ z₁)
    (hsupp₁ : LimitingBrolinMeasureAtSupportsJulia c₁ z₁)
    (hcrit₁ : CriticalOrbitAvoidingTarget c₁ z₁)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  q62_phiMero_bothconnected_of_oneSide_base_limitingBrolinMeasureAtSupportsJulia_frontier_offOther_visibility
    hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    hbase₁ hsupp₁ hcrit₁ hoff
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis) hrig₁₂

/-- Asymmetric fixed-target q62 support bridge using joint-frontier visibility,
with the target selected internally and no parabolic exception. -/
theorem q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_visibility
    hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    hbase₁ hsupp₁ hoff
    (offOtherCofinalNbhdVisible_of_jointFrontierVisible hvis) hrig₁₂

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Both-connected q62 from the asymmetric Brolin bridge plus the intrinsic
frontier-off-other dichotomy for distinct parameters.  After the point-set
separation chooses an orientation, only the Brolin-supported side in that
orientation is used. -/
theorem q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontierOffDichotomy_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁)
    (hrig₁₂ : SmoothPieceRigidity c₁ c₂)
    (hrig₂₁ : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  rcases exists_frontier_filledJulia_off_other hne with hoff₁₂ | hoff₂₁
  · exact
      q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_jointFrontierVisibility
        hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
        hbase₁ hsupp₁ hoff₁₂ hvis₁₂ hrig₁₂
  · exact noRelation_symm
      (q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_jointFrontierVisibility
        hUo hUc hUne hUinf hc₂M hc₁M hc₂0 hc₂m2 hc₁0 hc₁m2 hU₂ hU₁
        hbase₂ hsupp₂ hoff₂₁ hvis₂₁ hrig₂₁)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Asymmetric fixed-target q62 support bridge with the smooth-piece gatekeeper
fed by `SmoothArcSelection` on the exposed side. -/
theorem q62_phiMero_oneSide_brolin_frontierOff_smoothArcSelection_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hsel₁ : SmoothArcSelection c₁)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hoff : ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂)
    (hvis : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    q62_phiMero_bothconnected_of_oneSide_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontier_offOther_jointFrontierVisibility
      hUo hUc hUne hUinf hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hbase₁ hsupp₁ hoff hvis
      (smoothPieceRigidity_of_smoothArcSelection hc₁M hc₁0 hc₁m2 hconn₁ hsel₁)

/-- Distinct-parameter both-connected q62 from fixed-target Brolin support,
frontier separation, joint-frontier visibility, and the z-space smooth-arc
selection datum in both possible orientations. -/
theorem q62_phiMero_bothconnected_brolin_frontierOffDichotomy_smoothArcSelection_jointFrontierVisibility
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁m2 : c₁ ≠ -2)
    (hc₂0 : c₂ ≠ 0) (hc₂m2 : c₂ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hsel₁ : SmoothArcSelection c₁)
    (hconn₂ : IsPreconnected (filledJulia c₂))
    (hsel₂ : SmoothArcSelection c₂)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hbase₁ : ∀ a : ℂ, quadratic c₁ a = a →
      a ∉ positiveCriticalOrbit c₁ → OneSidedAtCofinalNbhd c₁ a)
    (hsupp₁ : ∀ a : ℂ, quadratic c₁ a = a → LimitingBrolinMeasureAtSupportsJulia c₁ a)
    (hbase₂ : ∀ a : ℂ, quadratic c₂ a = a →
      a ∉ positiveCriticalOrbit c₂ → OneSidedAtCofinalNbhd c₂ a)
    (hsupp₂ : ∀ a : ℂ, quadratic c₂ a = a → LimitingBrolinMeasureAtSupportsJulia c₂ a)
    (hvis₁₂ : OffOtherCofinalNbhdJointFrontierVisible c₁ c₂)
    (hvis₂₁ : OffOtherCofinalNbhdJointFrontierVisible c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    q62_phiMero_bothconnected_of_fixedPoint_cofinalNbhd_base_limitingBrolinMeasureAtSupportsJulia_all_notPostcritical_frontierOffDichotomy_jointFrontierVisibility
      hUo hUc hUne hUinf hne hc₁M hc₂M hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
      hbase₁ hsupp₁ hbase₂ hsupp₂ hvis₁₂ hvis₂₁
      (smoothPieceRigidity_of_smoothArcSelection hc₁M hc₁0 hc₁m2 hconn₁ hsel₁)
      (smoothPieceRigidity_of_smoothArcSelection hc₂M hc₂0 hc₂m2 hconn₂ hsel₂)

end

end Bottcher
