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
