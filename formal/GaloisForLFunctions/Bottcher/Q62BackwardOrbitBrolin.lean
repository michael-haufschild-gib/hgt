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
import GaloisForLFunctions.Bottcher.Brolin.TargetLimit

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
