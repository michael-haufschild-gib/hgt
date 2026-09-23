import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread

/-!
# Cofinal positive schedules do not carry the shifted-Xi obstruction

Every fixed shifted-Xi Hankel block becomes positive sufficiently far to the right.  Choosing one
threshold at each degree produces an actual cofinal mass--degree schedule of positive blocks, even
above an arbitrary prescribed lower escape floor.  Along that unconditional schedule the existing
projective law forces divergent Gauss-root spread, and the arithmetic surplus has its harmonic
lower bound.

Consequently cofinal positivity, divergent projective spread, and harmonic source work are jointly
far-right recession data; none can by itself detect RH.  The missing datum is an *upper* rate on
the selected masses, such as the parabolic restriction `w = O(n)`.  A delayed-switch family closes
the logical no-go: pointwise eventual positivity in every fixed degree gives no information on any
prescribed diagonal schedule.
-/

open Filter Matrix Topology

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- A hostile family whose fixed-degree limits are positive but whose prescribed diagonal is
strictly negative.  It isolates the order-of-limits obstruction without any analytic baggage. -/
def delayedPositiveSwitch (v : ℕ → ℝ) (w : ℝ) (n : ℕ) : ℝ :=
  if w ≤ v n then -1 else 1

/-- Every fixed coordinate of the delayed-switch family converges to the positive limit `1`. -/
theorem tendsto_delayedPositiveSwitch_one (v : ℕ → ℝ) (n : ℕ) :
    Tendsto (fun w : ℝ => delayedPositiveSwitch v w n) atTop (nhds 1) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (v n)] with w hw
  simp [delayedPositiveSwitch, not_le.mpr hw]

/-- Nevertheless every point of the prescribed diagonal is strictly negative. -/
theorem delayedPositiveSwitch_diagonal_neg (v : ℕ → ℝ) (n : ℕ) :
    delayedPositiveSwitch v (v n) n < 0 := by
  simp [delayedPositiveSwitch]

/-- **Closed order-of-limits countermodel.**  Every fixed degree eventually sees the positive
limit, while the degree-matched diagonal remains strictly negative at every grade. -/
theorem fixedDegreePositiveLimit_negative_degreeDiagonal :
    (∀ n : ℕ, Tendsto
      (fun w : ℝ => delayedPositiveSwitch (fun k => (k : ℝ)) w n)
      atTop (nhds 1)) ∧
    (∀ n : ℕ, delayedPositiveSwitch (fun k => (k : ℝ)) (n : ℝ) n < 0) := by
  constructor
  · exact fun n => tendsto_delayedPositiveSwitch_one (fun k => (k : ℝ)) n
  · exact fun n => delayedPositiveSwitch_diagonal_neg (fun k => (k : ℝ)) n

/-- **Unconditional mass--grade synchronization above an arbitrary lower floor.**  For every
real-valued escape floor `g`, there is an actual shifted-Xi mass schedule above both `g(n)` and
degree `n`, tending to infinity, whose degree-`n+2` moment block is positive definite.  Its
projective Gauss-root spread diverges. -/
theorem exists_xiShiftedCofinalPositiveProjectiveSchedule_above
    (g : ℕ → ℝ) :
    ∃ w : ℕ → ℝ,
      (∀ n : ℕ, max (n : ℝ) (g n) ≤ w n) ∧
      Tendsto w atTop atTop ∧
      (∀ n, (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (w n)) (n + 2)).PosDef) ∧
      Tendsto (fun n => projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w n)) n) atTop atTop := by
  have hthreshold : ∀ n : ℕ, ∃ W : ℝ, ∀ w ≥ W,
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 2)).PosDef := by
    intro n
    obtain ⟨W, hW⟩ := eventually_atTop.1
      (xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2))
    refine ⟨W, ?_⟩
    intro w hw
    have hblock := hW w hw
    have heq : HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 2) =
        xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2) := by
      ext i j
      rfl
    rwa [heq]
  choose W hW using hthreshold
  let w : ℕ → ℝ := fun n => max (max (n : ℝ) (g n)) (W n)
  have hfloor (n : ℕ) : max (n : ℝ) (g n) ≤ w n := by
    exact le_max_left _ _
  have hnat (n : ℕ) : (n : ℝ) ≤ w n :=
    le_trans (le_max_left _ _) (hfloor n)
  have hwtop : Tendsto w atTop atTop :=
    tendsto_atTop_mono hnat tendsto_natCast_atTop_atTop
  have hpos (n : ℕ) : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w n)) (n + 2)).PosDef := by
    apply hW n
    exact le_max_right _ _
  have hspread : Tendsto (fun n => projectiveGaussRootSpread
      (xiShiftedFarRightNormalizedMoment (w n)) n) atTop atTop := by
    exact tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
      w (fun n => n) hwtop tendsto_id hpos
  exact ⟨w, hfloor, hwtop, hpos, hspread⟩

/-- **Arbitrary-clock growth no-go.**  Given any mass floor and any requested projective-spread
floor in an external observation clock, an unconditional cofinal schedule of actual positive
shifted-Xi blocks beats both.  The degree clock is reindexed cofinally; therefore a spread rate
has RH content only after an intrinsic upper synchronization between mass, degree, and clock. -/
theorem exists_xiShiftedCofinalPositiveProjectiveSchedule_above_spreadFloor
    (g h : ℕ → ℝ) :
    ∃ w : ℕ → ℝ, ∃ n : ℕ → ℕ,
      Tendsto w atTop atTop ∧
      Tendsto n atTop atTop ∧
      (∀ l, g l ≤ w l) ∧
      (∀ l, h l < projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w l)) (n l)) ∧
      (∀ l, (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef) := by
  obtain ⟨w₀, _, hw₀top, hpos₀, hspread₀⟩ :=
    exists_xiShiftedCofinalPositiveProjectiveSchedule_above (fun _ => 0)
  have hmassThreshold : ∀ l : ℕ, ∃ N : ℕ, ∀ k ≥ N, g l ≤ w₀ k := by
    intro l
    exact eventually_atTop.1 ((tendsto_atTop.1 hw₀top) (g l))
  have hspreadThreshold : ∀ l : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      h l + 1 ≤ projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w₀ k)) k := by
    intro l
    exact eventually_atTop.1 ((tendsto_atTop.1 hspread₀) (h l + 1))
  choose M hM using hmassThreshold
  choose S hS using hspreadThreshold
  let n : ℕ → ℕ := fun l => max l (max (M l) (S l))
  let w : ℕ → ℝ := fun l => w₀ (n l)
  have hln (l : ℕ) : l ≤ n l := le_max_left _ _
  have hntop : Tendsto n atTop atTop :=
    tendsto_atTop_mono hln tendsto_id
  have hwtop : Tendsto w atTop atTop := hw₀top.comp hntop
  have hfloor (l : ℕ) : g l ≤ w l := by
    apply hM l
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hspreadFloor (l : ℕ) : h l < projectiveGaussRootSpread
      (xiShiftedFarRightNormalizedMoment (w l)) (n l) := by
    have hSn : S l ≤ n l :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_lt_of_le (by linarith : h l < h l + 1) (hS l (n l) hSn)
  have hpos (l : ℕ) : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef := by
    exact hpos₀ (n l)
  exact ⟨w, n, hwtop, hntop, hfloor, hspreadFloor, hpos⟩

/-- **Closed cofinal-recession no-go.**  Unconditionally, one actual shifted-Xi schedule has all
degree-matched blocks positive, divergent projective spread, and the harmonic lower bound for the
literal projective arithmetic surplus at every degree at least two. -/
theorem exists_xiShiftedCofinalPositiveSchedule_spread_and_harmonicWork :
    ∃ w : ℕ → ℝ,
      Tendsto w atTop atTop ∧
      (∀ n, (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (w n)) (n + 2)).PosDef) ∧
      Tendsto (fun n => projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w n)) n) atTop atTop ∧
      ∀ n, 2 ≤ n →
        dimensionlessProjectiveArithmeticSurplus (w n) n ≥
          1 / (2 * (2 * n + 1 : ℝ)) *
            dimensionlessCumulativeJacobiFlux (w n) n ^ (2 : ℕ) := by
  obtain ⟨W, hW⟩ := exists_uniform_lowEdgeAnchor_half
  obtain ⟨w, hfloor, hwtop, hpos, hspread⟩ :=
    exists_xiShiftedCofinalPositiveProjectiveSchedule_above (fun _ => W)
  refine ⟨w, hwtop, hpos, hspread, ?_⟩
  intro n hn
  have hWn : W ≤ w n := le_trans (le_max_right _ _) (hfloor n)
  have hnle : (n : ℝ) ≤ w n := le_trans (le_max_left _ _) (hfloor n)
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hw1 : 1 < w n := lt_of_lt_of_le hn1 hnle
  have hnormalized : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment (w n)) (n + 2)).PosDef := by
    have := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual
      hw1 (n + 2) (hpos n)
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using this
  exact dimensionlessProjectiveArithmeticSurplus_ge_harmonic
    hw1 hn hnormalized (hW (w n) hWn)

end
end XiShiftedCanonicalAdmission
end RHTower
