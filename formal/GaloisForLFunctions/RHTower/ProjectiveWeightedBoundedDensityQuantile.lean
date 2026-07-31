import GaloisForLFunctions.RHTower.ProjectiveWeightedHaarQuantileActiveSupport

/-!
# Bounded-density projective recurrence quantiles

Haar phase packets are not required for the finite-dimensional
early-recurrence estimate.  It is enough that the phase law be dominated by
a finite multiple of Haar measure.

This file proves:

* coordinatewise nonzero integer powers preserve Haar domination;
* Haar domination transfers directly to real set-measure bounds;
* the canonical weighted early-hit estimate acquires exactly the domination
  factor and no other loss.

The last theorem applies to correlated phase packets as well as independent
ones.  Independence is needed only when a concrete model is used to derive
the finite-head domination factor.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A law on a finite torus dominated by `B` times Haar remains so after any
nonzero coordinatewise integer power map. -/
theorem map_zsmul_le_smul_volume_of_le
    {d : ℕ} (μ : Measure (Fin d → UnitAddCircle)) (B : ENNReal)
    (hμ : μ ≤ B • volume) (n : ℤ) (hn : n ≠ 0) :
    Measure.map (fun z : Fin d → UnitAddCircle => n • z) μ ≤
      B • volume := by
  have hpow := Measure.measurePreserving_zsmul
    (G := Fin d → UnitAddCircle) volume hn
  calc
    Measure.map (fun z : Fin d → UnitAddCircle => n • z) μ ≤
        Measure.map (fun z : Fin d → UnitAddCircle => n • z)
          (B • volume) :=
      Measure.map_mono hμ hpow.measurable
    _ = B • Measure.map (fun z : Fin d → UnitAddCircle => n • z)
          volume := Measure.map_smul B volume _
    _ = B • volume := by rw [hpow.map_eq]

/-- A finite Haar-domination bound transfers to the corresponding real
set-measure bound. -/
theorem measureReal_le_nnreal_mul_volumeReal_of_le
    {d : ℕ} (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) (s : Set (Fin d → UnitAddCircle)) :
    μ.real s ≤ (B : ℝ) * volume.real s := by
  calc
    μ.real s ≤ (B • volume).real s :=
      ENNReal.toReal_mono (by finiteness) (hμ s)
    _ = (B : ℝ) * volume.real s :=
      measureReal_nnreal_smul_apply B

/-- **Bounded-density early-recurrence quantile.**  If a finite phase law is
dominated by `B` times product Haar, then the probability of hitting the
weighted projective target during the first `N` clocks is bounded by `B`
times the exact canonical Haar water budget. -/
theorem
    measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η : ℝ} (hη1 : η ≤ 1)
    (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) :
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (B : ℝ) *
        ((N : ℝ) * projectiveCanonicalHaarWaterBudget w η) := by
  calc
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
        (B : ℝ) * volume.real
          (torusProjectiveWeightedCoherenceHitUnion w N η) :=
      measureReal_le_nnreal_mul_volumeReal_of_le μ B hμ _
    _ ≤ (B : ℝ) *
        ((N : ℝ) * projectiveCanonicalHaarWaterBudget w η) :=
      mul_le_mul_of_nonneg_left
        (measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le
          w hw hmass N hη1)
        B.2

/-! ## Arbitrary water-level bounds -/

/-- Fixed, not necessarily canonical, water-level target budget. This is
the scale needed when a countable packet is reduced to a normalized finite
head and the water level is chosen from the original unnormalized weights. -/
def projectiveFixedHaarWaterBudget {d : ℕ}
    (w : Fin d → ℝ) (η lam : ℝ) : ℝ :=
  ∑ k, Real.exp (
    (Real.pi / 4) * (lam * η) -
      projectiveWaterEntropyAt w k lam)

/-- The weighted coherence target obeys the water-entropy estimate at every
positive prescribed water level, not only at its canonical optimizer. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_fixedWater_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η lam : ℝ} (hη1 : η ≤ 1) (hlam : 0 < lam) :
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
      projectiveFixedHaarWaterBudget w η lam := by
  have hbase := measureReal_torusProjectiveWeightedCoherenceTarget_le
    w hw hmass hη1 (fun _k ↦ (Real.pi / 16) * lam)
    (fun _k ↦ mul_pos (by positivity) hlam)
  have hterm : ∀ k : Fin d,
      Real.exp (4 * ((Real.pi / 16) * lam) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam * w j)) ≤
        Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveWaterEntropyAt w k lam) := by
    intro k
    have hprod := prod_circleChordExponentialMoment_waterEnvelope
      w k (hw := hw) hlam
    calc
      Real.exp (4 * ((Real.pi / 16) * lam) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam * w j)) ≤
          Real.exp (4 * ((Real.pi / 16) * lam) * η) *
            Real.exp (-projectiveWaterEntropyAt w k lam) := by
        exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveWaterEntropyAt w k lam) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
        ∑ k, Real.exp (4 * ((Real.pi / 16) * lam) * η) *
          ∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam * w j) := hbase
    _ ≤ ∑ k, Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveWaterEntropyAt w k lam) :=
      Finset.sum_le_sum fun k _hk ↦ hterm k
    _ = projectiveFixedHaarWaterBudget w η lam := rfl

/-- The fixed-water target estimate propagated through the first `N`
positive integer clocks. -/
theorem measureReal_torusProjectiveWeightedCoherenceHitUnion_fixedWater_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η lam : ℝ} (hη1 : η ≤ 1) (hlam : 0 < lam) :
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (N : ℝ) * projectiveFixedHaarWaterBudget w η lam := by
  exact (measureReal_torusProjectiveWeightedCoherenceHitUnion_le w N η).trans
    (mul_le_mul_of_nonneg_left
      (measureReal_torusProjectiveWeightedCoherenceTarget_fixedWater_le
        w hw hmass hη1 hlam)
      (Nat.cast_nonneg N))

/-- Bounded-density early-hit estimate at an arbitrary positive water level.
The phase law may be correlated; only finite-dimensional Haar domination is
used. -/
theorem
    measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_fixedWater_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η lam : ℝ} (hη1 : η ≤ 1) (hlam : 0 < lam)
    (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) :
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (B : ℝ) *
        ((N : ℝ) * projectiveFixedHaarWaterBudget w η lam) := by
  calc
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
        (B : ℝ) * volume.real
          (torusProjectiveWeightedCoherenceHitUnion w N η) :=
      measureReal_le_nnreal_mul_volumeReal_of_le μ B hμ _
    _ ≤ (B : ℝ) *
        ((N : ℝ) * projectiveFixedHaarWaterBudget w η lam) :=
      mul_le_mul_of_nonneg_left
        (measureReal_torusProjectiveWeightedCoherenceHitUnion_fixedWater_le
          w hw hmass N hη1 hlam)
        B.2

/-- Full fixed-level water entropy before deleting a projective pivot. -/
def projectiveFullWaterEntropyAt {d : ℕ}
    (w : Fin d → ℝ) (lam : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, Real.log (max 1 (lam * w j))

/-- Projective water entropy is full water entropy minus the deleted pivot
coordinate. -/
theorem projectiveWaterEntropyAt_eq_full_sub_pivot
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (lam : ℝ) :
    projectiveWaterEntropyAt w k lam =
      projectiveFullWaterEntropyAt w lam -
        (1 / 2 : ℝ) * Real.log (max 1 (lam * w k)) := by
  rw [projectiveWaterEntropyAt, projectiveFullWaterEntropyAt]
  have hsum :
      (∑ j, if j = k then 0 else
          Real.log (max 1 (lam * w j))) =
        (∑ j, Real.log (max 1 (lam * w j))) -
          Real.log (max 1 (lam * w k)) := by
    calc
      (∑ j, if j = k then 0 else
          Real.log (max 1 (lam * w j))) =
          ∑ j, (Real.log (max 1 (lam * w j)) -
            if j = k then Real.log (max 1 (lam * w j)) else 0) := by
              apply Finset.sum_congr rfl
              intro j _hj
              by_cases hj : j = k <;> simp [hj]
      _ = (∑ j, Real.log (max 1 (lam * w j))) -
          ∑ j, (if j = k then
            Real.log (max 1 (lam * w j)) else 0) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ j, Real.log (max 1 (lam * w j))) -
          Real.log (max 1 (lam * w k)) := by simp
  rw [hsum]
  ring

/-- If every normalized coordinate is at most one, deleting one pivot costs
at most one half-logarithmic water scale. -/
theorem pivotWaterCost_le_log
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {lam : ℝ} (hlam : 1 ≤ lam)
    (hw1 : w k ≤ 1) :
    Real.log (max 1 (lam * w k)) ≤ Real.log lam := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hmul : lam * w k ≤ lam := by
    nlinarith
  have hmax : max 1 (lam * w k) ≤ lam :=
    max_le hlam hmul
  exact Real.log_le_log (by positivity) hmax

/-- The arbitrary-water budget is controlled by full water entropy, with
the exact worst-pivot half-logarithmic loss. -/
theorem projectiveFixedHaarWaterBudget_le_fullEntropy
    {d : ℕ} (w : Fin d → ℝ)
    (hw1 : ∀ k, w k ≤ 1)
    (η : ℝ) {lam : ℝ} (hlam : 1 ≤ lam) :
    projectiveFixedHaarWaterBudget w η lam ≤
      (d : ℝ) * Real.exp (
        (Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam) := by
  rw [projectiveFixedHaarWaterBudget]
  have hterm : ∀ k : Fin d,
      Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveWaterEntropyAt w k lam) ≤
        Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam) := by
    intro k
    apply Real.exp_le_exp.mpr
    rw [projectiveWaterEntropyAt_eq_full_sub_pivot]
    have hpivot :=
      pivotWaterCost_le_log w k hlam (hw1 k)
    linarith
  calc
    (∑ k, Real.exp ((Real.pi / 4) * (lam * η) -
        projectiveWaterEntropyAt w k lam)) ≤
        ∑ _k : Fin d, Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam) :=
      Finset.sum_le_sum fun k _hk ↦ hterm k
    _ = (d : ℝ) * Real.exp ((Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam) := by
      simp [nsmul_eq_mul]

/--
Sharp finite-head early-hit bound. The exponent retains the full prescribed
water entropy; the only projective loss is one half-logarithmic pivot scale.
-/
theorem
    measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_fullEntropy_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hmass : ∑ i, w i = 1)
    (N : ℕ) {η lam : ℝ} (hη1 : η ≤ 1) (hlam : 1 ≤ lam)
    (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) :
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (B : ℝ) * ((N : ℝ) * ((d : ℝ) * Real.exp (
        (Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam))) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  calc
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (B : ℝ) *
        ((N : ℝ) * projectiveFixedHaarWaterBudget w η lam) :=
      measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_fixedWater_le
        w hw0 hmass N hη1 hlam0 μ B hμ
    _ ≤ (B : ℝ) * ((N : ℝ) * ((d : ℝ) * Real.exp (
        (Real.pi / 4) * (lam * η) -
          projectiveFullWaterEntropyAt w lam +
          (1 / 2 : ℝ) * Real.log lam))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (projectiveFixedHaarWaterBudget_le_fullEntropy
            w hw1 η hlam)
          (Nat.cast_nonneg N))
        B.2

end RHTower
