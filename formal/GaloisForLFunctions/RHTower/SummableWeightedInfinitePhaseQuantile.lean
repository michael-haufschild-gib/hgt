import GaloisForLFunctions.RHTower.SummableWeightedHeadReduction

/-!
# Countable weighted-phase early-recurrence quantiles

This file lifts the sharp finite-dimensional water-entropy estimate to a
countably infinite normalized phase packet.

The key reduction is exact: recurrence of the complete packet forces
recurrence of every positive-mass normalized head, with defect amplified
only by the reciprocal head mass. Therefore any finite-head marginal law
dominated by product Haar controls early recurrence of the full countable
packet. No independence or distributional assumption on the tail is used.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Restriction of a countable torus packet to its first `M` coordinates. -/
def countableTorusHead (M : ℕ)
    (x : ℕ → UnitAddCircle) : Fin M → UnitAddCircle :=
  fun i => x i

theorem measurable_countableTorusHead (M : ℕ) :
    Measurable (countableTorusHead M) := by
  unfold countableTorusHead
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (i : ℕ)

/-- Countable weighted coherence hits through the first `N` positive clocks. -/
def countableTorusWeightedCoherenceHitUnion
    (p : ℕ → ℝ) (N : ℕ) (η : ℝ) :
    Set (ℕ → UnitAddCircle) :=
  ⋃ n : Fin N, {x | 1 - η ≤
    ‖summableWeightedPhaseAmplitude p (fun k =>
      fourier 1 (((n.1 + 1 : ℕ) : ℤ) • x k))‖}

theorem measurable_summableWeightedPhaseAmplitude_fourier_zsmul
    (p : ℕ → ℝ) (n : ℤ) :
    Measurable (fun x : ℕ → UnitAddCircle =>
      summableWeightedPhaseAmplitude p (fun k =>
        fourier 1 (n • x k))) := by
  unfold summableWeightedPhaseAmplitude
  apply Measurable.tsum
  intro k
  fun_prop

theorem measurableSet_countableTorusWeightedCoherenceHitUnion
    (p : ℕ → ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet (countableTorusWeightedCoherenceHitUnion p N η) := by
  rw [countableTorusWeightedCoherenceHitUnion]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_le measurable_const
    ((measurable_summableWeightedPhaseAmplitude_fourier_zsmul
      p (((n.1 + 1 : ℕ) : ℤ))).norm)

/--
Every countable-packet hit forces a hit of every positive-mass normalized
head, with the exact reciprocal-head-mass defect.
-/
theorem countableTorusWeightedCoherenceHitUnion_subset_head
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M N : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    (η : ℝ) :
    countableTorusWeightedCoherenceHitUnion p N η ⊆
      countableTorusHead M ⁻¹'
        torusProjectiveWeightedCoherenceHitUnion
          (normalizedWeightedHeadWeight p M) N
          (η / summableWeightedHeadMass p M) := by
  intro x hx
  rw [countableTorusWeightedCoherenceHitUnion, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  rw [Set.mem_setOf_eq] at hn
  have hhead := full_coherence_implies_normalized_head_coherence
    p
    (fun k => fourier 1 (((n.1 + 1 : ℕ) : ℤ) • x k))
    hp hsum htotal
    (fun k => by rw [fourier_apply, Circle.norm_coe])
    M hmass hn
  rw [torusProjectiveWeightedCoherenceHitUnion, Set.mem_preimage,
    Set.mem_iUnion]
  refine ⟨n, ?_⟩
  rw [Set.mem_preimage, torusProjectiveWeightedCoherenceTarget,
    Set.mem_setOf_eq]
  simpa only [countableTorusHead, Pi.smul_apply,
    projectiveWeightedPhaseAmplitude,
    normalizedWeightedHeadPhaseAmplitude] using hhead

/--
A finite-head Haar-domination law controls early recurrence of the complete
countable packet. No independence of the tail is required.
-/
theorem
    measureReal_countableTorusWeightedCoherenceHitUnion_boundedDensity_fullEntropy_le
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M N : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {η lam : ℝ}
    (hη1 : η / summableWeightedHeadMass p M ≤ 1)
    (hlam : 1 ≤ lam)
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν] (B : NNReal)
    (hhead :
      Measure.map (countableTorusHead M) ν ≤ B • volume) :
    ν.real (countableTorusWeightedCoherenceHitUnion p N η) ≤
      (B : ℝ) * ((N : ℝ) * ((M : ℝ) * Real.exp (
        (Real.pi / 4) *
            (lam * (η / summableWeightedHeadMass p M)) -
          projectiveFullWaterEntropyAt
            (normalizedWeightedHeadWeight p M) lam +
          (1 / 2 : ℝ) * Real.log lam))) := by
  have hsubset :=
    countableTorusWeightedCoherenceHitUnion_subset_head
      p hp hsum htotal M N hmass η
  calc
    ν.real (countableTorusWeightedCoherenceHitUnion p N η) ≤
        ν.real (countableTorusHead M ⁻¹'
          torusProjectiveWeightedCoherenceHitUnion
            (normalizedWeightedHeadWeight p M) N
            (η / summableWeightedHeadMass p M)) :=
      measureReal_mono hsubset
    _ = (Measure.map (countableTorusHead M) ν).real
          (torusProjectiveWeightedCoherenceHitUnion
            (normalizedWeightedHeadWeight p M) N
            (η / summableWeightedHeadMass p M)) := by
      rw [measureReal_def, measureReal_def,
        Measure.map_apply (measurable_countableTorusHead M)
          (measurableSet_torusProjectiveWeightedCoherenceHitUnion _ _ _)]
    _ ≤ (B : ℝ) * ((N : ℝ) * ((M : ℝ) * Real.exp (
        (Real.pi / 4) *
            (lam * (η / summableWeightedHeadMass p M)) -
          projectiveFullWaterEntropyAt
            (normalizedWeightedHeadWeight p M) lam +
          (1 / 2 : ℝ) * Real.log lam))) := by
      apply
        measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_fullEntropy_le
      · exact fun i => normalizedWeightedHeadWeight_nonneg p hp M hmass i
      · exact fun i => normalizedWeightedHeadWeight_le_one p hp M hmass i
      · exact sum_normalizedWeightedHeadWeight p M hmass
      · exact hη1
      · exact hlam
      · exact hhead

/--
Original-weight form of the countable early-hit bound. Scaling normalized
head water by its mass recovers the water entropy of the original
unnormalized coordinates exactly.
-/
theorem
    measureReal_countableTorusWeightedCoherenceHitUnion_originalHeadEntropy_le
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M N : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {η lam : ℝ}
    (hη1 : η / summableWeightedHeadMass p M ≤ 1)
    (hwater : 1 ≤ summableWeightedHeadMass p M * lam)
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν] (B : NNReal)
    (hhead :
      Measure.map (countableTorusHead M) ν ≤ B • volume) :
    ν.real (countableTorusWeightedCoherenceHitUnion p N η) ≤
      (B : ℝ) * ((N : ℝ) * ((M : ℝ) * Real.exp (
        (Real.pi / 4) * (lam * η) -
          (1 / 2 : ℝ) *
            ∑ i : Fin M, Real.log (max 1 (lam * p i)) +
          (1 / 2 : ℝ) *
            Real.log (summableWeightedHeadMass p M * lam)))) := by
  have hbase :=
    measureReal_countableTorusWeightedCoherenceHitUnion_boundedDensity_fullEntropy_le
      p hp hsum htotal M N hmass hη1 hwater ν B hhead
  rw [projectiveFullWaterEntropyAt_normalizedHead_rescale
    p M hmass lam] at hbase
  have hscale :
      (summableWeightedHeadMass p M * lam) *
          (η / summableWeightedHeadMass p M) =
        lam * η := by
    field_simp [hmass.ne']
  rwa [hscale] at hbase

end RHTower
