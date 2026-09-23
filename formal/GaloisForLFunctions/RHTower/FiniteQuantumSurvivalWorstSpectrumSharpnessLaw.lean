import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphSharpness
import GaloisForLFunctions.RHTower.FiniteQuantumSurvivalHistoryLaw

/-!
# Worst-spectrum sharpness for finite quantum survival

For a uniform pure state on `d` energy sectors, scalar survival loss is
exactly one half of the squared Hilbert--Schmidt displacement of its density
matrix.  The deterministic Haar-avoidance spectra for the matrix observer
therefore transfer without loss to the same scalar survival metric used by
the finite survival-history law.

This gives matching worst-spectrum examples in every projective rank
`r = d - 1`.  It is a statement about the complete uniform pure-state
observer, not a sharpness theorem for an arbitrary coherence graph.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Uniform Born weight on `d` energy sectors. -/
def uniformSurvivalWeight (d : ℕ) (_ : Fin d) : ℝ :=
  (d : ℝ)⁻¹

theorem uniformSurvivalWeight_nonneg
    {d : ℕ} (i : Fin d) :
    0 ≤ uniformSurvivalWeight d i := by
  simp only [uniformSurvivalWeight]
  positivity

theorem uniformSurvivalWeight_sum
    {d : ℕ} (hd : 0 < d) :
    ∑ i : Fin d, uniformSurvivalWeight d i = 1 := by
  simp only [uniformSurvivalWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  field_simp

/-- The survival amplitude of the uniform Born packet is the equal-phase
amplitude used by the Haar sharpness theorem. -/
theorem finiteSpectralSurvivalAmplitude_uniformSurvivalWeight
    {d : ℕ} (z : Fin d → ℂ) :
    finiteSpectralSurvivalAmplitude (uniformSurvivalWeight d) z =
      equalPhaseAmplitude z := by
  rw [finiteSpectralSurvivalAmplitude, equalPhaseAmplitude,
    GaloisForLFunctions.HilbertMetric.hilbertCentroid]
  simp only [uniformSurvivalWeight, Fintype.card_fin, Complex.real_smul,
    Complex.ofReal_inv, Finset.mul_sum]

/--
**Exact scalar--matrix survival identity.**  On unit phases, the scalar
survival-probability deviation of the uniform state is exactly one half of
the squared Hilbert--Schmidt displacement of its pure-state density matrix.
-/
theorem uniformSurvivalDeviation_eq_half_observerDistanceSq
    {d : ℕ} (hd : 0 < d) (z : Fin d → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) :
    finiteSpectralSurvivalDeviation (uniformSurvivalWeight d) z =
      finiteQuantumObserverDistanceSq uniformPureObserverWeight z
        (uniformPureObserverBlock d) / 2 := by
  rw [finiteSpectralSurvivalDeviation_eq_one_sub
      (uniformSurvivalWeight d) z
      (uniformSurvivalWeight_nonneg (d := d))
      (uniformSurvivalWeight_sum hd) hunit,
    finiteSpectralSurvivalProbability,
    finiteSpectralSurvivalAmplitude_uniformSurvivalWeight,
    Complex.normSq_eq_norm_sq,
    uniformPureObserver_distanceSq_eq_two_mul_fidelityDeficit hd z hunit]
  ring

/--
**Deterministic hard spectra in the scalar survival metric.**  Below the
Haar target budget, one real `d`-sector spectrum has survival loss strictly
above the exact fidelity-defect threshold at every positive integer clock
through `N`.
-/
theorem exists_uniformSurvival_avoiding_return_through
    {d N : ℕ} (hd : 0 < d) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
        Real.sqrt (Real.pi * η / 2) ^ (d - 1)) < 1) :
    ∃ energy : Fin d → ℝ, ∀ n : ℕ, 0 < n → n ≤ N →
      1 - (1 - η) ^ (2 : ℕ) <
        finiteSpectralSurvivalDeviation (uniformSurvivalWeight d)
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) := by
  obtain ⟨energy, henergy⟩ :=
    exists_uniformPureObserver_avoiding_return_until
      (d := d) (N := N) hd hη0 hη1 hbudget
  refine ⟨energy, fun n hn0 hnN ↦ ?_⟩
  have hnlt : n - 1 < N := by omega
  have hnstep : n - 1 + 1 = n := by omega
  have hdistance := henergy ⟨n - 1, hnlt⟩
  have hdistance' :
      2 * (1 - (1 - η) ^ (2 : ℕ)) <
        finiteQuantumObserverDistanceSq uniformPureObserverWeight
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
          (uniformPureObserverBlock d) := by
    simpa only [hnstep] using hdistance
  rw [uniformSurvivalDeviation_eq_half_observerDistanceSq hd
    (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
    (finiteObserverHamiltonianVertexPhase_norm (n : ℝ) energy)]
  nlinarith

/--
For every projective rank `r`, the uniform pure state on `r + 1` sectors
realizes that rank and admits a deterministic spectrum whose scalar survival
loss avoids the target at every positive integer clock through `N`.  The
Haar budget has exponent `r`, matching the universal rank-`r` recurrence
exponent.
-/
theorem exists_rankSharp_uniformSurvival_avoiding_return_through
    (r N : ℕ) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * (((r + 1 : ℕ) : ℝ) *
        Real.exp (((r + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ r) < 1) :
    ∃ energy : Fin (r + 1) → ℝ,
      Module.finrank ℝ
          (LinearMap.range
            (GaloisForLFunctions.graphCoboundary
              (finiteObserverCoherenceGraph uniformPureObserverWeight
                (uniformPureObserverBlock (r + 1))) ℝ)) =
        r ∧
      ∀ n : ℕ, 0 < n → n ≤ N →
        1 - (1 - η) ^ (2 : ℕ) <
          finiteSpectralSurvivalDeviation
            (uniformSurvivalWeight (r + 1))
            (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) := by
  obtain ⟨energy, hcapacity, henergy⟩ :=
    exists_rankSharp_uniformPureObserver_avoiding_return_until
      r N hη0 hη1 hbudget
  refine ⟨energy, hcapacity, fun n hn0 hnN ↦ ?_⟩
  have hnlt : n - 1 < N := by omega
  have hnstep : n - 1 + 1 = n := by omega
  have hdistance := henergy ⟨n - 1, hnlt⟩
  have hdistance' :
      2 * (1 - (1 - η) ^ (2 : ℕ)) <
        finiteQuantumObserverDistanceSq uniformPureObserverWeight
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
          (uniformPureObserverBlock (r + 1)) := by
    simpa only [hnstep] using hdistance
  rw [uniformSurvivalDeviation_eq_half_observerDistanceSq
    (Nat.succ_pos r)
    (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
    (finiteObserverHamiltonianVertexPhase_norm (n : ℝ) energy)]
  nlinarith

/--
The matching constructive side in the same scalar survival metric: every
`d`-sector spectrum returns at quadratic resolution by clock
`(Q + 1)^(d - 1)`.
-/
theorem exists_uniformSurvival_rank_recurrence
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (d - 1) ∧
      finiteSpectralSurvivalDeviation (uniformSurvivalWeight d)
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) ≤
        2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) := by
  obtain ⟨n, hn0, hnQ, hdistance⟩ :=
    exists_uniformPureObserver_rank_recurrence hd energy Q
  refine ⟨n, hn0, hnQ, ?_⟩
  rw [uniformSurvivalDeviation_eq_half_observerDistanceSq hd
    (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
    (finiteObserverHamiltonianVertexPhase_norm (n : ℝ) energy)]
  nlinarith

end RHTower
