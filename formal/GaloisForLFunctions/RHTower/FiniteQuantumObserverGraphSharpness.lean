import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRecurrenceBound
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceMinimax
import GaloisForLFunctions.HTGeometry.GraphCoboundaryRank

/-!
# Sharpness of the observer-coherence recurrence exponent

The observer-graph recurrence theorem has exponent equal to visible
relative-phase rank.  This file supplies matching worst-spectrum examples
for every positive connected rank.  A uniform pure-state observer has the
complete coherence graph, rank `d - 1`, and its Hilbert--Schmidt displacement
is exactly twice the equal-phase fidelity defect.  Haar avoidance therefore
forces order `Q^(d-1)` clocks at quadratic resolution, matching the graph-rank
upper exponent.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Unit weight for the one-record uniform pure-state observer. -/
def uniformPureObserverWeight (_ : Unit) : ℝ := 1

/-- Matrix of the uniform pure state on `d` energy sectors. -/
def uniformPureObserverBlock (d : ℕ)
    (_ : Unit) (_i _j : Fin d) : ℂ :=
  ((d : ℝ)⁻¹ : ℂ)

theorem uniformPureObserverUnionWeight
    {d : ℕ} (hd : 0 < d) (i j : Fin d) :
    finiteObserverUnionWeight uniformPureObserverWeight
        (uniformPureObserverBlock d) i j =
      (d : ℝ)⁻¹ ^ 2 := by
  rw [finiteObserverUnionWeight]
  simp only [Finset.univ_unique, Finset.sum_singleton,
    uniformPureObserverWeight, uniformPureObserverBlock, one_mul]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by exact_mod_cast hd)]

theorem uniformPureObserver_totalUnionWeight
    {d : ℕ} (hd : 0 < d) :
    ∑ i : Fin d, ∑ j : Fin d,
        finiteObserverUnionWeight uniformPureObserverWeight
          (uniformPureObserverBlock d) i j =
      1 := by
  simp_rw [uniformPureObserverUnionWeight hd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  field_simp

/-- The uniform pure-state observer sees every off-diagonal coherence. -/
theorem uniformPureObserver_coherenceGraph_eq_top
    {d : ℕ} (hd : 0 < d) :
    finiteObserverCoherenceGraph uniformPureObserverWeight
        (uniformPureObserverBlock d) = ⊤ := by
  ext i j
  rw [finiteObserverCoherenceGraph_adj]
  rw [uniformPureObserverUnionWeight hd,
    uniformPureObserverUnionWeight hd]
  have hinv : 0 < (d : ℝ)⁻¹ := by positivity
  constructor
  · intro hij
    simpa only [SimpleGraph.top_adj] using hij.1
  · intro hij
    have hij' : i ≠ j := by
      simpa only [SimpleGraph.top_adj] using hij
    exact ⟨hij', Or.inl (sq_pos_of_pos hinv)⟩

/-- The uniform pure-state observer has visible phase rank exactly `d - 1`. -/
theorem uniformPureObserver_phaseCapacity
    {d : ℕ} (hd : 0 < d) :
    Module.finrank ℝ
        (LinearMap.range
          (GaloisForLFunctions.graphCoboundary
            (finiteObserverCoherenceGraph uniformPureObserverWeight
              (uniformPureObserverBlock d)) ℝ)) =
      d - 1 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hconnected :
      (finiteObserverCoherenceGraph uniformPureObserverWeight
        (uniformPureObserverBlock d)).Connected := by
    rw [uniformPureObserver_coherenceGraph_eq_top hd]
    exact SimpleGraph.connected_top
  simpa only [Fintype.card_fin] using
    (GaloisForLFunctions.finrank_graphCoboundary_range_of_connected
      (finiteObserverCoherenceGraph uniformPureObserverWeight
        (uniformPureObserverBlock d)) ℝ hconnected)

/-- Uniform pure-state observer displacement is exactly the normalized
ordered pairwise phase energy. -/
theorem uniformPureObserver_distanceSq_eq_pairwiseEnergy
    {d : ℕ} (hd : 0 < d) (z : Fin d → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverDistanceSq uniformPureObserverWeight z
        (uniformPureObserverBlock d) =
      (d : ℝ)⁻¹ ^ 2 * phasePairwiseSqEnergy z := by
  rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy,
    finiteQuantumObserverPhaseEnergy, phasePairwiseSqEnergy]
  simp_rw [uniformPureObserverUnionWeight hd]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [finiteQuantumObserverPhase]
  have hrewrite :
      z i * star (z j) - 1 = (z i - z j) * star (z j) := by
    rw [sub_mul]
    have hj : z j * star (z j) = 1 := by
      change z j * (starRingEnd ℂ) (z j) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit j]
      norm_num
    rw [hj]
  rw [hrewrite, norm_mul, norm_star, hunit j, mul_one]

/-- Uniform pure-state observer displacement is exactly twice the loss of
equal-phase return fidelity. -/
theorem uniformPureObserver_distanceSq_eq_two_mul_fidelityDeficit
    {d : ℕ} (hd : 0 < d) (z : Fin d → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverDistanceSq uniformPureObserverWeight z
        (uniformPureObserverBlock d) =
      2 * (1 - ‖equalPhaseAmplitude z‖ ^ 2) := by
  rw [uniformPureObserver_distanceSq_eq_pairwiseEnergy hd z hunit,
    phasePairwiseSqEnergy_eq_two_card_sq_mul_fidelityDeficit z hunit]
  simp only [Fintype.card_fin]
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  field_simp

/--
**Deterministic hard spectra for operational return.**  Below the Haar target
budget there is a real energy spectrum whose uniform pure-state density
matrix stays farther than the exact fidelity-defect threshold at every
positive integer clock through `N`.
-/
theorem exists_uniformPureObserver_avoiding_return_until
    {d N : ℕ} (hd : 0 < d) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
        Real.sqrt (Real.pi * η / 2) ^ (d - 1)) < 1) :
    ∃ energy : Fin d → ℝ, ∀ k : Fin N,
      2 * (1 - (1 - η) ^ 2) <
        finiteQuantumObserverDistanceSq uniformPureObserverWeight
          (finiteObserverHamiltonianVertexPhase
            (((k.1 + 1 : ℕ) : ℝ)) energy)
          (uniformPureObserverBlock d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨energy, henergy⟩ :=
    exists_real_frequency_avoiding_coherence_until
      (d := Fin d) N hη0 (by
        simpa only [Fintype.card_fin] using hbudget)
  refine ⟨energy, fun k ↦ ?_⟩
  rw [uniformPureObserver_distanceSq_eq_two_mul_fidelityDeficit hd
    (finiteObserverHamiltonianVertexPhase
      (((k.1 + 1 : ℕ) : ℝ)) energy)
    (finiteObserverHamiltonianVertexPhase_norm
      (((k.1 + 1 : ℕ) : ℝ)) energy)]
  have hcoh := henergy k
  have htarget : 0 ≤ 1 - η := sub_nonneg.mpr hη1
  have hnorm :
      0 ≤ ‖equalPhaseAmplitude
        (finiteObserverHamiltonianVertexPhase
          (((k.1 + 1 : ℕ) : ℝ)) energy)‖ := norm_nonneg _
  have hcoh' :
      ‖equalPhaseAmplitude
        (finiteObserverHamiltonianVertexPhase
          (((k.1 + 1 : ℕ) : ℝ)) energy)‖ < 1 - η := by
    simpa only [finiteObserverHamiltonianVertexPhase] using! hcoh
  nlinarith [sq_nonneg
    (‖equalPhaseAmplitude
      (finiteObserverHamiltonianVertexPhase
        (((k.1 + 1 : ℕ) : ℝ)) energy)‖ - (1 - η))]

/--
For every graph phase capacity `r`, a complete `r + 1` sector observer
realizes that graph-coboundary rank and has deterministic spectra attaining
the Haar-avoidance exponent `r`.  The conclusion does not assert rational
independence or arithmetic projective rank of the returned energy packet.
Thus no universal theorem depending only on graph phase capacity can replace
the graph-recurrence exponent by a smaller one.
-/
theorem exists_rankSharp_uniformPureObserver_avoiding_return_until
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
      ∀ k : Fin N,
        2 * (1 - (1 - η) ^ 2) <
          finiteQuantumObserverDistanceSq uniformPureObserverWeight
            (finiteObserverHamiltonianVertexPhase
              (((k.1 + 1 : ℕ) : ℝ)) energy)
            (uniformPureObserverBlock (r + 1)) := by
  obtain ⟨energy, henergy⟩ :=
    exists_uniformPureObserver_avoiding_return_until
      (d := r + 1) (N := N) (Nat.succ_pos r) hη0 hη1 (by
        simpa only [Nat.add_sub_cancel] using hbudget)
  refine ⟨energy, ?_, henergy⟩
  simpa only [Nat.add_sub_cancel] using
    (uniformPureObserver_phaseCapacity (d := r + 1) (Nat.succ_pos r))

/--
The matching constructive side for the same operational observer: every
spectrum returns at quadratic resolution by clock `(Q + 1)^(d - 1)`.
-/
theorem exists_uniformPureObserver_rank_recurrence
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (d - 1) ∧
      finiteQuantumObserverDistanceSq uniformPureObserverWeight
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy)
          (uniformPureObserverBlock d) ≤
        4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 := by
  obtain ⟨n, hn0, hnQ, hdistance⟩ :=
    exists_finiteQuantumObserver_graphRank_distance_recurrence
      uniformPureObserverWeight (uniformPureObserverBlock d)
      (fun _ ↦ zero_le_one) energy Q
  have hconnected :
      (finiteObserverCoherenceGraph uniformPureObserverWeight
        (uniformPureObserverBlock d)).Connected := by
    rw [uniformPureObserver_coherenceGraph_eq_top hd]
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    exact SimpleGraph.connected_top
  have hcard :
      Nat.card
          (finiteObserverCoherenceGraph uniformPureObserverWeight
            (uniformPureObserverBlock d)).ConnectedComponent =
        1 := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_eq_one_iff.mpr
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    refine ⟨(finiteObserverCoherenceGraph uniformPureObserverWeight
      (uniformPureObserverBlock d)).connectedComponentMk
        (Classical.arbitrary (Fin d)), ?_⟩
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
        exact SimpleGraph.ConnectedComponent.eq.mpr
          (hconnected.preconnected v (Classical.arbitrary (Fin d)))
  refine ⟨n, hn0, ?_, ?_⟩
  · simpa only [hcard] using hnQ
  · simpa only [uniformPureObserver_totalUnionWeight hd, mul_one] using
      hdistance

end RHTower
