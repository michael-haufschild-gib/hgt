import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRecurrenceBound

/-!
# Observer-graph rate--distortion law

Choose any simple graph on the energy sectors of a finite quantum observer
family.  Synchronizing only its edges lowers the recurrence exponent from
the full visible graph rank to the rank of the chosen graph.  Every omitted
directed coherence contributes an explicit bounded distortion remainder.

The accounting is directed: matrix-block weights need not be symmetric even
though the synchronization graph is undirected.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Total observer weight on the directed pairs selected by an undirected
synchronization graph.  Both orientations are counted separately. -/
noncomputable def finiteObserverSelectedDirectedWeightMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) : ℝ := by
  classical
  exact ∑ i, ∑ j,
    if G.Adj i j then finiteObserverUnionWeight lam block i j else 0

/-- Total observer weight on omitted directed non-loop pairs.  Diagonal
weights are excluded because Hamiltonian phase conjugation fixes them
exactly. -/
noncomputable def finiteObserverOmittedDirectedWeightMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) : ℝ := by
  classical
  exact ∑ i, ∑ j,
    if i ≠ j ∧ ¬ G.Adj i j
    then finiteObserverUnionWeight lam block i j
    else 0

/-- Total observer weight on all directed non-loop pairs. -/
noncomputable def finiteObserverOffDiagonalDirectedWeightMass
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) : ℝ := by
  classical
  exact ∑ i, ∑ j,
    if i ≠ j then finiteObserverUnionWeight lam block i j else 0

/-- Selected and omitted directed masses are an exact partition of the
off-diagonal observer mass, without any symmetry assumption on weights. -/
theorem finiteObserver_selected_add_omitted_eq_offDiagonal
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) :
    finiteObserverSelectedDirectedWeightMass G lam block +
        finiteObserverOmittedDirectedWeightMass G lam block =
      finiteObserverOffDiagonalDirectedWeightMass lam block := by
  classical
  unfold finiteObserverSelectedDirectedWeightMass
    finiteObserverOmittedDirectedWeightMass
    finiteObserverOffDiagonalDirectedWeightMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : G.Adj i j
  · have hne : i ≠ j := G.ne_of_adj hij
    simp [hij, hne]
  · by_cases hne : i ≠ j
    · simp [hij, hne]
    · simp [not_not.mp hne]

/-- Every selected directed weight mass is nonnegative. -/
theorem finiteObserverSelectedDirectedWeightMass_nonneg
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    0 ≤ finiteObserverSelectedDirectedWeightMass G lam block := by
  classical
  rw [finiteObserverSelectedDirectedWeightMass]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact finiteObserverUnionWeight_nonneg lam block hlam i j
  · exact le_rfl

/-- Every omitted directed weight mass is nonnegative. -/
theorem finiteObserverOmittedDirectedWeightMass_nonneg
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    0 ≤ finiteObserverOmittedDirectedWeightMass G lam block := by
  classical
  rw [finiteObserverOmittedDirectedWeightMass]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact finiteObserverUnionWeight_nonneg lam block hlam i j
  · exact le_rfl

private theorem finiteObserverHamiltonianPhase_chord_le_two
    {d : ℕ} (n : ℕ) (energy : Fin d → ℝ) (i j : Fin d) :
    ‖finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j - 1‖ ≤
      2 := by
  calc
    ‖finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j - 1‖ ≤
        ‖finiteQuantumObserverPhase
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [finiteQuantumObserverPhase, norm_mul, norm_star,
        finiteObserverHamiltonianVertexPhase_norm,
        finiteObserverHamiltonianVertexPhase_norm, norm_one]
      norm_num

/--
**Finite observer-graph rate--distortion law.**

For every finite observer family, every nonnegative observer weighting,
every energy list, every resolution, and every chosen synchronization graph
`G`, one positive integer time before the graph-rank deadline has total
squared observer displacement at most

`4 * omitted directed mass + 4 * resolution² * selected directed mass`.

No relation between `G` and the full coherence graph is required.
-/
theorem exists_finiteQuantumObserver_graph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card G.ConnectedComponent) ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
        4 * finiteObserverOmittedDirectedWeightMass G lam block +
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            finiteObserverSelectedDirectedWeightMass G lam block := by
  classical
  obtain ⟨n, hn0, hnQ, hedge⟩ :=
    exists_graphEdge_phase_approximation G energy Q
  refine ⟨n, hn0, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hnQ
  · rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy,
      finiteQuantumObserverPhaseEnergy]
    let δ : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
    let weight : Fin d → Fin d → ℝ :=
      finiteObserverUnionWeight lam block
    calc
      (∑ i, ∑ j, weight i j *
          ‖finiteQuantumObserverPhase
            (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j -
              1‖ ^ 2) ≤
          ∑ i, ∑ j, (
            4 * (if i ≠ j ∧ ¬ G.Adj i j then weight i j else 0) +
              4 * δ ^ 2 *
                (if G.Adj i j then weight i j else 0)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : G.Adj i j
        · obtain ⟨r, hr⟩ := hedge i j hij
          have hchord :
              ‖finiteQuantumObserverPhase
                  (finiteObserverHamiltonianVertexPhase
                    (n : ℝ) energy) i j - 1‖ ≤
                2 * δ := by
            rw [finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase]
            exact
              (norm_exp_I_mul_real_sub_one_le_mod_two_pi
                ((n : ℝ) * (energy i - energy j)) r).trans
                (by simpa only [δ] using hr)
          simp [hij]
          have hsq :
              ‖finiteQuantumObserverPhase
                  (finiteObserverHamiltonianVertexPhase
                    (n : ℝ) energy) i j - 1‖ ^ 2 ≤
                (2 * δ) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hchord
          calc
            weight i j *
                ‖finiteQuantumObserverPhase
                  (finiteObserverHamiltonianVertexPhase
                    (n : ℝ) energy) i j - 1‖ ^ 2 ≤
                weight i j * (2 * δ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq
                (finiteObserverUnionWeight_nonneg
                  lam block hlam i j)
            _ = 4 * δ ^ 2 * weight i j := by ring
        · by_cases hieqj : i = j
          · subst j
            have hunit :
                finiteQuantumObserverPhase
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy) i i = 1 := by
              rw [finiteQuantumObserverPhase]
              change
                finiteObserverHamiltonianVertexPhase
                    (n : ℝ) energy i *
                  (starRingEnd ℂ)
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy i) = 1
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
                finiteObserverHamiltonianVertexPhase_norm]
              norm_num
            simp [hunit]
          · have hchord :
                ‖finiteQuantumObserverPhase
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy) i j - 1‖ ≤ 2 :=
              finiteObserverHamiltonianPhase_chord_le_two
                n energy i j
            have hsq :
                ‖finiteQuantumObserverPhase
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy) i j - 1‖ ^ 2 ≤
                  (2 : ℝ) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 hchord
            simp [hij, hieqj]
            calc
              weight i j *
                  ‖finiteQuantumObserverPhase
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy) i j - 1‖ ^ 2 ≤
                  weight i j * (2 : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq
                  (finiteObserverUnionWeight_nonneg
                    lam block hlam i j)
              _ = 4 * weight i j := by ring
      _ = 4 * finiteObserverOmittedDirectedWeightMass G lam block +
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            finiteObserverSelectedDirectedWeightMass G lam block := by
        dsimp only [δ, weight]
        unfold finiteObserverOmittedDirectedWeightMass
          finiteObserverSelectedDirectedWeightMass
        rw [Finset.mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]

/-- Threshold graph retaining every unordered pair whose weight exceeds
`τ` in at least one directed orientation. -/
def finiteObserverThresholdCoherenceGraph
    {d : ℕ} {J : Type*} [Fintype J]
    (τ : ℝ) (lam : J → ℝ)
    (block : J → Fin d → Fin d → ℂ) :
    SimpleGraph (Fin d) where
  Adj i j :=
    i ≠ j ∧
      (τ < finiteObserverUnionWeight lam block i j ∨
       τ < finiteObserverUnionWeight lam block j i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every omitted orientation of a non-loop threshold pair has weight at
most the threshold. -/
theorem finiteObserverUnionWeight_le_threshold_of_not_adj
    {d : ℕ} {J : Type*} [Fintype J]
    (τ : ℝ) (lam : J → ℝ)
    (block : J → Fin d → Fin d → ℂ)
    {i j : Fin d} (hij : i ≠ j)
    (homit :
      ¬ (finiteObserverThresholdCoherenceGraph τ lam block).Adj i j) :
    finiteObserverUnionWeight lam block i j ≤ τ := by
  apply le_of_not_gt
  intro hlarge
  exact homit ⟨hij, Or.inl hlarge⟩

/-- Rate--distortion law for the graph obtained by thresholding directed
observer weights in either orientation. -/
theorem exists_finiteQuantumObserver_thresholdGraph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (τ : ℝ) (lam : J → ℝ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverThresholdCoherenceGraph
            τ lam block).ConnectedComponent) ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
        4 * finiteObserverOmittedDirectedWeightMass
            (finiteObserverThresholdCoherenceGraph τ lam block) lam block +
          4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            finiteObserverSelectedDirectedWeightMass
              (finiteObserverThresholdCoherenceGraph τ lam block)
              lam block :=
  exists_finiteQuantumObserver_graph_rateDistortion
    (finiteObserverThresholdCoherenceGraph τ lam block)
    lam block hlam energy Q

end RHTower
