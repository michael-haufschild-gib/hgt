import GaloisForLFunctions.RHTower.FiniteQuantumObserverCoherenceLaw
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence

/-!
# Coherence-graph recurrence deadline

A finite observer family does not pay for every Hilbert-space direction.
Choose one phase reference in each connected component of its coherence
graph.  Simultaneous approximation of the remaining relative energies gives
a deterministic recurrence deadline whose exponent is exactly

`number of energy sectors - number of coherence components`.

The bound holds for every finite Hamiltonian, every finite matrix-observer
family, every nonnegative observer weighting, and every resolution.
-/

open scoped BigOperators

noncomputable section

open SimpleGraph

namespace RHTower

/-- A canonical representative of a graph connected component. -/
def graphComponentRoot {V : Type*} (G : SimpleGraph V)
    (c : G.ConnectedComponent) : V :=
  Quot.out c

@[simp]
theorem connectedComponentMk_graphComponentRoot
    {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (graphComponentRoot G c) = c := by
  exact Quot.out_eq c

/-- A vertex is the chosen phase reference of its connected component. -/
def IsGraphComponentRoot
    {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  v = graphComponentRoot G (G.connectedComponentMk v)

/-- Chosen roots are in bijection with graph connected components. -/
noncomputable def graphComponentRootEquiv
    {V : Type*} (G : SimpleGraph V) :
    {v : V // IsGraphComponentRoot G v} ≃ G.ConnectedComponent where
  toFun v := G.connectedComponentMk v.1
  invFun c := ⟨graphComponentRoot G c, by
    rw [IsGraphComponentRoot, connectedComponentMk_graphComponentRoot]⟩
  left_inv v := by
    apply Subtype.ext
    exact v.2.symm
  right_inv c := connectedComponentMk_graphComponentRoot G c

/-- Vertices carrying non-reference relative phases. -/
abbrev graphNonRoot
    {V : Type*} (G : SimpleGraph V) :=
  {v : V // ¬ IsGraphComponentRoot G v}

noncomputable instance graphNonRoot.instFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype (graphNonRoot G) :=
  Fintype.ofFinite _

/-- Exact count of non-reference graph phases. -/
theorem card_graphNonRoot
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype.card (graphNonRoot G) =
      Fintype.card V - Nat.card G.ConnectedComponent := by
  classical
  calc
    Fintype.card (graphNonRoot G) =
        Fintype.card V -
          Fintype.card {v : V // IsGraphComponentRoot G v} :=
      Fintype.card_subtype_compl (IsGraphComponentRoot G)
    _ = Fintype.card V - Nat.card G.ConnectedComponent := by
      exact congrArg (fun n => Fintype.card V - n)
        (by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr (graphComponentRootEquiv G))

/-- Energy relative to the chosen reference of a vertex component. -/
def graphRelativeEnergy
    {V : Type*} (G : SimpleGraph V) (energy : V → ℝ) (v : V) : ℝ :=
  energy v - energy (graphComponentRoot G (G.connectedComponentMk v))

theorem graphRelativeEnergy_eq_zero_of_root
    {V : Type*} (G : SimpleGraph V) (energy : V → ℝ) {v : V}
    (hv : IsGraphComponentRoot G v) :
    graphRelativeEnergy G energy v = 0 := by
  rw [graphRelativeEnergy, hv, connectedComponentMk_graphComponentRoot]
  simp

/-- An edge energy gap is a difference of component-relative energies. -/
theorem energy_sub_eq_graphRelativeEnergy_sub_of_adj
    {V : Type*} (G : SimpleGraph V) (energy : V → ℝ)
    {i j : V} (hij : G.Adj i j) :
    energy i - energy j =
      graphRelativeEnergy G energy i - graphRelativeEnergy G energy j := by
  have hc :
      G.connectedComponentMk i = G.connectedComponentMk j :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hij
  rw [graphRelativeEnergy, graphRelativeEnergy, hc]
  ring

/--
Simultaneous recurrence of all component-relative energies.  One phase per
component is free, so the exponent is vertices minus components.
-/
theorem exists_graphRelativeEnergy_phase_approximation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (energy : V → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      ∃ r : V → ℤ, ∀ v,
        |(n : ℝ) * graphRelativeEnergy G energy v -
            2 * Real.pi * r v| ≤
          2 * Real.pi / (Q + 1 : ℝ) := by
  classical
  let e : graphNonRoot G ≃
      Fin (Fintype.card (graphNonRoot G)) :=
    Fintype.equivFin (graphNonRoot G)
  let omega : Fin (Fintype.card (graphNonRoot G)) → ℝ :=
    fun k => graphRelativeEnergy G energy (e.symm k).1
  obtain ⟨n, hn0, hnQ, r0, hr0⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q) omega
  let r : V → ℤ := fun v =>
    if hv : ¬ IsGraphComponentRoot G v
    then r0 (e ⟨v, hv⟩)
    else 0
  refine ⟨n, hn0, ?_, r, ?_⟩
  · simpa only [card_graphNonRoot G] using hnQ
  · intro v
    by_cases hv : ¬ IsGraphComponentRoot G v
    · simpa only [r, hv, ↓reduceDIte, omega, Equiv.symm_apply_apply] using!
        hr0 (e ⟨v, hv⟩)
    · have hrel :
          graphRelativeEnergy G energy v = 0 :=
        graphRelativeEnergy_eq_zero_of_root G energy (not_not.mp hv)
      simp only [r, hv, ↓reduceDIte, hrel, mul_zero, Int.cast_zero,
        sub_zero, abs_zero]
      exact div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (by positivity)

/-- Every visible graph edge recurs under the same graph-rank deadline. -/
theorem exists_graphEdge_phase_approximation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (energy : V → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^ (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      ∀ i j, G.Adj i j →
        ∃ r : ℤ,
          |(n : ℝ) * (energy i - energy j) -
              2 * Real.pi * r| ≤
            2 * (2 * Real.pi / (Q + 1 : ℝ)) := by
  obtain ⟨n, hn0, hnQ, r, hr⟩ :=
    exists_graphRelativeEnergy_phase_approximation G energy Q
  refine ⟨n, hn0, hnQ, ?_⟩
  intro i j hij
  refine ⟨r i - r j, ?_⟩
  rw [energy_sub_eq_graphRelativeEnergy_sub_of_adj G energy hij]
  have hrewrite :
      (n : ℝ) *
          (graphRelativeEnergy G energy i -
            graphRelativeEnergy G energy j) -
          2 * Real.pi * ((r i - r j : ℤ) : ℝ) =
        ((n : ℝ) * graphRelativeEnergy G energy i -
          2 * Real.pi * r i) -
        ((n : ℝ) * graphRelativeEnergy G energy j -
          2 * Real.pi * r j) := by
    push_cast
    ring
  rw [hrewrite]
  calc
    |((n : ℝ) * graphRelativeEnergy G energy i -
          2 * Real.pi * r i) -
        ((n : ℝ) * graphRelativeEnergy G energy j -
          2 * Real.pi * r j)| ≤
        |(n : ℝ) * graphRelativeEnergy G energy i -
          2 * Real.pi * r i| +
        |(n : ℝ) * graphRelativeEnergy G energy j -
          2 * Real.pi * r j| := abs_sub _ _
    _ ≤ 2 * (2 * Real.pi / (Q + 1 : ℝ)) := by
      linarith [hr i, hr j]

/-- Vertex-phase and energy-gap descriptions agree. -/
theorem finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase
    {d : ℕ} (n : ℕ) (energy : Fin d → ℝ) (i j : Fin d) :
    finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j =
      Complex.exp
        (Complex.I * ((((n : ℝ) * (energy i - energy j) : ℝ) : ℂ))) := by
  rw [finiteQuantumObserverPhase]
  simp only [finiteObserverHamiltonianVertexPhase, Complex.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/--
Universal observer-graph recurrence bound.  For every finite Hamiltonian,
finite matrix-observer family, nonnegative observer weighting and
resolution `Q`, one positive integer time no later than
`(Q+1)^(sectors-components)` makes the complete observer displacement
quadratically small.
-/
theorem exists_finiteQuantumObserver_graphRank_recurrence
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent) ∧
      finiteQuantumObserverPhaseEnergy lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
        4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
          ∑ i, ∑ j, finiteObserverUnionWeight lam block i j := by
  let G := finiteObserverCoherenceGraph lam block
  obtain ⟨n, hn0, hnQ, hedge⟩ :=
    exists_graphEdge_phase_approximation G energy Q
  refine ⟨n, hn0, ?_, ?_⟩
  · simpa only [Fintype.card_fin, G] using hnQ
  · rw [finiteQuantumObserverPhaseEnergy]
    calc
      (∑ i, ∑ j, finiteObserverUnionWeight lam block i j *
          ‖finiteQuantumObserverPhase
            (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) i j - 1‖ ^ (2 : ℕ)) ≤
          ∑ i, ∑ j, finiteObserverUnionWeight lam block i j *
            (2 * (2 * Real.pi / (Q + 1 : ℝ))) ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        by_cases hij : i = j
        · subst j
          have hunit :
              finiteObserverHamiltonianVertexPhase (n : ℝ) energy i *
                  star (finiteObserverHamiltonianVertexPhase
                    (n : ℝ) energy i) = 1 := by
            change
              finiteObserverHamiltonianVertexPhase (n : ℝ) energy i *
                  (starRingEnd ℂ)
                    (finiteObserverHamiltonianVertexPhase
                      (n : ℝ) energy i) = 1
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
              finiteObserverHamiltonianVertexPhase_norm]
            norm_num
          rw [finiteQuantumObserverPhase, hunit]
          simp
          exact mul_nonneg
            (finiteObserverUnionWeight_nonneg lam block hlam i i)
            (sq_nonneg _)
        by_cases hweight :
            finiteObserverUnionWeight lam block i j = 0
        · simp [hweight]
        have hpos : 0 < finiteObserverUnionWeight lam block i j :=
          lt_of_le_of_ne
            (finiteObserverUnionWeight_nonneg lam block hlam i j)
            (Ne.symm hweight)
        have hadj : G.Adj i j := by
          exact ⟨hij, Or.inl hpos⟩
        obtain ⟨r, hr⟩ := hedge i j hadj
        have hchord :
            ‖Complex.exp
                (Complex.I *
                  ((((n : ℝ) * (energy i - energy j) : ℝ) : ℂ))) - 1‖ ≤
              2 * (2 * Real.pi / (Q + 1 : ℝ)) :=
          (norm_exp_I_mul_real_sub_one_le_mod_two_pi
            ((n : ℝ) * (energy i - energy j)) r).trans hr
        rw [finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase]
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _)
            (by positivity)).2 hchord)
          (finiteObserverUnionWeight_nonneg lam block hlam i j)
      _ = 4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
          ∑ i, ∑ j, finiteObserverUnionWeight lam block i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring

/--
Distance form of the observer-graph recurrence bound.  The same deadline
controls the actual total squared Hilbert--Schmidt displacement.
-/
theorem exists_finiteQuantumObserver_graphRank_distance_recurrence
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent) ∧
      finiteQuantumObserverDistanceSq lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) block ≤
        4 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) *
          ∑ i, ∑ j, finiteObserverUnionWeight lam block i j := by
  obtain ⟨n, hn0, hnQ, henergy⟩ :=
    exists_finiteQuantumObserver_graphRank_recurrence
      lam block hlam energy Q
  refine ⟨n, hn0, hnQ, ?_⟩
  rw [finiteQuantumObserverDistanceSq_eq_phaseEnergy]
  exact henergy

end RHTower
