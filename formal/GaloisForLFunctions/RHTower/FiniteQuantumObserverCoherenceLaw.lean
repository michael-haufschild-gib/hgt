import GaloisForLFunctions.RHTower.FiniteSpectralBlockRecurrenceLaw
import GaloisForLFunctions.HTGeometry.CoherenceGraphCapacity

/-!
# Universal finite observer-coherence law

A finite family of matrix-valued records evolving under one diagonal phase
packet has one exact quadratic return signal.  Its weights are the union of
the energy-basis matrix entries visible to the observer family.  The signal
vanishes exactly when the phases are constant on every connected component
of the resulting coherence graph.

Consequently the observable relative-phase capacity is

`number of visible sectors - number of coherence components`.

The result applies to density matrices, observables, or any finite family of
both.  It is deterministic and does not assume random spectra.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Pairwise phase produced by conjugating matrix entries with a diagonal
unitary whose diagonal is `z`. -/
def finiteQuantumObserverPhase {d : ℕ}
    (z : Fin d → ℂ) (i j : Fin d) : ℂ :=
  z i * star (z j)

/-- Total weighted squared Hilbert--Schmidt displacement of a finite observer
family under a diagonal unitary phase packet. -/
def finiteQuantumObserverDistanceSq
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ) : ℝ :=
  finiteObserverBlockDistanceSq lam (finiteQuantumObserverPhase z) block

/-- Coherence-weighted phase energy of the observer union. -/
def finiteQuantumObserverPhaseEnergy
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ) : ℝ :=
  ∑ i, ∑ j, finiteObserverUnionWeight lam block i j *
    ‖finiteQuantumObserverPhase z i j - 1‖ ^ 2

/-- The observer-union weight is nonnegative when all observation weights
are nonnegative. -/
theorem finiteObserverUnionWeight_nonneg
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (i j : Fin d) :
    0 ≤ finiteObserverUnionWeight lam block i j := by
  rw [finiteObserverUnionWeight]
  exact Finset.sum_nonneg fun a _ha =>
    mul_nonneg (hlam a) (sq_nonneg ‖block a i j‖)

/-- Exact matrix observer law: total displacement equals the union-weighted
phase energy. -/
theorem finiteQuantumObserverDistanceSq_eq_phaseEnergy
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ) :
    finiteQuantumObserverDistanceSq lam z block =
      finiteQuantumObserverPhaseEnergy lam z block := by
  simpa only [finiteQuantumObserverDistanceSq,
    finiteQuantumObserverPhaseEnergy] using
    (finiteObserverBlockDistanceSq_eq_unionWeight
      lam (finiteQuantumObserverPhase z) block)

/-- Undirected coherence graph seen by the observer family.  An edge is
present exactly when at least one orientation of the corresponding matrix
block has positive aggregate weight. -/
def finiteObserverCoherenceGraph
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) :
    SimpleGraph (Fin d) where
  Adj i j :=
    i ≠ j ∧
      (0 < finiteObserverUnionWeight lam block i j ∨
       0 < finiteObserverUnionWeight lam block j i)
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable instance finiteObserverCoherenceGraph.instDecidableRel
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) :
    DecidableRel (finiteObserverCoherenceGraph lam block).Adj :=
  Classical.decRel _

theorem finiteObserverCoherenceGraph_adj
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (i j : Fin d) :
    (finiteObserverCoherenceGraph lam block).Adj i j ↔
      i ≠ j ∧
        (0 < finiteObserverUnionWeight lam block i j ∨
         0 < finiteObserverUnionWeight lam block j i) :=
  Iff.rfl

private theorem unit_mul_star
    (z : ℂ) (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  change z * (starRingEnd ℂ) z = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

private theorem unit_star_mul
    (z : ℂ) (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  rw [mul_comm]
  exact unit_mul_star z hz

private theorem eq_of_mul_star_eq_one
    (x y : ℂ) (hy : ‖y‖ = 1)
    (h : x * star y = 1) :
    x = y := by
  calc
    x = x * (star y * y) := by
      rw [unit_star_mul y hy, mul_one]
    _ = (x * star y) * y := by ring
    _ = y := by rw [h, one_mul]

private theorem nested_sum_term_eq_zero
    {d : ℕ} (f : Fin d → Fin d → ℝ)
    (hf : ∀ i j, 0 ≤ f i j)
    (hzero : ∑ i, ∑ j, f i j = 0)
    (i j : Fin d) :
    f i j = 0 := by
  have hi : ∑ j, f i j = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _hi =>
        Finset.sum_nonneg (fun j _hj => hf i j))).mp hzero
    exact hs i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _hj => hf i j)).mp hi
  exact hj j (Finset.mem_univ j)

private theorem phase_eq_of_positive_weight
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (hunit : ∀ i, ‖z i‖ = 1)
    (hzero : finiteQuantumObserverPhaseEnergy lam z block = 0)
    {i j : Fin d}
    (hpos : 0 < finiteObserverUnionWeight lam block i j) :
    z i = z j := by
  let f : Fin d → Fin d → ℝ := fun u v =>
    finiteObserverUnionWeight lam block u v *
      ‖finiteQuantumObserverPhase z u v - 1‖ ^ 2
  have hf : ∀ u v, 0 ≤ f u v := by
    intro u v
    exact mul_nonneg
      (finiteObserverUnionWeight_nonneg lam block hlam u v)
      (sq_nonneg _)
  have hsum : ∑ u, ∑ v, f u v = 0 := by
    simpa only [f, finiteQuantumObserverPhaseEnergy] using hzero
  have hterm := nested_sum_term_eq_zero f hf hsum i j
  have hsq :
      ‖finiteQuantumObserverPhase z i j - 1‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hpos.ne'
  have hnorm :
      ‖finiteQuantumObserverPhase z i j - 1‖ = 0 :=
    sq_eq_zero_iff.mp hsq
  have hphase :
      finiteQuantumObserverPhase z i j = 1 :=
    sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact eq_of_mul_star_eq_one (z i) (z j) (hunit j)
    (by simpa only [finiteQuantumObserverPhase] using hphase)

/-- Necessary-and-sufficient zero law.  A unit phase packet gives zero
observer displacement exactly when it is constant on every coherence edge,
equivalently on every connected component of the observer graph. -/
theorem finiteQuantumObserverPhaseEnergy_eq_zero_iff
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverPhaseEnergy lam z block = 0 ↔
      ∀ i j, (finiteObserverCoherenceGraph lam block).Adj i j →
        z i = z j := by
  constructor
  · intro hzero i j hij
    rcases hij.2 with hpos | hpos
    · exact phase_eq_of_positive_weight
        lam z block hlam hunit hzero hpos
    · exact (phase_eq_of_positive_weight
        lam z block hlam hunit hzero hpos).symm
  · intro hconstant
    rw [finiteQuantumObserverPhaseEnergy]
    apply Finset.sum_eq_zero
    intro i _hi
    apply Finset.sum_eq_zero
    intro j _hj
    by_cases hij : i = j
    · subst j
      rw [finiteQuantumObserverPhase, unit_mul_star (z i) (hunit i)]
      simp
    by_cases hweight :
        finiteObserverUnionWeight lam block i j = 0
    · simp [hweight]
    have hpos : 0 < finiteObserverUnionWeight lam block i j :=
      lt_of_le_of_ne
        (finiteObserverUnionWeight_nonneg lam block hlam i j)
        (Ne.symm hweight)
    have hphase : z i = z j :=
      hconstant i j ⟨hij, Or.inl hpos⟩
    rw [finiteQuantumObserverPhase, hphase,
      unit_mul_star (z j) (hunit j)]
    simp

/-- Exact universal phase-capacity law for a finite observer family. -/
theorem finiteObserverCoherenceGraph_phaseCapacity
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ) :
    Module.finrank ℝ
        (LinearMap.range
          (GaloisForLFunctions.graphCoboundary
            (finiteObserverCoherenceGraph lam block) ℝ)) =
      d -
        Fintype.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent := by
  classical
  simpa using
    (GaloisForLFunctions.finrank_range_graphCoboundary
      (finiteObserverCoherenceGraph lam block) ℝ)

/-- Vertex phase generated by a finite real energy list. -/
def finiteObserverHamiltonianVertexPhase
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i : Fin d) : ℂ :=
  Complex.exp
    (Complex.I * (((t * energy i : ℝ) : ℂ)))

theorem finiteObserverHamiltonianVertexPhase_norm
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i : Fin d) :
    ‖finiteObserverHamiltonianVertexPhase t energy i‖ = 1 := by
  rw [finiteObserverHamiltonianVertexPhase, Complex.norm_exp]
  simp [Complex.mul_re]

/--
Universal finite observer-coherence capstone.  For every finite Hamiltonian
energy list, every finite family of matrix records, and every nonnegative
observer weighting:

1. the exact squared return distance is the union-weighted phase energy;
2. zero return is equivalent to phase constancy on coherence components;
3. observable relative-phase capacity is `vertices - components`.
-/
theorem finite_quantum_observer_coherence_law
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (t : ℝ) (energy : Fin d → ℝ) :
    finiteQuantumObserverDistanceSq lam
        (finiteObserverHamiltonianVertexPhase t energy) block =
      finiteQuantumObserverPhaseEnergy lam
        (finiteObserverHamiltonianVertexPhase t energy) block ∧
    (finiteQuantumObserverPhaseEnergy lam
          (finiteObserverHamiltonianVertexPhase t energy) block = 0 ↔
      ∀ i j, (finiteObserverCoherenceGraph lam block).Adj i j →
        finiteObserverHamiltonianVertexPhase t energy i =
          finiteObserverHamiltonianVertexPhase t energy j) ∧
    Module.finrank ℝ
        (LinearMap.range
          (GaloisForLFunctions.graphCoboundary
            (finiteObserverCoherenceGraph lam block) ℝ)) =
      d -
        Fintype.card
          (finiteObserverCoherenceGraph lam block).ConnectedComponent := by
  refine ⟨finiteQuantumObserverDistanceSq_eq_phaseEnergy lam _ block,
    finiteQuantumObserverPhaseEnergy_eq_zero_iff
      lam _ block hlam
        (finiteObserverHamiltonianVertexPhase_norm t energy),
    finiteObserverCoherenceGraph_phaseCapacity lam block⟩

end RHTower
