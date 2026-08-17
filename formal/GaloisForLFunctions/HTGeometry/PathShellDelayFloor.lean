import GaloisForLFunctions.HTGeometry.PathShellEdgeTail
import GaloisForLFunctions.HTGeometry.WeakCutSynthesisCap

/-!
# The polynomial delay tail of the path-local shell

A shell point assembles a path-local Pauli Hamiltonian: one onsite word per site and axis, one
coupling word per edge and axis pair, with the shell coordinates as coefficients.  Deleting one edge
decouples the chain and changes the Hamiltonian by exactly that edge's interaction, whose operator
norm is at most three times the Euclidean norm of its nine coefficients.

The Duhamel synthesis cap therefore holds through time `L` on the whole event that the edge block is
smaller than the error margin divided by `3L`, and the ninth-power shell tail of one edge block turns
that event into a delay floor of order `L ^ (-9)`: the quenched probability of a delay longer than
`L` never decays faster than the ninth power.
-/

open MeasureTheory Metric Set
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Hamiltonian

variable {n : ℕ}

/-- The onsite Pauli word at one site and axis. -/
def onsiteWord (s : Fin (n + 2)) (q : Fin 3) : Fin (n + 2) → Option (Fin 3) :=
  fun t => if t = s then some q else none

/-- The coupling Pauli word of one edge and axis pair. -/
def couplingWord (e : Fin (n + 1)) (ab : Fin 3 × Fin 3) : Fin (n + 2) → Option (Fin 3) :=
  fun t => if t = e.castSucc then some ab.1 else if t = e.succ then some ab.2 else none

/-- The onsite part of the path-local Hamiltonian. -/
def onsitePart (u : PathShell n) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  ∑ sq : Fin (n + 2) × Fin 3,
    ((u (Sum.inl sq) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord sq.1 sq.2)

/-- The interaction across one edge, as an operator on the whole register. -/
def edgePart (u : PathShell n) (e : Fin (n + 1)) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  ∑ ab : Fin 3 × Fin 3, ((u (Sum.inr (e, ab)) : ℝ) : ℂ) • finitePauliMatrix (couplingWord e ab)

/-- **`(1)`.**  The path-local Hamiltonian assembled from the shell coordinates. -/
def pathHamiltonian (u : PathShell n) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  onsitePart u + ∑ e : Fin (n + 1), edgePart u e

/-- The path-local Hamiltonian with one edge deleted. -/
def pathHamiltonianCut (u : PathShell n) (e : Fin (n + 1)) :
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ :=
  pathHamiltonian u - edgePart u e

theorem pathHamiltonian_sub_cut (u : PathShell n) (e : Fin (n + 1)) :
    pathHamiltonian u - pathHamiltonianCut u e = edgePart u e := by
  rw [pathHamiltonianCut, sub_sub_cancel]

theorem isSelfAdjoint_pauliCombination {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (P : κ → σ → Option (Fin 3)) (J : κ → ℝ) :
    IsSelfAdjoint (∑ k, ((J k : ℝ) : ℂ) • finitePauliMatrix (P k)) := by
  rw [IsSelfAdjoint, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_smul, RCLike.star_def, Complex.conj_ofReal]
  congr 1
  exact finitePauliMatrix_isHermitian (P k)

theorem isSelfAdjoint_onsitePart (u : PathShell n) : IsSelfAdjoint (onsitePart u) :=
  isSelfAdjoint_pauliCombination (fun sq : Fin (n + 2) × Fin 3 => onsiteWord sq.1 sq.2)
    (fun sq => u (Sum.inl sq))

theorem isSelfAdjoint_edgePart (u : PathShell n) (e : Fin (n + 1)) :
    IsSelfAdjoint (edgePart u e) :=
  isSelfAdjoint_pauliCombination (fun ab : Fin 3 × Fin 3 => couplingWord e ab)
    (fun ab => u (Sum.inr (e, ab)))

theorem isSelfAdjoint_pathHamiltonian (u : PathShell n) : IsSelfAdjoint (pathHamiltonian u) := by
  refine (isSelfAdjoint_onsitePart u).add ?_
  rw [IsSelfAdjoint, star_sum]
  exact Finset.sum_congr rfl fun e _ => isSelfAdjoint_edgePart u e

theorem isSelfAdjoint_pathHamiltonianCut (u : PathShell n) (e : Fin (n + 1)) :
    IsSelfAdjoint (pathHamiltonianCut u e) :=
  (isSelfAdjoint_pathHamiltonian u).sub (isSelfAdjoint_edgePart u e)

/-- **`(19)` on the whole register.**  The deleted edge changes the Hamiltonian by at most three
times the Euclidean norm of its nine coefficients. -/
theorem norm_edgePart_le (u : PathShell n) (e : Fin (n + 1)) :
    ‖edgePart u e‖ ≤ 3 * edgeRho (edgeCoeff u e) := by
  have hcard : Real.sqrt (Fintype.card (Fin 3 × Fin 3) : ℝ) = 3 := by
    rw [show (Fintype.card (Fin 3 × Fin 3) : ℝ) = 3 ^ 2 by simp; norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hbound := l2_opNorm_pauliCombination_le (fun ab : Fin 3 × Fin 3 => couplingWord e ab)
    (fun ab => u (Sum.inr (e, ab)))
  rw [hcard] at hbound
  exact hbound

end Hamiltonian

section DelayFloor

variable {n : ℕ}

/-- The event that the split synthesis cap survives through time `L`. -/
def delayEvent {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (eps : ℝ) (S : ℕ)
    (L : ℝ) : Set (sphere (0 : PathShell n) 1) :=
  {v | ∀ t : ℝ, 0 ≤ t → t ≤ L →
    approxComplexity act chi eps (orbitState (pathHamiltonian (v : PathShell n)) ψ t) ≤ S}

/-- A weak edge keeps the split cap through time `L`. -/
theorem edgeSmall_subset_delayEvent {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta)
    {L : ℝ} (hL : 0 < L) :
    edgeSmall e ((eps - eta) / (3 * L)) ⊆ delayEvent act chi ψ eps S L := by
  intro v hv
  have hrho : edgeRho (edgeCoeff (v : PathShell n) e) ≤ (eps - eta) / (3 * L) := hv
  intro t ht0 htL
  refine approxComplexity_le_of_decoupled act chi (isSelfAdjoint_pathHamiltonian _)
    (isSelfAdjoint_pathHamiltonianCut _ e) hψ (hcert (v : PathShell n)) ht0 ?_
  rw [pathHamiltonian_sub_cut]
  have hnorm : ‖edgePart (v : PathShell n) e‖ ≤ 3 * ((eps - eta) / (3 * L)) :=
    le_trans (norm_edgePart_le _ e) (by linarith)
  have hnn : 0 ≤ ‖edgePart (v : PathShell n) e‖ := norm_nonneg _
  calc t * ‖edgePart (v : PathShell n) e‖ ≤ L * (3 * ((eps - eta) / (3 * L))) := by
        exact mul_le_mul htL hnorm hnn hL.le
    _ = eps - eta := by field_simp

/-- **`(20)`.**  The quenched delay tail of the path-local shell has a ninth-power floor: for a fixed
seed, error margin and synthesis cap, the shell probability that the split cap survives through time
`L` is at least a positive constant times `L ^ (-9)`. -/
theorem exists_delay_floor {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, (eps - eta) / 3 ≤ L →
      c / L ^ 9 ≤ pathShellProb (delayEvent act chi ψ eps S L) := by
  obtain ⟨C, c₀, hc₀, -, -, hlower⟩ := exists_edgeSmall_tail_bounds e
  refine ⟨c₀ * ((eps - eta) / 3) ^ 9, by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) hL
  have hx0 : (0 : ℝ) ≤ (eps - eta) / (3 * L) := by positivity
  have hx1 : (eps - eta) / (3 * L) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (eps - eta) / 3 ≤ L := hL
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 3)).mp this]
  calc c₀ * ((eps - eta) / 3) ^ 9 / L ^ 9
      = c₀ * ((eps - eta) / (3 * L)) ^ 9 := by
        have hL9 : (L : ℝ) ^ 9 ≠ 0 := by positivity
        field_simp
    _ ≤ pathShellProb (edgeSmall e ((eps - eta) / (3 * L))) := hlower _ hx0 hx1
    _ ≤ pathShellProb (delayEvent act chi ψ eps S L) :=
        pathShellProb_mono (edgeSmall_subset_delayEvent act chi ψ hψ e hcert hLpos)

end DelayFloor

end

end GaloisForLFunctions.HTGeometry
