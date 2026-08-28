import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphMetricEquivalence
import GaloisForLFunctions.HTGeometry.AnchoredPhaseFidelityComparisonLaw
import GaloisForLFunctions.HTGeometry.ReturnTimeThresholdComparisonLaw

/-!
# Exact first-return exponent for a finite quantum observer

An observer sees only phase differences inside its coherence graph.  The graph has one redundant
phase per connected component, so its visible phase capacity is the number of nonroot vertices.
This file constructs a virtual finite spectral packet with exactly those component-relative
frequencies and proves global two-sided comparison between its survival-fidelity deficit and the
physical observer phase energy.  The sharp continuous first-return exponent therefore transfers
without a local-small-angle restriction.

The final theorem in this file isolates the sole arithmetic input: non-very-well-approximability
of the visible relative clock.  A later local-Hamiltonian capstone discharges that input
simultaneously for every finite observer graph.
-/

open scoped BigOperators
open Filter Topology Real

namespace RHTower

noncomputable section

/-- Virtual spectrum consisting of one zero anchor and every observer-visible component-relative
energy.  A common sign is allowed so the first virtual gap can be oriented positively. -/
def observerVirtualEnergy {d e : ℕ} (G : SimpleGraph (Fin d))
    (energy : Fin d → ℝ) (q : Fin (e + 2) ≃ graphNonRoot G)
    (sigma : ℝ) : Fin (e + 3) → ℝ :=
  Fin.cases 0 (fun k => sigma * graphRelativeEnergy G energy (q k).1)

/-- Uniform positive weights on the virtual observer spectrum. -/
def observerVirtualWeight (e : ℕ) : Fin (e + 3) → ℝ :=
  fun _ => 1 / (e + 3 : ℝ)

/-- Schrödinger phase of a finite real energy list. -/
def spectralReturnPhase {D : ℕ} (E : Fin D → ℝ) (t : ℝ) (j : Fin D) : ℂ :=
  Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)

theorem sum_observerVirtualWeight (e : ℕ) :
    ∑ j, observerVirtualWeight e j = 1 := by
  simp [observerVirtualWeight]
  field_simp

theorem observerVirtualWeight_pos (e : ℕ) (j : Fin (e + 3)) :
    0 < observerVirtualWeight e j := by
  simp [observerVirtualWeight]
  positivity

theorem spectralReturnPhase_norm {D : ℕ}
    (E : Fin D → ℝ) (t : ℝ) (j : Fin D) :
    ‖spectralReturnPhase E t j‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase_real
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i j : Fin d) :
    finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase t energy) i j =
      Complex.exp
        (Complex.I * (((t * (energy i - energy j) : ℝ) : ℂ))) := by
  rw [finiteQuantumObserverPhase]
  simp only [finiteObserverHamiltonianVertexPhase, Complex.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

theorem norm_signed_spectralPhase_sub_one_eq
    (sigma t omega : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    ‖Complex.exp (((-(t * (sigma * omega)) : ℝ) : ℂ) * Complex.I) - 1‖ =
      ‖Complex.exp (((t * omega : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have hone : (1 : ℂ) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) := by simp
  rw [hone, GaloisForLFunctions.HTGeometry.norm_expI_sub_expI,
    GaloisForLFunctions.HTGeometry.norm_expI_sub_expI]
  rcases hsigma with rfl | rfl
  · rw [show (-(t * ((1 : ℝ) * omega)) - 0) / 2 = -(t * omega / 2) by ring,
      Real.sin_neg, abs_neg]
    ring_nf
  · congr 3
    ring

/-- Virtual pivot energy is exactly the observer's component-root chord energy, up to the uniform
weight. -/
theorem observerVirtualPivotEnergy_eq_rootChordEnergy
    {d e : ℕ} (G : SimpleGraph (Fin d)) (energy : Fin d → ℝ)
    (q : Fin (e + 2) ≃ graphNonRoot G) (sigma t : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    projectiveWeightedPivotEnergy (observerVirtualWeight e)
        (spectralReturnPhase (observerVirtualEnergy G energy q sigma) t) 0 =
      (1 / (e + 3 : ℝ)) *
        graphRootChordEnergy G
          (finiteObserverHamiltonianVertexPhase t energy) := by
  let z := finiteObserverHamiltonianVertexPhase t energy
  have hterm (k : Fin (e + 2)) :
      ‖spectralReturnPhase (observerVirtualEnergy G energy q sigma) t k.succ -
          spectralReturnPhase (observerVirtualEnergy G energy q sigma) t 0‖ =
        ‖z (q k).1 - z (graphComponentRoot G
          (G.connectedComponentMk (q k).1))‖ := by
    let r := graphComponentRoot G (G.connectedComponentMk (q k).1)
    let omega := graphRelativeEnergy G energy (q k).1
    calc
      ‖spectralReturnPhase (observerVirtualEnergy G energy q sigma) t k.succ -
          spectralReturnPhase (observerVirtualEnergy G energy q sigma) t 0‖ =
          ‖Complex.exp (((-(t * (sigma * omega)) : ℝ) : ℂ) * Complex.I) - 1‖ := by
        simp [spectralReturnPhase, observerVirtualEnergy, omega]
      _ = ‖Complex.exp (((t * omega : ℝ) : ℂ) * Complex.I) - 1‖ :=
        norm_signed_spectralPhase_sub_one_eq sigma t omega hsigma
      _ = ‖finiteQuantumObserverPhase z (q k).1 r - 1‖ := by
        rw [finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase_real]
        congr 2
        dsimp only [omega, r]
        rw [graphRelativeEnergy]
        push_cast
        ring
      _ = ‖z (q k).1 - z r‖ :=
        norm_mul_star_sub_one_eq_norm_sub _ _
          (finiteObserverHamiltonianVertexPhase_norm t energy r)
  rw [projectiveWeightedPivotEnergy, Fin.sum_univ_succ]
  have hzero : observerVirtualWeight e 0 *
      ‖spectralReturnPhase (observerVirtualEnergy G energy q sigma) t 0 -
        spectralReturnPhase (observerVirtualEnergy G energy q sigma) t 0‖ ^ 2 = 0 := by
    simp
  rw [hzero, zero_add]
  simp_rw [hterm]
  simp only [observerVirtualWeight]
  rw [graphRootChordEnergy, ← Finset.mul_sum]
  congr 1
  simpa only [z] using Equiv.sum_comp q
    (fun v : graphNonRoot G =>
      ‖finiteObserverHamiltonianVertexPhase t energy v.1 -
        finiteObserverHamiltonianVertexPhase t energy
          (graphComponentRoot G (G.connectedComponentMk v.1))‖ ^ 2)

theorem observerVirtualFidelityDeficit_pivot_comparable
    {d e : ℕ} (G : SimpleGraph (Fin d)) (energy : Fin d → ℝ)
    (q : Fin (e + 2) ≃ graphNonRoot G) (sigma t : ℝ) :
    (observerVirtualWeight e 0 / 2) *
        projectiveWeightedPivotEnergy (observerVirtualWeight e)
          (spectralReturnPhase (observerVirtualEnergy G energy q sigma) t) 0 ≤
        GaloisForLFunctions.HTGeometry.spectralReturnDeficit
          (observerVirtualEnergy G energy q sigma) (observerVirtualWeight e) t ∧
      GaloisForLFunctions.HTGeometry.spectralReturnDeficit
          (observerVirtualEnergy G energy q sigma) (observerVirtualWeight e) t ≤
        2 * projectiveWeightedPivotEnergy (observerVirtualWeight e)
          (spectralReturnPhase (observerVirtualEnergy G energy q sigma) t) 0 := by
  have h := weightedFidelityDeficit_pivot_comparable
    (observerVirtualWeight e)
    (spectralReturnPhase (observerVirtualEnergy G energy q sigma) t)
    (fun i => (observerVirtualWeight_pos e i).le)
    (sum_observerVirtualWeight e)
    (spectralReturnPhase_norm _ t) 0
  simpa only [GaloisForLFunctions.HTGeometry.spectralReturnDeficit,
    GaloisForLFunctions.HTGeometry.spectralReturnAmplitude,
    projectiveWeightedPhaseAmplitude, spectralReturnPhase] using h

/-- Observer phase energy and virtual survival-fidelity deficit are globally comparable, with
positive constants independent of time. -/
theorem observerPhaseEnergy_virtualFidelity_comparable
    {d e : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (energy : Fin d → ℝ)
    (q : Fin (e + 2) ≃
      graphNonRoot (finiteObserverCoherenceGraph lam block))
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ,
      A * GaloisForLFunctions.HTGeometry.spectralReturnDeficit
          (observerVirtualEnergy (finiteObserverCoherenceGraph lam block)
            energy q sigma) (observerVirtualWeight e) t ≤
        finiteQuantumObserverPhaseEnergy lam
          (finiteObserverHamiltonianVertexPhase t energy) block ∧
      finiteQuantumObserverPhaseEnergy lam
          (finiteObserverHamiltonianVertexPhase t energy) block ≤
        B * GaloisForLFunctions.HTGeometry.spectralReturnDeficit
          (observerVirtualEnergy (finiteObserverCoherenceGraph lam block)
            energy q sigma) (observerVirtualWeight e) t := by
  let G := finiteObserverCoherenceGraph lam block
  obtain ⟨a, b, ha, hb, hmetric⟩ :=
    observerPhaseEnergy_rootChordEnergy_comparable lam block hlam
  let c : ℝ := (observerVirtualWeight e 0 / 2) * (1 / (e + 3 : ℝ))
  let C : ℝ := 2 * (1 / (e + 3 : ℝ))
  have hc : 0 < c := by
    simp only [c, observerVirtualWeight]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨a / C, b / c, div_pos ha hC, div_pos hb hc, ?_⟩
  intro t
  let z := finiteObserverHamiltonianVertexPhase t energy
  have hz : ∀ i, ‖z i‖ = 1 :=
    finiteObserverHamiltonianVertexPhase_norm t energy
  have hm := hmetric z hz
  have hpivot := observerVirtualPivotEnergy_eq_rootChordEnergy
    G energy q sigma t hsigma
  have hf := observerVirtualFidelityDeficit_pivot_comparable
    G energy q sigma t
  let reference := GaloisForLFunctions.HTGeometry.spectralReturnDeficit
    (observerVirtualEnergy G energy q sigma) (observerVirtualWeight e) t
  let root := graphRootChordEnergy G z
  let signal := finiteQuantumObserverPhaseEnergy lam z block
  change projectiveWeightedPivotEnergy (observerVirtualWeight e)
      (spectralReturnPhase (observerVirtualEnergy G energy q sigma) t) 0 =
    (1 / (e + 3 : ℝ)) * root at hpivot
  rw [hpivot] at hf
  have hrootref : c * root ≤ reference ∧ reference ≤ C * root := by
    constructor
    · simpa only [c, root, reference, mul_assoc] using hf.1
    · simpa only [C, root, reference, mul_assoc] using hf.2
  constructor
  · calc
      (a / C) * reference ≤ (a / C) * (C * root) :=
        mul_le_mul_of_nonneg_left hrootref.2 (div_nonneg ha.le hC.le)
      _ = a * root := by field_simp
      _ ≤ signal := hm.1
  · calc
      signal ≤ b * root := hm.2
      _ = (b / c) * (c * root) := by field_simp
      _ ≤ (b / c) * reference :=
        mul_le_mul_of_nonneg_left hrootref.1 (div_nonneg hb.le hc.le)

/-- First return of physical observer phase energy after cutoff `t₀`. -/
def finiteQuantumObserverReturnTime
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (energy : Fin d → ℝ) (t₀ δ : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.scalarSignalReturnTime
    (fun t => finiteQuantumObserverPhaseEnergy lam
      (finiteObserverHamiltonianVertexPhase t energy) block) t₀ δ

/-- **Exact observer first-return exponent under visible-clock extremality.** Graph capacity is
`e+2`; continuous time removes one clock direction and the squared observer metric halves the
remaining exponent. -/
theorem tendsto_log_finiteQuantumObserverReturnTime_of_graphNonVWA
    {d e : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (energy : Fin d → ℝ)
    (q : Fin (e + 2) ≃
      graphNonRoot (finiteObserverCoherenceGraph lam block))
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (hgap : 0 <
      observerVirtualEnergy (finiteObserverCoherenceGraph lam block)
          energy q sigma 1 -
        observerVirtualEnergy (finiteObserverCoherenceGraph lam block)
          energy q sigma 0)
    (hnv : ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
      (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
        (observerVirtualEnergy (finiteObserverCoherenceGraph lam block)
          energy q sigma) 0 1 (fun k => k.succ.succ)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log
          (finiteQuantumObserverReturnTime lam block energy t₀ δ) /
        Real.log (1 / δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((e + 1 : ℕ) : ℝ) / 2)) := by
  let G := finiteObserverCoherenceGraph lam block
  let E := observerVirtualEnergy G energy q sigma
  let p := observerVirtualWeight e
  have hp1 : ∑ j, p j = 1 := sum_observerVirtualWeight e
  have hppos : ∀ j, 0 < p j := observerVirtualWeight_pos e
  have hpnn : ∀ j, 0 ≤ p j := fun j => (hppos j).le
  let c : ℝ := observerVirtualWeight e 0
  have hc : 0 < c := observerVirtualWeight_pos e 0
  have hcp : ∀ j, c ≤ p j := by
    intro j
    rfl
  have href := GaloisForLFunctions.HTGeometry.tendsto_log_fidelityReturnTime
    E p hp1 hppos hc hcp hgap hnv ht₀
  have hneRaw :=
    GaloisForLFunctions.HTGeometry.eventually_fidelityReturnTime_le
      E p hp1 hpnn hgap hnv t₀
  have hne : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (GaloisForLFunctions.HTGeometry.scalarSignalReturnSet
        (GaloisForLFunctions.HTGeometry.spectralReturnDeficit E p) t₀ δ).Nonempty := by
    filter_upwards [hneRaw] with δ hδ
    exact hδ.1
  obtain ⟨A, B, hA, hB, hcompare⟩ :=
    observerPhaseEnergy_virtualFidelity_comparable
      lam block hlam energy q sigma hsigma
  have htransfer :=
    GaloisForLFunctions.HTGeometry.tendsto_log_scalarSignalReturnTime_of_comparable
      (fun t => finiteQuantumObserverPhaseEnergy lam
        (finiteObserverHamiltonianVertexPhase t energy) block)
      (GaloisForLFunctions.HTGeometry.spectralReturnDeficit E p)
      hA hB ht₀ hcompare hne (by
        simpa only [
          GaloisForLFunctions.HTGeometry.scalarSignalReturnTime_spectralReturnDeficit]
          using href)
  simpa only [finiteQuantumObserverReturnTime] using htransfer

end

end RHTower
