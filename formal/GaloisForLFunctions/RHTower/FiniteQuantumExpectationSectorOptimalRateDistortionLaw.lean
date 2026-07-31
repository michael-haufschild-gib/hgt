import GaloisForLFunctions.RHTower.FiniteQuantumExpectationSectorGraphRateDistortionLaw

/-!
# Optimal observable recurrence capacity

The graph in the finite-sector recurrence theorem is a compression choice.
This file removes that choice from the final invariant: at fixed phase
resolution `Q` and allowed deviation `ε`, the observable recurrence capacity
is the least graph capacity among all sector graphs whose certified
distortion budget is at most `ε`.

Whenever the target is feasible, the minimum is attained.  The resulting
capacity controls a non-vacuous escape--return alternative at the target
deviation itself.
-/

noncomputable section

namespace RHTower

/-- Number of independent relative sector phases certified by a graph. -/
def finiteQuantumExpectationSectorGraphCapacity
    {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Fintype.card V - Nat.card G.ConnectedComponent

/--
Least graph capacity whose certified sector-history distortion is at most
`ε` at phase resolution `Q`.  The value on an infeasible target is the
standard `Nat.sInf` empty-set value; all operational theorems below carry
an explicit feasibility premise.
-/
def finiteQuantumExpectationSectorOptimalCapacity
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (Q : ℕ) (ε : ℝ) : ℕ :=
  sInf {k : ℕ |
    ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        k = finiteQuantumExpectationSectorGraphCapacity G}

/-- Every feasible distortion target has a graph attaining the optimal
observable recurrence capacity. -/
theorem exists_finiteQuantumExpectationSector_optimalGraph
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (Q : ℕ) (ε : ℝ)
    (hfeasible :
      ∃ G : SimpleGraph V,
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q ≤ ε) :
    ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        finiteQuantumExpectationSectorGraphCapacity G =
          finiteQuantumExpectationSectorOptimalCapacity
            lam coeff Q ε := by
  let S : Set ℕ := {k : ℕ |
    ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        k = finiteQuantumExpectationSectorGraphCapacity G}
  have hS : S.Nonempty := by
    obtain ⟨G, hG⟩ := hfeasible
    exact
      ⟨finiteQuantumExpectationSectorGraphCapacity G,
        G, hG, rfl⟩
  obtain ⟨G, hG, hmin⟩ := Nat.sInf_mem hS
  refine ⟨G, hG, ?_⟩
  simpa only [finiteQuantumExpectationSectorOptimalCapacity, S] using
    hmin.symm

/--
**Optimal capacity--distortion recurrence law.**

At every feasible target deviation, some positive recurrence is certified
before the deadline whose exponent is the least feasible graph capacity.
-/
theorem exists_finiteQuantumExpectationSector_optimalRateDistortion
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ) (ε : ℝ)
    (hfeasible :
      ∃ G : SimpleGraph V,
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q ≤ ε) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        finiteQuantumExpectationSectorOptimalCapacity
          lam coeff Q ε ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            (n : ℝ) energy) coeff ≤ ε := by
  obtain ⟨G, hG, hcapacity⟩ :=
    exists_finiteQuantumExpectationSector_optimalGraph
      lam coeff Q ε hfeasible
  obtain ⟨n, hn0, hnQ, hdev⟩ :=
    exists_finiteQuantumExpectationSector_graph_rateDistortion
      G lam coeff hlam energy Q
  refine ⟨n, hn0, ?_, hdev.trans hG⟩
  rw [← hcapacity]
  exact hnQ

/--
**Optimal observable escape--return law.**

At every feasible target deviation, the full finite sector-history family
either never exits that target at nonnegative times, or an exit is followed
strictly later by a return inside the same target.  The deadline exponent is
the least feasible graph capacity, not a user-selected graph rank.
-/
theorem finiteQuantumExpectationSector_optimal_neverExits_or_postExit_return
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ) (ε : ℝ)
    (hfeasible :
      ∃ G : SimpleGraph V,
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q ≤ ε)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤ ε) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^
        finiteQuantumExpectationSectorOptimalCapacity
          lam coeff Q ε ∧
      ε <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^
          finiteQuantumExpectationSectorOptimalCapacity
            lam coeff Q ε : ℕ) : ℝ) *
            (exitTime + guardTime) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) coeff ≤ ε := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteQuantumExpectationSectorTotalDeviation lam
            (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤ ε
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    obtain ⟨G, hG, hcapacity⟩ :=
      exists_finiteQuantumExpectationSector_optimalGraph
        lam coeff Q ε hfeasible
    have hexitGraph :
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q <
          finiteQuantumExpectationSectorTotalDeviation lam
            (finiteQuantumExpectationSectorVertexPhase
              exitTime energy) coeff :=
      hG.trans_lt hexit
    have htick : exitTime < exitTime + guardTime := by linarith
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_finiteQuantumExpectationSector_postExit_graph_rateDistortion
        G lam coeff hlam energy Q exitTime
        (exitTime + guardTime) hexitTime htick hexitGraph
    refine
      ⟨exitTime, n, hexitTime, hn0, ?_, hexit, hpost, ?_,
        hreturn.trans hG⟩
    · rw [← hcapacity]
      exact hnQ
    · rw [← hcapacity]
      exact hdeadline

/--
Least certified integer recurrence clock after jointly optimizing the phase
resolution and the retained sector graph at target deviation `ε`.
-/
def finiteQuantumExpectationSectorOptimalCertifiedDeadline
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (ε : ℝ) : ℕ :=
  sInf {T : ℕ |
    ∃ Q : ℕ, ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        T = (Q + 1) ^
          finiteQuantumExpectationSectorGraphCapacity G}

/-- Every jointly feasible target has a resolution--graph pair attaining
the least certified recurrence clock. -/
theorem exists_finiteQuantumExpectationSector_optimalCertifiedPair
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (ε : ℝ)
    (hfeasible :
      ∃ Q : ℕ, ∃ G : SimpleGraph V,
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q ≤ ε) :
    ∃ Q : ℕ, ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        (Q + 1) ^
            finiteQuantumExpectationSectorGraphCapacity G =
          finiteQuantumExpectationSectorOptimalCertifiedDeadline
            lam coeff ε := by
  let S : Set ℕ := {T : ℕ |
    ∃ Q : ℕ, ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε ∧
        T = (Q + 1) ^
          finiteQuantumExpectationSectorGraphCapacity G}
  have hS : S.Nonempty := by
    obtain ⟨Q, G, hG⟩ := hfeasible
    exact
      ⟨(Q + 1) ^ finiteQuantumExpectationSectorGraphCapacity G,
        Q, G, hG, rfl⟩
  obtain ⟨Q, G, hG, hmin⟩ := Nat.sInf_mem hS
  refine ⟨Q, G, hG, ?_⟩
  simpa only [finiteQuantumExpectationSectorOptimalCertifiedDeadline, S]
    using hmin.symm

/--
**Jointly optimal observable escape--return law.**

The least certified clock after optimizing both graph and resolution is
attained and controls the same-target post-exit return.
-/
theorem
    finiteQuantumExpectationSector_optimalCertifiedDeadline_neverExits_or_postExit
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (ε : ℝ)
    (hfeasible :
      ∃ Q : ℕ, ∃ G : SimpleGraph V,
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q ≤ ε)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤ ε) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ finiteQuantumExpectationSectorOptimalCertifiedDeadline
        lam coeff ε ∧
      ε <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (finiteQuantumExpectationSectorOptimalCertifiedDeadline
            lam coeff ε : ℝ) * (exitTime + guardTime) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) coeff ≤ ε := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteQuantumExpectationSectorTotalDeviation lam
            (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤ ε
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    obtain ⟨Q, G, hG, hclock⟩ :=
      exists_finiteQuantumExpectationSector_optimalCertifiedPair
        lam coeff ε hfeasible
    have hexitGraph :
        finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q <
          finiteQuantumExpectationSectorTotalDeviation lam
            (finiteQuantumExpectationSectorVertexPhase
              exitTime energy) coeff :=
      hG.trans_lt hexit
    have htick : exitTime < exitTime + guardTime := by linarith
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_finiteQuantumExpectationSector_postExit_graph_rateDistortion
        G lam coeff hlam energy Q exitTime
        (exitTime + guardTime) hexitTime htick hexitGraph
    refine
      ⟨exitTime, n, hexitTime, hn0, ?_, hexit, hpost, ?_,
        hreturn.trans hG⟩
    · rw [← hclock]
      exact hnQ
    · rw [← hclock]
      exact hdeadline

/-- The complete sector graph has no omitted directed coefficient mass. -/
theorem finiteQuantumExpectationSectorOmittedDirectedMass_top
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ) :
    finiteQuantumExpectationSectorOmittedDirectedMass
        (⊤ : SimpleGraph V) lam coeff = 0 := by
  classical
  unfold finiteQuantumExpectationSectorOmittedDirectedMass
  simp

/-- Selected directed coefficient mass is nonnegative for nonnegative
record weights. -/
theorem finiteQuantumExpectationSectorSelectedDirectedMass_nonneg
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    0 ≤ finiteQuantumExpectationSectorSelectedDirectedMass
      G lam coeff := by
  classical
  unfold finiteQuantumExpectationSectorSelectedDirectedMass
  apply Finset.sum_nonneg
  intro E _hE
  apply Finset.sum_nonneg
  intro F _hF
  split_ifs
  · exact
      finiteQuantumExpectationSectorUnionCoefficientMass_nonneg
        lam coeff hlam E F
  · exact le_rfl

/-- Every strictly positive target deviation is jointly feasible: use the
complete sector graph and take phase resolution sufficiently fine. -/
theorem exists_finiteQuantumExpectationSector_feasiblePair
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, ∃ G : SimpleGraph V,
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q ≤ ε := by
  let M :=
    finiteQuantumExpectationSectorSelectedDirectedMass
      (⊤ : SimpleGraph V) lam coeff
  have hM : 0 ≤ M :=
    finiteQuantumExpectationSectorSelectedDirectedMass_nonneg
      (⊤ : SimpleGraph V) lam coeff hlam
  let C : ℝ := 4 * Real.pi * M
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  obtain ⟨Q : ℕ, hQ⟩ := exists_nat_gt (C / ε)
  refine ⟨Q, ⊤, ?_⟩
  rw [finiteQuantumExpectationSectorGraphDistortionBudget,
    finiteQuantumExpectationSectorOmittedDirectedMass_top]
  have hdenom : 0 < (Q + 1 : ℝ) := by positivity
  have hQmul : C < (Q : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hQ
  have hQsucc : (Q : ℝ) * ε < (Q + 1 : ℝ) * ε := by
    nlinarith
  have hCdiv : C / (Q + 1 : ℝ) ≤ ε := by
    apply (div_le_iff₀ hdenom).2
    simpa only [mul_comm] using (hQmul.trans hQsucc).le
  calc
    2 * 0 +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteQuantumExpectationSectorSelectedDirectedMass
            (⊤ : SimpleGraph V) lam coeff =
      C / (Q + 1 : ℝ) := by
        dsimp only [C, M]
        ring
    _ ≤ ε := hCdiv

/--
**Unconditional positive-target optimal recurrence law.**

For every strictly positive deviation target, joint graph--resolution
optimization is feasible and the least certified clock controls a
never-exits or strictly post-exit return alternative.
-/
theorem
    finiteQuantumExpectationSector_positiveTarget_optimal_neverExits_or_postExit
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) {ε : ℝ} (hε : 0 < ε)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤ ε) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ finiteQuantumExpectationSectorOptimalCertifiedDeadline
        lam coeff ε ∧
      ε <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (finiteQuantumExpectationSectorOptimalCertifiedDeadline
            lam coeff ε : ℝ) * (exitTime + guardTime) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) coeff ≤ ε :=
  finiteQuantumExpectationSector_optimalCertifiedDeadline_neverExits_or_postExit
    lam coeff hlam energy ε
      (exists_finiteQuantumExpectationSector_feasiblePair
        lam coeff hlam hε)
      guardTime hguard

end RHTower
