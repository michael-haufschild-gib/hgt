import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRateDistortionLaw

/-!
# Scalar expectation-history graph rate--distortion law

A finite scalar expectation history in an energy basis is a finite sum of
pairwise phase characters.  This file treats the coefficient of every
ordered energy pair as arbitrary complex data, so equal Bohr gaps may cancel
in the actual history.  The theorem does not assume that they do not cancel:
it controls the history by the cancellation-resistant `ℓ¹` mass of those
coefficients.

Choosing any synchronization graph gives a deterministic recurrence
deadline with graph-rank exponent.  Coefficients on omitted ordered pairs
enter as an explicit distortion remainder.  This is a direct scalar-history
counterpart of the Hilbert--Schmidt matrix-record law.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Scalar displacement of one finite expectation history from its initial
value under a vertex-phase packet. -/
def finiteQuantumExpectationDisplacement
    {d : ℕ} {J : Type*}
    (z : Fin d → ℂ)
    (coeff : J → Fin d → Fin d → ℂ) (a : J) : ℂ :=
  ∑ i, ∑ j,
    coeff a i j * (finiteQuantumObserverPhase z i j - 1)

/-- Weighted sum of absolute scalar-history displacements. -/
def finiteQuantumExpectationTotalDeviation
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (coeff : J → Fin d → Fin d → ℂ) : ℝ :=
  ∑ a, lam a * ‖finiteQuantumExpectationDisplacement z coeff a‖

/-- Entrywise energy-basis evolution of a matrix under a vertex-phase
packet. -/
def finiteQuantumPhaseConjugatedMatrix
    {d : ℕ} (z : Fin d → ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => finiteQuantumObserverPhase z i j * rho i j

/-- Ordered-pair coefficient of the expectation history
`trace (rho(t) * observable)` in an energy basis. -/
def finiteQuantumStateObservableCoefficient
    {d : ℕ} {J : Type*}
    (rho observable : J → Matrix (Fin d) (Fin d) ℂ)
    (a : J) (i j : Fin d) : ℂ :=
  rho a i j * observable a j i

/-- The abstract scalar displacement is exactly the change in the ordinary
matrix expectation pairing.  Equal energy gaps may cancel inside either
side; no distinct-gap premise is present. -/
theorem finiteQuantumExpectationDisplacement_eq_trace_sub
    {d : ℕ} {J : Type*}
    (z : Fin d → ℂ)
    (rho observable : J → Matrix (Fin d) (Fin d) ℂ)
    (a : J) :
    finiteQuantumExpectationDisplacement z
        (finiteQuantumStateObservableCoefficient rho observable) a =
      (finiteQuantumPhaseConjugatedMatrix z (rho a) *
          observable a).trace -
        (rho a * observable a).trace := by
  classical
  unfold finiteQuantumExpectationDisplacement
    finiteQuantumStateObservableCoefficient
    finiteQuantumPhaseConjugatedMatrix
  change
    (∑ i, ∑ j,
      (rho a i j * observable a j i) *
        (finiteQuantumObserverPhase z i j - 1)) =
      (∑ i, ∑ j,
        finiteQuantumObserverPhase z i j *
          rho a i j * observable a j i) -
        ∑ i, ∑ j, rho a i j * observable a j i
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Aggregate cancellation-resistant coefficient mass on one ordered
energy pair. -/
def finiteExpectationUnionCoefficientMass
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (i j : Fin d) : ℝ :=
  ∑ a, lam a * ‖coeff a i j‖

/-- Directed coefficient mass retained by a chosen synchronization graph. -/
noncomputable def finiteExpectationSelectedDirectedMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ) : ℝ := by
  classical
  exact ∑ i, ∑ j,
    if G.Adj i j
    then finiteExpectationUnionCoefficientMass lam coeff i j
    else 0

/-- Directed non-loop coefficient mass omitted by a chosen graph. -/
noncomputable def finiteExpectationOmittedDirectedMass
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ) : ℝ := by
  classical
  exact ∑ i, ∑ j,
    if i ≠ j ∧ ¬ G.Adj i j
    then finiteExpectationUnionCoefficientMass lam coeff i j
    else 0

theorem finiteExpectationUnionCoefficientMass_nonneg
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (i j : Fin d) :
    0 ≤ finiteExpectationUnionCoefficientMass lam coeff i j := by
  unfold finiteExpectationUnionCoefficientMass
  exact Finset.sum_nonneg fun a _ha =>
    mul_nonneg (hlam a) (norm_nonneg _)

/-- Scalar-history deviation is bounded by the entrywise phase-chord mass.
This bound remains valid when equal-gap contributions cancel. -/
theorem finiteQuantumExpectationTotalDeviation_le_phaseMass
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (coeff : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    finiteQuantumExpectationTotalDeviation lam z coeff ≤
      ∑ i, ∑ j,
        finiteExpectationUnionCoefficientMass lam coeff i j *
          ‖finiteQuantumObserverPhase z i j - 1‖ := by
  classical
  rw [finiteQuantumExpectationTotalDeviation]
  calc
    (∑ a, lam a *
        ‖finiteQuantumExpectationDisplacement z coeff a‖) ≤
        ∑ a, lam a *
          ∑ i, ∑ j,
            ‖coeff a i j‖ *
              ‖finiteQuantumObserverPhase z i j - 1‖ := by
      apply Finset.sum_le_sum
      intro a _ha
      apply mul_le_mul_of_nonneg_left _ (hlam a)
      unfold finiteQuantumExpectationDisplacement
      calc
        ‖∑ i, ∑ j,
            coeff a i j *
              (finiteQuantumObserverPhase z i j - 1)‖ ≤
            ∑ i, ‖∑ j,
              coeff a i j *
                (finiteQuantumObserverPhase z i j - 1)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i, ∑ j,
              ‖coeff a i j *
                (finiteQuantumObserverPhase z i j - 1)‖ := by
          apply Finset.sum_le_sum
          intro i _hi
          exact norm_sum_le _ _
        _ = ∑ i, ∑ j,
              ‖coeff a i j‖ *
                ‖finiteQuantumObserverPhase z i j - 1‖ := by
          simp only [norm_mul]
    _ = ∑ i, ∑ j,
          finiteExpectationUnionCoefficientMass lam coeff i j *
            ‖finiteQuantumObserverPhase z i j - 1‖ := by
      unfold finiteExpectationUnionCoefficientMass
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [mul_assoc]

private theorem finiteExpectationHamiltonianPhase_chord_le_two
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (i j : Fin d) :
    ‖finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase t energy) i j - 1‖ ≤
      2 := by
  calc
    ‖finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase t energy) i j - 1‖ ≤
        ‖finiteQuantumObserverPhase
          (finiteObserverHamiltonianVertexPhase t energy) i j‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [finiteQuantumObserverPhase, norm_mul, norm_star,
        finiteObserverHamiltonianVertexPhase_norm,
        finiteObserverHamiltonianVertexPhase_norm, norm_one]
      norm_num

/--
**Scalar expectation-history graph rate--distortion law.**

For every finite family of scalar phase histories, every nonnegative history
weighting, every real energy list, every resolution, and every chosen
synchronization graph `G`, there is a positive integer time before the
graph-rank deadline at which

`weighted absolute deviation ≤ 2 * omitted ℓ¹ mass
  + 2 * resolution * selected ℓ¹ mass`.

No noncancellation or distinct-gap premise is used.
-/
theorem exists_finiteQuantumExpectation_graph_rateDistortion
    {d : ℕ} {J : Type*} [Fintype J]
    (G : SimpleGraph (Fin d))
    (lam : J → ℝ) (coeff : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : Fin d → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (d - Nat.card G.ConnectedComponent) ∧
      finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) coeff ≤
        2 * finiteExpectationOmittedDirectedMass G lam coeff +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) *
            finiteExpectationSelectedDirectedMass G lam coeff := by
  classical
  obtain ⟨n, hn0, hnQ, hedge⟩ :=
    exists_graphEdge_phase_approximation G energy Q
  refine ⟨n, hn0, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hnQ
  · let δ : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
    let mass : Fin d → Fin d → ℝ :=
      finiteExpectationUnionCoefficientMass lam coeff
    calc
      finiteQuantumExpectationTotalDeviation lam
          (finiteObserverHamiltonianVertexPhase (n : ℝ) energy) coeff ≤
          ∑ i, ∑ j, mass i j *
            ‖finiteQuantumObserverPhase
              (finiteObserverHamiltonianVertexPhase
                (n : ℝ) energy) i j - 1‖ :=
        finiteQuantumExpectationTotalDeviation_le_phaseMass
          lam _ coeff hlam
      _ ≤ ∑ i, ∑ j, (
          2 * (if i ≠ j ∧ ¬ G.Adj i j then mass i j else 0) +
            2 * δ * (if G.Adj i j then mass i j else 0)) := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
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
          simpa only [mass, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hchord
              (finiteExpectationUnionCoefficientMass_nonneg
                lam coeff hlam i j)
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
              finiteExpectationHamiltonianPhase_chord_le_two
                (n : ℝ) energy i j
            simp [hij, hieqj]
            simpa only [mass, mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_left hchord
                (finiteExpectationUnionCoefficientMass_nonneg
                  lam coeff hlam i j)
      _ = 2 * finiteExpectationOmittedDirectedMass G lam coeff +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) *
            finiteExpectationSelectedDirectedMass G lam coeff := by
        dsimp only [δ, mass]
        unfold finiteExpectationOmittedDirectedMass
          finiteExpectationSelectedDirectedMass
        rw [Finset.mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_add_distrib]

end RHTower
