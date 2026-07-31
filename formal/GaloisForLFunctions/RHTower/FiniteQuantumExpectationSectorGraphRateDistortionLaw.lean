import GaloisForLFunctions.RHTower.FiniteQuantumExpectationEscapeReturnDichotomyLaw

/-!
# Basis-invariant sector graph recurrence for expectation histories

Energy eigenspaces, rather than basis vectors chosen inside them, are the
physical vertices of a degenerate Hamiltonian.  This file therefore proves
the scalar graph recurrence law for an arbitrary finite sector type `V`.
Its primitive coefficient is one complex number for each ordered pair of
sectors, so no basis internal to a sector occurs in the recurrence theorem.

For a concrete finite-dimensional realization, supplied sector operators
`P E`, state records `rho a`, and observables `observable a` define the
sector coefficient

`trace (P E * rho a * P F * observable a)`.

This coefficient is proved invariant under every simultaneous similarity
change of coordinates.  The file does not assert that the supplied sector
operators exist or are spectral projectors; those are separate physical
input obligations.

Equal Bohr gaps may still cancel in the scalar history.  The theorem remains
valid because it uses the cancellation-resistant `ℓ¹` mass of the invariant
sector coefficients.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Phase attached to one finite energy sector. -/
def finiteQuantumExpectationSectorVertexPhase
    {V : Type*} (t : ℝ) (energy : V → ℝ) (E : V) : ℂ :=
  Complex.exp (Complex.I * (((t * energy E : ℝ) : ℂ)))

/-- Relative phase attached to an ordered pair of finite energy sectors. -/
def finiteQuantumExpectationSectorPairPhase
    {V : Type*} (z : V → ℂ) (E F : V) : ℂ :=
  z E * star (z F)

theorem finiteQuantumExpectationSectorVertexPhase_norm
    {V : Type*} (t : ℝ) (energy : V → ℝ) (E : V) :
    ‖finiteQuantumExpectationSectorVertexPhase t energy E‖ = 1 := by
  rw [finiteQuantumExpectationSectorVertexPhase, Complex.norm_exp]
  simp [Complex.mul_re]

/-- Sector-relative Hamiltonian phase equals the corresponding energy-gap
phase. -/
theorem finiteQuantumExpectationSectorPairPhase_eq_gapPhase
    {V : Type*} (n : ℕ) (energy : V → ℝ) (E F : V) :
    finiteQuantumExpectationSectorPairPhase
        (finiteQuantumExpectationSectorVertexPhase (n : ℝ) energy) E F =
      Complex.exp
        (Complex.I * ((((n : ℝ) * (energy E - energy F) : ℝ) : ℂ))) := by
  rw [finiteQuantumExpectationSectorPairPhase]
  simp only [finiteQuantumExpectationSectorVertexPhase, Complex.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- Scalar expectation history reconstructed from invariant ordered-sector
coefficients. -/
def finiteQuantumExpectationSectorHistory
    {V J : Type*} [Fintype V]
    (z : V → ℂ) (coeff : J → V → V → ℂ) (a : J) : ℂ :=
  ∑ E, ∑ F,
    coeff a E F * finiteQuantumExpectationSectorPairPhase z E F

/-- Initial value of a scalar sector history. -/
def finiteQuantumExpectationSectorInitialValue
    {V J : Type*} [Fintype V]
    (coeff : J → V → V → ℂ) (a : J) : ℂ :=
  ∑ E, ∑ F, coeff a E F

/-- Displacement of one scalar sector history from its initial value. -/
def finiteQuantumExpectationSectorDisplacement
    {V J : Type*} [Fintype V]
    (z : V → ℂ) (coeff : J → V → V → ℂ) (a : J) : ℂ :=
  ∑ E, ∑ F,
    coeff a E F * (finiteQuantumExpectationSectorPairPhase z E F - 1)

/-- The coefficient-level displacement is exactly final history minus
initial history. -/
theorem finiteQuantumExpectationSectorDisplacement_eq_history_sub
    {V J : Type*} [Fintype V]
    (z : V → ℂ) (coeff : J → V → V → ℂ) (a : J) :
    finiteQuantumExpectationSectorDisplacement z coeff a =
      finiteQuantumExpectationSectorHistory z coeff a -
        finiteQuantumExpectationSectorInitialValue coeff a := by
  classical
  unfold finiteQuantumExpectationSectorDisplacement
    finiteQuantumExpectationSectorHistory
    finiteQuantumExpectationSectorInitialValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E _hE
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F _hF
  ring

/-- Weighted sum of absolute scalar-history displacements. -/
def finiteQuantumExpectationSectorTotalDeviation
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (z : V → ℂ)
    (coeff : J → V → V → ℂ) : ℝ :=
  ∑ a, lam a * ‖finiteQuantumExpectationSectorDisplacement z coeff a‖

/-- Aggregate cancellation-resistant coefficient mass on one ordered pair
of energy sectors. -/
def finiteQuantumExpectationSectorUnionCoefficientMass
    {V J : Type*} [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (E F : V) : ℝ :=
  ∑ a, lam a * ‖coeff a E F‖

/-- Directed coefficient mass retained by a chosen sector synchronization
graph. -/
noncomputable def finiteQuantumExpectationSectorSelectedDirectedMass
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ) : ℝ := by
  classical
  exact ∑ E, ∑ F,
    if G.Adj E F
    then finiteQuantumExpectationSectorUnionCoefficientMass lam coeff E F
    else 0

/-- Directed non-loop coefficient mass omitted by a chosen sector
synchronization graph. -/
noncomputable def finiteQuantumExpectationSectorOmittedDirectedMass
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ) : ℝ := by
  classical
  exact ∑ E, ∑ F,
    if E ≠ F ∧ ¬ G.Adj E F
    then finiteQuantumExpectationSectorUnionCoefficientMass lam coeff E F
    else 0

theorem finiteQuantumExpectationSectorUnionCoefficientMass_nonneg
    {V J : Type*} [Fintype J]
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (E F : V) :
    0 ≤ finiteQuantumExpectationSectorUnionCoefficientMass
      lam coeff E F := by
  unfold finiteQuantumExpectationSectorUnionCoefficientMass
  exact Finset.sum_nonneg fun a _ha =>
    mul_nonneg (hlam a) (norm_nonneg _)

/-- Sector-history deviation is bounded by the invariant coefficient
`ℓ¹` phase-chord mass.  Equal-gap cancellation is allowed. -/
theorem finiteQuantumExpectationSectorTotalDeviation_le_phaseMass
    {V J : Type*} [Fintype V] [Fintype J]
    (lam : J → ℝ) (z : V → ℂ)
    (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    finiteQuantumExpectationSectorTotalDeviation lam z coeff ≤
      ∑ E, ∑ F,
        finiteQuantumExpectationSectorUnionCoefficientMass lam coeff E F *
          ‖finiteQuantumExpectationSectorPairPhase z E F - 1‖ := by
  classical
  rw [finiteQuantumExpectationSectorTotalDeviation]
  calc
    (∑ a, lam a *
        ‖finiteQuantumExpectationSectorDisplacement z coeff a‖) ≤
        ∑ a, lam a *
          ∑ E, ∑ F,
            ‖coeff a E F‖ *
              ‖finiteQuantumExpectationSectorPairPhase z E F - 1‖ := by
      apply Finset.sum_le_sum
      intro a _ha
      apply mul_le_mul_of_nonneg_left _ (hlam a)
      unfold finiteQuantumExpectationSectorDisplacement
      calc
        ‖∑ E, ∑ F,
            coeff a E F *
              (finiteQuantumExpectationSectorPairPhase z E F - 1)‖ ≤
            ∑ E, ‖∑ F,
              coeff a E F *
                (finiteQuantumExpectationSectorPairPhase z E F - 1)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ E, ∑ F,
              ‖coeff a E F *
                (finiteQuantumExpectationSectorPairPhase z E F - 1)‖ := by
          apply Finset.sum_le_sum
          intro E _hE
          exact norm_sum_le _ _
        _ = ∑ E, ∑ F,
              ‖coeff a E F‖ *
                ‖finiteQuantumExpectationSectorPairPhase z E F - 1‖ := by
          simp only [norm_mul]
    _ = ∑ E, ∑ F,
          finiteQuantumExpectationSectorUnionCoefficientMass lam coeff E F *
            ‖finiteQuantumExpectationSectorPairPhase z E F - 1‖ := by
      unfold finiteQuantumExpectationSectorUnionCoefficientMass
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _hE
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F _hF
      simp only [mul_assoc]

private theorem finiteQuantumExpectationSectorHamiltonianPhase_chord_le_two
    {V : Type*} (t : ℝ) (energy : V → ℝ) (E F : V) :
    ‖finiteQuantumExpectationSectorPairPhase
        (finiteQuantumExpectationSectorVertexPhase t energy) E F - 1‖ ≤
      2 := by
  calc
    ‖finiteQuantumExpectationSectorPairPhase
        (finiteQuantumExpectationSectorVertexPhase t energy) E F - 1‖ ≤
        ‖finiteQuantumExpectationSectorPairPhase
          (finiteQuantumExpectationSectorVertexPhase t energy) E F‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [finiteQuantumExpectationSectorPairPhase, norm_mul, norm_star,
        finiteQuantumExpectationSectorVertexPhase_norm,
        finiteQuantumExpectationSectorVertexPhase_norm, norm_one]
      norm_num

/--
**Basis-free finite-sector expectation graph rate--distortion law.**

For every finite sector type, every family of invariant ordered-sector
coefficients, every nonnegative history weighting, every real sector-energy
list, every resolution, and every chosen synchronization graph, one positive
integer time before the graph-rank deadline has

`weighted absolute deviation ≤ 2 * omitted ℓ¹ mass
  + 2 * resolution * selected ℓ¹ mass`.
-/
theorem exists_finiteQuantumExpectationSector_graph_rateDistortion
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            (n : ℝ) energy) coeff ≤
        2 * finiteQuantumExpectationSectorOmittedDirectedMass
          G lam coeff +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) *
            finiteQuantumExpectationSectorSelectedDirectedMass
              G lam coeff := by
  classical
  obtain ⟨n, hn0, hnQ, hedge⟩ :=
    exists_graphEdge_phase_approximation G energy Q
  refine ⟨n, hn0, hnQ, ?_⟩
  let δ : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
  let mass : V → V → ℝ :=
    finiteQuantumExpectationSectorUnionCoefficientMass lam coeff
  calc
    finiteQuantumExpectationSectorTotalDeviation lam
        (finiteQuantumExpectationSectorVertexPhase (n : ℝ) energy) coeff ≤
        ∑ E, ∑ F, mass E F *
          ‖finiteQuantumExpectationSectorPairPhase
            (finiteQuantumExpectationSectorVertexPhase
              (n : ℝ) energy) E F - 1‖ :=
      finiteQuantumExpectationSectorTotalDeviation_le_phaseMass
        lam _ coeff hlam
    _ ≤ ∑ E, ∑ F, (
        2 * (if E ≠ F ∧ ¬ G.Adj E F then mass E F else 0) +
          2 * δ * (if G.Adj E F then mass E F else 0)) := by
      apply Finset.sum_le_sum
      intro E _hE
      apply Finset.sum_le_sum
      intro F _hF
      by_cases hEF : G.Adj E F
      · obtain ⟨r, hr⟩ := hedge E F hEF
        have hchord :
            ‖finiteQuantumExpectationSectorPairPhase
                (finiteQuantumExpectationSectorVertexPhase
                  (n : ℝ) energy) E F - 1‖ ≤
              2 * δ := by
          rw [finiteQuantumExpectationSectorPairPhase_eq_gapPhase]
          exact
            (norm_exp_I_mul_real_sub_one_le_mod_two_pi
              ((n : ℝ) * (energy E - energy F)) r).trans
              (by simpa only [δ] using hr)
        simp [hEF]
        simpa only [mass, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hchord
            (finiteQuantumExpectationSectorUnionCoefficientMass_nonneg
              lam coeff hlam E F)
      · by_cases hEq : E = F
        · subst F
          have hunit :
              finiteQuantumExpectationSectorPairPhase
                  (finiteQuantumExpectationSectorVertexPhase
                    (n : ℝ) energy) E E = 1 := by
            rw [finiteQuantumExpectationSectorPairPhase]
            change
              finiteQuantumExpectationSectorVertexPhase
                  (n : ℝ) energy E *
                (starRingEnd ℂ)
                  (finiteQuantumExpectationSectorVertexPhase
                    (n : ℝ) energy E) = 1
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
              finiteQuantumExpectationSectorVertexPhase_norm]
            norm_num
          simp [hunit]
        · have hchord :
              ‖finiteQuantumExpectationSectorPairPhase
                  (finiteQuantumExpectationSectorVertexPhase
                    (n : ℝ) energy) E F - 1‖ ≤ 2 :=
            finiteQuantumExpectationSectorHamiltonianPhase_chord_le_two
              (n : ℝ) energy E F
          simp [hEF, hEq]
          simpa only [mass, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hchord
              (finiteQuantumExpectationSectorUnionCoefficientMass_nonneg
                lam coeff hlam E F)
    _ = 2 * finiteQuantumExpectationSectorOmittedDirectedMass
          G lam coeff +
        2 * (2 * Real.pi / (Q + 1 : ℝ)) *
          finiteQuantumExpectationSectorSelectedDirectedMass
            G lam coeff := by
      dsimp only [δ, mass]
      unfold finiteQuantumExpectationSectorOmittedDirectedMass
        finiteQuantumExpectationSectorSelectedDirectedMass
      rw [Finset.mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro E _hE
      rw [← Finset.sum_add_distrib]

/-- Graph rate--distortion radius for invariant sector expectation
histories. -/
def finiteQuantumExpectationSectorGraphDistortionBudget
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (Q : ℕ) : ℝ :=
  2 * finiteQuantumExpectationSectorOmittedDirectedMass G lam coeff +
    2 * (2 * Real.pi / (Q + 1 : ℝ)) *
      finiteQuantumExpectationSectorSelectedDirectedMass G lam coeff

/-- Scaling sector energies by one physical tick equals evaluating the
original sector energies at the corresponding physical time. -/
theorem finiteQuantumExpectationSectorVertexPhase_scaledEnergy
    {V : Type*} (n : ℕ) (tick : ℝ) (energy : V → ℝ) :
    finiteQuantumExpectationSectorVertexPhase (n : ℝ)
        (fun E => tick * energy E) =
      finiteQuantumExpectationSectorVertexPhase ((n : ℝ) * tick) energy := by
  funext E
  unfold finiteQuantumExpectationSectorVertexPhase
  congr 1
  push_cast
  ring

/-- Once an invariant sector history has exited its graph-distortion
neighborhood, every later positive sampling tick supplies a genuine
post-exit return inside the same neighborhood. -/
theorem exists_finiteQuantumExpectationSector_postExit_graph_rateDistortion
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ)
    (exitTime tick : ℝ)
    (hexitTime : 0 ≤ exitTime) (htick : exitTime < tick)
    (hexit :
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      exitTime < (n : ℝ) * tick ∧
      (n : ℝ) * tick ≤
        (((Q + 1) ^
          (Fintype.card V -
            Nat.card G.ConnectedComponent) : ℕ) : ℝ) * tick ∧
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            ((n : ℝ) * tick) energy) coeff ≤
        finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q := by
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_finiteQuantumExpectationSector_graph_rateDistortion
      G lam coeff hlam (fun E => tick * energy E) Q
  have htick0 : 0 < tick := hexitTime.trans_lt htick
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
  refine ⟨n, hn0, hnQ, ?_, ?_, hexit, ?_⟩
  · calc
      exitTime < tick := htick
      _ = (1 : ℝ) * tick := by ring
      _ ≤ (n : ℝ) * tick := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hn1) htick0.le
  · exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hnQ) htick0.le
  · rw [finiteQuantumExpectationSectorGraphDistortionBudget]
    rw [finiteQuantumExpectationSectorVertexPhase_scaledEnergy] at hreturn
    exact hreturn

/--
**Basis-free sector escape--return dichotomy.**

At every graph resolution, the complete finite sector-history family either
never leaves its graph-distortion neighborhood at any nonnegative time, or
it exits and subsequently returns inside the same neighborhood before the
graph-rank deadline.
-/
theorem finiteQuantumExpectationSector_neverExits_or_postExit_return
    {V J : Type*} [Fintype V] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ) (coeff : J → V → V → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤
        finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ (Q + 1) ^
        (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q <
        finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            exitTime energy) coeff ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^
          (Fintype.card V -
            Nat.card G.ConnectedComponent) : ℕ) : ℝ) *
            (exitTime + guardTime) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            ((n : ℝ) * (exitTime + guardTime)) energy) coeff ≤
        finiteQuantumExpectationSectorGraphDistortionBudget
          G lam coeff Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        finiteQuantumExpectationSectorTotalDeviation lam
            (finiteQuantumExpectationSectorVertexPhase t energy) coeff ≤
          finiteQuantumExpectationSectorGraphDistortionBudget
            G lam coeff Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    have htick : exitTime < exitTime + guardTime := by linarith
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_finiteQuantumExpectationSector_postExit_graph_rateDistortion
        G lam coeff hlam energy Q exitTime
        (exitTime + guardTime) hexitTime htick hexit
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        hpost, hdeadline, hreturn⟩

/-- Sector-block evolution reconstructed from supplied sector operators.
When those operators are the spectral projectors of a Hamiltonian, this is
the usual energy-sector decomposition of unitary evolution. -/
def finiteQuantumExpectationSectorEvolvedMatrix
    {V I : Type*} [Fintype V] [Fintype I]
    (z : V → ℂ) (sectorOperator : V → Matrix I I ℂ)
    (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ E, ∑ F,
    finiteQuantumExpectationSectorPairPhase z E F •
      (sectorOperator E * rho * sectorOperator F)

/-- Basis-free ordered-sector coefficient formed from supplied sector
operators, state records, and observables.  No assertion that `sectorOperator`
is a spectral-projector family is made here. -/
def finiteQuantumExpectationSectorTraceCoefficient
    {V I J : Type*} [Fintype I]
    (sectorOperator : V → Matrix I I ℂ)
    (rho observable : J → Matrix I I ℂ)
    (a : J) (E F : V) : ℂ :=
  (sectorOperator E * rho a * sectorOperator F * observable a).trace

/-- A complete supplied sector family reconstructs every matrix from its
ordered sector blocks.  Orthogonality and idempotence are not needed for this
algebraic identity. -/
theorem sum_finiteQuantumExpectationSectorBlocks_eq
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]
    (sectorOperator : V → Matrix I I ℂ)
    (hcomplete : ∑ E, sectorOperator E = 1)
    (rho : Matrix I I ℂ) :
    (∑ E, ∑ F, sectorOperator E * rho * sectorOperator F) = rho := by
  classical
  calc
    (∑ E, ∑ F, sectorOperator E * rho * sectorOperator F) =
        ∑ E, (sectorOperator E * rho) *
          (∑ F, sectorOperator F) := by
      apply Finset.sum_congr rfl
      intro E _hE
      rw [Finset.mul_sum]
    _ = ∑ E, (sectorOperator E * rho) * 1 := by rw [hcomplete]
    _ = ∑ E, sectorOperator E * rho := by
      apply Finset.sum_congr rfl
      intro E _hE
      rw [Matrix.mul_one]
    _ = (∑ E, sectorOperator E) * rho := by rw [Finset.sum_mul]
    _ = rho := by rw [hcomplete, Matrix.one_mul]

/-- The scalar history built from sector trace coefficients is exactly the
ordinary trace pairing with the sector-evolved matrix. -/
theorem finiteQuantumExpectationSectorHistory_traceCoefficient_eq_trace
    {V I J : Type*} [Fintype V] [Fintype I]
    (z : V → ℂ)
    (sectorOperator : V → Matrix I I ℂ)
    (rho observable : J → Matrix I I ℂ)
    (a : J) :
    finiteQuantumExpectationSectorHistory z
        (finiteQuantumExpectationSectorTraceCoefficient
          sectorOperator rho observable) a =
      (finiteQuantumExpectationSectorEvolvedMatrix z
          sectorOperator (rho a) * observable a).trace := by
  classical
  unfold finiteQuantumExpectationSectorHistory
    finiteQuantumExpectationSectorTraceCoefficient
    finiteQuantumExpectationSectorEvolvedMatrix
  simp_rw [Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro E _hE
  apply Finset.sum_congr rfl
  intro F _hF
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul, mul_comm]

/-- For a complete supplied sector family, the coefficient initial value is
the ordinary unevolved expectation pairing. -/
theorem finiteQuantumExpectationSectorInitialValue_traceCoefficient_eq_trace
    {V I J : Type*} [Fintype V] [Fintype I] [DecidableEq I]
    (sectorOperator : V → Matrix I I ℂ)
    (hcomplete : ∑ E, sectorOperator E = 1)
    (rho observable : J → Matrix I I ℂ)
    (a : J) :
    finiteQuantumExpectationSectorInitialValue
        (finiteQuantumExpectationSectorTraceCoefficient
          sectorOperator rho observable) a =
      (rho a * observable a).trace := by
  classical
  unfold finiteQuantumExpectationSectorInitialValue
    finiteQuantumExpectationSectorTraceCoefficient
  calc
    (∑ E, ∑ F,
        (sectorOperator E * rho a * sectorOperator F *
          observable a).trace) =
        ((∑ E, ∑ F, sectorOperator E * rho a * sectorOperator F) *
          observable a).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro E _hE
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = (rho a * observable a).trace := by
      rw [sum_finiteQuantumExpectationSectorBlocks_eq
        sectorOperator hcomplete (rho a)]

/--
Physical complete-sector identity: scalar displacement of the invariant
sector coefficients equals the change in the ordinary expectation trace of
the sector-evolved matrix.
-/
theorem finiteQuantumExpectationSectorDisplacement_traceCoefficient_eq_trace_sub
    {V I J : Type*} [Fintype V] [Fintype I] [DecidableEq I]
    (z : V → ℂ)
    (sectorOperator : V → Matrix I I ℂ)
    (hcomplete : ∑ E, sectorOperator E = 1)
    (rho observable : J → Matrix I I ℂ)
    (a : J) :
    finiteQuantumExpectationSectorDisplacement z
        (finiteQuantumExpectationSectorTraceCoefficient
          sectorOperator rho observable) a =
      (finiteQuantumExpectationSectorEvolvedMatrix z
          sectorOperator (rho a) * observable a).trace -
        (rho a * observable a).trace := by
  rw [finiteQuantumExpectationSectorDisplacement_eq_history_sub,
    finiteQuantumExpectationSectorHistory_traceCoefficient_eq_trace,
    finiteQuantumExpectationSectorInitialValue_traceCoefficient_eq_trace
      sectorOperator hcomplete]

/--
The sector trace coefficient is invariant under every simultaneous
similarity change of coordinates.  Taking `T = S⁻¹` gives ordinary
basis-change invariance. -/
theorem finiteQuantumExpectationSectorTraceCoefficient_similarityInvariant
    {V I J : Type*} [Fintype I] [DecidableEq I]
    (sectorOperator : V → Matrix I I ℂ)
    (rho observable : J → Matrix I I ℂ)
    (S T : Matrix I I ℂ) (hTS : T * S = 1)
    (a : J) (E F : V) :
    finiteQuantumExpectationSectorTraceCoefficient
        (fun K => S * sectorOperator K * T)
        (fun b => S * rho b * T)
        (fun b => S * observable b * T) a E F =
    finiteQuantumExpectationSectorTraceCoefficient
        sectorOperator rho observable a E F := by
  let X : Matrix I I ℂ :=
    sectorOperator E * rho a * sectorOperator F * observable a
  have hcancel (A : Matrix I I ℂ) : T * (S * A) = A := by
    rw [← Matrix.mul_assoc, hTS, Matrix.one_mul]
  unfold finiteQuantumExpectationSectorTraceCoefficient
  calc
    ((S * sectorOperator E * T) * (S * rho a * T) *
          (S * sectorOperator F * T) * (S * observable a * T)).trace =
        (S * X * T).trace := by
      congr 1
      dsimp only [X]
      simp only [Matrix.mul_assoc, hcancel]
    _ = (T * S * X).trace := Matrix.trace_mul_cycle S X T
    _ = X.trace := by rw [hTS, Matrix.one_mul]
    _ = (sectorOperator E * rho a * sectorOperator F *
          observable a).trace := rfl

/-- Concrete trace-coefficient specialization of the finite-sector graph
rate--distortion law. -/
theorem exists_finiteQuantumExpectationSector_trace_graph_rateDistortion
    {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V)
    (lam : J → ℝ)
    (sectorOperator : V → Matrix I I ℂ)
    (rho observable : J → Matrix I I ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    (energy : V → ℝ) (Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ (Q + 1) ^
        (Fintype.card V - Nat.card G.ConnectedComponent) ∧
      finiteQuantumExpectationSectorTotalDeviation lam
          (finiteQuantumExpectationSectorVertexPhase
            (n : ℝ) energy)
          (finiteQuantumExpectationSectorTraceCoefficient
            sectorOperator rho observable) ≤
        2 * finiteQuantumExpectationSectorOmittedDirectedMass G lam
          (finiteQuantumExpectationSectorTraceCoefficient
            sectorOperator rho observable) +
          2 * (2 * Real.pi / (Q + 1 : ℝ)) *
            finiteQuantumExpectationSectorSelectedDirectedMass G lam
              (finiteQuantumExpectationSectorTraceCoefficient
                sectorOperator rho observable) :=
  exists_finiteQuantumExpectationSector_graph_rateDistortion
    G lam
      (finiteQuantumExpectationSectorTraceCoefficient
        sectorOperator rho observable)
      hlam energy Q

end RHTower
