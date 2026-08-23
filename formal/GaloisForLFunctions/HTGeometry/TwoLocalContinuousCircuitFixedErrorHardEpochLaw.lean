import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness
import GaloisForLFunctions.HTGeometry.TwoLocalExactComplexityFull
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-!
# A fixed-error continuous-circuit hard epoch for an ordinary static two-local Hamiltonian

The exact algebraic exceptional-time theorem is upgraded here to operator-norm
fixed-error complexity against the complete continuous `SU(4)` circuit set.
For every register size, one explicit traceless integer two-local Hamiltonian
has a time in `[1,2]` whose endpoint stays a strictly positive operator-norm
distance from every architecture using at most `(2^n - 2) / 16` two-qubit
gates.  Compactness supplies one common positive error after the exact
exceptional times have been removed.

The error is existential and size-dependent; this theorem does not assert a
uniform noise threshold or an ensemble probability.
-/

open Matrix Polynomial Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace TwoQubitCircuit

/-- Architecture locations read in contraction order. -/
def reversePosition {n : ℕ} (C : TwoQubitCircuit n) :
    Fin C.gateCount → Fin n × Fin n :=
  fun k => C.architecture.sites (Fin.rev k)

/-- Lifted gates read in contraction order. -/
def reverseGate {n : ℕ} (C : TwoQubitCircuit n) :
    Fin C.gateCount → Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun k => (C.architecture.gateLift (Fin.rev k) (C.gates (Fin.rev k)) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ)

theorem reverseGate_isTwoQubitGate {n : ℕ} (C : TwoQubitCircuit n) :
    ∀ k, IsTwoQubitGate (C.reversePosition k).1
      (C.reversePosition k).2 (C.reverseGate k) := by
  intro k
  exact twoQubitLift_isTwoQubitGate _ _ _ _

/-- The polynomial-circuit word in contraction order evaluates to the native
architecture endpoint. -/
theorem reverseGate_prod_eq_eval {n : ℕ} (C : TwoQubitCircuit n) :
    (List.ofFn C.reverseGate).prod =
      (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [show List.ofFn C.reverseGate =
      (List.ofFn fun k =>
        (C.architecture.gateLift k (C.gates k) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).reverse by
    change List.ofFn (fun k =>
      (C.architecture.gateLift (Fin.rev k) (C.gates (Fin.rev k)) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) = _
    exact ofFn_comp_finRev (fun k =>
      (C.architecture.gateLift k (C.gates k) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ))]
  simp [TwoQubitCircuit.eval, TwoQubitArchitecture.contraction, Function.comp_def]

end TwoQubitCircuit

/-- Largest convenient integral budget strictly below the `16s < 2^n - 1`
algebraic-dimension threshold. -/
def exponentialContinuousCircuitBudget (m : ℕ) : ℕ :=
  (2 ^ (m + 1) - 2) / 16

theorem exponentialContinuousCircuitBudget_dimension_lt (m : ℕ) :
    exponentialContinuousCircuitBudget m * 16 < 2 ^ (m + 1) - 1 := by
  have hpow : 2 ≤ 2 ^ (m + 1) := by
    have hone : 1 ≤ 2 ^ m :=
      (Nat.one_le_iff_ne_zero).mpr (pow_ne_zero m (by omega))
    rw [pow_succ]
    omega
  have hmul := Nat.div_mul_le_self (2 ^ (m + 1) - 2) 16
  unfold exponentialContinuousCircuitBudget
  omega

/-- **Closed fixed-error continuous-circuit hard epoch.**  For every register
size `n = m + 1`, one explicit traceless integer two-local Hamiltonian has an
endpoint in the fixed time window `[1,2]` separated by one positive
operator-norm error from every continuous two-qubit circuit below an
exponential gate budget. -/
theorem exists_twoLocal_fixedError_continuousCircuitHardEpoch (m : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (N : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian),
      0 < N ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ) =
        (N : ℚ) • twoLocalHam
          (TwoLocalWitness.witnessConstant m) 0
          TwoLocalWitness.witnessCoupling u ∧
      ∃ t ∈ Set.Icc (1 : ℝ) 2, ∃ ε : ℝ, 0 < ε ∧
        ∀ C : TwoQubitCircuit (m + 1),
          C.gateCount ≤ exponentialContinuousCircuitBudget m →
          ε ≤ ‖unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t -
            (C.eval : Matrix (Fin (m + 1) → Bool)
              (Fin (m + 1) → Bool) ℂ)‖ := by
  obtain ⟨u, N, Hz, hH, hN, htrace, hlocal, hlaminj, hrigid, hc,
      hexact, hfinite⟩ :=
    TwoLocalWitness.exists_twoLocal_exact_complexity_and_finiteness m 1
  let s := exponentialContinuousCircuitBudget m
  let exceptional : Set ℝ :=
    ⋃ R : Fin (s + 1),
      {t ∈ Set.Icc (1 : ℝ) 2 |
        ∃ (pos : Fin R → Fin (m + 1) × Fin (m + 1))
          (G : Fin R → Matrix (Fin (m + 1) → Bool)
            (Fin (m + 1) → Bool) ℂ),
          (∀ k, TwoQubitCircuit.IsTwoQubitGate
            (pos k).1 (pos k).2 (G k)) ∧
          (List.ofFn G).prod *ᵥ TwoLocalWitness.zeroCubeState ℂ (m + 1) =
            unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ
              TwoLocalWitness.zeroCubeState ℂ (m + 1)}
  have hRdim : ∀ R : Fin (s + 1),
      (R : ℕ) * 16 < 2 ^ (m + 1) - 1 := by
    intro R
    have hR : (R : ℕ) ≤ s := Nat.le_of_lt_succ R.2
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 16 hR)
      (by simpa [s] using exponentialContinuousCircuitBudget_dimension_lt m)
  have hfiniteExceptional : exceptional.Finite := by
    dsimp [exceptional]
    have huniv : (Set.univ : Set (Fin (s + 1))).Finite := Set.toFinite _
    simpa using huniv.biUnion (fun R _ =>
      hfinite R (hRdim R) (Set.Icc (1 : ℝ) 2) isCompact_Icc)
  have hnotSubset : ¬ Set.Icc (1 : ℝ) 2 ⊆ exceptional := by
    intro hsub
    have hinf : exceptional.Infinite :=
      (Set.Icc_infinite (by norm_num)).mono hsub
    exact hinf hfiniteExceptional
  obtain ⟨t, htIcc, htNot⟩ := Set.not_subset.mp hnotSubset
  let U : Matrix.unitaryGroup (Fin (m + 1) → Bool) ℂ :=
    ⟨unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t,
      unitaryEvolution_mem_unitary hH t⟩
  have hUexact : ∀ C : TwoQubitCircuit (m + 1),
      C.gateCount ≤ s → C.eval ≠ U := by
    intro C hC hCU
    apply htNot
    dsimp [exceptional]
    simp only [Set.mem_iUnion]
    let R : Fin (s + 1) :=
      ⟨C.gateCount, Nat.lt_succ_iff.mpr hC⟩
    refine ⟨R, htIcc, C.reversePosition, C.reverseGate,
      C.reverseGate_isTwoQubitGate, ?_⟩
    rw [C.reverseGate_prod_eq_eval, hCU]
    rfl
  obtain ⟨ε, hε, hsep⟩ :=
    TwoQubitArchitecture.exists_positive_operator_error_of_exact_circuit_exclusion hUexact
  refine ⟨u, N, Hz, hH, hN, htrace, hlocal, t, htIcc, ε, hε, ?_⟩
  intro C hC
  simpa [U, norm_sub_rev] using hsep C hC

/-- **Continuous hard epoch.**  The fixed-error hard endpoint persists on a
nonzero time interval for the same static two-local Hamiltonian, against all
continuous two-qubit architectures simultaneously. -/
theorem exists_twoLocal_fixedError_continuousCircuitHardInterval (m : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (N : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian),
      0 < N ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ) =
        (N : ℚ) • twoLocalHam
          (TwoLocalWitness.witnessConstant m) 0
          TwoLocalWitness.witnessCoupling u ∧
      ∃ t ∈ Set.Icc (1 : ℝ) 2, ∃ ε δ : ℝ,
        0 < ε ∧ 0 < δ ∧
        ∀ τ : ℝ, |τ - t| ≤ δ →
          ∀ C : TwoQubitCircuit (m + 1),
            C.gateCount ≤ exponentialContinuousCircuitBudget m →
            ε / 2 ≤ ‖unitaryEvolution (Hz.map (Int.castRingHom ℂ)) τ -
              (C.eval : Matrix (Fin (m + 1) → Bool)
                (Fin (m + 1) → Bool) ℂ)‖ := by
  obtain ⟨u, N, Hz, hH, hN, htrace, hlocal, t, ht, ε, hε, hhard⟩ :=
    exists_twoLocal_fixedError_continuousCircuitHardEpoch m
  let H := Hz.map (Int.castRingHom ℂ)
  let δ := ε / (2 * (‖H‖ + 1))
  have hden : 0 < 2 * (‖H‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨u, N, Hz, hH, hN, htrace, hlocal, t, ht, ε, δ, hε, hδ, ?_⟩
  intro τ hτ C hC
  have hspeed := norm_unitaryEvolution_time_sub_le hH t τ
  have hnormRatio : ‖H‖ / (‖H‖ + 1) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by linarith [norm_nonneg H])
  have hmove : ‖unitaryEvolution H t - unitaryEvolution H τ‖ ≤ ε / 2 := by
    calc
      ‖unitaryEvolution H t - unitaryEvolution H τ‖ ≤ ‖H‖ * |t - τ| := hspeed
      _ = ‖H‖ * |τ - t| := by rw [abs_sub_comm]
      _ ≤ ‖H‖ * δ := mul_le_mul_of_nonneg_left hτ (norm_nonneg H)
      _ = (ε / 2) * (‖H‖ / (‖H‖ + 1)) := by
        dsimp [δ]
        field_simp
      _ ≤ ε / 2 := by
        simpa using mul_le_mul_of_nonneg_left hnormRatio (div_nonneg hε.le (by norm_num))
  have hcenter := hhard C hC
  have htriangle :
      ‖unitaryEvolution H t -
          (C.eval : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ)‖ ≤
        ‖unitaryEvolution H t - unitaryEvolution H τ‖ +
          ‖unitaryEvolution H τ -
            (C.eval : Matrix (Fin (m + 1) → Bool)
              (Fin (m + 1) → Bool) ℂ)‖ := by
    calc
      ‖unitaryEvolution H t -
          (C.eval : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ)‖ =
        ‖(unitaryEvolution H t - unitaryEvolution H τ) +
          (unitaryEvolution H τ -
            (C.eval : Matrix (Fin (m + 1) → Bool)
              (Fin (m + 1) → Bool) ℂ))‖ := by
          congr 1
          abel
      _ ≤ _ := norm_add_le _ _
  dsimp [H] at hmove hcenter htriangle ⊢
  linarith

end

end GaloisForLFunctions.HTGeometry
