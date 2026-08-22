import GaloisForLFunctions.HTGeometry.TwoLocalExactComplexityLaw
import GaloisForLFunctions.HTGeometry.TwoLocalCircuitExceptionalTimes

/-!
# The exact-complexity card in full: both equations at one explicit Hamiltonian

Equation `(1)` — every gate factorisation of the orbit at a nonzero algebraic time is long — and
equation `(2)` — the times at which the orbit is reachable by a bounded two-qubit circuit are
finite on every compact set — hold simultaneously for one explicit traceless integer two-local
Hamiltonian.

## Main results

* `exists_twoLocal_exact_complexity_and_finiteness` — **the card's Theorems A and B.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

set_option linter.unusedSectionVars false

noncomputable section

/-- **The card's Theorems A and B at one explicit witness.** -/
theorem exists_twoLocal_exact_complexity_and_finiteness (m q : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (N : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian),
      0 < N ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ)
        = (N : ℚ) • twoLocalHam (witnessConstant m) 0 witnessCoupling u ∧
      Function.Injective hH.eigenvalues ∧
      LinearMap.ker (SpectralExp.relationForm fun i => ((hH.eigenvalues i : ℝ) : ℂ))
        = PermSubspace.constLine (K := ℚ) (ι := (Fin (m + 1) → Bool)) ∧
      (∀ j, finiteComplexInner
          (hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH j)
          (zeroCubeState ℂ (m + 1)) ≠ 0) ∧
      (∀ t : ℝ, t ≠ 0 → IsAlgebraic ℚ ((t : ℝ) : ℂ) →
        ∀ l : List (Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ),
          (∀ M ∈ l, CircuitAdjoin.GeneratedBy (L := ℂ) (↥AlgebraicOrbit.algNum) q M) →
          l.prod *ᵥ zeroCubeState ℂ (m + 1)
            = unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ zeroCubeState ℂ (m + 1) →
          2 ^ (m + 1) - 1 ≤ l.length * q) ∧
      (∀ s : ℕ, s * 16 < 2 ^ (m + 1) - 1 → ∀ S : Set ℝ, IsCompact S →
        {t ∈ S | ∃ (pos : Fin s → Fin (m + 1) × Fin (m + 1))
            (G : Fin s → Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℂ),
            (∀ k, TwoQubitCircuit.IsTwoQubitGate (pos k).1 (pos k).2 (G k)) ∧
            (List.ofFn G).prod *ᵥ zeroCubeState ℂ (m + 1)
              = unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t
                  *ᵥ zeroCubeState ℂ (m + 1)}.Finite) := by
  classical
  obtain ⟨u, N, Hz, hH, hN, htrace, hA, hlaminj, hrigid, hc, hbound⟩ :=
    exists_twoLocal_exact_complexity_law m q
  refine ⟨u, N, Hz, hH, hN, htrace, hA, hlaminj, hrigid, hc, hbound, ?_⟩
  intro s hs S hS
  have hcardcube : Fintype.card (Fin (m + 1) → Bool) = 2 ^ (m + 1) := by simp
  -- the entries of the Hamiltonian are algebraic
  have hHalg : ∀ i j, IsAlgebraic ℚ ((Hz.map (Int.castRingHom ℂ)) i j) := by
    intro i j
    rw [Matrix.map_apply]
    have hcast : (Int.castRingHom ℂ) (Hz i j) = algebraMap ℚ ℂ ((Hz i j : ℤ) : ℚ) := by
      simp
    rw [hcast]
    exact isAlgebraic_algebraMap _
  -- the eigenvalues are algebraic: they are roots of the integer characteristic polynomial
  have hpne : (Hz.charpoly.map (Int.castRingHom ℚ)) ≠ 0 :=
    ((Hz.charpoly_monic).map _).ne_zero
  have hpmapC : (Hz.charpoly.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)
      = (Hz.map (Int.castRingHom ℂ)).charpoly := by
    rw [Polynomial.map_map, ← Matrix.charpoly_map]
    congr 1
  have hlamalg : ∀ i, IsAlgebraic ℚ ((hH.eigenvalues i : ℝ) : ℂ) := by
    intro i
    refine ⟨Hz.charpoly.map (Int.castRingHom ℚ), hpne, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpmapC, hH.charpoly_eq,
      Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
    simp
  -- the all-zero product state is the image of a rational vector
  have hΩ : (fun i => algebraMap ℚ ℂ (zeroCubeState ℚ (m + 1) i)) = zeroCubeState ℂ (m + 1) :=
    funext (map_zeroCubeState (m + 1))
  have hc' : ∀ j, finiteComplexInner
      (hermitianEigenBasis (Hz.map (Int.castRingHom ℂ)) hH j)
      (fun i => algebraMap ℚ ℂ (zeroCubeState ℚ (m + 1) i)) ≠ 0 := by
    intro j
    rw [hΩ]
    exact hc j
  have hs' : s * 16 < Fintype.card (Fin (m + 1) → Bool) - 1 := by
    rw [hcardcube]
    exact hs
  have hfin := AlgebraicOrbit.finite_twoQubit_circuit_times
    (isOrthoEigenBasis_hermitian _ hH) hlaminj hHalg hlamalg hc'
    (fun _ => false) hrigid hs' hS
  rw [hΩ] at hfin
  exact hfin

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
