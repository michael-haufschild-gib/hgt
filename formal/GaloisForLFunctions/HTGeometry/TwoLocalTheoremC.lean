import GaloisForLFunctions.HTGeometry.TwoLocalTheoremCWitness
import GaloisForLFunctions.HTGeometry.TwoLocalHardWindowLaw

/-!
# Theorem C of the arithmetic hardness–recurrence card

The selected integer two-local Hamiltonian obeys the arithmetic window law: on every window of the
arithmetic length, a definite fraction of the times carries a state that no member of a prescribed
finite target family approximates.  With the target family taken to be the outputs of all circuits
of a bounded length, that is `(36)`.

## Main results

* `exists_integer_twoLocal_hardWindow` — **Theorem C.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

set_option linter.unusedSectionVars false

noncomputable section

/-- **Theorem C.**  An explicit traceless integer two-local Hamiltonian with symmetric Galois group,
cyclic all-zero product state and spectral collision below `4(2/3)ⁿ`, whose orbit robustly avoids
every finite target family on a definite fraction of every long enough window. -/
theorem exists_integer_twoLocal_hardWindow (m : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (Nn : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian),
      0 < Nn ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ)
        = (Nn : ℚ) • twoLocalHam (witnessConstant m) 0 witnessCoupling u ∧
      Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (2 ^ (m + 1)).factorial ∧
      (∀ j, finiteComplexInner
          (hermitianEigenBasis _ hH j) (Walsh.zeroState (m + 1)) ≠ 0) ∧
      spectralCollision (hermitianEigenBasis _ hH) (Walsh.zeroState (m + 1))
        < 4 * (2 / 3 : ℝ) ^ (m + 1) ∧
      MaximallyProjectiveEnergy hH.eigenvalues ∧
      (∀ (C : Type) (_ : Fintype C) (_ : Nonempty C) (_ : DecidableEq C)
        (Z : C → ((Fin (m + 1) → Bool) → ℂ)),
        (∀ c, finiteComplexInner (Z c) (Z c) = 1) →
        ∀ (N : ℕ) (R ρ T a : ℝ) (r : ℕ),
          (∀ i, |hH.eigenvalues i| ≤ R) → 0 < ρ → ρ ≤ Real.pi →
          0 < 2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R → 0 < T → 0 < a →
          (Fintype.card C : ℝ) * (r.factorial : ℝ)
              * (16 * spectralCollision (hermitianEigenBasis _ hH)
                  (Walsh.zeroState (m + 1)) / a ^ (2 : ℕ)) ^ r < 1 →
          8 * Real.pi * ((2 ^ (m + 1) - 1 : ℕ) : ℝ)
            ≤ ρ * (ρ / (2 * Real.pi)) ^ (2 ^ (m + 1) - 1) * Real.sqrt ((N : ℝ) + 1) →
          8 * ((N : ℝ) + 1) ^ (2 ^ (m + 1) - 1)
            ≤ T * ((2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R)
                ^ ((2 ^ (m + 1)).factorial - 1))⁻¹ →
          ∀ u₀ : ℝ,
            ((ρ / (2 * Real.pi)) ^ (2 ^ (m + 1) - 1) / 2) * T
              ≤ (MeasureTheory.volume ({t : ℝ | ∀ c,
                  finitePureStateFidelity
                    (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ
                      Walsh.zeroState (m + 1)) (Z c) < a + 2 * ρ}
                    ∩ Set.Ioc u₀ (u₀ + T))).toReal) ∧
      (∀ (N : ℕ) (R δ T : ℝ),
        (∀ i, |hH.eigenvalues i| ≤ R) → 0 < δ → δ ≤ Real.pi →
        0 < 2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R → 0 < T →
        8 * Real.pi * ((2 ^ (m + 1) - 1 : ℕ) : ℝ)
          ≤ δ * (δ / (2 * Real.pi)) ^ (2 ^ (m + 1) - 1) * Real.sqrt ((N : ℝ) + 1) →
        8 * ((N : ℝ) + 1) ^ (2 ^ (m + 1) - 1)
          ≤ T * ((2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R)
              ^ ((2 ^ (m + 1)).factorial - 1))⁻¹ →
        ∀ u₀ : ℝ,
          ((δ / (2 * Real.pi)) ^ (2 ^ (m + 1) - 1) / 2) * T
            ≤ (MeasureTheory.volume ({t : ℝ | ∃ β : ℝ,
                ‖(WithLp.toLp 2 (unitaryEvolution (Hz.map (Int.castRingHom ℂ)) t *ᵥ
                    Walsh.zeroState (m + 1))
                    : EuclideanSpace ℂ (Fin (m + 1) → Bool))
                  - Complex.exp ((β : ℂ) * Complex.I) •
                    (WithLp.toLp 2 (Walsh.zeroState (m + 1))
                      : EuclideanSpace ℂ (Fin (m + 1) → Bool))‖ ≤ δ}
                  ∩ Set.Ioc u₀ (u₀ + T))).toReal) := by
  classical
  obtain ⟨u, Nn, Hz, hH, hNn, htr, hA, hgal, hirr, hlaminj, hc, hcoll⟩ :=
    exists_integer_twoLocal_theoremC m
  have hDpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
  have hcard : Fintype.card (Fin (m + 1) → Bool) = (2 ^ (m + 1) - 1) + 1 := by
    have hcc : Fintype.card (Fin (m + 1) → Bool) = 2 ^ (m + 1) := by simp
    rw [hcc]
    omega
  have hgal' : Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal
      = ((2 ^ (m + 1) - 1) + 1).factorial := by
    rw [show (2 ^ (m + 1) - 1) + 1 = 2 ^ (m + 1) from by omega]
    exact hgal
  have hd1 : 1 < (2 ^ (m + 1) - 1) + 1 := by
    have : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hΩ : finiteComplexInner (Walsh.zeroState (m + 1)) (Walsh.zeroState (m + 1)) = 1 := by
    rw [finiteComplexInner, Walsh.zeroState]
    rw [Finset.sum_eq_single (fun _ => false)]
    · rw [Pi.single_eq_same]
      simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  refine ⟨u, Nn, Hz, hH, hNn, htr, hA, hgal, hc, hcoll,
    maximallyProjectiveEnergy_of_integer_matrix hcard Hz hH hirr hgal' hd1 htr, ?_, ?_⟩
  · intro C instF instNE instDE Z hZ N R ρ T a r hRbd hρ hρπ hposR hT ha h22 hNbig hTbig u₀
    have hTbig' : 8 * ((N : ℝ) + 1) ^ (2 ^ (m + 1) - 1)
        ≤ T * ((2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R)
            ^ (((2 ^ (m + 1) - 1) + 1).factorial - 1))⁻¹ := by
      rw [show (2 ^ (m + 1) - 1) + 1 = 2 ^ (m + 1) from by omega]
      exact hTbig
    exact half_mul_le_measureReal_hardWindow_physical hcard Hz hH hirr hgal' hd1 htr hRbd hΩ
      Z hZ hρ hρπ hposR hT ha r h22 hNbig hTbig' u₀
  · intro N R δ T hRbd hδ hδπ hposR hT hNbig hTbig u₀
    have hTbig' : 8 * ((N : ℝ) + 1) ^ (2 ^ (m + 1) - 1)
        ≤ T * ((2 * ((2 ^ (m + 1) - 1 : ℕ) : ℝ) * (N : ℝ) * R)
            ^ (((2 ^ (m + 1) - 1) + 1).factorial - 1))⁻¹ := by
      rw [show (2 ^ (m + 1) - 1) + 1 = 2 ^ (m + 1) from by omega]
      exact hTbig
    exact half_mul_le_measureReal_recurrenceWindow_physical hcard Hz hH hirr hgal' hd1 htr
      hRbd hTbig' hΩ hδ hδπ hposR hT hNbig u₀

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
