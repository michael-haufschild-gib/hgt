import GaloisForLFunctions.HTGeometry.TwoLocalTheoremC
import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw
import GaloisForLFunctions.RHTower.StaticChoiFullStateProjectionLaw

/-!
# Theorem D: the selected two-local Hamiltonian alternates forever on its Choi orbit

The Hamiltonian selected for Theorem C has maximally projective energy, which is precisely the
hypothesis of the corpus's Choi complexity laws.  Its Choi/thermofield-double orbit therefore
alternates forever between operational recurrence to the identity channel and operational
separation from every circuit of bounded word length, with one finite bound on every leg.

## Main results

* `exists_integer_twoLocal_choiAlternation` — **Theorem D.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.TwoLocalWitness

set_option linter.unusedSectionVars false

/-- **Theorem D.**  An explicit traceless integer two-local Hamiltonian whose relabelled spectrum
has maximal projective energy, hence whose Choi orbit alternates forever between `ε`-recurrence to
the identity channel and `ε`-separation from every padded circuit word, with one finite bound on
every leg. -/
theorem exists_integer_twoLocal_choiAlternation (m : ℕ) :
    ∃ (u : Fin (m + 1) → ℚ) (Nn : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ)
      (hH : (Hz.map (Int.castRingHom ℂ)).IsHermitian)
      (energy : Fin ((2 ^ (m + 1) - 1) + 1) → ℝ),
      0 < Nn ∧ Hz.trace = 0 ∧
      Hz.map (Int.castRingHom ℚ)
        = (Nn : ℚ) • twoLocalHam (witnessConstant m) 0 witnessCoupling u ∧
      Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (2 ^ (m + 1)).factorial ∧
      spectralCollision (hermitianEigenBasis _ hH) (Walsh.zeroState (m + 1))
        < 4 * (2 / 3 : ℝ) ^ (m + 1) ∧
      MaximallyProjectiveEnergy energy ∧
      ∀ {gate : Type} [Fintype gate] (s : ℕ)
        (target : PaddedCircuitWord gate s →
          EuclideanSpace ℂ (Fin ((2 ^ (m + 1) - 1) + 1) × Fin ((2 ^ (m + 1) - 1) + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ (identityWord : PaddedCircuitWord gate s),
          target identityWord
            = fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                  (0 : Fin (2 ^ (m + 1) - 1) → UnitAddCircle)) →
          ∀ {ε : ℝ}, 0 < ε →
          (Fintype.card gate : ℝ) ^ (s + 1) *
              ((((2 ^ (m + 1) - 1) + 1 : ℕ) : ℝ)
                * Real.exp ((((2 ^ (m + 1) - 1) + 1 : ℕ) : ℝ) / 2)
                * Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * ε) ^ (2 : ℕ)) / 2)
                    ^ (((2 ^ (m + 1) - 1) + 1 : ℕ) - 1)) < 1 →
          ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
            ∃ tLow ∈ Set.Icc a (a + L),
            ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
            ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
              pureStateTraceDistance
                  (fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                    (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                      (projectivePhysicalPhaseFlow energy tLow)))
                  (fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                    (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                      (0 : Fin (2 ^ (m + 1) - 1) → UnitAddCircle))) < ε ∧
              (∀ w : PaddedCircuitWord gate s,
                ε < pureStateTraceDistance
                  (fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                    (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                      (projectivePhysicalPhaseFlow energy tHigh))) (target w)) ∧
              pureStateTraceDistance
                  (fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                    (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                      (projectivePhysicalPhaseFlow energy tLow')))
                  (fullUniformPhaseChoiVector ((2 ^ (m + 1) - 1) + 1)
                    (zeroAnchoredPhase (2 ^ (m + 1) - 1)
                      (0 : Fin (2 ^ (m + 1) - 1) → UnitAddCircle))) < ε := by
  classical
  obtain ⟨u, Nn, Hz, hH, hNn, htr, hA, hgal, hc, hcoll, hmax, -, -⟩ :=
    TwoLocalWitness.exists_integer_twoLocal_hardWindow m
  have hcard : Fintype.card (Fin (m + 1) → Bool) = (2 ^ (m + 1) - 1) + 1 := by
    have hcc : Fintype.card (Fin (m + 1) → Bool) = 2 ^ (m + 1) := by simp
    rw [hcc]
    have : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    omega
  set eqv : (Fin (m + 1) → Bool) ≃ Fin ((2 ^ (m + 1) - 1) + 1) :=
    Fintype.equivFinOfCardEq hcard with heqv
  refine ⟨u, Nn, Hz, hH, fun j => hH.eigenvalues (eqv.symm j), hNn, htr, hA, hgal, hcoll,
    maximallyProjectiveEnergy_reindex eqv hmax, ?_⟩
  intro gate instG s target htarget identityWord hidentity ε hε hentropy
  exact maximallyProjective_pureChoiComplexity_alternates_syndetically _
    (maximallyProjectiveEnergy_reindex eqv hmax) s target htarget identityWord hidentity hε
    hentropy

end

end RHTower
