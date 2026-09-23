import GaloisForLFunctions.HTGeometry.FinitePhaseFidelityDispersion
import GaloisForLFunctions.RHTower.PrimeMobiusLoschmidtPurity

/-!
# Prime-squarefree phase fidelity

The Bernoulli squarefree packet underlying the finite prime Möbius transfer has positive normalized
weights and pairwise distinct unit Loschmidt phases.  The general phase-dispersion/fidelity law
therefore applies exactly: its pairwise prime-energy phase dispersion is twice its fidelity
deficit, and that deficit vanishes exactly when the prime aperture is empty.

This is the source consumer missing from Born/Fisher phase blindness.  Born weights remain
unchanged by a phase twist, while the static interferometric overlap detects the nontrivial prime
phase packet.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive Bernoulli weight on the squarefree prime-energy packet. -/
def finitePrimeSquarefreePhaseWeight
    (S : Finset Nat.Primes) (sigma : ℝ) (T : ↥S.powerset) : ℝ :=
  finitePrimeSquarefreeProbability S sigma T.1

/-- Time-one phase overlap of the squarefree prime-energy packet. -/
def finitePrimeSquarefreePhaseOverlap
    (S : Finset Nat.Primes) (sigma : ℝ) : ℂ :=
  HTGeometry.finitePhaseOverlap
    (finitePrimeSquarefreePhaseWeight S sigma)
    (fun T : ↥S.powerset => finitePrimeSquarefreeLoschmidtMode T.1)

/-- Pairwise phase dispersion of the squarefree prime-energy packet. -/
def finitePrimeSquarefreePhaseDispersion
    (S : Finset Nat.Primes) (sigma : ℝ) : ℝ :=
  HTGeometry.finitePhasePairwiseDispersion
    (finitePrimeSquarefreePhaseWeight S sigma)
    (fun T : ↥S.powerset => finitePrimeSquarefreeLoschmidtMode T.1)

/-- The squarefree Bernoulli phase weights have total mass one. -/
theorem sum_finitePrimeSquarefreePhaseWeight
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ T : ↥S.powerset, finitePrimeSquarefreePhaseWeight S sigma T = 1 := by
  rw [Finset.univ_eq_attach]
  calc
    ∑ T ∈ S.powerset.attach, finitePrimeSquarefreePhaseWeight S sigma T =
        ∑ T ∈ S.powerset, finitePrimeSquarefreeProbability S sigma T := by
          simpa [finitePrimeSquarefreePhaseWeight] using
            (Finset.sum_attach S.powerset
              (fun T => finitePrimeSquarefreeProbability S sigma T))
    _ = 1 := sum_finitePrimeSquarefreeProbability S sigma

/-- Every squarefree Bernoulli phase weight is strictly positive. -/
theorem finitePrimeSquarefreePhaseWeight_pos
    (S : Finset Nat.Primes) (sigma : ℝ) (T : ↥S.powerset) :
    0 < finitePrimeSquarefreePhaseWeight S sigma T := by
  unfold finitePrimeSquarefreePhaseWeight finitePrimeSquarefreeProbability
  apply div_pos
  · exact Finset.prod_pos fun p _ => primeSchurWeight_pos sigma p
  · exact Finset.prod_pos fun p _ => by linarith [primeSchurWeight_pos sigma p]

/-- **Prime-squarefree phase value law.**  Pairwise prime-energy phase dispersion is exactly twice
the time-one fidelity deficit. -/
theorem finitePrimeSquarefreePhaseDispersion_eq_two_mul_fidelityDeficit
    (S : Finset Nat.Primes) (sigma : ℝ) :
    finitePrimeSquarefreePhaseDispersion S sigma =
      2 * (1 - ‖finitePrimeSquarefreePhaseOverlap S sigma‖ ^ (2 : ℕ)) := by
  exact HTGeometry.finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
    (finitePrimeSquarefreePhaseWeight S sigma)
    (fun T : ↥S.powerset => finitePrimeSquarefreeLoschmidtMode T.1)
    (sum_finitePrimeSquarefreePhaseWeight S sigma)
    (fun T => finitePrimeSquarefreeLoschmidtMode_norm T.1)

/-- **Faithful aperture criterion.**  The squarefree prime-phase fidelity deficit vanishes exactly
for the empty prime aperture. -/
theorem finitePrimeSquarefreePhase_fidelityDeficit_eq_zero_iff_empty
    (S : Finset Nat.Primes) (sigma : ℝ) :
    1 - ‖finitePrimeSquarefreePhaseOverlap S sigma‖ ^ (2 : ℕ) = 0 ↔ S = ∅ := by
  rw [show (1 - ‖finitePrimeSquarefreePhaseOverlap S sigma‖ ^ (2 : ℕ) = 0 ↔
      ∀ T U : ↥S.powerset,
        finitePrimeSquarefreeLoschmidtMode T.1 =
          finitePrimeSquarefreeLoschmidtMode U.1) from
    HTGeometry.finitePhase_fidelityDeficit_eq_zero_iff
      (finitePrimeSquarefreePhaseWeight S sigma)
      (fun T : ↥S.powerset => finitePrimeSquarefreeLoschmidtMode T.1)
      (sum_finitePrimeSquarefreePhaseWeight S sigma)
      (finitePrimeSquarefreePhaseWeight_pos S sigma)
      (fun T => finitePrimeSquarefreeLoschmidtMode_norm T.1)]
  constructor
  · intro hall
    by_contra hS
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    let T0 : ↥S.powerset := ⟨∅, by simp⟩
    let Tp : ↥S.powerset := ⟨{p}, by simp [hp]⟩
    have hmode := hall T0 Tp
    have hset : (∅ : Finset Nat.Primes) = {p} :=
      finitePrimeSquarefreeLoschmidtMode_injective hmode
    have hpempty : p ∈ (∅ : Finset Nat.Primes) := hset ▸ Finset.mem_singleton_self p
    simp at hpempty
  · intro hS
    subst S
    intro T U
    have hT : T.1 = ∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp T.2)
    have hU : U.1 = ∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp U.2)
    rw [hT, hU]

end

end RHTower
