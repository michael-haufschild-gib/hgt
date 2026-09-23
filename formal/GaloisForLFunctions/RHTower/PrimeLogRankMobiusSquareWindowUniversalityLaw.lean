import GaloisForLFunctions.RHTower.PrimeLogRankMobiusDistortionUniversalityLaw
import GaloisForLFunctions.RHTower.SquareDilatedMobiusFiniteWindowPrimeMassUniversalityLaw

/-!
# Prime-log rank, Möbius distortion, and square-window universality

At square cutoff `X²`, the prime-square support of the quarter-weighted dilated Möbius carrier is
indexed by exactly the same packet `primesBelow (X+1)` as the free prime-log phase family and the
critical Möbius phase distortion.  This identifies one finite prime packet across algebraic phase
rank, critical Poisson geometry, random multiplicative energy, and deterministic finite-window
energy.
-/

open Complex MeasureTheory intervalIntegral Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- **Prime-log rank/Möbius square-window universality law.**  Every cutoff `X` determines one
prime packet whose logarithms are integer-linearly independent, whose critical Möbius phase
distortion is bounded below by rank per cutoff, and whose square-dilated Möbius realization
simultaneously has exact Steinhaus diagonal and deterministic finite-window prime-mass survival. -/
theorem primeLogRank_mobiusDistortion_sqrtQuarterSquareWindow
    (N : ℕ) (T : ℝ) (hT : 0 < T) :
    LinearIndependent ℤ
        (fun p : ((N + 1).primesBelow : Finset ℕ) => Real.log (p : ℕ)) ∧
      1 + 4 * ((Nat.primeCounting' (N + 1) : ℝ) / (N : ℝ)) ≤
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (N + 1)) ∧
      (∫ ω,
          ‖∑ n ∈ Finset.Icc 1 (N ^ (2 : ℕ)),
            (sqrtQuarterWindowCoeff n : ℂ) * X n ω‖ ^ (2 : ℕ) ∂steinhausMeasure =
        ∑ n ∈ Finset.Icc 1 (N ^ (2 : ℕ)), sqrtQuarterWindowCoeff n ^ (2 : ℕ)) ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) ≤
        ∫ ω,
          ‖∑ n ∈ Finset.Icc 1 (N ^ (2 : ℕ)),
            (sqrtQuarterWindowCoeff n : ℂ) * X n ω‖ ^ (2 : ℕ) ∂steinhausMeasure ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) -
          dpolySincOffDiagonalEnergy
            sqrtQuarterWindowCoeff (Finset.Icc 1 (N ^ (2 : ℕ))) T ≤
        (∫ t in (-T)..T,
          ‖dpoly sqrtQuarterWindowCoeff (Finset.Icc 1 (N ^ (2 : ℕ))) t‖ ^ (2 : ℕ)) / (2 * T) := by
  have hrank := primeLogRank_and_mobiusPhaseDistortion N
  have hwindow :=
    sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound
      (N ^ (2 : ℕ)) T hT
  refine ⟨hrank.1, hrank.2, ?_⟩
  simpa only [pow_two, Nat.sqrt_eq] using hwindow

end

end RHTower
