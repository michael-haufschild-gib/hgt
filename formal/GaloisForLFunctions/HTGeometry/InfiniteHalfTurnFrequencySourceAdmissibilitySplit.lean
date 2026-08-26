import GaloisForLFunctions.HTGeometry.FiniteHalfTurnRepairedPacketNoGo
import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace

/-!
# Infinite half-turn frequency source admissibility split

This file closes the remaining universal statements of the corresponding research card.  It
reuses the corpus's arbitrary-measure Stieltjes log-convexity and the exact repaired-frequency
measure laws instead of rebuilding either moment theory or the zero-frequency analysis.
-/

open MeasureTheory Set Filter
open HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Markov/Stieltjes positivity of the repaired sequence forces the exact factorial curvature
lower bound on every positive raw moment. -/
theorem halfTurn_repaired_moment_curvature
    {M U : ℕ → ℝ} {nu : Measure ℝ}
    (hrep : HasStieltjesMoments U nu)
    (hrepair : ∀ k : ℕ, 1 ≤ k →
      U k = M k / (Nat.factorial (2 * k - 1) : ℝ))
    (hMpos : ∀ k : ℕ, 1 ≤ k → 0 < M k)
    (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ) /
        (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) ≤
      M k * M (k + 2) / M (k + 1) ^ 2 := by
  have hlog := adjacentHankel_nonneg_of_hasStieltjesMoments hrep k
  have hk1 : 1 ≤ k + 1 := by omega
  have hk2 : 1 ≤ k + 2 := by omega
  rw [hrepair k hk, hrepair (k + 1) hk1, hrepair (k + 2) hk2] at hlog
  have hMk : 0 < M k := hMpos k hk
  have hMk1 : 0 < M (k + 1) := hMpos (k + 1) hk1
  have hMk2 : 0 < M (k + 2) := hMpos (k + 2) hk2
  have hkpos : 0 < k := hk
  have h2k1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2k2 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  rw [h2k1, h2k2] at hlog
  have hf1 : (Nat.factorial (2 * k + 1) : ℝ) =
      ((2 * k + 1 : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ) *
        (Nat.factorial (2 * k - 1) : ℝ) := by
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, Nat.factorial_succ,
      show 2 * k = (2 * k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hf2 : (Nat.factorial (2 * k + 3) : ℝ) =
      ((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ) *
        ((2 * k + 1 : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ) *
          (Nat.factorial (2 * k - 1) : ℝ) := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, Nat.factorial_succ,
      show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ,
      show 2 * k + 1 = (2 * k) + 1 by omega, Nat.factorial_succ,
      show 2 * k = (2 * k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf1, hf2] at hlog
  field_simp
  field_simp at hlog
  nlinarith

end

end GaloisForLFunctions.HTGeometry
