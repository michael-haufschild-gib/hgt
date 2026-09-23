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
      M k * M (k + 2) / M (k + 1) ^ (2 : ℕ) := by
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

/-- The curvature obstruction has exact asymptotic constant `2`, stated in `EReal` so no
extraneous boundedness hypothesis is needed. -/
theorem two_le_limsup_halfTurn_rawMoment_curvature
    {M U : ℕ → ℝ} {nu : Measure ℝ}
    (hrep : HasStieltjesMoments U nu)
    (hrepair : ∀ k : ℕ, 1 ≤ k →
      U k = M k / (Nat.factorial (2 * k - 1) : ℝ))
    (hMpos : ∀ k : ℕ, 1 ≤ k → 0 < M k) :
    (2 : EReal) ≤ Filter.limsup
      (fun k : ℕ =>
        (((k : ℝ) * (M k * M (k + 2) / M (k + 1) ^ (2 : ℕ) - 1) : ℝ) : EReal))
      atTop := by
  apply Filter.le_limsup_of_frequently_le'
  apply (eventually_ge_atTop (1 : ℕ)).frequently.mono
  intro k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio := halfTurn_repaired_moment_curvature hrep hrepair hMpos k hk
  have hthreshold :
      (2 : ℝ) ≤ (k : ℝ) *
        (((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 3 : ℕ) : ℝ) /
          (((2 * k : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ)) - 1) := by
    push_cast
    field_simp
    nlinarith
  have hsub := sub_le_sub_right hratio 1
  have hmul := mul_le_mul_of_nonneg_left hsub (le_of_lt hkpos)
  change ((2 : ℝ) : EReal) ≤
    ((k : ℝ) * (M k * M (k + 2) / M (k + 1) ^ (2 : ℕ) - 1) : ℝ)
  exact EReal.coe_le_coe (hthreshold.trans hmul)

/-- Therefore a raw moment law whose normalized curvature has extended limsup below `2` cannot
admit a Stieltjes half-turn repair. -/
theorem not_limsup_halfTurn_rawMoment_curvature_lt_two
    {M U : ℕ → ℝ} {nu : Measure ℝ}
    (hrep : HasStieltjesMoments U nu)
    (hrepair : ∀ k : ℕ, 1 ≤ k →
      U k = M k / (Nat.factorial (2 * k - 1) : ℝ))
    (hMpos : ∀ k : ℕ, 1 ≤ k → 0 < M k) :
    ¬ Filter.limsup
        (fun k : ℕ =>
          (((k : ℝ) * (M k * M (k + 2) / M (k + 1) ^ (2 : ℕ) - 1) : ℝ) : EReal))
        atTop < (2 : EReal) := by
  exact not_lt_of_ge (two_le_limsup_halfTurn_rawMoment_curvature hrep hrepair hMpos)

end

end GaloisForLFunctions.HTGeometry
