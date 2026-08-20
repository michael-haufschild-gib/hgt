import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# A Gallagher polynomial over an interval is a difference of prefixes

The cofactor blocks of the ladder are intervals `Icc a b`
(`Sieve/TwoSidedCofactorBlock.geomCofactorBlockAt`), whereas the unconditional Möbius bounds are
stated for prefixes `∑_{n ≤ N}`.  The two differ by one subtraction, so any uniform prefix bound
gives the interval bound with a factor two.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The interval is the difference of two prefixes. -/
theorem logPoly_Icc_eq_sub (a : ℕ → ℂ) {lo hi : ℕ} (hlo : 1 ≤ lo) (hhi : lo ≤ hi + 1) (w : ℝ) :
    logPoly a (Finset.Icc lo hi) w
      = logPoly a (Finset.Icc 1 hi) w - logPoly a (Finset.Icc 1 (lo - 1)) w := by
  classical
  have hsub : Finset.Icc 1 (lo - 1) ⊆ Finset.Icc 1 hi := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    omega
  have hdiff : Finset.Icc 1 hi \ Finset.Icc 1 (lo - 1) = Finset.Icc lo hi := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [logPoly, logPoly, logPoly, ← hdiff, Finset.sum_sdiff_eq_sub hsub]

/-- **A uniform prefix bound gives the interval bound.** -/
theorem norm_logPoly_Icc_le_of_prefix (a : ℕ → ℂ) {lo hi : ℕ} (hlo : 1 ≤ lo) (hhi : lo ≤ hi + 1)
    (w : ℝ) {S : ℝ} (hpref : ∀ N : ℕ, ‖logPoly a (Finset.Icc 1 N) w‖ ≤ S) :
    ‖logPoly a (Finset.Icc lo hi) w‖ ≤ 2 * S := by
  rw [logPoly_Icc_eq_sub a hlo hhi w]
  refine le_trans (norm_sub_le _ _) ?_
  linarith [hpref hi, hpref (lo - 1)]

end

end RHTower.Sieve
