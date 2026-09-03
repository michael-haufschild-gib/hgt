import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareGeneric
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowBridge

/-!
# Menon's harmonic shell at the integer-start receiver

The generic Gallagher receiver expects coefficients on `Icc 1 M`, while Menon's harmonic
factorization lives on the dyadic shell `[A+1, floor (3(A+1))]`.  Extending the harmonic Möbius
coefficient by zero below `A+1` makes these polynomials literally equal and leaves every window
starting in `[A,B]` unchanged.

The terminal theorem feeds the exact Menon shell into the frequency-mean-square receiver.  It is
unconditional infrastructure: its frequency bounds are ordinary finite-integral inequalities,
not an asserted analytic premise or a renamed short-interval conclusion.
-/

namespace RHTower.Sieve

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Harmonic Möbius coefficient, extended by zero below the dyadic start. -/
def localizedHarmonicMoebiusR (A n : ℕ) : ℝ :=
  if A < n then harmonicMoebiusR n else 0

/-- The localized harmonic coefficient has the unit envelope required by Gallagher's receiver. -/
theorem abs_localizedHarmonicMoebiusR_le_one (A n : ℕ) :
    |localizedHarmonicMoebiusR A n| ≤ 1 := by
  rw [localizedHarmonicMoebiusR]
  split_ifs with h
  · have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le A) h
    rw [harmonicMoebiusR, abs_div]
    have hmu := abs_moebius_real_le_one n
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
    rw [hden]
    calc
      |((μ n : ℤ) : ℝ)| / (n : ℝ) ≤ 1 / (n : ℝ) :=
        div_le_div_of_nonneg_right hmu (by positivity)
      _ ≤ 1 := by exact (div_le_one (by positivity)).2 hnR
  · norm_num

/-- Localization changes no positive-length window whose left endpoint is at least `A`. -/
theorem fixedWindowSq_localizedHarmonic_eq (A z l : ℕ) (hl : 1 ≤ l) (hAz : A ≤ z) :
    fixedWindowSq (localizedHarmonicMoebiusR A) l z =
      fixedWindowSq harmonicMoebiusR l z := by
  rw [fixedWindowSq_eq_sq_sum _ hl, fixedWindowSq_eq_sq_sum _ hl]
  apply congrArg (fun x : ℝ => x ^ 2)
  apply Finset.sum_congr rfl
  intro n hn
  rw [localizedHarmonicMoebiusR, if_pos
    (lt_of_le_of_lt hAz (Finset.mem_Ioc.1 hn).1)]

/-- Localization changes no dyadic mean square on starts `[A,B]`. -/
theorem dyadicMeanSquare_localizedHarmonic_eq (A B l : ℕ) (hl : 1 ≤ l) :
    dyadicMeanSquare (localizedHarmonicMoebiusR A) l A B =
      dyadicMeanSquare harmonicMoebiusR l A B := by
  rw [dyadicMeanSquare, dyadicMeanSquare]
  apply Finset.sum_congr rfl
  intro z hz
  exact fixedWindowSq_localizedHarmonic_eq A z l hl (Finset.mem_Icc.1 hz).1

/-- Complexification of the real harmonic coefficient is Menon's complex coefficient. -/
theorem ofReal_harmonicMoebiusR_eq_harmonicMoebiusC (n : ℕ) :
    ((harmonicMoebiusR n : ℝ) : ℂ) = harmonicMoebiusC n := by
  rw [harmonicMoebiusR, harmonicMoebiusC]
  push_cast
  rfl

/-- The localized full initial polynomial is exactly Menon's final-range harmonic shell. -/
theorem logPoly_localizedHarmonic_eq_menonFinalRangeShell (A : ℕ) (w : ℝ) :
    logPoly (fun n => ((localizedHarmonicMoebiusR A n : ℝ) : ℂ))
        (Finset.Icc 1 (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ))) w =
      logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w := by
  classical
  have hshell : menonFinalRangeShell ((A + 1 : ℕ) : ℝ) =
      Finset.Icc (A + 1) (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)) := by
    unfold menonFinalRangeShell
    rw [Nat.ceil_natCast]
  rw [hshell, logPoly, logPoly]
  calc
    ∑ n ∈ Finset.Icc 1 (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
        ((localizedHarmonicMoebiusR A n : ℝ) : ℂ) * unitLogPhase w n =
      ∑ n ∈ Finset.Icc (A + 1) (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
        ((localizedHarmonicMoebiusR A n : ℝ) : ℂ) * unitLogPhase w n := by
          symm
          refine Finset.sum_subset (by
            intro n hn
            rw [Finset.mem_Icc] at hn ⊢
            omega) ?_
          intro n hn hnot
          have hnA : ¬ A < n := by
            rw [Finset.mem_Icc] at hn
            rw [Finset.mem_Icc] at hnot
            omega
          rw [localizedHarmonicMoebiusR, if_neg hnA]
          simp
    _ = ∑ n ∈ Finset.Icc (A + 1) (menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ)),
        harmonicMoebiusC n * unitLogPhase w n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [localizedHarmonicMoebiusR, if_pos (by
            rw [Finset.mem_Icc] at hn
            omega), ofReal_harmonicMoebiusR_eq_harmonicMoebiusC]

/-- Menon's exact harmonic shell feeds the generic large-values receiver without adding
coefficients below the dyadic start. -/
theorem dyadicMeanSquare_harmonic_le_menonFinalRange_largeValues
    {l A B K' : ℕ} {ε M₂ W I : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε)
    (hW : 0 < W) (hM₂ : 0 ≤ M₂) (hI0 : 0 ≤ I)
    (hM : B + 1 + l < menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hI : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ 2) ≤ I)
    (h₂ : ∀ w : ℝ,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ 2 ≤ M₂) :
    dyadicMeanSquare harmonicMoebiusR l A B ≤
      ((A : ℝ) * (1 + ε) ^ K') *
        ((K' : ℝ) * blockCostG (l : ℝ) ε
          (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ 2 * I +
            M₂ * (2 / (Real.pi ^ 2 * W)))) := by
  rw [← dyadicMeanSquare_localizedHarmonic_eq A B l hl]
  refine dyadicMeanSquare_le_largeValues (localizedHarmonicMoebiusR A)
    (abs_localizedHarmonicMoebiusR_le_one A) hl hA hAB hε hW hM₂ hI0 hM hcover ?_ ?_
  · simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using hI
  · intro w
    simpa only [logPoly_localizedHarmonic_eq_menonFinalRangeShell] using h₂ w

end

end RHTower.Sieve
