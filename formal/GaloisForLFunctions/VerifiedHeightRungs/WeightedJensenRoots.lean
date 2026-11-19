import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters
import GaloisForLFunctions.VerifiedHeightRungs.TheJensenRungAtTheSaddleScale
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# Root counts for weighted unshifted Xi Jensen polynomials

The symmetric zero strip of width `8999/24000` and verified height `67`
certify the unshifted polynomial through degree `31929`. Every positive
integer Euler word has the same splitting guarantee. At higher degrees a
nonreal zero of a filtered polynomial certifies at least the same nonreal
multiplicity in the original polynomial.
-/

open Polynomial FiniteFreeProbability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.VerifiedHeightRungs

/-- The narrower symmetric strip gives the width used in the Jensen sector inequality. -/
private theorem width_bound : zetaZeroWidth ≤ 8999 / 24000 := by
  refine (zetaZeroWidth_le_iff_re_le (by norm_num : (0 : ℝ) ≤ 8999/24000)).2 ?_
  intro ρ hρ
  obtain ⟨hz, hpos, -⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
  have hs := MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip hpos hz
  linarith only [hs.2]

/-- Exact largest degree paid by the narrower strip at the verified height. -/
theorem jensen_sector_at_sixtySeven_iff (d : ℕ) :
    ((d : ℝ)-1) * (8999/24000 : ℝ)^2 ≤ 67^2 ↔ d ≤ 31929 := by
  constructor
  · intro h
    by_contra! hd
    have hn : 31930 ≤ d := by omega
    have h' : (31930 : ℝ) ≤ d := by exact_mod_cast hn
    linarith
  · intro h
    have h' : (d : ℝ) ≤ 31929 := by exact_mod_cast h
    linarith

/-- The unshifted Xi polynomial has only real zeros through degree 31929. -/
theorem jensenNonrealCount_eq_zero_through_31929 (d : Fin 31930) : jensenNonrealCount d.val = 0 := by
  apply jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width (T := 67) (by norm_num)
    HadamardBudget.rhVerifiedThrough_sixtySeven
  have h := (jensen_sector_at_sixtySeven_iff d).2 (by omega)
  rcases le_or_gt ((d.val : ℝ)-1) 0 with hd | hd
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg _)).trans (sq_nonneg _)
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zetaZeroWidth_nonneg width_bound 2) hd.le).trans h

/-- A word's nonreal multiplicity is a lower bound on the actual unshifted Xi count. -/
theorem weightedXiJensen_nonreal_le (w : List ℕ) (d : ℕ) :
    nonrealRootCount (eulerWord w (xiJensenReal d)) ≤ jensenNonrealCount d := by
  rw [jensenNonrealCount_eq]
  exact eulerWord_nonreal_le w _

/-- All positive-integer Euler weights preserve the verified real-root range. -/
theorem weightedXiJensen_splits (w : List ℕ) (d : Fin 31930) :
    (eulerWord w (xiJensenReal d.val)).Splits := by
  have h := weightedXiJensen_nonreal_le w d
  rw [jensenNonrealCount_eq_zero_through_31929 d, nonrealRootCount] at h
  have hc := Polynomial.card_roots' (eulerWord w (xiJensenReal d))
  rw [splits_iff_card_roots]
  omega

#print axioms jensenNonrealCount_eq_zero_through_31929
#print axioms weightedXiJensen_splits

end GaloisForLFunctions.VerifiedHeightRungs
