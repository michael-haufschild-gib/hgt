import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCentralDiscSchedule
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBoundedDyadicSchedule

/-!
# Quantitative Möbius large values on a dyadic start range

The zero-free-region estimate controls Menon's exact harmonic shell on a polylogarithmic
central disc.  Keeping the reciprocal coefficient bound through Gallagher's discretization and
paying the complementary frequencies by the affine mean-value theorem gives a completely
unconditional finite large-values estimate for ordinary Möbius windows.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Menon's finite dyadic large-values estimate, with every scalar exposed.  The theorem has no
analytic premise: the central-disc bound is selected internally from the zero-free region. -/
theorem eventually_dyadicMeanSquare_moebius_le_menonCentral :
    ∀ᶠ A : ℕ in atTop, ∀ (l K : ℕ),
      0 < l → l ≤ A → 1 ≤ K →
      dyadicMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
          l A (2 * A - 1) ≤
        2 * ((2 * A - 1 : ℕ) : ℝ) ^ 2 *
            (((A : ℝ) * (1 + 1 / (K : ℝ)) ^ K) *
              ((K : ℝ) * blockCostGC (l : ℝ) (1 / (K : ℝ))
                (1 / ((A + 1 : ℕ) : ℝ))
                (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ 2 *
                    (Real.log ((A + 1 : ℕ) : ℝ)) ^ (-(80 : ℝ)) +
                  (4 * menonHarmonicAffineRate A /
                      (Real.pi ^ 2 * menonHarmonicCentralRadius ((A + 1 : ℕ) : ℝ)) +
                    4 * menonHarmonicAffineConst A /
                      (3 * Real.pi ^ 2 *
                        menonHarmonicCentralRadius ((A + 1 : ℕ) : ℝ) ^ 2))))) +
          2 * ((Finset.Icc A (2 * A - 1)).card : ℝ) *
            ((l : ℝ) ^ 2 / ((A + 1 : ℕ) : ℝ)) ^ 2 := by
  have hscale : Tendsto (fun A : ℕ => (((A + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hcentral :=
    eventually_integral_central_normSq_menonFinalRangeShell_le_log_rpow_neg
  filter_upwards [hscale.eventually hcentral, eventually_ge_atTop 2] with A hhead hA
  intro l K hl hlA hK
  have hApos : 0 < A := by omega
  have hAB : A ≤ 2 * A - 1 + 1 := by omega
  have hB : 2 * A - 1 + 1 ≤ 2 * A := by omega
  have hW : 0 < menonHarmonicCentralRadius ((A + 1 : ℕ) : ℝ) := by
    rw [menonHarmonicCentralRadius]
    have hlog : 0 < Real.log (((A + 1 : ℕ) : ℝ)) :=
      Real.log_pos (by exact_mod_cast (show 1 < A + 1 by omega))
    positivity
  have hI : 0 ≤ (Real.log ((A + 1 : ℕ) : ℝ)) ^ (-(80 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hM : 2 * A - 1 + 1 + l <
      menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1 := by
    rw [menonFinalRangeTopNat_nat]
    omega
  exact dyadicMeanSquare_moebius_le_menonFinalRange_boundedDyadicHead_two
    hl hApos hAB hB hK hW hI hM hhead

end

end RHTower.Sieve
