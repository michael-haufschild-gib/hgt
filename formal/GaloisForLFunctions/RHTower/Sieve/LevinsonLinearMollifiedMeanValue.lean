import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedMeanValueIcc
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier

/-!
# Linear-Levinson mollified twisted mean value

The AFE-ready twisted mean-value theorem is specialized to the literal linear mollifier.  Its
coefficient mass is eliminated using the sharp elementary `ell^1 <= 2 sqrt M` bound.
-/

open Finset Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- Twisted mean-value theorem specialized to the literal linear Levinson
mollifier, with its coefficient mass eliminated. -/
theorem integral_levinsonLinearMollified_cdpoly_Icc_error
    (a b : ℕ → ℂ) (L M : ℕ) (sigma : ℝ) (hM : 1 < M)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ∈ Finset.Icc 1 L, ∀ n ∈ Finset.Icc 1 L,
      ‖twistedCoeff a b sigma m n‖ ≤ C)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly a (Finset.Icc 1 L) sigma t *
              (starRingEnd ℂ) (cdpoly b (Finset.Icc 1 L) sigma t)) *
            (levinsonLinearMollifier M t *
              (starRingEnd ℂ) (levinsonLinearMollifier M t))) -
        (U : ℂ) * mollifiedTwistedDiagonalIcc a b
          (levinsonLinearMollifierCoeff M) (levinsonLinearMollifierCoeff M)
          L M sigma‖
      ≤ (4 * (L : ℝ) * C * ((L * M : ℕ) : ℝ) * (1 + Real.log L)) *
          (2 * Real.sqrt M) * (2 * Real.sqrt M) := by
  have hbase := integral_mollified_cdpoly_Icc_error a b
    (levinsonLinearMollifierCoeff M) (levinsonLinearMollifierCoeff M)
    L M sigma hC0 hC T U
  change ‖_‖ ≤ _ at hbase ⊢
  have hmass := sum_norm_levinsonLinearMollifierCoeff_le hM
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖levinsonLinearMollifierCoeff M n‖ := by positivity
  have hprod :
      (∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖) *
          (∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖) ≤
        (2 * Real.sqrt M) * (2 * Real.sqrt M) :=
    mul_le_mul hmass hmass hsum0 (by positivity)
  let E : ℝ := 4 * (L : ℝ) * C * ((L * M : ℕ) : ℝ) * (1 + Real.log L)
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  calc
    ‖_‖ ≤ E *
        (∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖) *
        (∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖) := hbase
    _ = E * ((∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖) *
        (∑ n ∈ Finset.Icc 1 M, ‖levinsonLinearMollifierCoeff M n‖)) := by ring
    _ ≤ E * ((2 * Real.sqrt M) * (2 * Real.sqrt M)) :=
      mul_le_mul_of_nonneg_left hprod hE0
    _ = E * (2 * Real.sqrt M) * (2 * Real.sqrt M) := by ring

end RHTower.Sieve
