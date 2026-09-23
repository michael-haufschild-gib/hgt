import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBoundedDyadicHeadReceiver

/-!
# Exact bounded-coefficient receiver on one dyadic start range

Menon's real-start mean square is used on literal dyadic ranges.  This file chooses the shrinking
geometric mesh `epsilon = 1 / K` without replacing the range by an asymptotic surrogate.  Bernoulli's
inequality proves that exactly `K` mesh steps cover every start range with `B + 1 <= 2 A`.

The terminal theorem also performs the harmonic-to-ordinary Abel transfer, retaining both the
bounded-coefficient discretization loss and the exact endpoint loss.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Bernoulli's inequality in the exact form needed by the shrinking receiver mesh. -/
theorem two_le_one_add_inv_nat_pow (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℝ) ≤ (1 + 1 / (K : ℝ)) ^ K := by
  have hKR : (K : ℝ) ≠ 0 := by positivity
  have hnonneg : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (K : ℝ) by linarith) K
  calc
    (2 : ℝ) = 1 + (K : ℝ) * (1 / (K : ℝ)) := by
      field_simp
      norm_num
    _ ≤ (1 + 1 / (K : ℝ)) ^ K := h

/-- The reciprocal-sized harmonic receiver on a literal dyadic start range.  The cover condition
is discharged by the exact `K`-step mesh `1 + 1/K`. -/
theorem dyadicMeanSquare_harmonic_le_menonFinalRange_boundedDyadicHead_two
    {l A B K : ℕ} {W I : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hAB : A ≤ B + 1) (hB : B + 1 ≤ 2 * A)
    (hK : 1 ≤ K) (hW : 0 < W) (hI0 : 0 ≤ I)
    (hM : B + 1 + l < menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1)
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ (2 : ℕ)) ≤ I) :
    dyadicMeanSquare harmonicMoebiusR l A B ≤
      ((A : ℝ) * (1 + 1 / (K : ℝ)) ^ K) *
        ((K : ℝ) * blockCostGC (l : ℝ) (1 / (K : ℝ))
          (1 / ((A + 1 : ℕ) : ℝ))
          (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ (2 : ℕ) * I
            + (4 * menonHarmonicAffineRate A / (Real.pi ^ (2 : ℕ) * W)
              + 4 * menonHarmonicAffineConst A /
                (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))))) := by
  have hcover :
      (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤
        (A : ℝ) * (1 + 1 / (K : ℝ)) ^ K := by
    have hpow := two_le_one_add_inv_nat_pow K hK
    calc
      (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) = ((B + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hAB]
        push_cast
        ring
      _ ≤ ((2 * A : ℕ) : ℝ) := by exact_mod_cast hB
      _ = (A : ℝ) * 2 := by push_cast; ring
      _ ≤ (A : ℝ) * (1 + 1 / (K : ℝ)) ^ K :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg A)
  exact dyadicMeanSquare_harmonic_le_menonFinalRange_boundedDyadicHead
    hl hA hAB (by positivity) hW hI0 hM hcover hHead

/-- Exact terminal harmonic-to-ordinary receiver on one dyadic start range. -/
theorem dyadicMeanSquare_moebius_le_menonFinalRange_boundedDyadicHead_two
    {l A B K : ℕ} {W I : ℝ}
    (hl : 0 < l) (hA : 0 < A) (hAB : A ≤ B + 1) (hB : B + 1 ≤ 2 * A)
    (hK : 1 ≤ K) (hW : 0 < W) (hI0 : 0 ≤ I)
    (hM : B + 1 + l < menonFinalRangeTopNat ((A + 1 : ℕ) : ℝ) + 1)
    (hHead : (∫ w in Set.Icc (-W) W,
      ‖logPoly harmonicMoebiusC (menonFinalRangeShell ((A + 1 : ℕ) : ℝ)) w‖ ^ (2 : ℕ)) ≤ I) :
    dyadicMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) l A B ≤
      2 * (B : ℝ) ^ (2 : ℕ) *
          (((A : ℝ) * (1 + 1 / (K : ℝ)) ^ K) *
            ((K : ℝ) * blockCostGC (l : ℝ) (1 / (K : ℝ))
              (1 / ((A + 1 : ℕ) : ℝ))
              (2 * Real.log (1 + (l : ℝ) / (A : ℝ)) ^ (2 : ℕ) * I
                + (4 * menonHarmonicAffineRate A / (Real.pi ^ (2 : ℕ) * W)
                  + 4 * menonHarmonicAffineConst A /
                    (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ)))))) +
        2 * ((Finset.Icc A B).card : ℝ) *
          ((l : ℝ) ^ (2 : ℕ) / ((A + 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
  have hharmonic :=
    dyadicMeanSquare_harmonic_le_menonFinalRange_boundedDyadicHead_two
      hl hA hAB hB hK hW hI0 hM hHead
  have htransfer := dyadicMeanSquare_moebius_le_harmonic (l := l) (A := A) (B := B) hl
  exact htransfer.trans
    (add_le_add (mul_le_mul_of_nonneg_left hharmonic (by positivity)) le_rfl)

end

end RHTower.Sieve
