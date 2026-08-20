import GaloisForLFunctions.RHTower.Sieve.RamarePartitionedLadder
import GaloisForLFunctions.RHTower.Sieve.RamareCofactorBlock

/-!
# The Ramaré bilinear mean square against a frequency partition

`Sieve/RamareLadderAnnulus.integral_normSq_ramareBilinear_annulus_le` needs one pointwise bound for
each prime block valid on the whole annulus.  Matomäki–Radziwiłł's partition supplies such a bound
only on a measurable part `T` of the window; on the complement the prime block is large by
definition and the roles of the two factors are exchanged.

This is the same statement with the annulus hypothesis split in two: `V j` on `T`, and on the
complement a cofactor bound `Us j` together with a supplied mean square `J j` for the prime block.
The ladder defect is left as a hypothesis, so this module stays off the Route-T stack that
`Sieve/RamareLadderAnnulus` pulls in through its affine-majorant layer; the corpus's
`integral_normSq_ramareLadderError_le_defectSum` discharges it at the call site.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **The Ramaré bilinear mean square over a cut window, against a frequency partition.** -/
theorem integral_normSq_ramareBilinear_annulus_partitioned_le {P : Finset ℕ} (M : ℕ)
    {Q η w₀ W Dfct : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (hw₀ : 0 ≤ w₀) (hwW : w₀ ≤ W)
    {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hErr : (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2) ≤ Dfct)
    {T : Set ℝ} (hTm : MeasurableSet T) (hTs : T ⊆ Set.Icc (-W) W)
    (V U Vlow Us J : ℕ → ℝ) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ T \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hcof : ∀ j ∈ Finset.range L, ∀ w ∈ (Set.Icc (-W) W \ T) \ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ Us j)
    (hJ : ∀ j ∈ Finset.range L,
      (∫ w in (Set.Icc (-W) W \ T) \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2) ≤ J j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
            (V j ^ 2 * ((5 * Real.pi / 2 * W
                  + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                * ((geomCofactorBlock M Q η j).card : ℝ))
              + Us j ^ 2 * J j
              + Vlow j ^ 2 * U j ^ 2 * (2 * w₀))
        + 2 * Dfct := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hbase := integral_normSq_ramareBilinear_le_ladder_error (P := P) M hQ0 hη hL hP (W := W)
  have hsteps : ∑ j ∈ Finset.range L,
      (∫ w in Set.Icc (-W) W,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w
          * logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ ∑ j ∈ Finset.range L,
          (V j ^ 2 * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M Q η j).card : ℝ))
            + Us j ^ 2 * J j
            + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hbounds := geomCofactorBlockAt_bounds (A₀ := 1) (B₀ := M) (by norm_num) hQ0 hη j
    exact integral_normSq_blockProduct_partitioned_le (ramareCofactorCoeff P)
      (norm_ramareCofactorCoeff_le_one P) (geomBlock P Q (1 + η) j)
      (geomCofactorBlock M Q η j) hbounds.1 hbounds.2 hW hw₀ hwW (hV j) (hVlow j) (hU j)
      hTm hTs (hann j hj) (hcof j hj) (hJ j hj) (hlowP j hj) (hlowC j hj)
  have hLnn : (0 : ℝ) ≤ 2 * (L : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsteps hLnn
  linarith [hbase, hmul, hErr]

end

end RHTower.Sieve
