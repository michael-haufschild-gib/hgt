import GaloisForLFunctions.RHTower.GaussSampleTranslationL2
import GaloisForLFunctions.RHTower.GaussUniformTranslationL2
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation
import GaloisForLFunctions.HTGeometry.LatticeTailSums

/-!
# The shifted diagonal as a weighted Parseval sum

The normalized shifted diagonal block multiplies the `l`-th Fourier coefficient by the sampled
ratio `‖d_(n+l)‖/‖d_n‖`, so its squared norm is the ratio-weighted coefficient mass.  Away from
the spike `|n+l| < n/2` the ratio is bounded by a constant; on the spike it is bounded by the
square root of the harmonic factor, which is what makes the whole band summable at the linear
rate.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions

noncomputable section

/-- The sampled ratio carried by the normalized shifted diagonal at frequency `l`. -/
def gaussShiftRatio {m : ℕ} (k : Fin m) (p : Nat.Primes) (n l : ℤ) : ℝ :=
  ‖gaussSampleValue k p (n + l)‖ / ‖gaussSampleValue k p n‖

theorem gaussShiftRatio_nonneg {m : ℕ} (k : Fin m) (p : Nat.Primes) (n l : ℤ) :
    0 ≤ gaussShiftRatio k p n l := by
  rw [gaussShiftRatio]
  positivity

/-- The normalized shifted diagonal acts on Fourier coefficients by the sampled ratio. -/
theorem norm_fourierCoeff_gaussShiftedBlockDiag {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℤ) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    ‖fourierCoeff ((gaussShiftedBlockDiag hm k p n v : AddCircle (1 : ℝ) → ℂ)) l‖
      = gaussShiftRatio k p n l * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ := by
  rw [fourierCoeff_gaussShiftedBlockDiag, norm_mul, norm_mul, norm_inv, gaussShiftRatio,
    div_eq_inv_mul, mul_assoc]

/-- **The ratio-weighted Parseval identity.** -/
theorem norm_sq_gaussShiftedBlockDiag_eq_tsum {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℤ) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ENNReal.ofReal (‖gaussShiftedBlockDiag hm k p n v‖ ^ (2 : ℝ))
      = ∑' l : ℤ, ENNReal.ofReal (gaussShiftRatio k p n l ^ 2 *
          ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) := by
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockDiag hm k p n v with hu
  have hcongr : ∀ l : ℤ,
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l‖ ^ (2 : ℝ)
        = gaussShiftRatio k p n l ^ 2 * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2 := by
    intro l
    rw [hu, norm_fourierCoeff_gaussShiftedBlockDiag,
      Real.mul_rpow (gaussShiftRatio_nonneg k p n l) (norm_nonneg _),
      ← Real.rpow_natCast (gaussShiftRatio k p n l) 2,
      ← Real.rpow_natCast (‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖) 2]
    norm_num
  have hsummable : Summable fun l : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr u)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun l => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun l : ℤ =>
      gaussShiftRatio k p n l ^ 2 * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2 :=
    hsummable.congr hcongr
  rw [norm_sq_eq_tsum_fourierCoeff u, tsum_congr hcongr,
    ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) hsummable']

/-! ## The two regimes of the ratio -/

/-- Off the spike the ratio is bounded by a constant depending only on the lattice constant. -/
theorem gaussShiftRatio_sq_le_of_not_spike {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) (hspike : I ≤ 2 * ((I : ℤ) + l).natAbs) :
    gaussShiftRatio k p (I : ℤ) l ^ 2 ≤ 1 + 2 * K := by
  set R : ℝ := gaussShiftRatio k p (I : ℤ) l with hR
  have hR0 : 0 ≤ R := gaussShiftRatio_nonneg k p (I : ℤ) l
  have hbase : R ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm k p hKb I l
  rcases le_or_gt R 1 with hle | hgt
  · nlinarith
  · have hpow : R ^ 2 ≤ R ^ (2 * m) := pow_le_pow_right₀ hgt.le (by omega)
    have hquot : K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) ≤ 2 * K := by
      rcases Nat.eq_zero_or_pos ((I : ℤ) + l).natAbs with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, div_zero]
        positivity
      · have hposR : (0 : ℝ) < (((I : ℤ) + l).natAbs : ℝ) := by exact_mod_cast hpos
        have hI : (I : ℝ) ≤ 2 * (((I : ℤ) + l).natAbs : ℝ) := by exact_mod_cast hspike
        rw [div_le_iff₀ hposR]
        nlinarith
    linarith [hbase, hpow, hquot]

/-- On the spike the ratio is bounded by the square root of the harmonic factor. -/
theorem gaussShiftRatio_sq_le_sqrt {m : ℕ} (hm : 2 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) :
    gaussShiftRatio k p (I : ℤ) l ^ 2
      ≤ 1 + (K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)) ^ (1 / 2 : ℝ) := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm
  set R : ℝ := gaussShiftRatio k p (I : ℤ) l with hR
  have hR0 : 0 ≤ R := gaussShiftRatio_nonneg k p (I : ℤ) l
  have hbase : R ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm1 k p hKb I l
  set Y : ℝ := K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) with hY
  have hY0 : 0 ≤ Y := by
    rw [hY]
    positivity
  have hYrpow : 0 ≤ Y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hY0 _
  rcases le_or_gt R 1 with hle | hgt
  · nlinarith
  · have hpow4 : R ^ 4 ≤ R ^ (2 * m) := pow_le_pow_right₀ hgt.le (by omega)
    have hR4 : R ^ 4 ≤ Y := le_trans hpow4 hbase
    have hstep : (R ^ 2) ^ (2 : ℕ) ≤ Y := by
      rw [← pow_mul]
      exact hR4
    have hmono : ((R ^ 2) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤ Y ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hstep (by norm_num)
    have hsimp : ((R ^ 2) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = R ^ 2 := by
      rw [← Real.rpow_natCast (R ^ 2) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hsimp] at hmono
    linarith

end

end RHTower
