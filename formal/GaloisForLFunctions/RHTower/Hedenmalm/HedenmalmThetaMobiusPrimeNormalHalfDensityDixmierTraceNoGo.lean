import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityWeakSchattenBoundary
import GaloisForLFunctions.RHTower.PrimeDiagonalSingularValues

/-!
# Möbius prime-normal half-density Dixmier-trace no-go

The literal physical half-density has a legal weak-`S₂` diagonal realization, but prime sparsity
makes its ordinary logarithmic Schatten-2 residue vanish on every Xi copy.  This includes
nonneutral copies: a bounded diagonal/Dixmier-trace compensation cannot detect the theta Green
boundary flux.

The proof sharpens the generic weak-ideal estimate.  Truncation in ordered-prime coordinates gives
`a_n(T_q)² ≤ 1/p_n`; reciprocal-prime prefixes are `o(log N)`, so the logarithmically normalized
Schatten-2 energy tends to zero.  Any surviving compensated codiagonal must therefore use genuinely
unbounded or non-diagonal Gamma--theta support/grade transport before taking a trace.
-/

open Complex Filter
open scoped ENNReal NNReal BigOperators Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HTGeometry

private theorem universalCriticalChannelAmplitude_sq_eq_one_div
    (p : Nat.Primes) :
    routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 = 1 / (p : ℝ) := by
  rw [routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
    routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
  simp

/-- Prime-sparse approximation bound for the literal physical half-density diagonal. -/
theorem approxNumber_thetaMobiusPrimeNormalHalfDensityDiagonal_sq_le_primeReciprocal
    (q : XiZeroCopy) (n : ℕ) :
    approxNumber (thetaMobiusPrimeNormalHalfDensityDiagonal q) n ^ 2 ≤
      1 / (nthPrimeSubtype n : ℝ) := by
  let lam := thetaMobiusPrimeNormalHalfDensityDiagonalSymbol q
  let hC := norm_thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_le_one q
  let F := ellTwoDiagonal (equivTruncMultiplier nthPrimeEquiv lam n)
    (norm_equivTruncMultiplier_le nthPrimeEquiv hC n)
  let tail : Nat.Primes → ℂ := fun i =>
    if n ≤ nthPrimeEquiv.symm i then lam i else 0
  let r := routeNGammaSewnUniversalCriticalChannelAmplitude (nthPrimeSubtype n)
  have hr0 : 0 ≤ r := by
    dsimp [r, routeNGammaSewnUniversalCriticalChannelAmplitude]
    exact Real.rpow_nonneg (by exact_mod_cast (nthPrimeSubtype n).2.pos.le) _
  have htail : ∀ i, ‖tail i‖ ≤ r := by
    intro i
    dsimp [tail]
    split_ifs with hi
    · let m := nthPrimeEquiv.symm i
      have hindexNat : (nthPrimeSubtype n : ℕ) ≤ (i : ℕ) := by
        have hm : nthPrimeSubtype m = i := by
          change nthPrimeEquiv (nthPrimeEquiv.symm i) = i
          exact nthPrimeEquiv.apply_symm_apply i
        rw [← hm]
        exact nthPrimeSubtype_strictMono.monotone hi
      have hindex : (nthPrimeSubtype n : ℝ) ≤ (i : ℝ) := by
        exact_mod_cast hindexNat
      have hinv : 1 / (i : ℝ) ≤ 1 / (nthPrimeSubtype n : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast (nthPrimeSubtype n).2.pos) hindex
      have hui0 : 0 ≤ routeNGammaSewnUniversalCriticalChannelAmplitude i := by
        rw [routeNGammaSewnUniversalCriticalChannelAmplitude]
        exact Real.rpow_nonneg (by exact_mod_cast i.2.pos.le) _
      have huTail : routeNGammaSewnUniversalCriticalChannelAmplitude i ≤ r := by
        have hsqi := universalCriticalChannelAmplitude_sq_eq_one_div i
        have hsqn := universalCriticalChannelAmplitude_sq_eq_one_div (nthPrimeSubtype n)
        nlinarith
      calc
        ‖lam i‖ = |thetaMobiusPrimeNormalProfileHalfDensityAmplitude i q| := by
          simp [lam, thetaMobiusPrimeNormalHalfDensityDiagonalSymbol, Real.norm_eq_abs]
        _ ≤ routeNGammaSewnUniversalCriticalChannelAmplitude i :=
          abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_universal i q
        _ ≤ r := huTail
    · simpa using hr0
  have hsub :
      thetaMobiusPrimeNormalHalfDensityDiagonal q - F =
        ellTwoDiagonal tail htail := by
    ext f i
    change lam i * f i - equivTruncMultiplier nthPrimeEquiv lam n i * f i =
      tail i * f i
    dsimp [tail, equivTruncMultiplier]
    by_cases hi : nthPrimeEquiv.symm i < n
    · simp [hi, Nat.not_le.mpr hi]
    · simp [hi, Nat.le_of_not_gt hi]
  have happ : approxNumber (thetaMobiusPrimeNormalHalfDensityDiagonal q) n ≤ r := by
    calc
      approxNumber (thetaMobiusPrimeNormalHalfDensityDiagonal q) n ≤
          ‖thetaMobiusPrimeNormalHalfDensityDiagonal q - F‖ :=
        approxNumber_le _ n _
          (hasRankLE_ellTwoDiagonal_equivTrunc nthPrimeEquiv lam hC n)
      _ = ‖ellTwoDiagonal tail htail‖ := by rw [hsub]
      _ ≤ r := norm_ellTwoDiagonal_le tail htail hr0
  calc
    approxNumber (thetaMobiusPrimeNormalHalfDensityDiagonal q) n ^ 2 ≤ r ^ 2 := by
      nlinarith [approxNumber_nonneg (thetaMobiusPrimeNormalHalfDensityDiagonal q) n]
    _ = 1 / (nthPrimeSubtype n : ℝ) :=
      universalCriticalChannelAmplitude_sq_eq_one_div (nthPrimeSubtype n)

/-- Every Schatten-2 prefix is bounded by the corresponding reciprocal-prime prefix. -/
theorem schattenPowerPartialSum_two_thetaMobiusPrimeNormalHalfDensityDiagonal_le_primeDiagonalSum
    (q : XiZeroCopy) (N : ℕ) :
    schattenPowerPartialSum 2 (thetaMobiusPrimeNormalHalfDensityDiagonal q) N ≤
      primeDiagonalSum N := by
  rw [schattenPowerPartialSum, primeDiagonalSum]
  calc
    (∑ n ∈ Finset.range N,
        approxNumber (thetaMobiusPrimeNormalHalfDensityDiagonal q) n ^ (2 : ℝ)) ≤
        ∑ n ∈ Finset.range N, ((Nat.nth Nat.Prime n : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [Real.rpow_natCast, nthPrimeSubtype, one_div] using
        approxNumber_thetaMobiusPrimeNormalHalfDensityDiagonal_sq_le_primeReciprocal q n
    _ ≤ (∑ n ∈ Finset.range N, ((Nat.nth Nat.Prime n : ℕ) : ℝ)⁻¹) +
        ((Nat.nth Nat.Prime N : ℕ) : ℝ)⁻¹ := by
      apply le_add_of_nonneg_right
      exact inv_nonneg.mpr (by exact_mod_cast
        (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime N).pos.le)
    _ = ∑ n ∈ Finset.range (N + 1), ((Nat.nth Nat.Prime n : ℕ) : ℝ)⁻¹ := by
      rw [Finset.sum_range_succ]

/-- Prime sparsity makes the ordinary logarithmic Schatten-2 residue blind to every physical
half-density boundary, including nonneutral copies. -/
theorem thetaMobiusPrimeNormalHalfDensityDiagonal_hasSchattenLogResidue_two_zero
    (q : XiZeroCopy) :
    HasSchattenLogResidue 2 (thetaMobiusPrimeNormalHalfDensityDiagonal q) 0 := by
  rw [HasSchattenLogResidue]
  apply squeeze_zero'
  · filter_upwards [] with N
    exact div_nonneg (Finset.sum_nonneg fun n _ =>
      Real.rpow_nonneg (approxNumber_nonneg _ _) _) (Real.log_nonneg (by
        show (1 : ℝ) ≤ (N : ℝ) + 1
        have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith))
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hlogN1 : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    have hlogle : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      have hNlt : (N : ℝ) < (N : ℝ) + 1 := by norm_num
      exact (Real.strictMonoOn_log hN0 (lt_trans hN0 hNlt) hNlt).le
    calc
      schattenPowerPartialSum 2 (thetaMobiusPrimeNormalHalfDensityDiagonal q) N /
          Real.log ((N : ℝ) + 1) ≤
          primeDiagonalSum N / Real.log ((N : ℝ) + 1) := by
        exact div_le_div_of_nonneg_right
          (schattenPowerPartialSum_two_thetaMobiusPrimeNormalHalfDensityDiagonal_le_primeDiagonalSum
            q N) hlogN1.le
      _ ≤ primeDiagonalSum N / Real.log (N : ℝ) := by
        exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun n _ => by positivity)
          hlogN hlogle
  · simpa [Nat.cast_add, Nat.cast_one] using tendsto_primeDiagonalSum_div_log

end

end RHTower.HedenmalmThetaSource
