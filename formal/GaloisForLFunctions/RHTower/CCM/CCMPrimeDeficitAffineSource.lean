import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitMobiusCenteredEnergy
import GaloisForLFunctions.RHTower.LogarithmicCoprimeEnergy

/-!
# An exact affine counterterm for the arithmetic deficit source

Subtracting the dilation sum of a known affine profile leaves a uniformly
bounded elementary source. Its literal Möbius inverse reconstructs the
original deficit minus that affine profile. Thus the bounded coprime source
balance has no additional unknown Mertens main channels.

The coprime cross term remains signed. No lower bound for it, bound for the
deficit energy alone, or zero exclusion is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitAffineSlope : ℝ := Real.log (2 * Real.pi)

def ccmPrimeDeficitAffineIntercept : ℝ :=
  Real.eulerMascheroniConstant + 1 - ccmPrimeDeficitAffineSlope

def ccmPrimeDeficitAffineProfile (T : ℝ) : ℝ :=
  ccmPrimeDeficitAffineIntercept + ccmPrimeDeficitAffineSlope * T

def ccmPrimeDeficitAffineSource (T : ℝ) : ℝ :=
  ccmPrimeDeficitDilationSource T - logarithmicDilationSum ccmPrimeDeficitAffineProfile T

def ccmPrimeDeficitAffineReconstruction (T : ℝ) : ℝ :=
  logarithmicMobiusInverse ccmPrimeDeficitAffineSource T

def ccmPrimeDeficitAffineSourceBound : ℝ :=
  7 / 2 + |Real.eulerMascheroniConstant + 1| + |ccmPrimeDeficitAffineIntercept| +
    ccmPrimeDeficitAffineSlope ^ 2 / 2 + 2 * |ccmPrimeDeficitAffineSlope|

theorem ccmPrimeDeficitAffineSourceBound_nonneg : 0 ≤ ccmPrimeDeficitAffineSourceBound := by
  unfold ccmPrimeDeficitAffineSourceBound
  positivity

private def logCellPrimitive (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (T - Real.log n)

private theorem logCellPrimitive_eq (T : ℝ) :
    logCellPrimitive T = (⌊Real.exp T⌋₊ : ℝ) * T -
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, Real.log n := by
  simp [logCellPrimitive, Finset.sum_sub_distrib, Nat.card_Icc, nsmul_eq_mul]

private theorem logCellPrimitive_stirling_bound {T : ℝ} (hT : 0 ≤ T) :
    |logCellPrimitive T - Real.exp T + T / 2 + ccmPrimeDeficitAffineSlope / 2| ≤ 2 := by
  let N := ⌊Real.exp T⌋₊
  let S : ℝ := ∑ n ∈ Finset.Icc 1 N, Real.log n
  let E : ℝ := S - ((N : ℝ) * Real.log N - N + Real.log N / 2 +
    ccmPrimeDeficitAffineSlope / 2)
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos T).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hNx : (N : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos T).le
  have hxN : Real.exp T < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp T)
  have hd0 : 0 ≤ T - Real.log N := sub_nonneg.mpr
    ((Real.log_le_iff_le_exp hNp).mpr hNx)
  have hd : T - Real.log N ≤ Real.exp T / N - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos T) hNp)
    rw [Real.log_div (Real.exp_ne_zero T) hNp.ne', Real.log_exp] at h
    exact h
  have hNd : (N : ℝ) * (T - Real.log N) ≤ Real.exp T - N := by
    have h := mul_le_mul_of_nonneg_left hd hNp.le
    have he : (N : ℝ) * (Real.exp T / N - 1) = Real.exp T - N := by
      field_simp
    rwa [he] at h
  have hd1 : T - Real.log N ≤ 1 := by
    have h := mul_nonneg (sub_nonneg.mpr hNR) hd0
    nlinarith
  have hSt := sum_log_Icc_exact_stirling_bounds hN
  have hE0 : 0 ≤ E := by
    dsimp [E, S, ccmPrimeDeficitAffineSlope]
    linarith only [hSt.1]
  have hE1 : E ≤ 1 := by
    have hb : 1 / (12 * (N : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 12 * N)]
      linarith only [hNR]
    dsimp [E, S, ccmPrimeDeficitAffineSlope]
    linarith only [hSt.2, hb]
  have heq : logCellPrimitive T - Real.exp T + T / 2 + ccmPrimeDeficitAffineSlope / 2 =
      (N : ℝ) * (T - Real.log N) - (Real.exp T - N) +
        (T - Real.log N) / 2 - E := by
    rw [logCellPrimitive_eq]
    dsimp [E, S, N]
    ring
  rw [heq, abs_le]
  constructor <;> nlinarith [mul_nonneg hNp.le hd0]

private theorem dilation_affineProfile (T : ℝ) :
    logarithmicDilationSum ccmPrimeDeficitAffineProfile T =
      ccmPrimeDeficitAffineIntercept * ⌊Real.exp T⌋₊ +
        ccmPrimeDeficitAffineSlope * logCellPrimitive T := by
  simp only [logarithmicDilationSum, logarithmicWeightedDilation,
    ccmPrimeDeficitAffineProfile, one_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, logCellPrimitive]
  ring

/-- A bound on the exact elementary source, after subtracting an exactly
invertible counterterm. It is not a bound on the reconstructed deficit. -/
theorem abs_ccmPrimeDeficitAffineSource_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitAffineSource T| ≤ ccmPrimeDeficitAffineSourceBound := by
  let U : ℝ := logCellPrimitive T - Real.exp T + T / 2 + ccmPrimeDeficitAffineSlope / 2
  have hU : |U| ≤ 2 := logCellPrimitive_stirling_bound hT
  have hr := abs_ccmPrimeDeficitDilationRemainder_le_uniform hT
  have hf0 : 0 ≤ Real.exp T - (⌊Real.exp T⌋₊ : ℝ) :=
    sub_nonneg.mpr (Nat.floor_le (Real.exp_pos T).le)
  have hf1 : Real.exp T - (⌊Real.exp T⌋₊ : ℝ) ≤ 1 := by
    linarith only [Nat.lt_floor_add_one (Real.exp T)]
  have ha : |ccmPrimeDeficitAffineIntercept * (Real.exp T - ⌊Real.exp T⌋₊)| ≤
      |ccmPrimeDeficitAffineIntercept| := by
    rw [abs_mul, abs_of_nonneg hf0]
    simpa using mul_le_mul_of_nonneg_left hf1 (abs_nonneg ccmPrimeDeficitAffineIntercept)
  have hb : |ccmPrimeDeficitAffineSlope * U| ≤ 2 * |ccmPrimeDeficitAffineSlope| := by
    rw [abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hU (abs_nonneg ccmPrimeDeficitAffineSlope)
  have heq : ccmPrimeDeficitAffineSource T =
      ccmPrimeDeficitDilationRemainder T - (Real.eulerMascheroniConstant + 1) +
        ccmPrimeDeficitAffineIntercept * (Real.exp T - ⌊Real.exp T⌋₊) +
          ccmPrimeDeficitAffineSlope ^ 2 / 2 - ccmPrimeDeficitAffineSlope * U := by
    rw [ccmPrimeDeficitAffineSource, dilation_affineProfile]
    dsimp [ccmPrimeDeficitDilationRemainder, ccmPrimeDeficitAffineIntercept,
      ccmPrimeDeficitAffineSlope, U]
    ring
  rw [heq, abs_le]
  rw [abs_le] at hr ha hb
  unfold ccmPrimeDeficitAffineSourceBound
  constructor <;> nlinarith [le_abs_self (Real.eulerMascheroniConstant + 1),
    neg_abs_le (Real.eulerMascheroniConstant + 1), sq_nonneg ccmPrimeDeficitAffineSlope]

theorem ccmPrimeDeficitAffineSource_eq_dilation (T : ℝ) :
    ccmPrimeDeficitAffineSource T = logarithmicDilationSum
      (fun t => ccmLogChebyshevDeficitPrimitive t - ccmPrimeDeficitAffineProfile t) T := by
  rw [ccmPrimeDeficitAffineSource, ← ccmLogChebyshevDeficitPrimitive_dilation_conservation]
  simp only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul,
    Finset.sum_sub_distrib]

/-- The full original deficit has a known affine term and one literal
bounded-source Möbius inverse, with no unknown explicit main channel. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_affine_reconstruction {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmPrimeDeficitAffineProfile T + ccmPrimeDeficitAffineReconstruction T := by
  have heq : ccmPrimeDeficitAffineSource = logarithmicDilationSum
      (fun t => ccmLogChebyshevDeficitPrimitive t - ccmPrimeDeficitAffineProfile t) :=
    funext ccmPrimeDeficitAffineSource_eq_dilation
  rw [ccmPrimeDeficitAffineReconstruction, heq, logarithmicMobiusInverse_dilationSum _ hT]
  ring

def ccmPrimeDeficitAffineSquareSource (T : ℝ) : ℝ :=
  Real.exp (-T) * logarithmicMobiusInverse (fun t => ccmPrimeDeficitAffineSource t ^ 2) T

theorem abs_ccmPrimeDeficitAffineSquareSource_le (T : ℝ) :
    |ccmPrimeDeficitAffineSquareSource T| ≤ ccmPrimeDeficitAffineSourceBound ^ 2 := by
  let K := ccmPrimeDeficitAffineSourceBound
  have hK : 0 ≤ K := ccmPrimeDeficitAffineSourceBound_nonneg
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
      |(ArithmeticFunction.moebius n : ℝ) * ccmPrimeDeficitAffineSource (T - Real.log n) ^ 2| ≤ K ^ 2 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    have hsource := abs_ccmPrimeDeficitAffineSource_le (sub_nonneg.mpr hlog)
    have hsquare : ccmPrimeDeficitAffineSource (T - Real.log n) ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hsource 2
    rw [abs_mul, abs_of_nonneg (sq_nonneg
      (ccmPrimeDeficitAffineSource (T - Real.log n)))]
    exact (mul_le_mul (abs_moebiusCoeff_le_one n) hsquare (sq_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  rw [ccmPrimeDeficitAffineSquareSource, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  unfold logarithmicMobiusInverse logarithmicWeightedDilation
  calc
    _ ≤ Real.exp (-T) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        |(ArithmeticFunction.moebius n : ℝ) * ccmPrimeDeficitAffineSource (T - Real.log n) ^ 2| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos (-T)).le
    _ ≤ Real.exp (-T) * ((⌊Real.exp T⌋₊ : ℝ) * K ^ 2) := by
      have h := Finset.sum_le_sum hterm
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
      exact mul_le_mul_of_nonneg_left h (Real.exp_pos (-T)).le
    _ ≤ Real.exp (-T) * (Real.exp T * K ^ 2) := by
      gcongr
      exact Nat.floor_le (Real.exp_pos T).le
    _ = K ^ 2 := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- Exact coprime balance for the original deficit after its known affine
counterterm. Every off-diagonal coprime pair remains present. -/
theorem ccmPrimeDeficitAffine_coprime_balance {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-T) * ((ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitAffineProfile T) ^ 2 +
      logarithmicCoprimeCross ccmPrimeDeficitAffineReconstruction T) =
        ccmPrimeDeficitAffineSquareSource T := by
  have h := logarithmicCoprimeEnergy_mobiusInverse ccmPrimeDeficitAffineSource T
  change logarithmicCoprimeEnergy ccmPrimeDeficitAffineReconstruction T = _ at h
  rw [logarithmicCoprimeEnergy_eq_endpoint_add_cross _ hT] at h
  rw [ccmLogChebyshevDeficitPrimitive_eq_affine_reconstruction hT,
    add_sub_cancel_left, ccmPrimeDeficitAffineSquareSource, h]

/-- Unconditional bound on energy plus signed work. Extracting an energy
bound still requires a lower bound for the retained cross work. -/
theorem ccmPrimeDeficitCriticalEnergy_add_affine_cross_le {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T +
      2 * Real.exp (-T) * logarithmicCoprimeCross ccmPrimeDeficitAffineReconstruction T ≤
        2 * ccmPrimeDeficitAffineSourceBound ^ 2 +
          2 * Real.exp (-T) * ccmPrimeDeficitAffineProfile T ^ 2 := by
  have hbalance := ccmPrimeDeficitAffine_coprime_balance hT
  have hsource := (abs_le.mp (abs_ccmPrimeDeficitAffineSquareSource_le T)).2
  have hsquare : ccmLogChebyshevDeficitPrimitive T ^ 2 ≤
      2 * (ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitAffineProfile T) ^ 2 +
        2 * ccmPrimeDeficitAffineProfile T ^ 2 := by
    nlinarith [sq_nonneg (ccmLogChebyshevDeficitPrimitive T - 2 * ccmPrimeDeficitAffineProfile T)]
  have hweighted := mul_le_mul_of_nonneg_left hsquare (Real.exp_pos (-T)).le
  unfold ccmPrimeDeficitCriticalEnergy
  nlinarith

end RHTower
