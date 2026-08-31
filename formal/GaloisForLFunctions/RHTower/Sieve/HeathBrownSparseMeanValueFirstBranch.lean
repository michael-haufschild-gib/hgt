import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSqrtScale

/-!
# First explicit Heath--Brown sparse mean-value branch

This file removes the natural square-root floor and divisor-scale artifacts from the exact
square-root-scale estimate.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- Natural square root lies below real square root after casting. -/
theorem heathBrown_natSqrt_cast_le_realSqrt (N : ℕ) :
    (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hs : ((N.sqrt : ℝ) ^ 2) ≤ (N : ℝ) := by
    rw [pow_two]
    exact_mod_cast heathBrown_sqrt_mul_sqrt_le N
  have hK : 0 ≤ (N.sqrt : ℝ) := by positivity
  rw [← Real.sqrt_sq hK]
  exact Real.sqrt_le_sqrt hs

/-- At square-root scale the divisor normalizer is bounded by `C_eta N^eta`. -/
theorem heathBrownSquareDivisorScale_sqrt_le
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) :
    heathBrownSquareDivisorScale N.sqrt eta ≤
      divisorBoundConst eta * (N : ℝ) ^ eta := by
  rw [heathBrownSquareDivisorScale]
  have hs : (((N.sqrt * N.sqrt : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast heathBrown_sqrt_mul_sqrt_le N
  have hpow : (((N.sqrt * N.sqrt : ℕ) : ℝ)) ^ eta ≤ (N : ℝ) ^ eta :=
    Real.rpow_le_rpow (by positivity) hs heta.le
  exact mul_le_mul_of_nonneg_left hpow (divisorBoundConst_pos heta).le

/-- The square-root branch with floor losses and divisor scale fully absorbed. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_le_firstBranch
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ 2) ≤
      75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        35 * Real.pi * (T : ℝ) * Real.sqrt (N : ℝ) * (A.card : ℝ) ^ 2 +
        (25 * Real.pi) ^ 2 * (N : ℝ) *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := by
  have hbase := integral_Icc_normSq_heathBrown_fullUnit_le_sqrtScale
    A T hT hA hN heta
  dsimp only at hbase
  have hK : 1 ≤ N.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hKcast := heathBrown_natSqrt_cast_le_realSqrt N
  have hk3nat : N.sqrt + 3 ≤ 4 * N.sqrt := by omega
  have h2k5nat : 2 * N.sqrt + 5 ≤ 7 * N.sqrt := by omega
  have hk3 : ((N.sqrt + 3 : ℕ) : ℝ) ≤ 4 * Real.sqrt (N : ℝ) := by
    calc
      ((N.sqrt + 3 : ℕ) : ℝ) ≤ ((4 * N.sqrt : ℕ) : ℝ) := by exact_mod_cast hk3nat
      _ = 4 * (N.sqrt : ℝ) := by push_cast; ring
      _ ≤ 4 * Real.sqrt (N : ℝ) := by gcongr
  have h2k5 : ((2 * N.sqrt + 5 : ℕ) : ℝ) ≤ 7 * Real.sqrt (N : ℝ) := by
    calc
      ((2 * N.sqrt + 5 : ℕ) : ℝ) ≤ ((7 * N.sqrt : ℕ) : ℝ) := by exact_mod_cast h2k5nat
      _ = 7 * (N.sqrt : ℝ) := by push_cast; ring
      _ ≤ 7 * Real.sqrt (N : ℝ) := by gcongr
  have hscale := heathBrownSquareDivisorScale_sqrt_le hN heta
  have hscale0 : 0 ≤ heathBrownSquareDivisorScale N.sqrt eta :=
    (one_le_heathBrownSquareDivisorScale hK heta).trans' zero_le_one
  have hscaleBig0 : 0 ≤ divisorBoundConst eta * (N : ℝ) ^ eta :=
    mul_nonneg (divisorBoundConst_pos heta).le (Real.rpow_nonneg (by positivity) _)
  have hMS :
      (5 * Real.pi * Real.exp 1 * (T : ℝ) +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ) =
        ((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
          (A.card : ℝ) := by
    change (5 * Real.pi * Real.exp 1 * (T : ℝ) +
        (5 * Real.pi / 2) * ((T : ℝ) / 2)) * (A.card : ℝ) = _
    ring
  have hterm2 :
      5 * Real.pi * (T : ℝ) * ((2 * N.sqrt + 5 : ℕ) : ℝ) *
          (A.card : ℝ) ^ 2 ≤
        35 * Real.pi * (T : ℝ) * Real.sqrt (N : ℝ) * (A.card : ℝ) ^ 2 := by
    calc
      _ ≤ 5 * Real.pi * (T : ℝ) * (7 * Real.sqrt (N : ℝ)) *
          (A.card : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hbaseCoeff :
      (25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ) ≤
        25 * Real.pi * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ (25 * Real.pi / 4) * (4 * Real.sqrt (N : ℝ)) := by gcongr
      _ = _ := by ring
  have hsmallCoeff0 : 0 ≤
      (25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ) := by positivity
  have hbigCoeff0 : 0 ≤ 25 * Real.pi * Real.sqrt (N : ℝ) := by positivity
  have hMS0 : 0 ≤
      ((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
        (A.card : ℝ) := by positivity
  have hterm3 :
      ((25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ)) ^ 2 *
          (((5 * Real.pi * Real.exp 1 * (T : ℝ) +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
            (heathBrownSquareDivisorScale N.sqrt eta ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) ≤
        (25 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := by
    rw [hMS]
    gcongr
  have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    _ ≤ 75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        5 * Real.pi * (T : ℝ) * ((2 * N.sqrt + 5 : ℕ) : ℝ) *
          (A.card : ℝ) ^ 2 +
        ((25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ)) ^ 2 *
          (((5 * Real.pi * Real.exp 1 * (T : ℝ) +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
            (heathBrownSquareDivisorScale N.sqrt eta ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) := hbase
    _ ≤ 75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        35 * Real.pi * (T : ℝ) * Real.sqrt (N : ℝ) * (A.card : ℝ) ^ 2 +
        (25 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 *
          (((5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (T : ℝ)) *
            (A.card : ℝ) *
            ((divisorBoundConst eta * (N : ℝ) ^ eta) ^ 2 *
              (25 * Real.pi / 8) * (25 * Real.pi / 8))) :=
      add_le_add (add_le_add_right hterm2 _) hterm3
    _ = _ := by rw [mul_pow, hsqrtSq]

end RHTower.Sieve
