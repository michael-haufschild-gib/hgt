import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedEnergy
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedFortyNineError

/-!
# Included-head energy error at mollifier exponent `49/100`

At `L=N^(100 : ℕ)`, `M=N^(49 : ℕ)`, and detector parameter `r/log M`, the aggregate included-head
approximation error is `O_r(N⁻²)`.  All scale and logarithmic estimates are reused from the
existing omitted-head specialization.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Explicit coefficient in the included aggregate `N⁻²` error. -/
def barbanVehovIncludedFortyNineErrorConstant (r : ℝ) : ℝ :=
  3 + (1800 / 49 : ℝ) * |r| + (270000 / 2401 : ℝ) * r ^ (2 : ℕ)

theorem abs_levinsonCriticalDetectorLongEnergy_fortyNine_sub_polynomialMain_le
    (r : ℝ) {N : ℕ} (hN : 8 ≤ N) :
    |levinsonCriticalDetectorLongEnergy
          (r / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
        barbanVehovIncludedLongEnergyPolynomialMain
          (r / (49 * Real.log N)) (100 * Real.log N) (N ^ (49 : ℕ))| ≤
      barbanVehovIncludedFortyNineErrorConstant r / (N : ℝ) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hM : 1 < N ^ (49 : ℕ) := by
    have hNpow : N ≤ N ^ (49 : ℕ) := by
      calc
        N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos hN0 48)
        _ = N ^ (49 : ℕ) := by ring
    exact (by omega : 1 < N).trans_le hNpow
  have hlogM : Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) =
      49 * Real.log (N : ℝ) := by
    rw [show (((N ^ (49 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  have hlogL : Real.log (((N ^ (100 : ℕ) : ℕ) : ℝ)) =
      100 * Real.log (N : ℝ) := by
    rw [show (((N ^ (100 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (100 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  let K : ℝ := Real.log (N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1))
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have hKsq : K ^ (2 : ℕ) ≤ 22500 * Real.log N ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (K - 150 * Real.log N)]
  have herr :=
    abs_levinsonCriticalDetectorLongEnergy_sub_includedPolynomialMain_le
      (r / (49 * Real.log N)) hM (fortyNine_scale_condition hN)
  rw [hlogL, hlogM] at herr
  have herr' :
      |levinsonCriticalDetectorLongEnergy
            (r / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovIncludedLongEnergyPolynomialMain
            (r / (49 * Real.log N)) (100 * Real.log N) (N ^ (49 : ℕ))| ≤
        (3 + 12 * |r| * (K / Real.log N) / 49 +
            12 * r ^ (2 : ℕ) * (K ^ (2 : ℕ) / Real.log N ^ (2 : ℕ)) / 49 ^ (2 : ℕ)) /
          (N : ℝ) ^ (2 : ℕ) := by
    calc
      _ ≤ (((((N : ℝ) ^ (49 : ℕ)) * (49 * Real.log N)) ^ (2 : ℕ) *
              (3 / (N : ℝ) ^ (100 : ℕ)) +
            2 * |r / (49 * Real.log N)| *
              (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log N)) ^ (2 : ℕ) *
                (6 * K / (N : ℝ) ^ (100 : ℕ))) +
            (r / (49 * Real.log N)) ^ (2 : ℕ) *
              (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log N)) ^ (2 : ℕ) *
                (12 * K ^ (2 : ℕ) / (N : ℝ) ^ (100 : ℕ)))) /
          (49 * Real.log N) ^ (2 : ℕ)) := by
            simpa [K, Nat.cast_pow] using herr
      _ = _ := by
        rw [abs_div, abs_of_pos (by positivity : 0 < (49 : ℝ) * Real.log N)]
        field_simp [hlogN, hNR.ne']
        ring
  refine herr'.trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg (N : ℝ))
  have hKratio : K / Real.log N ≤ 150 := (div_le_iff₀ hlogPos).2 hK
  have hKsqRatio : K ^ (2 : ℕ) / Real.log N ^ (2 : ℕ) ≤ 22500 :=
    (div_le_iff₀ (pow_pos hlogPos 2)).2 hKsq
  rw [barbanVehovIncludedFortyNineErrorConstant]
  have hcross : 12 * |r| * (K / Real.log N) / 49 ≤
      (1800 / 49 : ℝ) * |r| := by
    calc
      12 * |r| * (K / Real.log N) / 49 =
          (12 / 49 : ℝ) * |r| * (K / Real.log N) := by ring
      _ ≤ (12 / 49 : ℝ) * |r| * 150 :=
        mul_le_mul_of_nonneg_left hKratio (by positivity)
      _ = (1800 / 49 : ℝ) * |r| := by ring
  have hderiv : 12 * r ^ (2 : ℕ) * (K ^ (2 : ℕ) / Real.log N ^ (2 : ℕ)) / 49 ^ (2 : ℕ) ≤
      (270000 / 2401 : ℝ) * r ^ (2 : ℕ) := by
    calc
      12 * r ^ (2 : ℕ) * (K ^ (2 : ℕ) / Real.log N ^ (2 : ℕ)) / 49 ^ (2 : ℕ) =
          (12 / 49 ^ (2 : ℕ) : ℝ) * r ^ (2 : ℕ) *
            (K ^ (2 : ℕ) / Real.log N ^ (2 : ℕ)) := by ring
      _ ≤ (12 / 49 ^ (2 : ℕ) : ℝ) * r ^ (2 : ℕ) * 22500 :=
        mul_le_mul_of_nonneg_left hKsqRatio (by positivity)
      _ = (270000 / 2401 : ℝ) * r ^ (2 : ℕ) := by norm_num; ring
  linarith

end

end RHTower.Sieve
