import GaloisForLFunctions.RHTower.MobiusSquareDivisorLowProduct

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

theorem mobiusSquareDivisorProductEnvelope_le_polylog
    {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) :
    mobiusSquareDivisorProductEnvelope N Q ≤
      2104 * (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt Q) *
        (1 + Real.log (N : ℝ)) ^ 5 := by
  let T : ℝ := 1 + Real.log (N : ℝ)
  let A : ℝ := (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt Q)
  let L : ℝ := Real.log ((N : ℝ) ^ 2 + 1)
  let H : ℝ := 1 + Real.log (1 + (N : ℝ) * Real.sqrt Q)
  let W : ℝ := Real.log (Q : ℝ) + L / 2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQN' : (Q : ℝ) ≤ N := by exact_mod_cast hQN
  have hNpos : (0 : ℝ) < N := by linarith
  have hT : 1 ≤ T := by dsimp [T]; linarith [Real.log_natCast_nonneg N]
  have hT0 : 0 ≤ T := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [sq_nonneg (N : ℝ)])
  have hLsharp : L ≤ 1 + 2 * Real.log (N : ℝ) := by
    have harg : (N : ℝ) ^ 2 + 1 ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < (N : ℝ) ^ 2 + 1) harg
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [L]
    norm_num at hl h2
    linarith
  have hL : L ≤ 2 * T := by dsimp [T]; linarith
  have hrootQ : Real.sqrt Q ≤ (N : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg Q)]
    nlinarith
  have hH : H ≤ 2 * T := by
    have hl : Real.log (1 + (N : ℝ) * Real.sqrt Q) ≤ L :=
      Real.log_le_log (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hrootQ (show (0 : ℝ) ≤ N by positivity)])
    dsimp [H, T]
    linarith
  have hH0 : 0 ≤ H := by
    have hl : 0 ≤ Real.log (1 + (N : ℝ) * Real.sqrt Q) := by
      apply Real.log_nonneg
      have hh : (0 : ℝ) ≤ N * Real.sqrt Q := by positivity
      linarith
    dsimp [H]
    linarith
  have hlogQN := Real.log_le_log (by linarith : (0 : ℝ) < Q) hQN'
  have hW : W ≤ 2 * T := by dsimp [W, T]; linarith
  have hW0 : 0 ≤ W := by dsimp [W]; linarith [Real.log_natCast_nonneg Q]
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAN : (N : ℝ) ≤ A := by
    have hNs : (1 : ℝ) ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN1
    have hQs : (1 : ℝ) ≤ Real.sqrt Q := by simpa using Real.sqrt_le_sqrt hQ1
    have hQss : (1 : ℝ) ≤ Real.sqrt (Real.sqrt Q) := by simpa using Real.sqrt_le_sqrt hQs
    have hp : (1 : ℝ) ≤ Real.sqrt N * Real.sqrt (Real.sqrt Q) := by
      simpa using mul_le_mul hNs hQss (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ N by positivity)
    dsimp [A]
    nlinarith
  have hT3 : (1 : ℝ) ≤ T ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hT 3
  have hT14 : T ≤ T ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left hT3 (show 0 ≤ T by linarith)
    nlinarith
  have hT25 : T ^ 2 ≤ T ^ 5 := by
    have hm := mul_le_mul_of_nonneg_left hT3 (sq_nonneg T)
    nlinarith
  have hfirst : (N : ℝ) * (7 + 2 * L) ≤ 11 * A * T ^ 4 := by
    calc
      _ ≤ (N : ℝ) * (11 * T) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ A * (11 * T) := mul_le_mul_of_nonneg_right hAN (by positivity)
      _ = 11 * A * T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hT14 (by positivity)
  have hlarge : 32 * A * H ^ 4 ≤ 512 * A * T ^ 4 := by
    calc
      _ ≤ 32 * A * (2 * T) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hH 4) (by positivity)
      _ = _ := by ring
  have hF : (N : ℝ) * (7 + 2 * L) + 32 * A * H ^ 4 ≤ 523 * A * T ^ 4 := by
    linarith
  have hboundary : 2 * ((N : ℝ) * (7 + 2 * L) + 32 * A * H ^ 4) * W ≤
      2092 * A * T ^ 5 := by
    calc
      _ ≤ (2 * (523 * A * T ^ 4)) * (2 * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hW hW0 (by positivity)
      _ = _ := by ring
  have hinner : (N : ℝ) / 2 * (8 + 2 * L) * L ≤ 12 * A * T ^ 5 := by
    calc
      _ ≤ ((N : ℝ) / 2 * (12 * T)) * (2 * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hL hL0 (by positivity)
      _ = 12 * (N : ℝ) * T ^ 2 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hAN (by norm_num)) hT25 (by positivity) (by positivity)
  calc
    mobiusSquareDivisorProductEnvelope N Q =
        2 * ((N : ℝ) * (7 + 2 * L) + 32 * A * H ^ 4) * W +
          (N : ℝ) / 2 * (8 + 2 * L) * L := by
      dsimp [mobiusSquareDivisorProductEnvelope, A, L, H, W]
      ring
    _ ≤ 2104 * A * T ^ 5 := by linarith
    _ = _ := by dsimp [A, T]; ring

theorem abs_mobiusSquareDivisorLowProductRemainder_le_polylog
    {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) :
    |mobiusSquareDivisorLowProductRemainder N Q| ≤
      2104 * (N : ℝ) * Real.sqrt N * Q * Real.sqrt (Real.sqrt Q) *
        (1 + Real.log (N : ℝ)) ^ 6 := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlog := Real.log_le_log hQpos (by exact_mod_cast hQN : (Q : ℝ) ≤ N)
  have hNlog := Real.log_natCast_nonneg N
  have hcount : (Q : ℝ) * (1 + Real.log (Q : ℝ)) ≤ (Q : ℝ) * (1 + Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) * mobiusSquareDivisorProductEnvelope N Q :=
      abs_mobiusSquareDivisorLowProductRemainder_le N Q
    _ ≤ ((Q : ℝ) * (1 + Real.log (N : ℝ))) *
        (2104 * (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt Q) *
          (1 + Real.log (N : ℝ)) ^ 5) :=
      mul_le_mul hcount (mobiusSquareDivisorProductEnvelope_le_polylog hN hQ hQN)
        (mobiusSquareDivisorProductEnvelope_nonneg N Q) (by positivity)
    _ = _ := by ring

/-- An explicit growing product region contributes only at the critical quadratic scale. -/
theorem abs_mobiusSquareDivisorLowProductRemainder_le_log_budget
    {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N)
    (hbudget : (Q : ℝ) ^ 5 * (1 + Real.log (N : ℝ)) ^ 24 ≤ (N : ℝ) ^ 2) :
    |mobiusSquareDivisorLowProductRemainder N Q| ≤ 2104 * (N : ℝ) ^ 2 := by
  let T : ℝ := 1 + Real.log (N : ℝ)
  let Z : ℝ := (N : ℝ) * Real.sqrt N * Q * Real.sqrt (Real.sqrt Q) * T ^ 6
  have hN4 : (Real.sqrt (N : ℝ)) ^ 4 = (N : ℝ) ^ 2 := by
    calc
      _ = ((Real.sqrt (N : ℝ)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hQ4 : (Real.sqrt (Real.sqrt (Q : ℝ))) ^ 4 = (Q : ℝ) := by
    calc
      _ = ((Real.sqrt (Real.sqrt (Q : ℝ))) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg Q)]
  have hZ4 : Z ^ 4 ≤ ((N : ℝ) ^ 2) ^ 4 := by
    calc
      Z ^ 4 = (N : ℝ) ^ 4 * (Real.sqrt N) ^ 4 * (Q : ℝ) ^ 4 *
          (Real.sqrt (Real.sqrt Q)) ^ 4 * T ^ 24 := by dsimp [Z]; ring
      _ = (N : ℝ) ^ 6 * ((Q : ℝ) ^ 5 * T ^ 24) := by rw [hN4, hQ4]; ring
      _ ≤ (N : ℝ) ^ 6 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by ring
  have hZsq : Z ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 := by
    apply (sq_le_sq₀ (sq_nonneg Z) (sq_nonneg ((N : ℝ) ^ 2))).mp
    simpa only [← pow_mul] using hZ4
  have hZ : Z ≤ (N : ℝ) ^ 2 :=
    (sq_le_sq₀ (by dsimp [Z]; positivity) (sq_nonneg _)).mp hZsq
  calc
    _ ≤ 2104 * Z := by
      convert abs_mobiusSquareDivisorLowProductRemainder_le_polylog hN hQ hQN using 1
      dsimp [Z, T]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by norm_num)

end RHTower
