import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDilationSourceBounds

/-!
# The surviving floor oscillation and a decaying force error

The complete centered elementary force is a centered sawtooth times
`T-1`, plus an error bounded by `3 exp(-T)`. The growing pointwise
oscillation must be integrated with its sign; taking its absolute value
would lose the cancellation between successive integer cells.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitDilationOscillation (T : ℝ) : ℝ :=
  (Int.fract (Real.exp T) - 1 / 2) * (T - 1)

def ccmPrimeDeficitDilationForceError (T : ℝ) : ℝ :=
  ccmPrimeDeficitDilationForce T - (Real.eulerMascheroniConstant + 1) * Real.exp T +
    Real.log (2 * Real.pi) / 2 - ccmPrimeDeficitDilationOscillation T

/-- After retaining the literal sawtooth, the remaining complete force is
absolutely integrable in logarithmic time, with an explicit envelope. -/
theorem abs_ccmPrimeDeficitDilationForceError_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationForceError T| ≤ 3 * Real.exp (-T) := by
  let N := ⌊Real.exp T⌋₊
  let H : ℝ := ((harmonic N : ℚ) : ℝ)
  let S : ℝ := ∑ k ∈ Finset.Icc 1 N, Real.log k
  let c : ℝ := Real.log (2 * Real.pi) / 2
  let d : ℝ := Real.exp T - N
  let a : ℝ := H - Real.log N - Real.eulerMascheroniConstant - 1 / (2 * N)
  let b : ℝ := S - ((N : ℝ) * Real.log N - N + Real.log N / 2 + c)
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos := zero_lt_one.trans_le hNR
  have hNx : (N : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos T).le
  have hxN : Real.exp T < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp T)
  have hx2N : Real.exp T ≤ 2 * (N : ℝ) := by linarith only [hxN, hNR]
  have hd0 : 0 ≤ d := sub_nonneg.mpr hNx
  have hd1 : d ≤ 1 := by dsimp only [d]; linarith only [hxN]
  have hfract : Int.fract (Real.exp T) = d := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor (Real.exp_pos T).le]
  have hLT : Real.log (N : ℝ) ≤ T := (Real.log_le_iff_le_exp hpos).mpr hNx
  have hlog : |Real.log (N : ℝ) - T| ≤ 1 / N := by
    rw [abs_of_nonpos (sub_nonpos.mpr hLT)]
    have h := Real.log_le_sub_one_of_pos (x := Real.exp T / N) (by positivity)
    rw [Real.log_div (Real.exp_pos T).ne' hpos.ne', Real.log_exp] at h
    have hquot : Real.exp T / N - 1 ≤ 1 / N := by
      calc
        _ = (Real.exp T - N) / N := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hxN]) hpos.le
    linarith only [h, hquot]
  have ha : |a| ≤ 1 / (12 * (N : ℝ) ^ 2) := by
    have hlo : 1 / (2 * (N : ℝ)) - 1 / (12 * (N : ℝ) ^ 2) ≤
        H - Real.log N - Real.eulerMascheroniConstant := harmonic_mascheroni_ge_half_sub_twelfth hN
    have hhi : H - Real.log N - Real.eulerMascheroniConstant ≤ 1 / (2 * (N : ℝ)) :=
      (harmonic_mascheroni_half_bounds hN).2
    rw [abs_le]
    dsimp only [a]
    constructor <;> linarith only [hlo, hhi, (by positivity : (0 : ℝ) ≤ 1 / (12 * (N : ℝ) ^ 2))]
  have hb : |b| ≤ 1 / (12 * (N : ℝ)) := by
    have hSt : (N : ℝ) * Real.log N - N + Real.log N / 2 + c ≤ S ∧
        S ≤ (N : ℝ) * Real.log N - N + Real.log N / 2 + c + 1 / (12 * N) :=
      sum_log_Icc_exact_stirling_bounds hN
    dsimp only [b]
    rw [abs_le]
    constructor <;> linarith only [hSt.1, hSt.2, (by positivity : (0 : ℝ) ≤ 1 / (12 * N))]
  have hfirst : |(d - 1 / 2) * (Real.log (N : ℝ) - T)| ≤ 1 / (2 * (N : ℝ)) := by
    rw [abs_mul]
    have hd : |d - 1 / 2| ≤ 1 / 2 := abs_le.mpr (by constructor <;> linarith only [hd0, hd1])
    calc
      _ ≤ (1 / 2 : ℝ) * (1 / N) := mul_le_mul hd hlog (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsecond : |d / (2 * (N : ℝ))| ≤ 1 / (2 * (N : ℝ)) := by
    rw [abs_of_nonneg (div_nonneg hd0 (by positivity))]
    exact div_le_div_of_nonneg_right hd1 (by positivity)
  have hthird : |Real.exp T * a| ≤ 1 / (6 * (N : ℝ)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos T)]
    calc
      _ ≤ (2 * (N : ℝ)) * (1 / (12 * (N : ℝ) ^ 2)) :=
        mul_le_mul hx2N ha (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  have hforce : ccmPrimeDeficitDilationForce T = Real.exp T * H - S := by
    simp only [ccmPrimeDeficitDilationForce, logarithmicEntrySum, H, S, N,
      harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have heq : ccmPrimeDeficitDilationForceError T =
      (d - 1 / 2) * (Real.log (N : ℝ) - T) + d / (2 * N) + Real.exp T * a - b := by
    rw [ccmPrimeDeficitDilationForceError, hforce, ccmPrimeDeficitDilationOscillation, hfract]
    dsimp only [a, b, c, d]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(d - 1 / 2) * (Real.log (N : ℝ) - T)| + |d / (2 * N)| + |Real.exp T * a| + |b| := by
      calc
        _ ≤ |(d - 1 / 2) * (Real.log (N : ℝ) - T) + d / (2 * N) + Real.exp T * a| + |b| := abs_sub _ _
        _ ≤ (|(d - 1 / 2) * (Real.log (N : ℝ) - T) + d / (2 * N)| + |Real.exp T * a|) + |b| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ 1 / (2 * (N : ℝ)) + 1 / (2 * N) + 1 / (6 * N) + 1 / (12 * N) := by
      gcongr
    _ = 5 / (4 * (N : ℝ)) := by ring
    _ ≤ 3 / Real.exp T := by
      rw [div_le_div_iff₀ (by positivity) (Real.exp_pos T)]
      linarith only [hx2N, hpos]
    _ = _ := by rw [Real.exp_neg]; ring

end RHTower
