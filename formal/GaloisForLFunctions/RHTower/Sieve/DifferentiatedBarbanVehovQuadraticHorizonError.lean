import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelAsymptotics
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovContinuousKernels
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovStrongScaleError
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovLinearL1

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem natCast_div_antitone_denominator_hybrid
    {e L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    (e : ℝ) / (U : ℝ) ≤ (e : ℝ) / (L : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hL.trans_le hLU
  have hLUR : (L : ℝ) ≤ (U : ℝ) := by exact_mod_cast hLU
  exact div_le_div_of_nonneg_left (by positivity) hLR hLUR

theorem abs_harmonicLogWindowMain_zero_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (heL : e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMain 0 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) -
          Real.log ((L : ℝ) / (e : ℝ)))| ≤
      2 * (e : ℝ) / (L : ℝ) := by
  have hL : 0 < L := he.trans_le heL
  have hU : 0 < U := hL.trans_le hLU
  have hu := abs_log_natDiv_add_one_sub_log_div_le hU he
  have hl := abs_log_natDiv_add_one_sub_log_div_le hL he
  norm_num [Nat.cast_add, Nat.cast_one] at hu hl
  have hdiv := natCast_div_antitone_denominator_hybrid (e := e) hL hLU
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive,
    Nat.cast_add, Nat.cast_one]
  calc
    |(Real.log (((U / e : ℕ) : ℝ) + 1) -
        Real.log (((L / e : ℕ) : ℝ) + 1)) -
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| =
      |(Real.log (((U / e : ℕ) : ℝ) + 1) - Real.log ((U : ℝ) / (e : ℝ))) +
        -(Real.log (((L / e : ℕ) : ℝ) + 1) - Real.log ((L : ℝ) / (e : ℝ)))| := by
          congr 1
          ring
    _ ≤ |Real.log (((U / e : ℕ) : ℝ) + 1) - Real.log ((U : ℝ) / (e : ℝ))| +
        |Real.log (((L / e : ℕ) : ℝ) + 1) - Real.log ((L : ℝ) / (e : ℝ))| := by
          simpa only [abs_neg] using abs_add_le
            (Real.log (((U / e : ℕ) : ℝ) + 1) - Real.log ((U : ℝ) / (e : ℝ)))
            (-(Real.log (((L / e : ℕ) : ℝ) + 1) - Real.log ((L : ℝ) / (e : ℝ))))
    _ ≤ (e : ℝ) / (U : ℝ) + (e : ℝ) / (L : ℝ) := add_le_add hu hl
    _ ≤ (e : ℝ) / (L : ℝ) + (e : ℝ) / (L : ℝ) := add_le_add hdiv le_rfl
    _ = 2 * (e : ℝ) / (L : ℝ) := by ring

private theorem log_nat_succ_le_log_nat_succ_hybrid {L U : ℕ} (hLU : L ≤ U) :
    Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log ((U + 1 : ℕ) : ℝ) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hLU 1

theorem abs_harmonicLogWindowMain_one_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (heL : e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMain 1 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ 2 / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ 2 / 2)| ≤
      2 * Real.log ((U + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ)) := by
  have hL : 0 < L := he.trans_le heL
  have hU : 0 < U := hL.trans_le hLU
  have heU : e ≤ U := heL.trans hLU
  let K : ℝ := Real.log ((U + 1 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have hu := abs_log_natDiv_add_one_sq_sub_log_div_sq_le hU he heU
  have hl := abs_log_natDiv_add_one_sq_sub_log_div_sq_le hL he heL
  have hdiv := natCast_div_antitone_denominator_hybrid (e := e) hL hLU
  have hlogLU := log_nat_succ_le_log_nat_succ_hybrid hLU
  have hu' :
      |Real.log (U / e + 1 : ℕ) ^ 2 - Real.log ((U : ℝ) / (e : ℝ)) ^ 2| / 2 ≤
        K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (2 * K * ((e : ℝ) / (U : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hu (by norm_num)
      _ = K * ((e : ℝ) / (U : ℝ)) := by ring
      _ ≤ K * ((e : ℝ) / (L : ℝ)) := mul_le_mul_of_nonneg_left hdiv hK0
  have hl' :
      |Real.log (L / e + 1 : ℕ) ^ 2 - Real.log ((L : ℝ) / (e : ℝ)) ^ 2| / 2 ≤
        K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (2 * Real.log ((L + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hl (by norm_num)
      _ = Real.log ((L + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ)) := by ring
      _ ≤ K * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogLU (by positivity)
  have hend :
      |(Real.log (U / e + 1 : ℕ) ^ 2 / 2 -
          Real.log (L / e + 1 : ℕ) ^ 2 / 2) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ 2 / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ 2 / 2)| ≤
        2 * K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(Real.log (U / e + 1 : ℕ) ^ 2 -
            Real.log ((U : ℝ) / (e : ℝ)) ^ 2) / 2 -
          (Real.log (L / e + 1 : ℕ) ^ 2 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ 2) / 2| := by
              congr 1
              ring
      _ ≤ |Real.log (U / e + 1 : ℕ) ^ 2 -
            Real.log ((U : ℝ) / (e : ℝ)) ^ 2| / 2 +
          |Real.log (L / e + 1 : ℕ) ^ 2 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ 2| / 2 := by
              calc
                _ ≤ |(Real.log (U / e + 1 : ℕ) ^ 2 -
                        Real.log ((U : ℝ) / (e : ℝ)) ^ 2) / 2| +
                    |(Real.log (L / e + 1 : ℕ) ^ 2 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ 2) / 2| := abs_sub _ _
                _ = _ := by rw [abs_div, abs_div]; norm_num
      _ ≤ K * ((e : ℝ) / (L : ℝ)) + K * ((e : ℝ) / (L : ℝ)) :=
        add_le_add hu' hl'
      _ = 2 * K * ((e : ℝ) / (L : ℝ)) := by ring
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive,
    Nat.cast_add, Nat.cast_one, K] at hend ⊢
  exact hend

theorem abs_harmonicLogWindowMain_two_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (heL : e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMain 2 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ 3 / 3 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ 3 / 3)| ≤
      2 * Real.log ((U + 1 : ℕ) : ℝ) ^ 2 * ((e : ℝ) / (L : ℝ)) := by
  have hL : 0 < L := he.trans_le heL
  have hU : 0 < U := hL.trans_le hLU
  have heU : e ≤ U := heL.trans hLU
  let K : ℝ := Real.log ((U + 1 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have hu := abs_log_natDiv_add_one_cube_sub_log_div_cube_le hU he heU
  have hl := abs_log_natDiv_add_one_cube_sub_log_div_cube_le hL he heL
  have hdiv := natCast_div_antitone_denominator_hybrid (e := e) hL hLU
  have hlogLU := log_nat_succ_le_log_nat_succ_hybrid hLU
  have hlogL0 : 0 ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L + 1))
  have hlogL2 : Real.log ((L + 1 : ℕ) : ℝ) ^ 2 ≤ K ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hlogLU hlogL0
    have h2 := mul_le_mul_of_nonneg_right hlogLU hK0
    nlinarith
  have hu' :
      |Real.log (U / e + 1 : ℕ) ^ 3 - Real.log ((U : ℝ) / (e : ℝ)) ^ 3| / 3 ≤
        K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (3 * K ^ 2 * ((e : ℝ) / (U : ℝ))) / 3 :=
        div_le_div_of_nonneg_right hu (by norm_num)
      _ = K ^ 2 * ((e : ℝ) / (U : ℝ)) := by ring
      _ ≤ K ^ 2 * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg K)
  have hl' :
      |Real.log (L / e + 1 : ℕ) ^ 3 - Real.log ((L : ℝ) / (e : ℝ)) ^ 3| / 3 ≤
        K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (3 * Real.log ((L + 1 : ℕ) : ℝ) ^ 2 *
          ((e : ℝ) / (L : ℝ))) / 3 :=
        div_le_div_of_nonneg_right hl (by norm_num)
      _ = Real.log ((L + 1 : ℕ) : ℝ) ^ 2 * ((e : ℝ) / (L : ℝ)) := by ring
      _ ≤ K ^ 2 * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogL2 (by positivity)
  have hend :
      |(Real.log (U / e + 1 : ℕ) ^ 3 / 3 -
          Real.log (L / e + 1 : ℕ) ^ 3 / 3) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ 3 / 3 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ 3 / 3)| ≤
        2 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(Real.log (U / e + 1 : ℕ) ^ 3 -
            Real.log ((U : ℝ) / (e : ℝ)) ^ 3) / 3 -
          (Real.log (L / e + 1 : ℕ) ^ 3 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ 3) / 3| := by
              congr 1
              ring
      _ ≤ |Real.log (U / e + 1 : ℕ) ^ 3 -
            Real.log ((U : ℝ) / (e : ℝ)) ^ 3| / 3 +
          |Real.log (L / e + 1 : ℕ) ^ 3 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ 3| / 3 := by
              calc
                _ ≤ |(Real.log (U / e + 1 : ℕ) ^ 3 -
                        Real.log ((U : ℝ) / (e : ℝ)) ^ 3) / 3| +
                    |(Real.log (L / e + 1 : ℕ) ^ 3 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ 3) / 3| := abs_sub _ _
                _ = _ := by rw [abs_div, abs_div]; norm_num
      _ ≤ K ^ 2 * ((e : ℝ) / (L : ℝ)) +
          K ^ 2 * ((e : ℝ) / (L : ℝ)) := add_le_add hu' hl'
      _ = 2 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by ring
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive,
    Nat.cast_add, Nat.cast_one, K] at hend ⊢
  exact hend

private theorem abs_log_natDiv_le_log_succ_hybrid
    {U e d : ℕ} (he : 0 < e) (hd : 0 < d) (hde : d ∣ e) (heU : e ≤ U) :
    |Real.log (((e / d : ℕ) : ℝ))| ≤ Real.log ((U + 1 : ℕ) : ℝ) := by
  have hed : 0 < e / d := Nat.div_pos (Nat.le_of_dvd he hde) hd
  have hone : (1 : ℝ) ≤ ((e / d : ℕ) : ℝ) := by exact_mod_cast hed
  have hleNat : e / d ≤ U + 1 :=
    (Nat.div_le_self e d).trans (heU.trans (Nat.le_succ U))
  have hle : Real.log (((e / d : ℕ) : ℝ)) ≤ Real.log ((U + 1 : ℕ) : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hleNat)
  rw [abs_of_nonneg (Real.log_nonneg hone)]
  exact hle

theorem abs_barbanVehovLongHarmonicKernelMain_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongHarmonicKernelMain L U q r -
        barbanVehovLongHarmonicKernelContinuous L U q r| ≤
      2 / (L : ℝ) := by
  let e := Nat.lcm q r
  have he : 0 < e := Nat.lcm_pos hq hr
  have hmoment :=
    abs_harmonicLogWindowMain_zero_natDiv_sub_continuous_le he heL hLU
  rw [barbanVehovLongHarmonicKernelMain,
    barbanVehovLongHarmonicKernelContinuous]
  change |1 / (e : ℝ) * harmonicLogWindowMain 0 (L / e) (U / e) -
      1 / (e : ℝ) *
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤ _
  rw [← mul_sub, abs_mul,
    abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) *
        |harmonicLogWindowMain 0 (L / e) (U / e) -
          (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤
      1 / (e : ℝ) * (2 * (e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 2 / (L : ℝ) := by field_simp

theorem abs_barbanVehovLongFirstLogKernelMain_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongFirstLogKernelMain L U q r -
        barbanVehovLongFirstLogKernelContinuous L U q r| ≤
      4 * Real.log ((U + 1 : ℕ) : ℝ) / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / r : ℕ) : ℝ))
  let M0 := harmonicLogWindowMain 0 (L / e) (U / e)
  let M1 := harmonicLogWindowMain 1 (L / e) (U / e)
  let C0 := Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))
  let C1 := Real.log ((U : ℝ) / (e : ℝ)) ^ 2 / 2 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ 2 / 2
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hr (Nat.dvd_lcm_right q r) heU
  have h0 : |M0 - C0| ≤ 2 * (e : ℝ) / (L : ℝ) := by
    exact abs_harmonicLogWindowMain_zero_natDiv_sub_continuous_le he heL hLU
  have h1 : |M1 - C1| ≤ 2 * K * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMain_one_natDiv_sub_continuous_le he heL hLU
  have hinner : |a * M0 + M1 - (a * C0 + C1)| ≤
      4 * K * ((e : ℝ) / (L : ℝ)) := by
    calc
      |a * M0 + M1 - (a * C0 + C1)| = |a * (M0 - C0) + (M1 - C1)| := by ring_nf
      _ ≤ |a * (M0 - C0)| + |M1 - C1| := abs_add_le _ _
      _ = |a| * |M0 - C0| + |M1 - C1| := by rw [abs_mul]
      _ ≤ K * (2 * (e : ℝ) / (L : ℝ)) +
          2 * K * ((e : ℝ) / (L : ℝ)) :=
        add_le_add (mul_le_mul ha h0 (abs_nonneg _) hK0) h1
      _ = 4 * K * ((e : ℝ) / (L : ℝ)) := by ring
  rw [barbanVehovLongFirstLogKernelMain,
    barbanVehovLongFirstLogKernelContinuous]
  change |1 / (e : ℝ) * (a * M0 + M1) -
      1 / (e : ℝ) * (a * C0 + C1)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) * |a * M0 + M1 - (a * C0 + C1)| ≤
        1 / (e : ℝ) * (4 * K * ((e : ℝ) / (L : ℝ))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * Real.log ((U + 1 : ℕ) : ℝ) / (L : ℝ) := by
      dsimp [K]
      field_simp

theorem abs_barbanVehovLongSecondLogKernelMain_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongSecondLogKernelMain L U q r -
        barbanVehovLongSecondLogKernelContinuous L U q r| ≤
      8 * Real.log ((U + 1 : ℕ) : ℝ) ^ 2 / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / q : ℕ) : ℝ))
  let b := Real.log (((e / r : ℕ) : ℝ))
  let M0 := harmonicLogWindowMain 0 (L / e) (U / e)
  let M1 := harmonicLogWindowMain 1 (L / e) (U / e)
  let M2 := harmonicLogWindowMain 2 (L / e) (U / e)
  let C0 := Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))
  let C1 := Real.log ((U : ℝ) / (e : ℝ)) ^ 2 / 2 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ 2 / 2
  let C2 := Real.log ((U : ℝ) / (e : ℝ)) ^ 3 / 3 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ 3 / 3
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hq (Nat.dvd_lcm_left q r) heU
  have hb : |b| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hr (Nat.dvd_lcm_right q r) heU
  have hab : |a * b| ≤ K ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) hK0]
  have habadd : |a + b| ≤ 2 * K := by
    exact (abs_add_le a b).trans (by linarith)
  have h0 : |M0 - C0| ≤ 2 * (e : ℝ) / (L : ℝ) := by
    exact abs_harmonicLogWindowMain_zero_natDiv_sub_continuous_le he heL hLU
  have h1 : |M1 - C1| ≤ 2 * K * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMain_one_natDiv_sub_continuous_le he heL hLU
  have h2 : |M2 - C2| ≤ 2 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMain_two_natDiv_sub_continuous_le he heL hLU
  have hinner :
      |a * b * M0 + (a + b) * M1 + M2 -
        (a * b * C0 + (a + b) * C1 + C2)| ≤
      8 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(a * b * (M0 - C0) + (a + b) * (M1 - C1)) + (M2 - C2)| := by ring_nf
      _ ≤ |a * b * (M0 - C0) + (a + b) * (M1 - C1)| + |M2 - C2| :=
        abs_add_le _ _
      _ ≤ (|a * b * (M0 - C0)| + |(a + b) * (M1 - C1)|) + |M2 - C2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = (|a * b| * |M0 - C0| + |a + b| * |M1 - C1|) + |M2 - C2| := by
        simp only [abs_mul]
      _ ≤ (K ^ 2 * (2 * (e : ℝ) / (L : ℝ)) +
            (2 * K) * (2 * K * ((e : ℝ) / (L : ℝ)))) +
          2 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by
        exact add_le_add
          (add_le_add
            (mul_le_mul hab h0 (abs_nonneg _) (sq_nonneg K))
            (mul_le_mul habadd h1 (abs_nonneg _) (by positivity))) h2
      _ = 8 * K ^ 2 * ((e : ℝ) / (L : ℝ)) := by ring
  rw [barbanVehovLongSecondLogKernelMain,
    barbanVehovLongSecondLogKernelContinuous]
  change |1 / (e : ℝ) * (a * b * M0 + (a + b) * M1 + M2) -
      1 / (e : ℝ) * (a * b * C0 + (a + b) * C1 + C2)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) *
        |a * b * M0 + (a + b) * M1 + M2 -
          (a * b * C0 + (a + b) * C1 + C2)| ≤
      1 / (e : ℝ) * (8 * K ^ 2 * ((e : ℝ) / (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 8 * Real.log ((U + 1 : ℕ) : ℝ) ^ 2 / (L : ℝ) := by
      dsimp [K]
      field_simp

/-- Uniform base-kernel error through the exact lcm horizon. -/
theorem abs_barbanVehovLongHarmonicKernel_sub_continuous_le_horizon
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongHarmonicKernel L U q r -
        barbanVehovLongHarmonicKernelContinuous L U q r| ≤
      322 / (L : ℝ) := by
  let e := Nat.lcm q r
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := he.trans_le heL
  by_cases hscale : 8 * e ≤ L
  · have hsharp := abs_barbanVehovLongHarmonicKernel_sub_continuous_le
      hq hr hscale hLU
    exact hsharp.trans (by
      apply div_le_div_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 322)
      positivity)
  · have hmain := abs_barbanVehovLongHarmonicKernel_sub_main_le hLU hq hr
    have hend := abs_barbanVehovLongHarmonicKernelMain_sub_continuous_le
      hq hr heL hLU
    have hrec : 40 / (e : ℝ) ≤ 320 / (L : ℝ) := by
      have hlt : L < 8 * e := by omega
      have hltR : (L : ℝ) < 8 * (e : ℝ) := by exact_mod_cast hlt
      rw [div_le_div_iff₀ (by exact_mod_cast he) (by exact_mod_cast hL)]
      nlinarith
    calc
      |barbanVehovLongHarmonicKernel L U q r -
          barbanVehovLongHarmonicKernelContinuous L U q r| ≤
        |barbanVehovLongHarmonicKernel L U q r -
            barbanVehovLongHarmonicKernelMain L U q r| +
          |barbanVehovLongHarmonicKernelMain L U q r -
            barbanVehovLongHarmonicKernelContinuous L U q r| := by
          simpa only [sub_add_sub_cancel] using abs_add_le
            (barbanVehovLongHarmonicKernel L U q r -
              barbanVehovLongHarmonicKernelMain L U q r)
            (barbanVehovLongHarmonicKernelMain L U q r -
              barbanVehovLongHarmonicKernelContinuous L U q r)
      _ ≤ 40 / (e : ℝ) + 2 / (L : ℝ) := add_le_add hmain hend
      _ ≤ 320 / (L : ℝ) + 2 / (L : ℝ) := add_le_add hrec le_rfl
      _ = 322 / (L : ℝ) := by ring

private theorem one_div_lcm_le_eight_div_of_large_fibre
    {L e : ℕ} (he : 0 < e) (hL : 0 < L) (hlarge : ¬ 8 * e ≤ L) :
    1 / (e : ℝ) ≤ 8 / (L : ℝ) := by
  rw [div_le_div_iff₀ (by exact_mod_cast he) (by exact_mod_cast hL)]
  norm_num
  exact_mod_cast (show L ≤ 8 * e by omega)

/-- Uniform first-log kernel error through the exact lcm horizon. -/
theorem abs_barbanVehovLongFirstLogKernel_sub_continuous_le_horizon
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongFirstLogKernel L U q r -
        barbanVehovLongFirstLogKernelContinuous L U q r| ≤
      2000 * (1 + Real.log ((U + 1 : ℕ) : ℝ)) ^ 2 / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / r : ℕ) : ℝ))
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := he.trans_le heL
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hr (Nat.dvd_lcm_right q r) heU
  by_cases hscale : 8 * e ≤ L
  · have hsharp := abs_barbanVehovLongFirstLogKernel_sub_continuous_le
      hq hr hscale hLU
    have hnum : 6 * K ≤ 2000 * (1 + K) ^ 2 := by nlinarith
    exact hsharp.trans (by
      apply div_le_div_of_nonneg_right hnum
      positivity)
  · have hmain := abs_barbanVehovLongFirstLogKernel_sub_main_le hLU hq hr
    have hend := abs_barbanVehovLongFirstLogKernelMain_sub_continuous_le
      hq hr heL hLU
    have hrec := one_div_lcm_le_eight_div_of_large_fibre he hL hscale
    have hnum0 : 0 ≤ 40 * |a| + 200 := by positivity
    have hmain' : (40 * |a| + 200) / (e : ℝ) ≤
        (320 * K + 1600) / (L : ℝ) := by
      calc
        (40 * |a| + 200) / (e : ℝ) =
            (40 * |a| + 200) * (1 / (e : ℝ)) := by ring
        _ ≤ (40 * |a| + 200) * (8 / (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hrec hnum0
        _ ≤ (40 * K + 200) * (8 / (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · positivity
        _ = (320 * K + 1600) / (L : ℝ) := by ring
    have hdom : (320 * K + 1600) / (L : ℝ) + 4 * K / (L : ℝ) ≤
        2000 * (1 + K) ^ 2 / (L : ℝ) := by
      calc
        (320 * K + 1600) / (L : ℝ) + 4 * K / (L : ℝ) =
            (324 * K + 1600) / (L : ℝ) := by ring
        _ ≤ 2000 * (1 + K) ^ 2 / (L : ℝ) := by
          apply div_le_div_of_nonneg_right (by nlinarith)
          positivity
    calc
      |barbanVehovLongFirstLogKernel L U q r -
          barbanVehovLongFirstLogKernelContinuous L U q r| ≤
        |barbanVehovLongFirstLogKernel L U q r -
            barbanVehovLongFirstLogKernelMain L U q r| +
          |barbanVehovLongFirstLogKernelMain L U q r -
            barbanVehovLongFirstLogKernelContinuous L U q r| := by
          simpa only [sub_add_sub_cancel] using abs_add_le
            (barbanVehovLongFirstLogKernel L U q r -
              barbanVehovLongFirstLogKernelMain L U q r)
            (barbanVehovLongFirstLogKernelMain L U q r -
              barbanVehovLongFirstLogKernelContinuous L U q r)
      _ ≤ (40 * |a| + 200) / (e : ℝ) + 4 * K / (L : ℝ) := by
        exact add_le_add hmain hend
      _ ≤ (320 * K + 1600) / (L : ℝ) + 4 * K / (L : ℝ) :=
        add_le_add hmain' le_rfl
      _ ≤ 2000 * (1 + K) ^ 2 / (L : ℝ) := hdom

/-- Uniform second-log kernel error through the exact lcm horizon. -/
theorem abs_barbanVehovLongSecondLogKernel_sub_continuous_le_horizon
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (heL : Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongSecondLogKernel L U q r -
        barbanVehovLongSecondLogKernelContinuous L U q r| ≤
      20000 * (1 + Real.log ((U + 1 : ℕ) : ℝ)) ^ 2 / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / q : ℕ) : ℝ))
  let b := Real.log (((e / r : ℕ) : ℝ))
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := he.trans_le heL
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hq (Nat.dvd_lcm_left q r) heU
  have hb : |b| ≤ K := by
    exact abs_log_natDiv_le_log_succ_hybrid he hr (Nat.dvd_lcm_right q r) heU
  have hab : |a * b| ≤ K ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) hK0]
  have habadd : |a + b| ≤ 2 * K := by
    exact (abs_add_le a b).trans (by linarith)
  by_cases hscale : 8 * e ≤ L
  · have hsharp := abs_barbanVehovLongSecondLogKernel_sub_continuous_le
      hq hr hscale hLU
    have hnum : 12 * K ^ 2 ≤ 20000 * (1 + K) ^ 2 := by nlinarith [sq_nonneg K]
    exact hsharp.trans (by
      apply div_le_div_of_nonneg_right hnum
      positivity)
  · have hmain := abs_barbanVehovLongSecondLogKernel_sub_main_le hLU hq hr
    have hend := abs_barbanVehovLongSecondLogKernelMain_sub_continuous_le
      hq hr heL hLU
    have hrec := one_div_lcm_le_eight_div_of_large_fibre he hL hscale
    have hnum0 : 0 ≤ 40 * |a * b| + 200 * |a + b| + 2000 := by positivity
    have hmain' :
        (40 * |a * b| + 200 * |a + b| + 2000) / (e : ℝ) ≤
          (320 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) := by
      calc
        (40 * |a * b| + 200 * |a + b| + 2000) / (e : ℝ) =
            (40 * |a * b| + 200 * |a + b| + 2000) * (1 / (e : ℝ)) := by ring
        _ ≤ (40 * |a * b| + 200 * |a + b| + 2000) * (8 / (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hrec hnum0
        _ ≤ (40 * K ^ 2 + 400 * K + 2000) * (8 / (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · positivity
        _ = (320 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) := by ring
    have hdom :
        (320 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) +
            8 * K ^ 2 / (L : ℝ) ≤
          20000 * (1 + K) ^ 2 / (L : ℝ) := by
      calc
        (320 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) +
            8 * K ^ 2 / (L : ℝ) =
          (328 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) := by ring
        _ ≤ 20000 * (1 + K) ^ 2 / (L : ℝ) := by
          apply div_le_div_of_nonneg_right (by nlinarith [sq_nonneg K])
          positivity
    calc
      |barbanVehovLongSecondLogKernel L U q r -
          barbanVehovLongSecondLogKernelContinuous L U q r| ≤
        |barbanVehovLongSecondLogKernel L U q r -
            barbanVehovLongSecondLogKernelMain L U q r| +
          |barbanVehovLongSecondLogKernelMain L U q r -
            barbanVehovLongSecondLogKernelContinuous L U q r| := by
          simpa only [sub_add_sub_cancel] using abs_add_le
            (barbanVehovLongSecondLogKernel L U q r -
              barbanVehovLongSecondLogKernelMain L U q r)
            (barbanVehovLongSecondLogKernelMain L U q r -
              barbanVehovLongSecondLogKernelContinuous L U q r)
      _ ≤ (40 * |a * b| + 200 * |a + b| + 2000) / (e : ℝ) +
          8 * K ^ 2 / (L : ℝ) := by
        exact add_le_add hmain hend
      _ ≤ (320 * K ^ 2 + 3200 * K + 16000) / (L : ℝ) +
          8 * K ^ 2 / (L : ℝ) := add_le_add hmain' le_rfl
      _ ≤ 20000 * (1 + K) ^ 2 / (L : ℝ) := hdom

theorem lcm_le_square_of_bounded
    {M q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqM : q ≤ M) (hrM : r ≤ M) :
    Nat.lcm q r ≤ M ^ 2 := by
  exact (Nat.lcm_le_mul hq hr).trans (by
    rw [pow_two]
    exact Nat.mul_le_mul hqM hrM)

/-- Full base lcm moment has bounded discretization error at the quadratic horizon. -/
theorem abs_barbanVehovFullLongBaseLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovFullLongBaseLcm L M -
        barbanVehovFullLongBaseContinuous L M| ≤
      (M : ℝ) ^ 2 * (322 / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongBaseLcm, barbanVehovFullLongBaseContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (322 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongHarmonicKernel_sub_continuous_le_horizon
        hp1.1 hp2.1
        ((lcm_le_square_of_bounded hp1.1 hp2.1 hp1.2 hp2.2).trans hscale) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
              barbanVehovLongHarmonicKernelContinuous L (L * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (322 / (L : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ (M : ℝ) ^ 2 * (322 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_le_quadratic hM) (by positivity)

/-- Full base--derivative cross moment has bounded discretization error at the quadratic horizon. -/
theorem abs_barbanVehovFullLongCrossLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovFullLongCrossLcm L M -
        barbanVehovFullLongCrossContinuous L M| ≤
      (M : ℝ) ^ 2 *
        (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongCrossLcm, barbanVehovFullLongCrossContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongFirstLogKernel_sub_continuous_le_horizon
        hp1.1 hp2.1
        ((lcm_le_square_of_bounded hp1.1 hp2.1 hp1.2 hp2.2).trans hscale) hLU
      calc
        _ = |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2))| := by
                congr 1
                ring
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2| := by
                rw [abs_neg, abs_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ (M : ℝ) ^ 2 *
        (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_le_quadratic hM)
      positivity

/-- Full derivative-square moment has bounded discretization error at the quadratic horizon. -/
theorem abs_barbanVehovFullLongDerivativeLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovFullLongDerivativeLcm L M -
        barbanVehovFullLongDerivativeContinuous L M| ≤
      (M : ℝ) ^ 2 *
        (20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongDerivativeLcm, barbanVehovFullLongDerivativeContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongSecondLogKernel_sub_continuous_le_horizon
        hp1.1 hp2.1
        ((lcm_le_square_of_bounded hp1.1 hp2.1 hp1.2 hp2.2).trans hscale) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongSecondLogKernelContinuous L (L * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ (M : ℝ) ^ 2 *
        (20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_le_quadratic hM)
      positivity

end
end RHTower.Sieve
