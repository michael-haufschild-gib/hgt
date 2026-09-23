import GaloisForLFunctions.RHTower.Sieve.HarmonicNatDivContinuousError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelMoments

namespace RHTower.Sieve

noncomputable section

/-- Continuous-quotient main term for the undifferentiated long lcm fibre. -/
def barbanVehovLongHarmonicKernelContinuous (L U q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log ((U : ℝ) / (Nat.lcm q r : ℝ)) -
      Real.log ((L : ℝ) / (Nat.lcm q r : ℝ)))

/-- Continuous-quotient main term for the first differentiated long lcm fibre. -/
def barbanVehovLongFirstLogKernelContinuous (L U q r : ℕ) : ℝ :=
  let e := Nat.lcm q r
  1 / (e : ℝ) *
    (Real.log (((e / r : ℕ) : ℝ)) *
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))) +
      (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
        Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2))

/-- Continuous-quotient main term for the twice differentiated long lcm fibre. -/
def barbanVehovLongSecondLogKernelContinuous (L U q r : ℕ) : ℝ :=
  let e := Nat.lcm q r
  1 / (e : ℝ) *
    (Real.log (((e / q : ℕ) : ℝ)) * Real.log (((e / r : ℕ) : ℝ)) *
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))) +
      (Real.log (((e / q : ℕ) : ℝ)) + Real.log (((e / r : ℕ) : ℝ))) *
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2) +
      (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
        Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3))

private theorem abs_log_natDiv_le_log_succ
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

theorem abs_barbanVehovLongHarmonicKernel_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hscale : 8 * Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongHarmonicKernel L U q r -
        barbanVehovLongHarmonicKernelContinuous L U q r| ≤
      3 / (L : ℝ) := by
  let e := Nat.lcm q r
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := by nlinarith
  have h0 := abs_harmonicLogWindowMoment_zero_natDiv_sub_continuous_le
    he hscale hLU
  rw [barbanVehovLongHarmonicKernel_eq_moment hq hr,
    barbanVehovLongHarmonicKernelContinuous]
  change |1 / (e : ℝ) * harmonicLogWindowMoment 0 (L / e) (U / e) -
      1 / (e : ℝ) *
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) *
        |harmonicLogWindowMoment 0 (L / e) (U / e) -
          (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤
      1 / (e : ℝ) * (3 * (e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
    _ = 3 / (L : ℝ) := by field_simp

theorem abs_barbanVehovLongFirstLogKernel_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hscale : 8 * Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongFirstLogKernel L U q r -
        barbanVehovLongFirstLogKernelContinuous L U q r| ≤
      6 * Real.log ((U + 1 : ℕ) : ℝ) / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / r : ℕ) : ℝ))
  let H0 := harmonicLogWindowMoment 0 (L / e) (U / e)
  let H1 := harmonicLogWindowMoment 1 (L / e) (U / e)
  let C0 := Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))
  let C1 := Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := by nlinarith
  have heL : e ≤ L := by nlinarith
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ he hr (Nat.dvd_lcm_right q r) heU
  have h0 : |H0 - C0| ≤ 3 * (e : ℝ) / (L : ℝ) := by
    exact abs_harmonicLogWindowMoment_zero_natDiv_sub_continuous_le he hscale hLU
  have h1 : |H1 - C1| ≤ 3 * K * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMoment_one_natDiv_sub_continuous_le he hscale hLU
  have hinner : |a * H0 + H1 - (a * C0 + C1)| ≤
      6 * K * ((e : ℝ) / (L : ℝ)) := by
    calc
      |a * H0 + H1 - (a * C0 + C1)| = |a * (H0 - C0) + (H1 - C1)| := by ring_nf
      _ ≤ |a * (H0 - C0)| + |H1 - C1| := abs_add_le _ _
      _ = |a| * |H0 - C0| + |H1 - C1| := by rw [abs_mul]
      _ ≤ K * (3 * (e : ℝ) / (L : ℝ)) +
          3 * K * ((e : ℝ) / (L : ℝ)) :=
        add_le_add (mul_le_mul ha h0 (abs_nonneg _) hK0) h1
      _ = 6 * K * ((e : ℝ) / (L : ℝ)) := by ring
  rw [barbanVehovLongFirstLogKernel_eq_moments hq hr,
    barbanVehovLongFirstLogKernelContinuous]
  change |1 / (e : ℝ) * (a * H0 + H1) -
      1 / (e : ℝ) * (a * C0 + C1)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) * |a * H0 + H1 - (a * C0 + C1)| ≤
        1 / (e : ℝ) * (6 * K * ((e : ℝ) / (L : ℝ))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 6 * Real.log ((U + 1 : ℕ) : ℝ) / (L : ℝ) := by
      dsimp [K]
      field_simp

theorem abs_barbanVehovLongSecondLogKernel_sub_continuous_le
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hscale : 8 * Nat.lcm q r ≤ L) (hLU : L ≤ U) :
    |barbanVehovLongSecondLogKernel L U q r -
        barbanVehovLongSecondLogKernelContinuous L U q r| ≤
      12 * Real.log ((U + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / q : ℕ) : ℝ))
  let b := Real.log (((e / r : ℕ) : ℝ))
  let H0 := harmonicLogWindowMoment 0 (L / e) (U / e)
  let H1 := harmonicLogWindowMoment 1 (L / e) (U / e)
  let H2 := harmonicLogWindowMoment 2 (L / e) (U / e)
  let C0 := Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))
  let C1 := Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2
  let C2 := Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
    Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3
  let K := Real.log ((U + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hL : 0 < L := by nlinarith
  have heL : e ≤ L := by nlinarith
  have heU : e ≤ U := heL.trans hLU
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have ha : |a| ≤ K := by
    exact abs_log_natDiv_le_log_succ he hq (Nat.dvd_lcm_left q r) heU
  have hb : |b| ≤ K := by
    exact abs_log_natDiv_le_log_succ he hr (Nat.dvd_lcm_right q r) heU
  have hab : |a * b| ≤ K ^ (2 : ℕ) := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) hK0]
  have habadd : |a + b| ≤ 2 * K := by
    exact (abs_add_le a b).trans (by linarith)
  have h0 : |H0 - C0| ≤ 3 * (e : ℝ) / (L : ℝ) := by
    exact abs_harmonicLogWindowMoment_zero_natDiv_sub_continuous_le he hscale hLU
  have h1 : |H1 - C1| ≤ 3 * K * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMoment_one_natDiv_sub_continuous_le he hscale hLU
  have h2 : |H2 - C2| ≤ 3 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    exact abs_harmonicLogWindowMoment_two_natDiv_sub_continuous_le he hscale hLU
  have hinner :
      |a * b * H0 + (a + b) * H1 + H2 -
        (a * b * C0 + (a + b) * C1 + C2)| ≤
      12 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(a * b * (H0 - C0) + (a + b) * (H1 - C1)) + (H2 - C2)| := by ring_nf
      _ ≤ |a * b * (H0 - C0) + (a + b) * (H1 - C1)| + |H2 - C2| :=
        abs_add_le _ _
      _ ≤ (|a * b * (H0 - C0)| + |(a + b) * (H1 - C1)|) + |H2 - C2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = (|a * b| * |H0 - C0| + |a + b| * |H1 - C1|) + |H2 - C2| := by
        simp only [abs_mul]
      _ ≤ (K ^ (2 : ℕ) * (3 * (e : ℝ) / (L : ℝ)) +
            (2 * K) * (3 * K * ((e : ℝ) / (L : ℝ)))) +
          3 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
        exact add_le_add
          (add_le_add
            (mul_le_mul hab h0 (abs_nonneg _) (sq_nonneg K))
            (mul_le_mul habadd h1 (abs_nonneg _) (by positivity))) h2
      _ = 12 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by ring
  rw [barbanVehovLongSecondLogKernel_eq_moments hq hr,
    barbanVehovLongSecondLogKernelContinuous]
  change |1 / (e : ℝ) * (a * b * H0 + (a + b) * H1 + H2) -
      1 / (e : ℝ) * (a * b * C0 + (a + b) * C1 + C2)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  calc
    1 / (e : ℝ) *
        |a * b * H0 + (a + b) * H1 + H2 -
          (a * b * C0 + (a + b) * C1 + C2)| ≤
      1 / (e : ℝ) * (12 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 12 * Real.log ((U + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
      dsimp [K]
      field_simp

end

end RHTower.Sieve
