import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowLowerMoments

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Integral main term for a harmonic logarithmic window moment. -/
def harmonicLogWindowMain (m A B : ℕ) : ℝ :=
  harmonicLogMomentPrimitive m (B + 1 : ℕ) -
    harmonicLogMomentPrimitive m (A + 1 : ℕ)

theorem abs_harmonicLogWindowMoment_zero_sub_main_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 0 A B - harmonicLogWindowMain 0 A B| ≤ 40 := by
  have h := abs_harmonicLogWindowMoment_zero_sub_log_uniform_le hAB
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive] at h ⊢
  exact h

theorem abs_harmonicLogWindowMoment_one_sub_main_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 1 A B - harmonicLogWindowMain 1 A B| ≤ 200 := by
  have h := abs_harmonicLogWindowMoment_one_sub_logSquare_uniform_le hAB
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive] at h ⊢
  exact h

theorem abs_harmonicLogWindowMoment_two_sub_main_le
    {A B : ℕ} (hAB : A ≤ B) :
    |harmonicLogWindowMoment 2 A B - harmonicLogWindowMain 2 A B| ≤ 2000 := by
  have h := abs_harmonicLogWindowMoment_two_sub_cubic_uniform_le hAB
  norm_num [harmonicLogWindowMain, harmonicLogMomentPrimitive] at h ⊢
  exact h

/-- Integral-model main term for the undifferentiated long lcm fibre. -/
def barbanVehovLongHarmonicKernelMain (L U q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    harmonicLogWindowMain 0 (L / Nat.lcm q r) (U / Nat.lcm q r)

/-- Integral-model main term for the first differentiated long lcm fibre. -/
def barbanVehovLongFirstLogKernelMain (L U q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
        harmonicLogWindowMain 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
      harmonicLogWindowMain 1 (L / Nat.lcm q r) (U / Nat.lcm q r))

/-- Integral-model main term for the twice differentiated long lcm fibre. -/
def barbanVehovLongSecondLogKernelMain (L U q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
          Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
          harmonicLogWindowMain 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
      (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
          Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
          harmonicLogWindowMain 1 (L / Nat.lcm q r) (U / Nat.lcm q r) +
      harmonicLogWindowMain 2 (L / Nat.lcm q r) (U / Nat.lcm q r))

theorem abs_barbanVehovLongHarmonicKernel_sub_main_le
    {L U q r : ℕ} (hLU : L ≤ U) (hq : 0 < q) (hr : 0 < r) :
    |barbanVehovLongHarmonicKernel L U q r -
        barbanVehovLongHarmonicKernelMain L U q r| ≤
      40 / (Nat.lcm q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hdiv : L / Nat.lcm q r ≤ U / Nat.lcm q r := Nat.div_le_div_right hLU
  have hmoment := abs_harmonicLogWindowMoment_zero_sub_main_le hdiv
  rw [barbanVehovLongHarmonicKernel_eq_moment hq hr,
    barbanVehovLongHarmonicKernelMain, ← mul_sub, abs_mul]
  rw [abs_of_nonneg (show 0 ≤ 1 / (Nat.lcm q r : ℝ) by positivity)]
  calc
    1 / (Nat.lcm q r : ℝ) *
        |harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) -
          harmonicLogWindowMain 0 (L / Nat.lcm q r) (U / Nat.lcm q r)| ≤
      1 / (Nat.lcm q r : ℝ) * 40 :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 40 / (Nat.lcm q r : ℝ) := by ring

theorem abs_barbanVehovLongFirstLogKernel_sub_main_le
    {L U q r : ℕ} (hLU : L ≤ U) (hq : 0 < q) (hr : 0 < r) :
    |barbanVehovLongFirstLogKernel L U q r -
        barbanVehovLongFirstLogKernelMain L U q r| ≤
      (40 * |Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| + 200) /
        (Nat.lcm q r : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / r : ℕ) : ℝ))
  let H0 := harmonicLogWindowMoment 0 (L / e) (U / e)
  let H1 := harmonicLogWindowMoment 1 (L / e) (U / e)
  let M0 := harmonicLogWindowMain 0 (L / e) (U / e)
  let M1 := harmonicLogWindowMain 1 (L / e) (U / e)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hdiv : L / e ≤ U / e := Nat.div_le_div_right hLU
  have h0 : |H0 - M0| ≤ 40 := abs_harmonicLogWindowMoment_zero_sub_main_le hdiv
  have h1 : |H1 - M1| ≤ 200 := abs_harmonicLogWindowMoment_one_sub_main_le hdiv
  rw [barbanVehovLongFirstLogKernel_eq_moments hq hr,
    barbanVehovLongFirstLogKernelMain]
  change |1 / (e : ℝ) * (a * H0 + H1) - 1 / (e : ℝ) * (a * M0 + M1)| ≤
    (40 * |a| + 200) / (e : ℝ)
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  have hinner : |a * H0 + H1 - (a * M0 + M1)| ≤ |a| * 40 + 200 := by
    calc
      |a * H0 + H1 - (a * M0 + M1)| = |a * (H0 - M0) + (H1 - M1)| := by ring_nf
      _ ≤ |a * (H0 - M0)| + |H1 - M1| := abs_add_le _ _
      _ = |a| * |H0 - M0| + |H1 - M1| := by rw [abs_mul]
      _ ≤ |a| * 40 + 200 := add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg a)) h1
  calc
    1 / (e : ℝ) * |a * H0 + H1 - (a * M0 + M1)| ≤
        1 / (e : ℝ) * (|a| * 40 + 200) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (40 * |a| + 200) / (e : ℝ) := by ring

theorem abs_barbanVehovLongSecondLogKernel_sub_main_le
    {L U q r : ℕ} (hLU : L ≤ U) (hq : 0 < q) (hr : 0 < r) :
    |barbanVehovLongSecondLogKernel L U q r -
        barbanVehovLongSecondLogKernelMain L U q r| ≤
      (40 * |Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
          Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| +
        200 * |Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
          Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| + 2000) /
        (Nat.lcm q r : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / q : ℕ) : ℝ)) * Real.log (((e / r : ℕ) : ℝ))
  let b := Real.log (((e / q : ℕ) : ℝ)) + Real.log (((e / r : ℕ) : ℝ))
  let H0 := harmonicLogWindowMoment 0 (L / e) (U / e)
  let H1 := harmonicLogWindowMoment 1 (L / e) (U / e)
  let H2 := harmonicLogWindowMoment 2 (L / e) (U / e)
  let M0 := harmonicLogWindowMain 0 (L / e) (U / e)
  let M1 := harmonicLogWindowMain 1 (L / e) (U / e)
  let M2 := harmonicLogWindowMain 2 (L / e) (U / e)
  have he : 0 < e := Nat.lcm_pos hq hr
  have hdiv : L / e ≤ U / e := Nat.div_le_div_right hLU
  have h0 : |H0 - M0| ≤ 40 := abs_harmonicLogWindowMoment_zero_sub_main_le hdiv
  have h1 : |H1 - M1| ≤ 200 := abs_harmonicLogWindowMoment_one_sub_main_le hdiv
  have h2 : |H2 - M2| ≤ 2000 := abs_harmonicLogWindowMoment_two_sub_main_le hdiv
  rw [barbanVehovLongSecondLogKernel_eq_moments hq hr,
    barbanVehovLongSecondLogKernelMain]
  change |1 / (e : ℝ) * (a * H0 + b * H1 + H2) -
      1 / (e : ℝ) * (a * M0 + b * M1 + M2)| ≤
    (40 * |a| + 200 * |b| + 2000) / (e : ℝ)
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  have hinner : |a * H0 + b * H1 + H2 - (a * M0 + b * M1 + M2)| ≤
      |a| * 40 + |b| * 200 + 2000 := by
    calc
      |a * H0 + b * H1 + H2 - (a * M0 + b * M1 + M2)| =
          |(a * (H0 - M0) + b * (H1 - M1)) + (H2 - M2)| := by ring_nf
      _ ≤ |a * (H0 - M0) + b * (H1 - M1)| + |H2 - M2| := abs_add_le _ _
      _ ≤ (|a * (H0 - M0)| + |b * (H1 - M1)|) + |H2 - M2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = (|a| * |H0 - M0| + |b| * |H1 - M1|) + |H2 - M2| := by
        simp only [abs_mul]
      _ ≤ (|a| * 40 + |b| * 200) + 2000 :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg a))
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg b))) h2
      _ = |a| * 40 + |b| * 200 + 2000 := by ring
  calc
    1 / (e : ℝ) * |a * H0 + b * H1 + H2 - (a * M0 + b * M1 + M2)| ≤
        1 / (e : ℝ) * (|a| * 40 + |b| * 200 + 2000) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (40 * |a| + 200 * |b| + 2000) / (e : ℝ) := by ring

end

end RHTower.Sieve
