import GaloisForLFunctions.RHTower.Sieve.HarmonicLogMomentConstant
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelAsymptotics

/-!
# Barban--Vehov lcm kernels on a window reaching the origin

The long-range lcm kernels are windows `(A, B]` whose two endpoints both carry a factor `1/e`,
`e = [q,r]`, so the logarithm of `e` cancels between them.  A window that starts at the origin has
no lower endpoint to cancel against: its main term keeps `log(X/e)` together with the additive
constant of the harmonic logarithmic moment.

These are the kernels of the *short* range of the mollified detector energy, `k ≤ X`, where the
detector head imposes no restriction.  As long as `8·e ≤ X` — which the Levinson scaling
`e ≤ M² ≤ X/8` guarantees — the error is `O(log^m X / X)` per pair, matching the long-range shape.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- Main term of the origin-based harmonic lcm kernel. -/
def barbanVehovShortHarmonicKernelMain (X q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (harmonicLogMomentPrimitive 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
      harmonicLogMomentTotalConstant 0)

/-- Main term of the origin-based first complementary-divisor log kernel. -/
def barbanVehovShortFirstLogKernelMain (X q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
        (harmonicLogMomentPrimitive 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 0) +
      (harmonicLogMomentPrimitive 1 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
        harmonicLogMomentTotalConstant 1))

/-- Main term of the origin-based second complementary-divisor log kernel. -/
def barbanVehovShortSecondLogKernelMain (X q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) * Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
        (harmonicLogMomentPrimitive 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 0) +
      (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) + Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
        (harmonicLogMomentPrimitive 1 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 1) +
      (harmonicLogMomentPrimitive 2 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
        harmonicLogMomentTotalConstant 2))

/-- The origin-based harmonic lcm kernel, with its additive constant. -/
theorem abs_barbanVehovLongHarmonicKernel_zeroStart_sub_main_le
    {X q r : ℕ} (hq : 0 < q) (hr : 0 < r) (h8 : 8 ≤ X / Nat.lcm q r) :
    |barbanVehovLongHarmonicKernel 0 X q r - barbanVehovShortHarmonicKernelMain X q r| ≤
      RHTower.logPowDivId 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) / (Nat.lcm q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hmoment := abs_harmonicLogWindowMoment_zeroStart_zero_sub_le h8
  rw [barbanVehovLongHarmonicKernel_eq_moment hq hr, barbanVehovShortHarmonicKernelMain,
    Nat.zero_div, ← mul_sub, abs_mul,
    abs_of_nonneg (show 0 ≤ 1 / (Nat.lcm q r : ℝ) by positivity)]
  calc
    1 / (Nat.lcm q r : ℝ) *
        |harmonicLogWindowMoment 0 0 (X / Nat.lcm q r) -
          (harmonicLogMomentPrimitive 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
            harmonicLogMomentTotalConstant 0)| ≤
        1 / (Nat.lcm q r : ℝ) *
          RHTower.logPowDivId 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by ring

/-- The origin-based first log lcm kernel, with its additive constants. -/
theorem abs_barbanVehovLongFirstLogKernel_zeroStart_sub_main_le
    {X q r : ℕ} (hq : 0 < q) (hr : 0 < r) (h8 : 8 ≤ X / Nat.lcm q r) :
    |barbanVehovLongFirstLogKernel 0 X q r - barbanVehovShortFirstLogKernelMain X q r| ≤
      (|Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| *
          RHTower.logPowDivId 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
        RHTower.logPowDivId 1 ((X / Nat.lcm q r + 1 : ℕ) : ℝ)) / (Nat.lcm q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  set e := Nat.lcm q r with hedef
  set a := Real.log (((e / r : ℕ) : ℝ)) with hadef
  set A := X / e with hAdef
  have h0 := abs_harmonicLogWindowMoment_zeroStart_zero_sub_le h8
  have h1 := abs_harmonicLogWindowMoment_zeroStart_one_sub_le h8
  rw [barbanVehovLongFirstLogKernel_eq_moments hq hr, barbanVehovShortFirstLogKernelMain,
    Nat.zero_div, ← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  have hinner :
      |a * harmonicLogWindowMoment 0 0 A + harmonicLogWindowMoment 1 0 A -
          (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 0) +
            (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 1))| ≤
        |a| * RHTower.logPowDivId 0 ((A + 1 : ℕ) : ℝ) +
          RHTower.logPowDivId 1 ((A + 1 : ℕ) : ℝ) := by
    have hsplit :
        a * harmonicLogWindowMoment 0 0 A + harmonicLogWindowMoment 1 0 A -
            (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 0) +
              (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 1)) =
          a * (harmonicLogWindowMoment 0 0 A -
              (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 0)) +
            (harmonicLogWindowMoment 1 0 A -
              (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 1)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg a)) h1
  calc
    1 / (e : ℝ) *
        |a * harmonicLogWindowMoment 0 0 A + harmonicLogWindowMoment 1 0 A -
          (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 0) +
            (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 1))| ≤
        1 / (e : ℝ) * (|a| * RHTower.logPowDivId 0 ((A + 1 : ℕ) : ℝ) +
          RHTower.logPowDivId 1 ((A + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by ring

/-- The origin-based second log lcm kernel, with its additive constants. -/
theorem abs_barbanVehovLongSecondLogKernel_zeroStart_sub_main_le
    {X q r : ℕ} (hq : 0 < q) (hr : 0 < r) (h8 : 8 ≤ X / Nat.lcm q r) :
    |barbanVehovLongSecondLogKernel 0 X q r - barbanVehovShortSecondLogKernelMain X q r| ≤
      (|Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) * Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| *
            RHTower.logPowDivId 0 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
          |Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) + Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| *
            RHTower.logPowDivId 1 ((X / Nat.lcm q r + 1 : ℕ) : ℝ) +
          RHTower.logPowDivId 2 ((X / Nat.lcm q r + 1 : ℕ) : ℝ)) / (Nat.lcm q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  set e := Nat.lcm q r with hedef
  set a := Real.log (((e / q : ℕ) : ℝ)) * Real.log (((e / r : ℕ) : ℝ)) with hadef
  set b := Real.log (((e / q : ℕ) : ℝ)) + Real.log (((e / r : ℕ) : ℝ)) with hbdef
  set A := X / e with hAdef
  have h0 := abs_harmonicLogWindowMoment_zeroStart_zero_sub_le h8
  have h1 := abs_harmonicLogWindowMoment_zeroStart_one_sub_le h8
  have h2 := abs_harmonicLogWindowMoment_zeroStart_two_sub_le h8
  rw [barbanVehovLongSecondLogKernel_eq_moments hq hr, barbanVehovShortSecondLogKernelMain,
    Nat.zero_div, ← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ 1 / (e : ℝ) by positivity)]
  have hinner :
      |a * harmonicLogWindowMoment 0 0 A + b * harmonicLogWindowMoment 1 0 A +
            harmonicLogWindowMoment 2 0 A -
          (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 0) +
            b * (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 1) +
            (harmonicLogMomentPrimitive 2 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 2))| ≤
        |a| * RHTower.logPowDivId 0 ((A + 1 : ℕ) : ℝ) +
          |b| * RHTower.logPowDivId 1 ((A + 1 : ℕ) : ℝ) +
          RHTower.logPowDivId 2 ((A + 1 : ℕ) : ℝ) := by
    have hsplit :
        a * harmonicLogWindowMoment 0 0 A + b * harmonicLogWindowMoment 1 0 A +
              harmonicLogWindowMoment 2 0 A -
            (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 0) +
              b * (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 1) +
              (harmonicLogMomentPrimitive 2 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 2)) =
          a * (harmonicLogWindowMoment 0 0 A -
              (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 0)) +
            b * (harmonicLogWindowMoment 1 0 A -
              (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 1)) +
            (harmonicLogWindowMoment 2 0 A -
              (harmonicLogMomentPrimitive 2 ((A + 1 : ℕ) : ℝ) +
                harmonicLogMomentTotalConstant 2)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans ?_) h2
    refine add_le_add ?_ ?_
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h0 (abs_nonneg a)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg b)
  calc
    1 / (e : ℝ) *
        |a * harmonicLogWindowMoment 0 0 A + b * harmonicLogWindowMoment 1 0 A +
            harmonicLogWindowMoment 2 0 A -
          (a * (harmonicLogMomentPrimitive 0 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 0) +
            b * (harmonicLogMomentPrimitive 1 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 1) +
            (harmonicLogMomentPrimitive 2 ((A + 1 : ℕ) : ℝ) +
              harmonicLogMomentTotalConstant 2))| ≤
        1 / (e : ℝ) * (|a| * RHTower.logPowDivId 0 ((A + 1 : ℕ) : ℝ) +
          |b| * RHTower.logPowDivId 1 ((A + 1 : ℕ) : ℝ) +
          RHTower.logPowDivId 2 ((A + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = _ := by ring


/-- The per-pair kernel error of an origin-based window is `O(log^m X / X)`, uniformly in the
lcm: the reciprocal of the rescaled endpoint absorbs the lcm exactly. -/
theorem logPowDivId_succ_div_le {m X e : ℕ} (hX : 0 < X) (he : 0 < e) :
    RHTower.logPowDivId m ((X / e + 1 : ℕ) : ℝ) / (e : ℝ) ≤
      Real.log ((X + 1 : ℕ) : ℝ) ^ m / (X : ℝ) := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hAle : X / e + 1 ≤ X + 1 := by
    have := Nat.div_le_self X e
    omega
  have hApos : (0 : ℝ) < ((X / e + 1 : ℕ) : ℝ) := by
    have : 0 < X / e + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ ((X / e + 1 : ℕ) : ℝ) := by
    have : 1 ≤ X / e + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have hlogle : Real.log ((X / e + 1 : ℕ) : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
    refine Real.log_le_log hApos ?_
    exact_mod_cast hAle
  have hlognn : (0 : ℝ) ≤ Real.log ((X / e + 1 : ℕ) : ℝ) := Real.log_nonneg hone
  have hXlt : X < e * (X / e + 1) := by
    have hmod := Nat.div_add_mod X e
    have hlt := Nat.mod_lt X he
    nlinarith [hmod, hlt]
  have hXA : (X : ℝ) ≤ ((X / e + 1 : ℕ) : ℝ) * (e : ℝ) := by
    have : (X : ℝ) ≤ ((e * (X / e + 1) : ℕ) : ℝ) := by exact_mod_cast hXlt.le
    push_cast at this ⊢
    linarith
  rw [RHTower.logPowDivId, div_div]
  calc Real.log ((X / e + 1 : ℕ) : ℝ) ^ m / (((X / e + 1 : ℕ) : ℝ) * (e : ℝ))
      ≤ Real.log ((X + 1 : ℕ) : ℝ) ^ m / (((X / e + 1 : ℕ) : ℝ) * (e : ℝ)) := by
        gcongr
    _ ≤ Real.log ((X + 1 : ℕ) : ℝ) ^ m / (X : ℝ) := by
        have hnn : (0 : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) ^ m := by
          refine pow_nonneg (Real.log_nonneg ?_) m
          have : (1 : ℕ) ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le _)
          exact_mod_cast this
        gcongr

end RHTower.Sieve

end
