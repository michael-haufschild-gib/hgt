import GaloisForLFunctions.RHTower.PutnamKernelLimits
import GaloisForLFunctions.RHTower.PutnamPeriodization
import GaloisForLFunctions.HTGeometry.UniformTsumLimit

/-!
# One-sided limits of the periodised kernel

The translate series is normally convergent on every bounded set, so its one-sided limits are the
term-by-term ones.  The left limit differs from the value by the jump of `⌊e^x⌋`, which is
supported on the integer points of the exponential.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

/-- The left limit of the kernel, written as the value plus the jump. -/
def putnamKernelLeft (a : ℝ) (z : ℝ) : ℂ :=
  putnamKernel a z
    + ((⌊Real.exp z⌋ - ⌈Real.exp z⌉ + 1 : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * z)

theorem tendsto_putnamKernel_left' (a y : ℝ) :
    Tendsto (putnamKernel a) (𝓝[<] y) (𝓝 (putnamKernelLeft a y)) := by
  have h := tendsto_putnamKernel_left a y
  refine h.congr' (Eventually.of_forall fun _ => rfl) |>.mono_right (le_of_eq ?_)
  congr 1
  rw [putnamKernelLeft, putnamKernel_eq_floor]
  push_cast
  ring

theorem norm_putnamKernelLeft_le (a z : ℝ) :
    ‖putnamKernelLeft a z‖ ≤ 2 * Real.exp (-(|z| / 2)) := by
  have hK := norm_putnamKernel_le a z
  rcases lt_or_ge z 0 with hz | hz
  · have hlt : Real.exp z < 1 := by simpa using Real.exp_lt_one_iff.mpr hz
    have hpos : (0 : ℝ) < Real.exp z := Real.exp_pos z
    have hfl : ⌊Real.exp z⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      exact ⟨hpos.le, hlt⟩
    have hce : ⌈Real.exp z⌉ = 1 := by
      refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast
        linarith
      · push_cast
        linarith
    have hzero : ((⌊Real.exp z⌋ - ⌈Real.exp z⌉ + 1 : ℤ) : ℂ) = 0 := by
      rw [hfl, hce]
      norm_num
    rw [putnamKernelLeft, hzero, zero_mul, add_zero]
    have hnn : (0 : ℝ) ≤ Real.exp (-(|z| / 2)) := (Real.exp_pos _).le
    linarith
  · have hcoef : ‖((⌊Real.exp z⌋ - ⌈Real.exp z⌉ + 1 : ℤ) : ℂ)‖ ≤ 1 := by
      have h1 : ⌊Real.exp z⌋ ≤ ⌈Real.exp z⌉ := Int.floor_le_ceil _
      have h2 : ⌈Real.exp z⌉ ≤ ⌊Real.exp z⌋ + 1 := Int.ceil_le_floor_add_one _
      have hb : ((⌊Real.exp z⌋ - ⌈Real.exp z⌉ + 1 : ℤ)) = 0 ∨
          ((⌊Real.exp z⌋ - ⌈Real.exp z⌉ + 1 : ℤ)) = 1 := by omega
      rcases hb with hb | hb <;> rw [hb] <;> norm_num
    have hexpn : ‖Complex.exp (-(1 / 2 + (a : ℂ) * I) * (z : ℂ))‖ = Real.exp (-(z / 2)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
      ring
    rw [abs_of_nonneg hz] at hK
    rw [putnamKernelLeft]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, hexpn, abs_of_nonneg hz]
    have hnn : (0 : ℝ) ≤ Real.exp (-(z / 2)) := (Real.exp_pos _).le
    nlinarith [hK, hcoef, hnn]

theorem summable_putnamKernelLeft_translates {a d : ℝ} (hd : 0 < d) (x : ℝ) :
    Summable (fun k : ℤ => putnamKernelLeft a (x + (k : ℝ) * putnamPeriod d)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  refine Summable.of_norm_bounded
    (g := fun k : ℤ => 2 * (Real.exp (|x| / 2) * Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|))))
    (((summable_exp_neg_abs_int (r := putnamPeriod d / 2) (by positivity)).mul_left
      (Real.exp (|x| / 2))).mul_left 2) (fun k => ?_)
  refine le_trans (norm_putnamKernelLeft_le a _) ?_
  have hstep : Real.exp (-(|x + (k : ℝ) * putnamPeriod d| / 2))
      ≤ Real.exp (|x| / 2) * Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs : |(k : ℝ)| * putnamPeriod d - |x| ≤ |x + (k : ℝ) * putnamPeriod d| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * putnamPeriod d) (-x)
      rw [abs_neg, sub_neg_eq_add] at h
      have h2 : |(k : ℝ) * putnamPeriod d| = |(k : ℝ)| * putnamPeriod d := by
        rw [abs_mul, abs_of_pos hP]
      rw [h2] at h
      have h3 : |(k : ℝ) * putnamPeriod d + x| = |x + (k : ℝ) * putnamPeriod d| := by rw [add_comm]
      rw [h3] at h
      linarith
    linarith
  linarith [hstep, (Real.exp_pos (-(|x + (k : ℝ) * putnamPeriod d| / 2))).le]

theorem tendsto_putnamPeriodization_right {a d : ℝ} (hd : 0 < d) (y : ℝ) :
    Tendsto (putnamPeriodization a d) (𝓝[>] y)
      (𝓝 (∑' k : ℤ, putnamKernel a (y + (k : ℝ) * putnamPeriod d))) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  set P : ℝ := putnamPeriod d with hPdef
  have hmem : Icc (y - P) (y + P) ∈ 𝓝[>] y :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
  refine HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on (s := Icc (y - P) (y + P)) hmem
    (u := fun k : ℤ => Real.exp ((|y| + P) / 2) * Real.exp (-(P / 2 * |(k : ℝ)|)))
    ((summable_exp_neg_abs_int (r := P / 2) (by positivity)).mul_left _)
    (fun k x hx => ?_) (summable_putnamKernel_translates hd y) (fun k => ?_)
  · refine le_trans (norm_putnamKernel_le a _) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hxb : |x| ≤ |y| + P := by
      rw [abs_le]
      constructor
      · have := hx.1
        have := abs_nonneg y
        have hy := neg_abs_le y
        linarith [hx.1, neg_abs_le y]
      · have := hx.2
        linarith [le_abs_self y]
    have habs : |(k : ℝ)| * P - |x| ≤ |x + (k : ℝ) * P| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * P) (-x)
      rw [abs_neg, sub_neg_eq_add] at h
      have h2 : |(k : ℝ) * P| = |(k : ℝ)| * P := by rw [abs_mul, abs_of_pos hP]
      rw [h2] at h
      have h3 : |(k : ℝ) * P + x| = |x + (k : ℝ) * P| := by rw [add_comm]
      rw [h3] at h
      linarith
    linarith
  · have hshift : Tendsto (fun x : ℝ => x + (k : ℝ) * P) (𝓝[>] y)
        (𝓝[>] (y + (k : ℝ) * P)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_add_const _).continuousAt.continuousWithinAt) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mem_Ioi.mpr (by
        have := mem_Ioi.mp hx
        linarith)
    exact (tendsto_putnamKernel_right a _).comp hshift

theorem tendsto_putnamPeriodization_left {a d : ℝ} (hd : 0 < d) (y : ℝ) :
    Tendsto (putnamPeriodization a d) (𝓝[<] y)
      (𝓝 (∑' k : ℤ, putnamKernelLeft a (y + (k : ℝ) * putnamPeriod d))) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  set P : ℝ := putnamPeriod d with hPdef
  have hmem : Icc (y - P) (y + P) ∈ 𝓝[<] y :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
  refine HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on (s := Icc (y - P) (y + P)) hmem
    (u := fun k : ℤ => Real.exp ((|y| + P) / 2) * Real.exp (-(P / 2 * |(k : ℝ)|)))
    ((summable_exp_neg_abs_int (r := P / 2) (by positivity)).mul_left _)
    (fun k x hx => ?_) (summable_putnamKernelLeft_translates hd y) (fun k => ?_)
  · refine le_trans (norm_putnamKernel_le a _) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hxb : |x| ≤ |y| + P := by
      rw [abs_le]
      constructor
      · linarith [hx.1, neg_abs_le y]
      · linarith [hx.2, le_abs_self y]
    have habs : |(k : ℝ)| * P - |x| ≤ |x + (k : ℝ) * P| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * P) (-x)
      rw [abs_neg, sub_neg_eq_add] at h
      have h2 : |(k : ℝ) * P| = |(k : ℝ)| * P := by rw [abs_mul, abs_of_pos hP]
      rw [h2] at h
      have h3 : |(k : ℝ) * P + x| = |x + (k : ℝ) * P| := by rw [add_comm]
      rw [h3] at h
      linarith
    linarith
  · have hshift : Tendsto (fun x : ℝ => x + (k : ℝ) * P) (𝓝[<] y)
        (𝓝[<] (y + (k : ℝ) * P)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_add_const _).continuousAt.continuousWithinAt) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mem_Iio.mpr (by
        have := mem_Iio.mp hx
        linarith)
    exact (tendsto_putnamKernel_left' a _).comp hshift

end RHTower

end
