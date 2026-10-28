import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The finite part of the logarithmic harmonic sum

Subtracting half the squared logarithm from the logarithmic harmonic sum leaves
a convergent sequence. Its increments are dominated by `(log n + 1) / n²`.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

/-- The logarithm-weighted harmonic sum. -/
def logarithmicHarmonic (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)

/-- The summable error between a logarithmic harmonic increment and the
corresponding squared-logarithm increment. -/
def logarithmicHarmonicError (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) -
    (Real.log ((n : ℝ) + 1) ^ 2 - Real.log n ^ 2) / 2

theorem abs_logarithmicHarmonicError_le (n : ℕ) :
    |logarithmicHarmonicError n| ≤ (Real.log n + 1) / (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logarithmicHarmonicError]
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let r := Real.log ((n : ℝ) + 1) - Real.log n
  let t := 1 / (n : ℝ)
  let s := 1 / ((n : ℝ) + 1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hx1
  have hrlo : s ≤ r := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
    rw [Real.log_div hx.ne' (by positivity)] at h
    have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -s := by dsimp [s]; field_simp; ring
    rw [heq] at h
    dsimp [r]
    linarith only [h]
  have hrhi : r ≤ t := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by positivity) hx.ne'] at h
    have heq : ((n : ℝ) + 1) / n - 1 = t := by dsimp [t]; field_simp; ring
    rwa [heq] at h
  have hgap : t - s ≤ t ^ 2 := by
    have heq : t - s = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      dsimp [t, s]
      field_simp
      ring
    rw [heq]
    dsimp [t]
    rw [div_pow, one_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hx)
      (by nlinarith only [hx.le])
  have hr0 : 0 ≤ r := hs.trans hrlo
  have hrs : 0 ≤ r * s := mul_nonneg hr0 hs
  have hrs2 : r * s ≤ t ^ 2 := by
    simpa only [sq] using mul_le_mul hrhi (hrlo.trans hrhi) hs ht
  have hr2 : r ^ 2 ≤ t ^ 2 := by
    simpa only [sq] using mul_le_mul hrhi hrhi hr0 ht
  have hzr : 0 ≤ Real.log n * (r - s) := mul_nonneg hlog (sub_nonneg.mpr hrlo)
  have hzr2 : Real.log n * (r - s) ≤ Real.log n * t ^ 2 :=
    mul_le_mul_of_nonneg_left (by linarith only [hrhi, hgap]) hlog
  have heq : logarithmicHarmonicError n =
      -Real.log n * (r - s) + r * s - r ^ 2 / 2 := by
    dsimp [logarithmicHarmonicError, r, s]
    ring
  have hmajor : (Real.log n + 1) / (n : ℝ) ^ 2 = (Real.log n + 1) * t ^ 2 := by
    dsimp [t]
    ring
  rw [heq, hmajor, abs_le]
  constructor <;> nlinarith only [hrs, hrs2, hr2, hzr, hzr2, sq_nonneg t, sq_nonneg r]

theorem summable_logarithmicHarmonicError : Summable logarithmicHarmonicError := by
  have hlog := RHTower.Mertens.summable_log_div_rpow (s := 2) (by norm_num)
  have hsq := Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))
  have hmajor : Summable (fun n : ℕ => (Real.log n + 1) / (n : ℝ) ^ 2) := by
    simpa only [Real.rpow_two, add_div, one_div] using hlog.add hsq
  exact summable_norm_iff.mp (hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact abs_logarithmicHarmonicError_le n))

theorem logarithmicHarmonic_sub_eq_sum (N : ℕ) :
    logarithmicHarmonic N - Real.log N ^ 2 / 2 =
      ∑ n ∈ range N, logarithmicHarmonicError n := by
  induction N with
  | zero => simp [logarithmicHarmonic]
  | succ N ih =>
      rw [sum_range_succ, ← ih, logarithmicHarmonic,
        sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      simp only [logarithmicHarmonic, logarithmicHarmonicError, Nat.cast_add, Nat.cast_one]
      ring

/-- The finite logarithmic harmonic constant. -/
def logarithmicHarmonicConstant : ℝ := ∑' n : ℕ, logarithmicHarmonicError n

/-- The logarithmic harmonic sum has a constant remainder after its quadratic
logarithmic divergence is removed. -/
theorem tendsto_logarithmicHarmonic_sub :
    Tendsto (fun N : ℕ => logarithmicHarmonic N - Real.log N ^ 2 / 2) atTop
      (𝓝 logarithmicHarmonicConstant) := by
  simpa only [← logarithmicHarmonic_sub_eq_sum, logarithmicHarmonicConstant] using
    summable_logarithmicHarmonicError.hasSum.tendsto_sum_nat

end GaloisForLFunctions.HTGeometry
