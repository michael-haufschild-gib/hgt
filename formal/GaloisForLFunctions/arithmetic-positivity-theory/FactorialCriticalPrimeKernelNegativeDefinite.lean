import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalBandWeightPoissonWindow
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeContinuousKernel
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeSingletonNegative

/-!
# Negative definiteness of the complete critical prime form

Summation by parts writes the reflected critical kernel `R` as a charge-weighted sum of
harmonic tails `T_m`. Poisson windows identify each reflected tail pair with its unit-cell
mean, the harmonic defect `J_m/m`, up to a uniformly bounded curvature correction. The mean
part is the singleton prime limit `Σ A(m)J_m/m⁴ ≤ -(log 2)/390`; the correction costs at most
`½ Σ |A(m)|/m³ |W_m - 2∫γ|`, paid by quartic window bounds at `m = 2, 3` and by the integral
test beyond. Hence `R ≤ -1/7000` on the whole cell, and unit-cell Parseval gives
`P∞(S,b) ≤ -(4/(7000π⁴)) Σ b_j²` for every finite real pattern.
-/

open MeasureTheory Set Filter

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- Harmonic tail `T_m(t) = Σ_j γ(j + m + t)` of the critical kernel weight. -/
def factorialCriticalPrimeHarmonicTail (m : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, factorialCriticalPrimeKernelWeight (((j + m : ℕ) : ℝ) + t)

/-- The critical kernel weight is nonnegative on the closed half-line. -/
private theorem criticalKernelWeight_nonneg_of_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ factorialCriticalPrimeKernelWeight u :=
  mul_nonneg (Real.rpow_nonneg hu _) (sub_nonneg.mpr (Real.cos_le_one _))

private theorem kernelWeight_eq_band_shift {n : ℕ} {t : ℝ} (hn : 0 < n) (ht : 0 ≤ t) :
    factorialCriticalPrimeKernelWeight ((n : ℝ) + t) = criticalBandWeight (t + (n : ℝ)) := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  rw [factorialCriticalPrimeKernelWeight_eq_band (by positivity), add_comm]

private theorem summable_kernelWeight_shift {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    Summable fun j : ℕ => factorialCriticalPrimeKernelWeight (((j + m + 1 : ℕ) : ℝ) + t) := by
  refine ((summable_nat_add_iff (m + 1)).mpr (summable_criticalBandWeight_nat t)).congr fun j => ?_
  rw [kernelWeight_eq_band_shift (by omega) ht]
  push_cast; ring_nf

/-- Summation by parts: the cell kernel `Σ_k H_{k+1} γ(k+1+t)` equals `Σ_m (A(m)/m³) T_m(t)`. -/
theorem factorialCriticalPrimeCellKernel_eq_tsum_tail {t : ℝ} (ht : 0 ≤ t) :
    factorialCriticalPrimeCellKernel t = ∑' m : ℕ,
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * factorialCriticalPrimeHarmonicTail m t := by
  set c : ℕ → ℝ := fun m => factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 with hc
  set φ : ℕ → ℝ := fun n => factorialCriticalPrimeKernelWeight ((n : ℝ) + t) with hφ
  have hφ0 (n : ℕ) : 0 ≤ φ n := criticalKernelWeight_nonneg_of_nonneg (by positivity)
  have hφs : Summable fun k : ℕ => φ (k + 1) :=
    (summable_kernelWeight_shift ht 0).congr fun k => rfl
  have hcs : Summable fun m => |c m| :=
    summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.congr fun m => by
      simp only [c, abs_div, abs_pow, Nat.abs_cast]
  let F : ℕ → ℕ → ℝ := fun k m => if m ∈ Finset.Icc 1 (k + 1) then c m * φ (k + 1) else 0
  have hFb (k m : ℕ) : ‖F k m‖ ≤ φ (k + 1) * |c m| := by
    simp only [F]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 _), mul_comm]
    · simp only [norm_zero]; exact mul_nonneg (hφ0 _) (abs_nonneg _)
  have hF : Summable (Function.uncurry F) :=
    (hφs.mul_of_nonneg hcs (fun k => hφ0 _) (fun m => abs_nonneg _)).of_norm_bounded
      fun p => hFb p.1 p.2
  have hrow (k : ℕ) : ∑' m, F k m = factorialCriticalPrimeCumulativeCharge (k + 1) * φ (k + 1) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (k + 1)) (fun m hm => by simp only [F, if_neg hm])]
    unfold factorialCriticalPrimeCumulativeCharge
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => by simp only [F, if_pos hm]; rfl
  have hcol (m : ℕ) : ∑' k, F k m = c m * factorialCriticalPrimeHarmonicTail m t := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, c]
    · have hs : Summable fun k => F k m :=
        (hφs.mul_right |c m|).of_norm_bounded fun k => hFb k m
      rw [← hs.sum_add_tsum_nat_add (m - 1)]
      have h1 : ∑ k ∈ Finset.range (m - 1), F k m = 0 := Finset.sum_eq_zero fun k hk => by
        have := Finset.mem_range.mp hk
        simp only [F]; rw [if_neg (by simp; omega)]
      rw [h1, zero_add, factorialCriticalPrimeHarmonicTail, ← tsum_mul_left]
      congr 1; funext j
      simp only [F]
      rw [if_pos (by simp; omega), show j + (m - 1) + 1 = j + m by omega]
  unfold factorialCriticalPrimeCellKernel
  calc ∑' k : ℕ, factorialCriticalPrimeCumulativeCharge (k + 1) *
        factorialCriticalPrimeKernelWeight (((k + 1 : ℕ) : ℝ) + t) = ∑' k, ∑' m, F k m :=
        tsum_congr fun k => (hrow k).symm
    _ = ∑' m, ∑' k, F k m := hF.tsum_comm.symm
    _ = _ := tsum_congr hcol

/-- Poisson closes the reflected tail pair: `T_m(t) + T_m(1-t) = π²/6 - W_m(t)`. -/
theorem factorialCriticalPrimeHarmonicTail_add_reflect {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t) =
      Real.pi ^ 2 / 6 - criticalBandWindow m t := by
  have h1 : factorialCriticalPrimeHarmonicTail m t =
      ∑' j : ℕ, criticalBandWeight (t + ((j + m : ℕ) : ℝ)) :=
    tsum_congr fun j => kernelWeight_eq_band_shift (by omega) ht.1
  have h2 : factorialCriticalPrimeHarmonicTail m (1 - t) =
      ∑' j : ℕ, criticalBandWeight (t - ((j + m : ℕ) : ℝ) - 1) := by
    refine tsum_congr fun j => ?_
    have hj : (0 : ℝ) < ((j + m : ℕ) : ℝ) := by exact_mod_cast (show 0 < j + m by omega)
    rw [factorialCriticalPrimeKernelWeight_eq_band (by linarith [ht.2]), ← criticalBandWeight_neg]
    ring_nf
  rw [h1, h2, ← Summable.tsum_add ((summable_nat_add_iff m).mpr (summable_criticalBandWeight_nat t))
    ((summable_nat_add_iff m).mpr (summable_criticalBandWeight_nat_neg t)),
    ← tsum_criticalBandWeight_outside_window]

theorem factorialCriticalPrimeHarmonicTail_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ factorialCriticalPrimeHarmonicTail m t :=
  tsum_nonneg fun j => criticalKernelWeight_nonneg_of_nonneg (by positivity)

/-- Every positive harmonic tail is at most the total band mass on the closed cell. -/
theorem factorialCriticalPrimeHarmonicTail_le {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : factorialCriticalPrimeHarmonicTail m t ≤ Real.pi ^ 2 / 6 := by
  have := factorialCriticalPrimeHarmonicTail_add_reflect hm ht
  have := factorialCriticalPrimeHarmonicTail_nonneg m (show 0 ≤ 1 - t by linarith [ht.2])
  have := criticalBandWindow_nonneg m t
  linarith

/-- The reflected tail pair is the harmonic defect up to the window deviation:
`(T_m(t) + T_m(1-t))/2 = J_m/m - (W_m(t) - 2∫₀^m γ)/2`. -/
theorem factorialCriticalPrimeHarmonicTail_mean {m : ℕ} (hm : 0 < m) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicTail m (1 - t)) / 2 =
      factorialCriticalHarmonicDefect m / m - criticalBandWindowDeviation m t / 2 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [factorialCriticalPrimeHarmonicTail_add_reflect hm ht, factorialCriticalHarmonicDefect_eq_band hm,
    criticalBandWindowDeviation]
  field_simp
  ring

/-- **Exact kernel formula.** On the closed cell,
`R(t) = Σ_m A(m)J_m/m⁴ - ½ Σ_m (A(m)/m³)(W_m(t) - 2∫₀^m γ)`: the singleton prime limit plus a
uniformly bounded curvature correction. -/
theorem factorialCriticalPrimeContinuousRealKernel_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeContinuousRealKernel t =
      (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m /
        (m : ℝ) ^ 4) - (1 / 2) * ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
          criticalBandWindowDeviation m t := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcs := summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube
  have hcb (m : ℕ) : |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3| =
      |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3 := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hsT {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : Summable fun m : ℕ =>
      factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * factorialCriticalPrimeHarmonicTail m u := by
    refine (hcs.mul_right (Real.pi ^ 2 / 6)).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Real.norm_eq_abs, abs_mul, hcb, abs_of_nonneg (factorialCriticalPrimeHarmonicTail_nonneg m hu.1)]
      exact mul_le_mul_of_nonneg_left (factorialCriticalPrimeHarmonicTail_le hm hu)
        (div_nonneg (abs_nonneg _) (by positivity))
  have hsJ : Summable fun m : ℕ => factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 := by
    refine (hcs.mul_right 2).of_norm_bounded fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      obtain ⟨hJ0, hJ2⟩ := factorialCriticalHarmonicDefect_bounds m
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hJ0, abs_pow, Nat.abs_cast,
        show (m : ℝ) ^ 4 = (m : ℝ) ^ 3 * m by ring, div_mul_eq_div_div_swap]
      rw [div_le_iff₀ (by positivity)]
      have : |factorialCriticalPrimeHarmonicCharge m| * factorialCriticalHarmonicDefect m ≤
          |factorialCriticalPrimeHarmonicCharge m| * 2 :=
        mul_le_mul_of_nonneg_left hJ2 (abs_nonneg _)
      calc |factorialCriticalPrimeHarmonicCharge m| * factorialCriticalHarmonicDefect m / (m : ℝ)
          ≤ |factorialCriticalPrimeHarmonicCharge m| * 2 / 1 := by
            apply div_le_div₀ (by positivity) this one_pos hmR
        _ = _ := by field_simp
  have hsD : Summable fun m : ℕ => factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
      criticalBandWindowDeviation m t := by
    refine (hcs.mul_right ((Real.pi / 6) ^ 3 / 35)).of_norm_bounded fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, hcb]
    exact mul_le_mul_of_nonneg_left (abs_criticalBandWindowDeviation_le_cube m ht)
      (div_nonneg (abs_nonneg _) (by positivity))
  have hterm (m : ℕ) : (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        factorialCriticalPrimeHarmonicTail m t + factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
        factorialCriticalPrimeHarmonicTail m (1 - t)) / 2 =
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 -
        1 / 2 * (factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandWindowDeviation m t) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have h := factorialCriticalPrimeHarmonicTail_mean hm ht
      rw [← mul_add, mul_div_assoc, h]
      field_simp
  unfold factorialCriticalPrimeContinuousRealKernel
  rw [factorialCriticalPrimeCellKernel_eq_tsum_tail ht.1, factorialCriticalPrimeCellKernel_eq_tsum_tail ht'.1,
    ← (hsT ht).tsum_add (hsT ht'), ← tsum_div_const, tsum_congr hterm,
    hsJ.tsum_sub (hsD.mul_left (1 / 2)), tsum_mul_left]

/-- The curvature correction converges absolutely. -/
theorem summable_charge_mul_criticalBandWindowDeviation {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable fun m : ℕ => |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
      criticalBandWindowDeviation m t| := by
  refine (summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube.mul_right
    ((Real.pi / 6) ^ 3 / 35)).of_norm_bounded fun m => ?_
  rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (abs_criticalBandWindowDeviation_le_cube m ht)
    (div_nonneg (abs_nonneg _) (by positivity))

private theorem log_three_le_twentySevenSeventeenths : Real.log 3 ≤ (27 / 17) * Real.log 2 := by
  have h := Real.log_le_log (by norm_num : 0 < (3 : ℝ) ^ 17) (by norm_num : (3 : ℝ) ^ 17 ≤ 2 ^ 27)
  simp only [Real.log_pow] at h
  push_cast at h
  linarith

/-- Absolute curvature budget. Only `m = 2`, `m = 3` and `m ≥ 5` carry charge; the first two use
the quartic window bound, the tail uses `|A(m)| ≤ m log m` and the integral test. -/
theorem tsum_abs_charge_mul_criticalBandWindowDeviation_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 * criticalBandWindowDeviation m t| ≤
      Real.log 2 / 4 * ((Real.pi / 6) ^ 4 / 35) + Real.log 3 / 9 * (3 * (Real.pi / 6) ^ 4 / 70) +
        (Real.pi / 6) ^ 3 / 35 * ((2 * Real.log 2 + 1) / 4) := by
  set x : ℕ → ℝ := fun m => |factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
    criticalBandWindowDeviation m t| with hx
  have hs : Summable x := summable_charge_mul_criticalBandWindowDeviation ht
  have hzero {m : ℕ} (hm : m = 1 ∨ m % 4 = 0) : x m = 0 := by
    simp [x, (factorialCriticalPrimeHarmonicCharge_sign m).2.1.mpr hm]
  have hx0 : x 0 = 0 := by simp [x]
  have hx1 : x 1 = 0 := hzero (Or.inl rfl)
  have hx4 : x 4 = 0 := hzero (Or.inr (by norm_num))
  have hx2 : x 2 ≤ Real.log 2 / 4 * ((Real.pi / 6) ^ 4 / 35) := by
    have hd := abs_criticalBandWindowDeviation_le_quartic 2 ht
    simp only [x, abs_mul, factorialCriticalPrimeHarmonicCharge_two]
    have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [show |-2 * Real.log 2 / ((2 : ℕ) : ℝ) ^ 3| = Real.log 2 / 4 by
      rw [abs_div, abs_mul]; norm_num [abs_of_pos hl]; ring]
    push_cast at hd
    nlinarith
  have hx3 : x 3 ≤ Real.log 3 / 9 * (3 * (Real.pi / 6) ^ 4 / 70) := by
    have hd := abs_criticalBandWindowDeviation_le_quartic 3 ht
    simp only [x, abs_mul, factorialCriticalPrimeHarmonicCharge_odd_prime Nat.prime_three
      (by norm_num : 3 % 2 = 1)]
    have hl := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    rw [show |((3 : ℕ) : ℝ) * Real.log ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) ^ 3| = Real.log 3 / 9 by
      push_cast; rw [abs_div, abs_mul]; norm_num [abs_of_pos hl]; ring]
    push_cast at hd
    nlinarith
  have htail (j : ℕ) : x (j + 5) ≤ (Real.pi / 6) ^ 3 / 35 *
      (Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2) := by
    have hd := abs_criticalBandWindowDeviation_le_cube (j + 5) ht
    have hA := abs_factorialCriticalPrimeHarmonicCharge_le (j + 5)
    have hq : (0 : ℝ) < ((j + 5 : ℕ) : ℝ) := by positivity
    simp only [x, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    have hc : |factorialCriticalPrimeHarmonicCharge (j + 5)| / ((j + 5 : ℕ) : ℝ) ^ 3 ≤
        Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e : (4 + ((j : ℝ) + 1)) = ((j + 5 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      calc |factorialCriticalPrimeHarmonicCharge (j + 5)| * ((j + 5 : ℕ) : ℝ) ^ 2 ≤
          ((j + 5 : ℕ) : ℝ) * Real.log ((j + 5 : ℕ) : ℝ) * ((j + 5 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = _ := by ring
    calc |factorialCriticalPrimeHarmonicCharge (j + 5)| / ((j + 5 : ℕ) : ℝ) ^ 3 *
          |criticalBandWindowDeviation (j + 5) t| ≤
        Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 * ((Real.pi / 6) ^ 3 / 35) :=
          mul_le_mul hc hd (abs_nonneg _) (by
            have : (1 : ℝ) ≤ 4 + ((j : ℝ) + 1) := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
            exact div_nonneg (Real.log_nonneg this) (by positivity))
      _ = _ := by ring
  have hlogsum := GaloisForLFunctions.HTGeometry.tsum_logLin_div_sq_le (N := 4)
    (by have := Real.exp_one_lt_d9; linarith)
  have hlsum : Summable fun j : ℕ => Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := by
    refine ((summable_nat_add_iff 5).mpr GaloisForLFunctions.HTGeometry.summable_logLin_div_sq).congr
      fun j => ?_
    push_cast; ring_nf
  have htsum : ∑' j : ℕ, x (j + 5) ≤ (Real.pi / 6) ^ 3 / 35 * ((Real.log 4 + 1) / 4) := by
    calc ∑' j : ℕ, x (j + 5) ≤ ∑' j : ℕ, (Real.pi / 6) ^ 3 / 35 *
          (Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2) :=
          Summable.tsum_le_tsum htail ((summable_nat_add_iff 5).mpr hs) (hlsum.mul_left _)
      _ = (Real.pi / 6) ^ 3 / 35 * ∑' j : ℕ,
          Real.log (4 + ((j : ℝ) + 1)) / (4 + ((j : ℝ) + 1)) ^ 2 := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogsum (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [← hs.sum_add_tsum_nat_add 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hx0, hx1, hx4]
  rw [hlog4] at htsum
  linarith

private theorem kernel_numeric_margin :
    -(1 / 390) * Real.log 2 + (1 / 2) * (Real.log 2 / 4 * ((Real.pi / 6) ^ 4 / 35) +
      Real.log 3 / 9 * (3 * (Real.pi / 6) ^ 4 / 70) +
        (Real.pi / 6) ^ 3 / 35 * ((2 * Real.log 2 + 1) / 4)) ≤ -1 / 7000 := by
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  set P := Real.pi / 6 with hP
  have hP0 : 0 ≤ P := by positivity
  have hP1 : P ≤ 0.5236 := by rw [hP]; linarith
  have hP3 : P ^ 3 ≤ 0.5236 ^ 3 := pow_le_pow_left₀ hP0 hP1 3
  have hP4 : P ^ 4 ≤ 0.5236 ^ 4 := pow_le_pow_left₀ hP0 hP1 4
  set L := Real.log 2 with hLdef
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have h3 := log_three_le_twentySevenSeventeenths
  have h30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have a1 : L * P ^ 4 ≤ 0.6931471808 * 0.5236 ^ 4 :=
    mul_le_mul hL2.le hP4 (by positivity) (by norm_num)
  have a2 : Real.log 3 * P ^ 4 ≤ (27 / 17 * 0.6931471808) * 0.5236 ^ 4 :=
    mul_le_mul (by linarith) hP4 (by positivity) (by norm_num)
  have a3 : P ^ 3 * L ≤ 0.5236 ^ 3 * 0.6931471808 :=
    mul_le_mul hP3 hL2.le (by linarith) (by norm_num)
  nlinarith

/-- **The critical prime kernel is uniformly negative:** `R(t) ≤ -1/7000` on `[0, 1]`. -/
theorem factorialCriticalPrimeContinuousRealKernel_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    factorialCriticalPrimeContinuousRealKernel t ≤ -1 / 7000 := by
  rw [factorialCriticalPrimeContinuousRealKernel_eq ht]
  have hM := factorialCriticalPrimeHarmonicSum_negative_bound
  have hs := summable_charge_mul_criticalBandWindowDeviation ht
  have hD : -(∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m / (m : ℝ) ^ 3 *
      criticalBandWindowDeviation m t) ≤ ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m /
        (m : ℝ) ^ 3 * criticalBandWindowDeviation m t| := by
    refine (neg_le_abs _).trans ?_
    have := norm_tsum_le_tsum_norm (f := fun m : ℕ => factorialCriticalPrimeHarmonicCharge m /
      (m : ℝ) ^ 3 * criticalBandWindowDeviation m t) (by simpa only [Real.norm_eq_abs] using hs)
    simpa only [Real.norm_eq_abs] using this
  have hB := tsum_abs_charge_mul_criticalBandWindowDeviation_le ht
  have hN := kernel_numeric_margin
  linarith

/-- **Negative coercivity of the complete limiting critical prime form.** Every finite real
pattern satisfies `P∞(S,b) ≤ -(4/(7000π⁴)) Σ b_j²`. The Weil form subtracts the prime channel,
so this channel contributes a uniformly positive-definite amount to the complete form. -/
theorem factorialCriticalTranslatedPrimeLimit_le_neg_energy (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b ≤
      -(4 / (7000 * Real.pi ^ 4)) * ∑ j ∈ S, b j ^ 2 := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral]
  have hQ := continuous_factorialCriticalPatternDensity S b
  have hR := continuousOn_factorialCriticalPrimeContinuousRealKernel
  have hint : ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t *
      factorialCriticalPatternDensity S b t ≤
      ∫ t in (0 : ℝ)..1, (-1 / 7000) * factorialCriticalPatternDensity S b t := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact hR.mul hQ.continuousOn
    · exact (by fun_prop : Continuous fun t => (-1 / 7000 : ℝ) *
        factorialCriticalPatternDensity S b t).intervalIntegrable _ _
    · intro t ht
      exact mul_le_mul_of_nonneg_right (factorialCriticalPrimeContinuousRealKernel_le ht)
        (factorialCriticalPatternDensity_nonneg S b t)
  have hE : ∫ t in (0 : ℝ)..1, factorialCriticalPatternDensity S b t = ∑ j ∈ S, b j ^ 2 := by
    simpa using factorialCriticalPatternDensity_cell S b one_pos 0
  rw [intervalIntegral.integral_const_mul, hE] at hint
  have hπ : 0 < Real.pi ^ 4 := by positivity
  calc 4 / Real.pi ^ 4 * ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t *
        factorialCriticalPatternDensity S b t ≤ 4 / Real.pi ^ 4 * (-1 / 7000 * ∑ j ∈ S, b j ^ 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

/-- Every nonzero finite real pattern is a strictly negative direction of the limiting prime form. -/
theorem factorialCriticalTranslatedPrimeLimit_neg {S : Finset ℕ} {b : ℕ → ℝ}
    (h : ∃ j ∈ S, b j ≠ 0) : factorialCriticalTranslatedPrimeLimit S b < 0 := by
  obtain ⟨j, hj, hb⟩ := h
  have hE : 0 < ∑ i ∈ S, b i ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hc : 0 < 4 / (7000 * Real.pi ^ 4) := by positivity
  nlinarith [factorialCriticalTranslatedPrimeLimit_le_neg_energy S b]

end GaloisForLFunctions.ArithmeticPositivityTheory
