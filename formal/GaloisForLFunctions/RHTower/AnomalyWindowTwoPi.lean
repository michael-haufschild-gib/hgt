import GaloisForLFunctions.RHTower.DigammaBinetFourthOrder
import GaloisForLFunctions.RHTower.ArchimedeanResonanceRange

/-!
# The anomaly window lies just beyond `2π`

`Ω(τ) = Re ψ(¼ + iτ/2) − log π` is negative exactly on `|τ| < t₀` (`exists_anomaly_window`).  Here
(`anomaly_window_two_pi`): `2π < t₀ ≤ 2π + 1/50`, i.e.

* `Re ψ(¼ + iπ) < log π` (`gammaBracket_two_pi_neg`, margin `≈ 1.1·10⁻³`), and
* `Re ψ(¼ + i(π + 1/100)) > log π` (`gammaBracket_two_pi_add_pos`).

Both values come from `ψ(z) = ψ(z + 10) − Σ_{k<10} 1/(z + k)` and the fourth-order estimate
`|ψ(w) − log w + 1/(2w) + 1/(12w²)| ≤ 1/(120 (Re w)⁴)` at `Re w = 41/4`, where the error is
below `10⁻⁶`; the remaining logarithm is bracketed by Taylor bounds for `exp`.
-/

open Complex Real Set
open Zeta23

namespace RHTower.AnomalyWindow

noncomputable section

/-- The shifted point `w = 41/4 + iy`. -/
abbrev shiftPt (y : ℝ) : ℂ := ((41 / 4 : ℝ) : ℂ) + (y : ℂ) * I

theorem shiftPt_re (y : ℝ) : (shiftPt y).re = 41 / 4 := by simp [shiftPt]

theorem shiftPt_im (y : ℝ) : (shiftPt y).im = y := by simp [shiftPt]

theorem normSq_shiftPt (y : ℝ) : Complex.normSq (shiftPt y) = (41 / 4) ^ 2 + y ^ 2 := by
  rw [Complex.normSq_apply, shiftPt_re, shiftPt_im]; ring

theorem re_log_shiftPt (y : ℝ) : (Complex.log (shiftPt y)).re = Real.log ((41 / 4) ^ 2 + y ^ 2) / 2 := by
  rw [Complex.log_re, Complex.norm_def, normSq_shiftPt, Real.log_sqrt (by positivity)]

theorem re_half_inv_shiftPt (y : ℝ) :
    (1 / (2 * shiftPt y)).re = (41 / 4) / (2 * ((41 / 4) ^ 2 + y ^ 2)) := by
  have hN : (0 : ℝ) < (41 / 4) ^ 2 + y ^ 2 := by positivity
  rw [one_div, Complex.inv_re, Complex.normSq_mul, normSq_shiftPt, Complex.mul_re, shiftPt_re,
    shiftPt_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  field_simp
  ring

theorem re_twelfth_inv_sq_shiftPt (y : ℝ) :
    (1 / (12 * shiftPt y ^ 2)).re = ((41 / 4) ^ 2 - y ^ 2) / (12 * ((41 / 4) ^ 2 + y ^ 2) ^ 2) := by
  have hN : (0 : ℝ) < (41 / 4) ^ 2 + y ^ 2 := by positivity
  rw [one_div, Complex.inv_re, Complex.normSq_mul, map_pow, normSq_shiftPt,
    Complex.mul_re, sq, Complex.mul_re, Complex.mul_im, shiftPt_re, shiftPt_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  field_simp
  ring

/-- Two-sided real-part form of the fourth-order estimate at `w = 41/4 + iy`. -/
theorem abs_re_digamma_shiftPt_sub_le (y : ℝ) :
    |(Complex.digamma (shiftPt y)).re -
      (Real.log ((41 / 4) ^ 2 + y ^ 2) / 2 - (41 / 4) / (2 * ((41 / 4) ^ 2 + y ^ 2)) -
        ((41 / 4) ^ 2 - y ^ 2) / (12 * ((41 / 4) ^ 2 + y ^ 2) ^ 2))| ≤
      1 / (120 * (41 / 4) ^ 4) := by
  have hw : 0 < (shiftPt y).re := by rw [shiftPt_re]; norm_num
  have h := DigammaBinet.norm_digamma_sub_stirling_le hw
  rw [shiftPt_re] at h
  have h2 := (Complex.abs_re_le_norm _).trans h
  rw [Complex.add_re, Complex.add_re, Complex.sub_re, re_log_shiftPt, re_half_inv_shiftPt,
    re_twelfth_inv_sq_shiftPt] at h2
  rw [abs_le] at h2 ⊢
  constructor <;> linarith [h2.1, h2.2]

/-- `ψ(¼ + iy) = ψ(41/4 + iy) − Σ_{k<10} 1/(¼ + iy + k)`, real parts. -/
theorem re_digamma_quarter (y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma ((1 / 4 : ℂ) + (y : ℂ) * I)).re = (Complex.digamma (shiftPt y)).re -
      ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
  set z : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I with hz
  have hpole : ∀ k : ℕ, z ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.im h
    simp [hz] at this
    exact hy this
  have hrec := HTGeometry.digamma_add_nat z hpole 10
  have hw : z + ((10 : ℕ) : ℂ) = shiftPt y := by
    rw [hz, shiftPt]; push_cast; ring
  rw [hw] at hrec
  rw [hrec, Complex.add_re, Complex.re_sum]
  have hterm : ∀ k ∈ Finset.range 10, ((z + (k : ℂ))⁻¹).re =
      ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
    intro k _
    have hre : (z + (k : ℂ)).re = (k : ℝ) + 1 / 4 := by simp [hz]; ring
    have him : (z + (k : ℂ)).im = y := by simp [hz]
    rw [Complex.inv_re, Complex.normSq_apply, hre, him]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- `Ω(2y) = Re ψ(¼ + iy) − log π`. -/
theorem gammaBracket_two_mul_eq (y : ℝ) :
    EF.gammaBracket (2 * y) = (Complex.digamma ((1 / 4 : ℂ) + (y : ℂ) * I)).re - Real.log π := by
  unfold EF.gammaBracket
  congr 3
  push_cast
  ring

/-! ### Numerical brackets -/

theorem pi_sq_gt : (9869600 / 1000000 : ℝ) < π ^ 2 := by
  have := Real.pi_gt_d6
  nlinarith

theorem pi_sq_lt : π ^ 2 < (9869607 / 1000000 : ℝ) := by
  have := Real.pi_lt_d6
  have := Real.pi_pos
  nlinarith

/-- `log(1 + (41/4)²/π²) ≤ 2.4552`. -/
theorem log_ratio_le : Real.log (((41 / 4) ^ 2 + π ^ 2) / π ^ 2) ≤ 24552 / 10000 := by
  have hpi2 := pi_sq_gt
  have hpos : (0 : ℝ) < π ^ 2 := by positivity
  rw [Real.log_le_iff_le_exp (by positivity)]
  -- `exp(2.4552) ≥ e² · Σ_{i<6} 0.4552^i/i!`
  have he := Real.exp_one_gt_d9
  have hT := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4552 / 10000 by norm_num) 6
  have hsplit : Real.exp (24552 / 10000) = Real.exp 1 * Real.exp 1 * Real.exp (4552 / 10000) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hratio : ((41 / 4) ^ 2 + π ^ 2) / π ^ 2 ≤ 1 + (41 / 4) ^ 2 / (9869600 / 1000000) := by
    rw [add_div, div_self hpos.ne']
    have : (41 / 4 : ℝ) ^ 2 / π ^ 2 ≤ (41 / 4) ^ 2 / (9869600 / 1000000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi2.le
    linarith
  have hee : (27182818283 / 10000000000 : ℝ) ^ 2 ≤ Real.exp 1 * Real.exp 1 := by
    nlinarith [Real.exp_pos 1]
  have hfin : 1 + (41 / 4 : ℝ) ^ 2 / (9869600 / 1000000) ≤
      (27182818283 / 10000000000 : ℝ) ^ 2 *
        (1 + 4552 / 10000 + (4552 / 10000) ^ 2 / 2 + (4552 / 10000) ^ 3 / 6 +
          (4552 / 10000) ^ 4 / 24 + (4552 / 10000) ^ 5 / 120) := by norm_num
  calc ((41 / 4) ^ 2 + π ^ 2) / π ^ 2 ≤ 1 + (41 / 4) ^ 2 / (9869600 / 1000000) := hratio
    _ ≤ _ := hfin
    _ ≤ Real.exp 1 * Real.exp 1 * Real.exp (4552 / 10000) := by
      apply mul_le_mul hee _ (by positivity) (by positivity)
      linarith [hT]

/-- **`Re ψ(¼ + iπ) < log π`**, i.e. `Ω(2π) < 0`. -/
theorem gammaBracket_two_pi_neg : EF.gammaBracket (2 * π) < 0 := by
  rw [gammaBracket_two_mul_eq, re_digamma_quarter π Real.pi_ne_zero]
  have habs := abs_re_digamma_shiftPt_sub_le π
  have hup := (abs_le.mp habs).2
  have hpi2 := pi_sq_lt
  have hpi2' := pi_sq_gt
  have hlog := log_ratio_le
  have hpos : (0 : ℝ) < π ^ 2 := by positivity
  -- `½ log((41/4)² + π²) − log π = ½ log(((41/4)² + π²)/π²)`
  have hlogsplit : Real.log ((41 / 4) ^ 2 + π ^ 2) / 2 - Real.log π =
      Real.log (((41 / 4) ^ 2 + π ^ 2) / π ^ 2) / 2 := by
    rw [Real.log_div (by positivity) hpos.ne', Real.log_pow]; push_cast; ring
  -- the rational pieces at the worst end `π² < 9.869607`
  have hA : (41 / 4) / (2 * ((41 / 4) ^ 2 + (9869607 / 1000000 : ℝ))) ≤
      (41 / 4) / (2 * ((41 / 4) ^ 2 + π ^ 2)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hB : ((41 / 4) ^ 2 - (9869607 / 1000000 : ℝ)) / (12 * ((41 / 4) ^ 2 + 9869607 / 1000000) ^ 2) ≤
      ((41 / 4) ^ 2 - π ^ 2) / (12 * ((41 / 4) ^ 2 + π ^ 2) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((41 / 4 : ℝ) ^ 2 + π ^ 2) ^ 2 ≤ ((41 / 4) ^ 2 + 9869607 / 1000000) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [h1, sq_nonneg ((41 / 4 : ℝ) ^ 2 + π ^ 2)]
  have hS : ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 9869607 / 1000000) ≤
      ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + π ^ 2) :=
    Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by linarith)
  have hnum : (24552 / 10000 : ℝ) / 2 - (41 / 4) / (2 * ((41 / 4) ^ 2 + 9869607 / 1000000)) -
      ((41 / 4) ^ 2 - 9869607 / 1000000) / (12 * ((41 / 4) ^ 2 + 9869607 / 1000000) ^ 2) +
      1 / (120 * (41 / 4) ^ 4) -
      ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 9869607 / 1000000) < 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  linarith

/-- **`Re ψ(¼ + i(π + 1/100)) > log π`**, i.e. `Ω(2π + 1/50) > 0`. -/
theorem gammaBracket_two_pi_add_pos : 0 < EF.gammaBracket (2 * π + 1 / 50) := by
  set y : ℝ := π + 1 / 100 with hy
  have h2y : 2 * π + 1 / 50 = 2 * y := by rw [hy]; ring
  have hy0 : y ≠ 0 := by rw [hy]; positivity
  rw [h2y, gammaBracket_two_mul_eq, re_digamma_quarter y hy0]
  have habs := abs_re_digamma_shiftPt_sub_le y
  have hlow := (abs_le.mp habs).1
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hy2 : (9932532 / 1000000 : ℝ) < y ^ 2 := by rw [hy]; nlinarith
  have hpi2 := pi_sq_lt
  have hpos : (0 : ℝ) < π ^ 2 := by positivity
  have hlogsplit : Real.log ((41 / 4) ^ 2 + y ^ 2) / 2 - Real.log π =
      Real.log (((41 / 4) ^ 2 + y ^ 2) / π ^ 2) / 2 := by
    rw [Real.log_div (by positivity) hpos.ne', Real.log_pow]; push_cast; ring
  -- `log(((41/4)² + y²)/π²) ≥ 2.455`
  have hlog : (2455 / 1000 : ℝ) ≤ Real.log (((41 / 4) ^ 2 + y ^ 2) / π ^ 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    have hT := Real.exp_bound' (show (0 : ℝ) ≤ 455 / 1000 by norm_num)
      (show (455 / 1000 : ℝ) ≤ 1 by norm_num) (show 0 < 6 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
    norm_num at hT
    have hsplit : Real.exp (2455 / 1000) = Real.exp 1 * Real.exp 1 * Real.exp (455 / 1000) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [hsplit]
    have hee : Real.exp 1 * Real.exp 1 ≤ (27182818286 / 10000000000 : ℝ) ^ 2 := by
      nlinarith [Real.exp_pos 1]
    have hratio : 1 + (41 / 4 : ℝ) ^ 2 / (9869607 / 1000000) +
        (9932532 / 1000000 - 9869607 / 1000000) / (9869607 / 1000000) ≤
        ((41 / 4) ^ 2 + y ^ 2) / π ^ 2 := by
      rw [le_div_iff₀ hpos]
      have : (1 + (41 / 4 : ℝ) ^ 2 / (9869607 / 1000000) +
          (9932532 / 1000000 - 9869607 / 1000000) / (9869607 / 1000000)) * π ^ 2 ≤
          (1 + (41 / 4 : ℝ) ^ 2 / (9869607 / 1000000) +
          (9932532 / 1000000 - 9869607 / 1000000) / (9869607 / 1000000)) * (9869607 / 1000000) :=
        mul_le_mul_of_nonneg_left hpi2.le (by norm_num)
      have e : (1 + (41 / 4 : ℝ) ^ 2 / (9869607 / 1000000) +
          (9932532 / 1000000 - 9869607 / 1000000) / (9869607 / 1000000)) * (9869607 / 1000000) =
          (41 / 4) ^ 2 + 9932532 / 1000000 := by norm_num
      linarith
    have hfin : (27182818286 / 10000000000 : ℝ) ^ 2 *
        (1 + 455 / 1000 + (455 / 1000) ^ 2 / 2 + (455 / 1000) ^ 3 / 6 + (455 / 1000) ^ 4 / 24 +
          (455 / 1000) ^ 5 / 120 + (455 / 1000) ^ 6 * (6 + 1) / (720 * 6)) ≤
        1 + (41 / 4 : ℝ) ^ 2 / (9869607 / 1000000) +
          (9932532 / 1000000 - 9869607 / 1000000) / (9869607 / 1000000) := by norm_num
    calc Real.exp 1 * Real.exp 1 * Real.exp (455 / 1000) ≤
        (27182818286 / 10000000000 : ℝ) ^ 2 *
          (1 + 455 / 1000 + (455 / 1000) ^ 2 / 2 + (455 / 1000) ^ 3 / 6 + (455 / 1000) ^ 4 / 24 +
            (455 / 1000) ^ 5 / 120 + (455 / 1000) ^ 6 * (6 + 1) / (720 * 6)) :=
          mul_le_mul hee (by linarith [hT]) (Real.exp_pos _).le (by positivity)
      _ ≤ _ := hfin
      _ ≤ _ := hratio
  have hA : (41 / 4) / (2 * ((41 / 4) ^ 2 + y ^ 2)) ≤
      (41 / 4) / (2 * ((41 / 4) ^ 2 + (9932532 / 1000000 : ℝ))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hB : ((41 / 4) ^ 2 - y ^ 2) / (12 * ((41 / 4) ^ 2 + y ^ 2) ^ 2) ≤
      ((41 / 4) ^ 2 - (9932532 / 1000000 : ℝ)) / (12 * ((41 / 4) ^ 2 + 9932532 / 1000000) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((41 / 4 : ℝ) ^ 2 + 9932532 / 1000000) ^ 2 ≤ ((41 / 4) ^ 2 + y ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hy2' : y ^ 2 < (41 / 4 : ℝ) ^ 2 := by rw [hy]; nlinarith
    nlinarith [h1, mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ (41 / 4) ^ 2 - 9932532 / 1000000 by norm_num)]
  have hS : ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) ≤
      ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 9932532 / 1000000) :=
    Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by linarith)
  have hnum : 0 < (2455 / 1000 : ℝ) / 2 - (41 / 4) / (2 * ((41 / 4) ^ 2 + 9932532 / 1000000)) -
      ((41 / 4) ^ 2 - 9932532 / 1000000) / (12 * ((41 / 4) ^ 2 + 9932532 / 1000000) ^ 2) -
      1 / (120 * (41 / 4) ^ 4) -
      ∑ k ∈ Finset.range 10, ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + 9932532 / 1000000) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  linarith

/-- **The anomaly window**: `Ω < 0` exactly on `|τ| < t₀`, with `2π < t₀ ≤ 2π + 1/50`. -/
theorem anomaly_window_two_pi :
    ∃ t₀ : ℝ, 2 * π < t₀ ∧ t₀ ≤ 2 * π + 1 / 50 ∧ ∀ t : ℝ, EF.gammaBracket t < 0 ↔ |t| < t₀ := by
  obtain ⟨t₀, ht₀, -, hwin⟩ := ArchimedeanResonance.exists_anomaly_window
  refine ⟨t₀, ?_, ?_, hwin⟩
  · have := (hwin (2 * π)).mp gammaBracket_two_pi_neg
    rwa [abs_of_pos (by positivity)] at this
  · by_contra h
    push Not at h
    have := (hwin (2 * π + 1 / 50)).mpr (by rw [abs_of_pos (by positivity)]; exact h)
    linarith [gammaBracket_two_pi_add_pos]

end

end RHTower.AnomalyWindow
