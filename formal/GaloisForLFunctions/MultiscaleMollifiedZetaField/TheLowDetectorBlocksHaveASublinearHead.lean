import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLinearDetectorKeepsTheWeylBound
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound
import GaloisForLFunctions.RHTower.DyadicLawLowBlocks

/-!
# Weyl control of low detector blocks

A coefficient envelope normalized to the critical line bounds the
mollifier by `2 B sqrt N`. The detector's Weyl bound then gives
`C B² N A^(11/8)` for every block in `[1,A]`, including blocks shorter
than the square of the mollifier length.
-/

open Complex MeasureTheory Set
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A critical-line coefficient envelope gives the square-root length bound. -/
theorem norm_edPoly_le_sqrt_of_envelope {N : ℕ} {b : ℕ → ℂ} {s : ℂ} {B : ℝ}
    (hB : 0 ≤ B)
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ B * (n : ℝ) ^ (s.re - 1 / 2)) :
    ‖edPoly b (Finset.Icc 1 N) s‖ ≤ 2 * B * Real.sqrt N := by
  unfold edPoly
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
        Complex.neg_re]
      refine (mul_le_mul_of_nonneg_right (hb n hn) (Real.rpow_nonneg hn0.le _)).trans_eq ?_
      rw [mul_assoc, ← Real.rpow_add hn0]
      congr 2
      ring
    _ = B * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ B * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left (sum_rpow_neg_half_le N) hB
    _ = _ := by ring

/-- A single Weyl constant controls every low block and every normalized coefficient envelope. -/
theorem exists_integral_linearDetector_head_bound :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0,
      ∀ (N : ℕ) (b : ℕ → ℂ) (σ lam B a v A : ℝ),
      |σ - 1 / 2| ≤ r → |lam| ≤ 1 → 0 ≤ B →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ B * (n : ℝ) ^ (σ - 1 / 2)) →
      1 ≤ a → a ≤ v → v ≤ A →
      (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * B ^ 2 * N * A ^ (11 / 8 : ℝ) := by
  obtain ⟨r, hr, hrhalf, D, hD, hdet⟩ := exists_norm_linearDetector_thin_strip_le
  refine ⟨r, hr, hrhalf, 4 * D ^ 2 * (2 : ℝ) ^ (3 / 8 : ℝ), by positivity, ?_⟩
  intro N b σ lam B a v A hσ hlam hB hb ha hav hvA
  have hA : 1 ≤ A := ha.trans (hav.trans hvA)
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let E : ℝ := D * (1 + A) ^ (3 / 16 : ℝ) * (2 * B * Real.sqrt N)
  have hpoint (t : ℝ) (ht : t ∈ Icc a v) :
      ‖levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ E ^ 2 := by
    have ht0 : 0 ≤ t := (zero_lt_one.trans_le (ha.trans ht.1)).le
    have hζ : ‖levinsonG (lam : ℂ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (1 + A) ^ (3 / 16 : ℝ) := by
      have hh := hdet ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) lam hlam
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
        abs_of_nonneg ht0] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [ht.2, hvA]) (by norm_num)) hD.le)
    have hm : ‖edPoly b (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * B * Real.sqrt N :=
      norm_edPoly_le_sqrt_of_envelope hB (by simpa using hb)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    unfold levinsonMollifiedDetector
    rw [norm_mul]
    exact mul_le_mul hζ hm (norm_nonneg _) (by positivity)
  have hi : IntervalIntegrable (fun t : ℝ =>
      ‖levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume a v := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hav] at ht
    have hz : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at hh
      linarith only [hh, ht.1, ha]
    have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
    have hf := (analyticAt_levinsonMollifiedDetector (lam : ℂ) b hs hz).continuousAt
    have hmap : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact ((hf.comp hmap).norm.pow 2).continuousWithinAt
  have hp : ((1 + A) ^ (3 / 16 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (3 / 8 : ℝ) * A ^ (3 / 8 : ℝ) := by
    calc
      _ = (1 + A) ^ (3 / 8 : ℝ) := by
        rw [pow_two, ← Real.rpow_add (by positivity)]
        norm_num
      _ ≤ (2 * A) ^ (3 / 8 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith only [hA]) (by norm_num)
      _ = _ := Real.mul_rpow (by norm_num) hA0.le
  have hE : E ^ 2 ≤ 4 * D ^ 2 * B ^ 2 * N *
      ((2 : ℝ) ^ (3 / 8 : ℝ) * A ^ (3 / 8 : ℝ)) := by
    calc
      _ = 4 * D ^ 2 * B ^ 2 * N * ((1 + A) ^ (3 / 16 : ℝ)) ^ 2 := by
        dsimp only [E]
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ ≤ ∫ t in a..v, E ^ 2 := intervalIntegral.integral_mono_on hav hi (by simp) hpoint
    _ = (v - a) * E ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ A * E ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hvA, ha]) (sq_nonneg E)
    _ ≤ A * (4 * D ^ 2 * B ^ 2 * N * ((2 : ℝ) ^ (3 / 8 : ℝ) * A ^ (3 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_left hE hA0.le
    _ = _ := by
      have he : A * A ^ (3 / 8 : ℝ) = A ^ (11 / 8 : ℝ) := by
        rw [show (11 / 8 : ℝ) = 1 + 3 / 8 by norm_num, Real.rpow_add hA0, Real.rpow_one]
      calc
        _ = (4 * D ^ 2 * (2 : ℝ) ^ (3 / 8 : ℝ)) * B ^ 2 * N *
            (A * A ^ (3 / 8 : ℝ)) := by ring
        _ = _ := by rw [he]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
