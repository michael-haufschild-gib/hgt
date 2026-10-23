import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros

/-!
# Prime signs and prime means do not decide the half-damped receiver

The quarter law of the constant-sign model, `z^{Ω(d)} d^{-1/2}` paid iff `z < 1/2`, suggests reading
the half-damped receiver of a multiplicative weight off its prime data on the real axis: which primes
are flipped, and the logarithmic prime mean `Σ_p f(p) p^{-w} = ν log(1/(w − 1)) + O(1)`. Both readings
fail. For `t₀ ≠ 0` the oscillating pattern `f(p) = a cos(t₀ log p)` has bounded real prime sums on
`1 < w < 3/2` (`exists_abs_tsum_oscPattern_le`, from `|log|ζ||` bounded on the segments
`[1, 3/2] ± it₀`), so its prime mean is `ν = 0` for every amplitude, and its sign at each prime does not
depend on `a > 0`. Choosing `t₀` with `ζ(1/2 + it₀) ≠ 0`, the amplitudes `1/2` and `1` give a paid and an
unpaid weight with the same prime signs and the same prime mean
(`exists_paid_unpaid_with_same_prime_signs_and_mean`): the receiver reads the amplitude at the critical
height, which no real-axis prime datum records.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- On a horizontal segment `Re z ∈ [1, 3/2]`, `Im z = y ≠ 0`, `log|ζ|` is bounded: `ζ` is continuous
and zero-free there. -/
theorem exists_abs_log_norm_zeta_le_segment {y : ℝ} (hy : y ≠ 0) :
    ∃ B : ℝ, ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 3 / 2 → z.im = y →
      |Real.log ‖riemannZeta z‖| ≤ B := by
  set K : Set ℂ := (Icc (1 : ℝ) (3 / 2)) ×ℂ (Icc y y)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hne1 : ∀ z ∈ K, z ≠ 1 := fun z hz h => by
    have := (Complex.mem_reProdIm.mp hz).2
    rw [h, Complex.one_im, mem_Icc] at this
    exact hy (le_antisymm this.1 this.2)
  have hre : ∀ z ∈ K, 1 ≤ z.re := fun z hz => (Complex.mem_reProdIm.mp hz).1.1
  have hc1 : ContinuousOn riemannZeta K := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun z => (riemannZeta z)⁻¹) K := fun z hz =>
    ((differentiableAt_riemannZeta (hne1 z hz)).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re (hre z hz))).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hc1
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨Real.log (max C₁ 1) + Real.log (max C₂ 1), fun z hz1 hz2 hzy => ?_⟩
  have hmem : z ∈ K := Complex.mem_reProdIm.mpr ⟨⟨hz1, hz2⟩, by rw [hzy]; exact ⟨le_rfl, le_rfl⟩⟩
  have hpos := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (hre z hmem))
  have h1 : ‖riemannZeta z‖ ≤ max C₁ 1 := (hC₁ z hmem).trans (le_max_left _ _)
  have h2 : ‖riemannZeta z‖⁻¹ ≤ max C₂ 1 := by
    have := hC₂ z hmem
    rw [norm_inv] at this
    exact this.trans (le_max_left _ _)
  have hl1 : Real.log ‖riemannZeta z‖ ≤ Real.log (max C₁ 1) := Real.log_le_log hpos h1
  have hl2 : -Real.log ‖riemannZeta z‖ ≤ Real.log (max C₂ 1) := by
    rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.mpr hpos) h2
  have hm1 : 0 ≤ Real.log (max C₁ 1) := Real.log_nonneg (le_max_right _ _)
  have hm2 : 0 ≤ Real.log (max C₂ 1) := Real.log_nonneg (le_max_right _ _)
  rw [abs_le]; constructor <;> linarith

/-- The real prime sum of the oscillating pattern: on real `w > 1`,
`Σ_p f(p) p^{-w} = (a/2)(Re Σ_p p^{-(w − it₀)} + Re Σ_p p^{-(w + it₀)})`. -/
theorem tsum_oscPattern_prime_eq (a t₀ : ℝ) {w : ℝ} (hw : 1 < w) :
    ∑' p : Nat.Primes, oscPattern a t₀ p * ((p : ℕ) : ℝ) ^ (-w) =
      a / 2 * ((∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) - t₀ * I))).re +
        (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) + t₀ * I))).re) := by
  have hwm : 1 < ((w : ℂ) - t₀ * I).re := by simpa using hw
  have hwp : 1 < ((w : ℂ) + t₀ * I).re := by simpa using hw
  have hsm := summable_prime_cpow_neg hwm
  have hsp := summable_prime_cpow_neg hwp
  have hC : ((∑' p : Nat.Primes, oscPattern a t₀ p * ((p : ℕ) : ℝ) ^ (-w) : ℝ) : ℂ) =
      ((a / 2 : ℝ) : ℂ) * (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) - t₀ * I)) +
        ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) + t₀ * I))) := by
    rw [Complex.ofReal_tsum, ← hsm.tsum_add hsp, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), oscPattern_prime a t₀ p.2,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_neg, mul_assoc,
      cos_mul_cpow_eq p.2.pos]
    push_cast
    ring
  have h := congrArg Complex.re hC
  rwa [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.add_re] at h

/-- **The prime mean of an oscillating pattern vanishes**: for `|a| ≤ 1` and `t₀ ≠ 0` the real prime
sums `Σ_p f(p) p^{-w}` are bounded on `1 < w < 3/2`. -/
theorem exists_abs_tsum_oscPattern_le {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : t₀ ≠ 0) :
    ∃ B : ℝ, ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' p : Nat.Primes, oscPattern a t₀ p * ((p : ℕ) : ℝ) ^ (-w)| ≤ B := by
  obtain ⟨Bm, hBm⟩ := exists_abs_log_norm_zeta_le_segment (y := -t₀) (neg_ne_zero.mpr ht₀)
  obtain ⟨Bp, hBp⟩ := exists_abs_log_norm_zeta_le_segment ht₀
  set S := primeSquareMass
  refine ⟨1 / 2 * ((Bm + S) + (Bp + S)), fun w hw hw2 => ?_⟩
  have hwm : 1 < ((w : ℂ) - t₀ * I).re := by simpa using hw
  have hwp : 1 < ((w : ℂ) + t₀ * I).re := by simpa using hw
  rw [tsum_oscPattern_prime_eq a t₀ hw]
  -- each real prime sum is `log|ζ| + O(S)`, and `log|ζ|` is bounded on the segments
  have hRm : |(∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) - t₀ * I))).re| ≤ Bm + S := by
    have h1 := abs_log_norm_riemannZeta_sub_re_le hwm
    have h2 := hBm ((w : ℂ) - t₀ * I) (by simp; linarith) (by simp; linarith) (by simp)
    have h3 := abs_sub_abs_le_abs_sub
      (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) - t₀ * I))).re
      (Real.log ‖riemannZeta ((w : ℂ) - t₀ * I)‖)
    rw [abs_sub_comm] at h3
    linarith
  have hRp : |(∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) + t₀ * I))).re| ≤ Bp + S := by
    have h1 := abs_log_norm_riemannZeta_sub_re_le hwp
    have h2 := hBp ((w : ℂ) + t₀ * I) (by simp; linarith) (by simp; linarith) (by simp)
    have h3 := abs_sub_abs_le_abs_sub
      (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((w : ℂ) + t₀ * I))).re
      (Real.log ‖riemannZeta ((w : ℂ) + t₀ * I)‖)
    rw [abs_sub_comm] at h3
    linarith
  have ha2 : |a / 2| ≤ 1 / 2 := by rw [abs_div, abs_two]; linarith
  rw [abs_mul]
  exact mul_le_mul ha2 ((abs_add_le _ _).trans (add_le_add hRm hRp)) (abs_nonneg _) (by norm_num)

/-- **Prime signs and prime means do not decide the half-damped receiver.** There is a frequency
`t₀ > 0` such that the oscillating patterns of amplitudes `1/2` and `1` have the same sign at every
prime (`f_{1/2}(p) = f_1(p)/2`) and bounded real prime sums (prime mean `0`), while the half-damped
weight of the first is paid and that of the second is not. -/
theorem exists_paid_unpaid_with_same_prime_signs_and_mean :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ReceiverBounded (oscWeight (1 / 2) t₀) ∧
      ¬ ReceiverBounded (oscWeight 1 t₀) ∧
      (∀ p : ℕ, p.Prime → oscPattern (1 / 2) t₀ p = 1 / 2 * oscPattern 1 t₀ p) ∧
      ∃ B : ℝ, ∀ w : ℝ, 1 < w → w < 3 / 2 →
        |∑' p : Nat.Primes, oscPattern 1 t₀ p * ((p : ℕ) : ℝ) ^ (-w)| ≤ B ∧
        |∑' p : Nat.Primes, oscPattern (1 / 2) t₀ p * ((p : ℕ) : ℝ) ^ (-w)| ≤ B := by
  obtain ⟨r, hr, hζh⟩ := exists_norm_zeta_gt_near_half
  set t₀ : ℝ := r / 2
  have ht₀ : 0 < t₀ := by positivity
  have hz : riemannZeta (1 / 2 + t₀ * I) ≠ 0 := by
    have h := hζh (1 / 2 + t₀ * I) (by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht₀]
      simp only [t₀]; linarith)
    intro h0; rw [h0, norm_zero] at h; linarith
  obtain ⟨B₁, hB₁⟩ := exists_abs_tsum_oscPattern_le (a := 1) (by norm_num) ht₀.ne'
  obtain ⟨B₂, hB₂⟩ := exists_abs_tsum_oscPattern_le (a := 1 / 2) (by norm_num) ht₀.ne'
  refine ⟨t₀, ht₀, receiverBounded_oscWeight_of_lt_one (by norm_num) (by norm_num) ht₀.ne',
    not_receiverBounded_oscWeight_one ht₀ hz, fun p hp => ?_, max B₁ B₂, fun w hw hw2 =>
      ⟨(hB₁ w hw hw2).trans (le_max_left _ _), (hB₂ w hw hw2).trans (le_max_right _ _)⟩⟩
  rw [oscPattern_prime _ _ hp, oscPattern_prime _ _ hp]
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
