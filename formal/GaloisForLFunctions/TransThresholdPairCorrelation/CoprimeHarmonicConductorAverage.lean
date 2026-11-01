import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeHarmonicCentering
import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole
import GaloisForLFunctions.RHTower.RieszMellinPair

/-!
# Uniform coprime-harmonic errors averaged over conductors

The reciprocal-totient square weight has a summable logarithmic moment.
Möbius decomposition bounds each coprime-harmonic defect uniformly in its
summation horizon; divisor swapping then bounds the conductor-weighted
aggregate by `36864 (1 + log Q)`, even with a different horizon for each
conductor. The arithmetic first moment reuses the existing totient-ratio bound.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open RHTower.Sieve
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem square_weight_nonneg (q : ℕ) :
    0 ≤ sqfreeTotientInv q / (q.totient : ℝ) :=
  div_nonneg (sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _)

private theorem first_moment_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q,
      (q : ℝ) * (sqfreeTotientInv q / (q.totient : ℝ))) ≤ 64 * (1 + Real.log Q) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) ^ 2 / (q : ℝ) := by
      apply sum_le_sum
      intro q hq
      have hq0 : 0 < q := (mem_Icc.mp hq).1
      have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
      by_cases hs : Squarefree q
      · rw [sqfreeTotientInv_apply, if_pos hs]
        apply le_of_eq
        field_simp
      · rw [sqfreeTotientInv_apply, if_neg hs, zero_div, mul_zero]
        positivity
    _ ≤ _ := sum_totientRatio_sq_div_le Q

private theorem sqrt_weight_summable_bound :
    Summable (fun q : ℕ => (sqfreeTotientInv q / (q.totient : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ)) ∧
    (∑' q : ℕ, (sqfreeTotientInv q / (q.totient : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ)) ≤ 192 := by
  let c : ℕ → ℝ := fun q => (q : ℝ) * (sqfreeTotientInv q / (q.totient : ℝ))
  have hc (q : ℕ) : 0 ≤ c q := by
    exact mul_nonneg (Nat.cast_nonneg q) (square_weight_nonneg q)
  have hpartial (N : ℕ) : RHTower.weightPartialSum c N ≤ 64 * (Real.log N + 1) := by
    have he : (∑ q ∈ Icc 0 N, c q) = ∑ q ∈ Icc 1 N, c q := by
      symm
      apply sum_subset (by intro q hq; simp only [mem_Icc] at hq ⊢; omega)
      intro q hq hn
      have hq0 : q = 0 := by simp only [mem_Icc] at hq hn; omega
      subst q
      simp [c]
    unfold RHTower.weightPartialSum
    rw [he]
    have h := first_moment_le N
    nlinarith only [h, Real.log_natCast_nonneg N]
  obtain ⟨hs, hb⟩ := RHTower.summable_and_mul_tsum_weightedDirichlet_le
    (c := c) (by norm_num [c]) hc (by norm_num : (0 : ℝ) ≤ 64) hpartial
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he : (fun q : ℕ => c q * (q : ℝ) ^ (-(1 / 2 : ℝ))) =
      (fun q : ℕ => (sqfreeTotientInv q / (q.totient : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ)) := by
    funext q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · norm_num [c]
    · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have hp : (q : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) = (q : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          _ = (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hq0]; norm_num
      dsimp [c]
      calc
        _ = (sqfreeTotientInv q / (q.totient : ℝ)) * ((q : ℝ) * (q : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hp]
  rw [he] at hs hb
  exact ⟨hs, by nlinarith only [hb]⟩

/-- The reciprocal-totient square weight has a summable logarithmic
moment, sufficient for conductor-averaged coprime-harmonic errors. -/
theorem summable_sqfreeTotientInv_log_div_totient :
    Summable (fun q : ℕ => (sqfreeTotientInv q / (q.totient : ℝ)) * (1 + Real.log q)) ∧
    (∑' q : ℕ, (sqfreeTotientInv q / (q.totient : ℝ)) * (1 + Real.log q)) ≤ 576 := by
  let f : ℕ → ℝ := fun q => (sqfreeTotientInv q / (q.totient : ℝ)) * (1 + Real.log q)
  let b : ℕ → ℝ := fun q => (sqfreeTotientInv q / (q.totient : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ)
  have hf (q : ℕ) : 0 ≤ f q := by
    exact mul_nonneg (square_weight_nonneg q) (by linarith [Real.log_natCast_nonneg q])
  have hpt (q : ℕ) : f q ≤ 3 * b q := by
    dsimp [f, b]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · norm_num [sqfreeTotientInv_apply]
    · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hl := GaloisForLFunctions.RHTower.log_le_rpow_div (by norm_num : (0 : ℝ) < 1) hq1
      norm_num at hl
      have hp : 1 ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
      have hlog : 1 + Real.log q ≤ 3 * (q : ℝ) ^ (1 / 2 : ℝ) := by linarith only [hl, hp]
      have h := mul_le_mul_of_nonneg_left hlog (square_weight_nonneg q)
      nlinarith only [h]
  have hb : Summable b := sqrt_weight_summable_bound.1
  have hfs : Summable f := (hb.mul_left 3).of_norm_bounded (fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf q)]
    exact hpt q)
  refine ⟨hfs, ?_⟩
  calc
    (∑' q : ℕ, f q) ≤ ∑' q : ℕ, 3 * b q := hfs.tsum_le_tsum hpt (hb.mul_left 3)
    _ = 3 * ∑' q : ℕ, b q := tsum_mul_left
    _ ≤ 3 * 192 := mul_le_mul_of_nonneg_left sqrt_weight_summable_bound.2 (by norm_num)
    _ = _ := by norm_num

private theorem harmonic_div_log_error_le {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |(∑ n ∈ Icc 1 (N / d), 1 / (n : ℝ)) - Real.log N| ≤ 1 + Real.log d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo := log_le_harmonic_floor ((N : ℝ) / d) (by positivity)
  rw [Nat.floor_div_natCast, Nat.floor_natCast, Real.log_div hNr.ne' hdr.ne'] at hlo
  have hup := harmonic_le_one_add_log (N / d)
  have hlog : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos (N / d) with hz | hp
    · rw [hz, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg N
    · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast Nat.div_le_self N d)
  simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] at hlo hup
  simp only [← one_div] at hlo hup
  rw [abs_le]
  constructor <;> linarith only [hlo, hup, hlog, Real.log_natCast_nonneg d]

/-- Uniform in the summation horizon, the coprime harmonic error costs only
an explicit logarithmic divisor sum. -/
theorem abs_coprimeHarmonic_sub_totient_log_le {q N : ℕ} (hq : 0 < q) (hN : 0 < N) :
    |coprimeHarmonic q N - (q.totient : ℝ) / (q : ℝ) * Real.log N| ≤
      ∑ d ∈ q.divisors, (1 + Real.log d) / (d : ℝ) := by
  rw [coprimeHarmonic_sub_totient_mul hq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [abs_mul, abs_div, abs_of_pos hdr]
  calc
    _ ≤ (1 / (d : ℝ)) * (1 + Real.log d) :=
      mul_le_mul (div_le_div_of_nonneg_right (RHTower.Sieve.abs_moebius_le_one d) hdr.le)
        (harmonic_div_log_error_le hN hd0) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem square_weight_mul_le (d k : ℕ) :
    sqfreeTotientInv (d * k) / ((d * k).totient : ℝ) ≤
      (sqfreeTotientInv d / (d.totient : ℝ)) * (sqfreeTotientInv k / (k.totient : ℝ)) := by
  by_cases hsq : Squarefree (d * k)
  · obtain ⟨hc, hd, hk⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [sqfreeTotientInv_apply, if_pos hsq, sqfreeTotientInv_apply, if_pos hd,
      sqfreeTotientInv_apply, if_pos hk, Nat.totient_mul hc]
    push_cast
    exact le_of_eq (by ring)
  · rw [sqfreeTotientInv_apply, if_neg hsq, zero_div]
    exact mul_nonneg (square_weight_nonneg d) (square_weight_nonneg k)

private theorem weighted_divisor_error_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) * (sqfreeTotientInv q / (q.totient : ℝ)) *
      ∑ d ∈ q.divisors, (1 + Real.log d) / (d : ℝ)) ≤ 36864 * (1 + Real.log Q) := by
  let A : ℕ → ℝ := fun q => sqfreeTotientInv q / (q.totient : ℝ)
  let G : ℕ → ℕ → ℝ := fun d k => (k : ℝ) * A (d * k) * (1 + Real.log d)
  have hsplit : (∑ q ∈ Icc 1 Q, (q : ℝ) * A q *
      ∑ d ∈ q.divisors, (1 + Real.log d) / (d : ℝ)) =
      ∑ d ∈ Icc 1 Q, ∑ k ∈ Icc 1 (Q / d), G d k := by
    rw [← sum_divisors_swap]
    apply sum_congr rfl
    intro q hq
    rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hdiv : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
    dsimp only [G]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    calc
      _ = ((d : ℝ) * ((q / d : ℕ) : ℝ)) * A q * ((1 + Real.log d) / (d : ℝ)) := by rw [← hdiv]
      _ = _ := by field_simp
  have hinner (d : ℕ) :
      (∑ k ∈ Icc 1 (Q / d), G d k) ≤ A d * (1 + Real.log d) * (64 * (1 + Real.log Q)) := by
    have hc : 0 ≤ A d * (1 + Real.log d) :=
      mul_nonneg (square_weight_nonneg d) (by linarith [Real.log_natCast_nonneg d])
    calc
      _ ≤ ∑ k ∈ Icc 1 (Q / d), A d * (1 + Real.log d) * ((k : ℝ) * A k) := by
        apply sum_le_sum
        intro k _
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (square_weight_mul_le d k) (Nat.cast_nonneg k))
          (by linarith [Real.log_natCast_nonneg d] : 0 ≤ 1 + Real.log d)
        calc
          G d k ≤ (k : ℝ) * (A d * A k) * (1 + Real.log d) := h
          _ = _ := by ring
      _ ≤ ∑ k ∈ Icc 1 Q, A d * (1 + Real.log d) * ((k : ℝ) * A k) := by
        apply sum_le_sum_of_subset_of_nonneg
          (by intro k hk; exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans (Nat.div_le_self Q d)⟩)
        intro k _ _
        exact mul_nonneg hc (mul_nonneg (Nat.cast_nonneg k) (square_weight_nonneg k))
      _ = A d * (1 + Real.log d) * ∑ k ∈ Icc 1 Q, (k : ℝ) * A k := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (first_moment_le Q) hc
  have hfinite : (∑ d ∈ Icc 1 Q, A d * (1 + Real.log d)) ≤ 576 := by
    apply le_trans (Summable.sum_le_tsum (Icc 1 Q)
      (fun d _ => mul_nonneg (square_weight_nonneg d) (by linarith [Real.log_natCast_nonneg d]))
      summable_sqfreeTotientInv_log_div_totient.1)
    exact summable_sqfreeTotientInv_log_div_totient.2
  change (∑ q ∈ Icc 1 Q, (q : ℝ) * A q *
    ∑ d ∈ q.divisors, (1 + Real.log d) / (d : ℝ)) ≤ _
  rw [hsplit]
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, A d * (1 + Real.log d) * (64 * (1 + Real.log Q)) := sum_le_sum (fun d _ => hinner d)
    _ = (∑ d ∈ Icc 1 Q, A d * (1 + Real.log d)) * (64 * (1 + Real.log Q)) := by rw [sum_mul]
    _ ≤ 576 * (64 * (1 + Real.log Q)) :=
      mul_le_mul_of_nonneg_right hfinite (by positivity)
    _ = _ := by ring

/-- Coprime-harmonic errors have only logarithmic conductor cost, uniformly
for an arbitrary positive summation horizon at every conductor. -/
theorem sum_weighted_abs_coprimeHarmonic_sub_totient_log_le (Q : ℕ) (N : ℕ → ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) * (sqfreeTotientInv q / (q.totient : ℝ)) *
      |coprimeHarmonic q (N q + 1) - (q.totient : ℝ) / (q : ℝ) * Real.log ((N q + 1 : ℕ) : ℝ)|) ≤
      36864 * (1 + Real.log Q) := by
  apply le_trans (sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left
    (abs_coprimeHarmonic_sub_totient_log_le (mem_Icc.mp hq).1 (Nat.succ_pos (N q)))
    (mul_nonneg (Nat.cast_nonneg q) (square_weight_nonneg q))))
    (weighted_divisor_error_le Q)

end GaloisForLFunctions.TransThresholdPairCorrelation
