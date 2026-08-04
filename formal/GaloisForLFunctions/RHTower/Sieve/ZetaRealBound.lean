import GaloisForLFunctions.RHTower.Sieve.ZetaThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaOneLineBound
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The size of the real zeta series near the pole

The upper bound the three-four-one inequality needs on the real axis is the elementary comparison of
`∑_n n^{-σ}` with `∫_1^∞ x^{-σ} dx`:

`∑'_{n} n^{-σ} ≤ 1 + 1/(σ − 1)`  for `σ > 1`.

The `1` is the term `n = 1` (the `n = 0` term vanishes by the `rpow` convention), and the tail is
dominated by the integral through mathlib's antitone sum-integral comparison.
-/

namespace RHTower.Sieve

open Finset

/-- The negative real power is antitone on the positives. -/
theorem antitoneOn_rpow_neg {σ : ℝ} (hσ : 0 ≤ σ) (a b : ℕ) (ha : 1 ≤ a) :
    AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc (a : ℝ) (b : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith [hx.1]
  exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)

/-- The tail integral of a negative power. -/
theorem integral_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ)) ≤ 1 / (σ - 1) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hNR]
    intro hcon
    exact absurd hcon.1 (by norm_num)
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hexp : -σ + 1 = -(σ - 1) := by ring
  rw [hexp]
  have hden : (0 : ℝ) < σ - 1 := by linarith
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(σ - 1)) :=
    Real.rpow_nonneg (by linarith) _
  have hone : (1 : ℝ) ^ (-(σ - 1)) = 1 := Real.one_rpow _
  rw [hone]
  have hrw : ((N : ℝ) ^ (-(σ - 1)) - 1) / (-(σ - 1))
      = (1 - (N : ℝ) ^ (-(σ - 1))) / (σ - 1) := by
    field_simp
    ring
  rw [hrw]
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hden)

/-- **The real zeta series near the pole.** -/
theorem tsum_nat_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) ?_
  intro N
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hinv : (0 : ℝ) ≤ (σ - 1)⁻¹ := inv_nonneg.2 (by linarith)
    interval_cases N
    · simp
      linarith
    · norm_num [Real.zero_rpow (by linarith : -σ ≠ 0)]
      linarith
  · have hsplit : ∑ i ∈ Finset.range N, (i : ℝ) ^ (-σ)
        = ((0 : ℝ) ^ (-σ) + (1 : ℝ) ^ (-σ)) + ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2) hN]
      congr 1
      rw [show Finset.Ico 0 2 = {0, 1} by decide, Finset.sum_insert (by decide),
        Finset.sum_singleton]
      norm_num
    have hzero : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
    have hone : (1 : ℝ) ^ (-σ) = 1 := Real.one_rpow _
    have hreindex : ∑ i ∈ Finset.Ico 1 (N - 1), ((i : ℝ) + 1) ^ (-σ)
        = ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ) := by
      have h := Finset.sum_Ico_add' (fun k : ℕ => ((k : ℝ)) ^ (-σ)) 1 (N - 1) 1
      push_cast at h
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using h
    have hsubset : ∑ i ∈ Finset.Ico 1 (N - 1), ((i : ℝ) + 1) ^ (-σ)
        ≤ ∑ i ∈ Finset.Ico 1 N, ((i : ℝ) + 1) ^ (-σ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Real.rpow_nonneg (by positivity) _)
      exact Finset.Ico_subset_Ico (le_refl 1) (by omega)
    have hcomp := (antitoneOn_rpow_neg (by linarith : (0:ℝ) ≤ σ) 1 N (le_refl 1)).sum_le_integral_Ico
      (by omega : 1 ≤ N)
    norm_num at hcomp
    have hint := integral_rpow_neg_le hσ (by omega : 1 ≤ N)
    rw [hsplit, hzero, hone]
    have hchain : ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ) ≤ 1 / (σ - 1) := by
      rw [← hreindex]
      exact le_trans hsubset (le_trans hcomp hint)
    linarith

/-- The norm of a reciprocal prime-power term. -/
theorem norm_one_div_nat_cpow {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    ‖(1 : ℂ) / (n : ℂ) ^ ((σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith)]
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg n)]
    exact one_div _

/-- **The real zeta function near the pole.** -/
theorem norm_riemannZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  have hre : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  have hnormsum : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ ((σ : ℂ))‖) := by
    have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hnat.congr fun n => (norm_one_div_nat_cpow hσ n).symm
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  have hcongr : ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ ((σ : ℂ))‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
    tsum_congr fun n => norm_one_div_nat_cpow hσ n
  rw [hcongr]
  exact tsum_nat_rpow_neg_le hσ

/-- **The logarithmic form**, which is the `A` of `log_norm_zeta_shift_ge`. -/
theorem log_norm_riemannZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    Real.log ‖riemannZeta (σ : ℂ)‖ ≤ Real.log (1 + 1 / (σ - 1)) := by
  have hpos : 0 < ‖riemannZeta (σ : ℂ)‖ := by
    refine norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re ?_)
    rw [Complex.ofReal_re]
    linarith
  exact Real.log_le_log hpos (norm_riemannZeta_real_le hσ)

/-- The norm of a reciprocal power, at a complex exponent. -/
theorem norm_one_div_nat_cpow_complex {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖(1 : ℂ) / (n : ℂ) ^ s‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (by
      intro hcon
      rw [hcon] at hs
      simp at hs
      linarith)]
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn,
      Real.rpow_neg (Nat.cast_nonneg n)]
    exact one_div _

/-- **The trivial bound for zeta on the open half-plane.**  Uniform in the imaginary part. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hnormsum : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖) := by
    have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
      rw [Real.summable_nat_rpow]
      linarith
    exact hnat.congr fun n => (norm_one_div_nat_cpow_complex hs n).symm
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  have hcongr : ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
    tsum_congr fun n => norm_one_div_nat_cpow_complex hs n
  rw [hcongr]
  exact tsum_nat_rpow_neg_le hs

/-- The logarithmic form of the trivial bound. -/
theorem log_norm_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ ≤ Real.log (1 + 1 / (s.re - 1)) := by
  have hpos : 0 < ‖riemannZeta s‖ :=
    norm_pos_iff.2 (riemannZeta_ne_zero_of_one_le_re (by linarith))
  exact Real.log_le_log hpos (norm_riemannZeta_le hs)

end RHTower.Sieve
