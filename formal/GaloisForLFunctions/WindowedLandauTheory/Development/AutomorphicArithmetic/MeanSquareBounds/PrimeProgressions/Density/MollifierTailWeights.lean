import GaloisForLFunctions.RHTower.ChenGuptaLiTailCoefficientBounds
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-! Weighted coefficient energy for the truncated Möbius detector. -/

open Complex Finset RHTower RHTower.Sieve

namespace QH.PrimeProgressions

/-- The Möbius convolution coefficient with divisor cutoff Q cubed. -/
noncomputable def mollifierCoeff (Q n : ℕ) : ℂ :=
  (zeroDetectionMobiusCoefficient (Q ^ 3 - 1) n : ℂ)

theorem mollifierCoeff_eq {Q n : ℕ} (hQ : 0 < Q) :
    mollifierCoeff Q n =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (ArithmeticFunction.moebius d : ℂ) := by
  have h : Q ^ 3 - 1 + 1 = Q ^ 3 := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hQ.ne'))
  simp [mollifierCoeff, zeroDetectionMobiusCoefficient, h]

/-- Uniform coefficient-square bound on the real parts used in the holomorphic submean estimate. -/
theorem mollifier_coeff_energy (Q : ℕ) (hQ : 2 ≤ Q) {σ : ℝ} (hσ : 1 - 3 / 800 ≤ σ) :
    ∑ n ∈ Ioc (Q ^ 3) (Q ^ 6), ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) *
      ‖mollifierCoeff Q n * (n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 ≤
    (240 * (divisorBoundConst (1 / 400)) ^ 2) * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  let K := divisorBoundConst (1 / 400)
  let θ : ℝ := 1 / 80
  have hK : 0 < K := divisorBoundConst_pos (by norm_num)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hpoint (n : ℕ) (hn : n ∈ Ioc (Q ^ 3) (Q ^ 6)) :
      ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) * ‖mollifierCoeff Q n * (n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 ≤
      3 * K ^ 2 * (n : ℝ) ^ (θ - 1) := by
    have hnpos : 0 < n := (Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
    have hnQ : (Q : ℝ) ^ 3 < n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hweight : (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n ≤ 3 * n := by
      have h23 := pow_le_pow_right₀ hQ1 (show 2 ≤ 3 by omega)
      nlinarith only [hnQ, h23]
    have hcoef : ‖mollifierCoeff Q n‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400) :=
      (norm_zeroDetectionMobiusCoefficient_le_card_divisors _ _).trans
        (card_divisors_le_rpow (by norm_num) hnpos.ne')
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Complex.ofReal_re, mul_pow]
    calc
      _ ≤ (3 * n) * ((K * (n : ℝ) ^ ((1 : ℝ) / 400)) ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by
        gcongr
      _ = 3 * K ^ 2 * (n : ℝ) ^ (1 / 200 + 1 - 2 * σ) := by
        rw [show (1 : ℝ) / 200 + 1 - 2 * σ = (1 / 400) * 2 + 1 + (-σ) * 2 by ring,
          Real.rpow_add hnR, Real.rpow_add hnR, Real.rpow_one, Real.rpow_mul hnR.le,
          Real.rpow_mul hnR.le, Real.rpow_two, Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [θ]; linarith only [hσ])) (by positivity)
  have hs : Ioc (Q ^ 3) (Q ^ 6) ⊆ Icc 1 (Q ^ 6) := fun n hn =>
    mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1), (mem_Ioc.mp hn).2⟩
  have hpow : ∑ n ∈ Icc 1 (Q ^ 6), (n : ℝ) ^ (θ - 1) ≤ 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    have hreindex : ∑ n ∈ Icc 1 (Q ^ 6), (n : ℝ) ^ (θ - 1) =
        ∑ k ∈ range (Q ^ 6), ((k : ℝ) + 1) ^ (θ - 1) := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact sum_congr rfl fun k _ => by push_cast; ring_nf
    rw [hreindex]
    refine (HTGeometry.sum_rpow_sub_one_le (a := θ) (by norm_num [θ]) (by norm_num [θ]) _).trans ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (Q : ℝ) 6, ← Real.rpow_mul (Nat.cast_nonneg Q)]
    have h := Real.rpow_le_rpow_of_exponent_le hQ1 (show (6 : ℝ) * θ ≤ 1 / 8 by norm_num [θ])
    have hθ : θ⁻¹ = 80 := by norm_num [θ]
    rw [div_eq_mul_inv, hθ, mul_comm]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  calc
    _ ≤ ∑ n ∈ Ioc (Q ^ 3) (Q ^ 6), 3 * K ^ 2 * (n : ℝ) ^ (θ - 1) :=
      sum_le_sum hpoint
    _ ≤ 3 * K ^ 2 * (80 * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => by positivity).trans hpow) (by positivity)
    _ = _ := by dsimp [K]; ring

end QH.PrimeProgressions
