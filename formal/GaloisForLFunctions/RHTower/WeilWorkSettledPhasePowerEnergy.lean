import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePowerCoefficients
import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePowerLogMoment

/-!
# Critical square energy of complex source powers

Full positivity controls powers in `Re (1/z) > 1/2`. The exponent is
`1 / (2 * Re (1/z) - 1)`. This does not cover imaginary powers or assert
settlement of the canonical boundary phase.
-/

open Complex Finset
open scoped ComplexConjugate

noncomputable section
namespace RHTower.WeilWorkSettledPhase

/-- Complex self-pairing keeps the real part of the inverse power parameter. -/
theorem exists_powerCoeff_log_moment_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {z : ℂ} (hz : z ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (2 * z⁻¹.re) * ∑ n ∈ Icc 1 N, Real.log n * ‖powerCoeff lam z n‖ ^ 2 / n ≤
        (Real.log N + C) * ∑ n ∈ Icc 1 N, ‖powerCoeff lam z n‖ ^ 2 / n := by
  classical
  obtain ⟨C, hC⟩ := weil_multiplicativeToeplitz_bound (weilPositive_of_weilPositiveFull hW)
  refine ⟨max C 0, le_max_right _ _, fun N hN => ?_⟩
  let a := powerCoeff lam z
  let c : ℕ → ℂ := fun m => if m ≤ N then a m / (Real.sqrt m : ℂ) else 0
  let F : ℕ → ℕ → ℝ := fun n m => (if 2 ≤ n then lam n else 0) *
    ((a (n * m)).re * (a m).re + (a (n * m)).im * (a m).im) / (n * m : ℕ)
  have hcN : ∀ m, N < m → c m = 0 := by
    intro m hm
    simp [c, not_le.mpr hm]
  have hcnorm (m : ℕ) (hm : m ∈ Icc 1 N) : ‖c m‖ ^ 2 = ‖a m‖ ^ 2 / m := by
    simp only [c, if_pos (mem_Icc.mp hm).2, norm_div, Complex.norm_real,
      Real.norm_eq_abs, div_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hpair (n m : ℕ) (hn : 2 ≤ n) (hm : m ∈ Icc 1 N) :
      lam n / Real.sqrt n * (c (n * m) * conj (c m)).re =
        if n * m ≤ N then F n m else 0 := by
    by_cases hnm : n * m ≤ N
    · simp only [c, if_pos hnm, if_pos (mem_Icc.mp hm).2, F, if_pos hn,
        Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.div_ofReal_re, Complex.div_ofReal_im]
      have hden : Real.sqrt n * (Real.sqrt (n * m : ℕ) * Real.sqrt m) = (n * m : ℕ) := by
        rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n)]
        calc
          _ = (Real.sqrt n) ^ 2 * (Real.sqrt m) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg m)]
      calc
        _ = lam n * ((a (n * m)).re * (a m).re + (a (n * m)).im * (a m).im) /
            (Real.sqrt n * (Real.sqrt (n * m : ℕ) * Real.sqrt m)) := by ring
        _ = _ := by rw [hden]
    · simp [c, hnm]
  have hrow (n : ℕ) (hn : n ∈ Icc 2 N) :
      lam n / Real.sqrt n * (∑ m ∈ Icc 1 N, c (n * m) * conj (c m)).re =
        ∑ m ∈ Icc 1 (N / n), F n m := by
    have hn2 := (mem_Icc.mp hn).1
    have hn0 : 0 < n := by omega
    have hsub : Icc 1 (N / n) ⊆ Icc 1 N := by
      intro m hm
      exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans (Nat.div_le_self N n)⟩
    rw [Complex.re_sum, mul_sum]
    calc
      _ = ∑ m ∈ Icc 1 N, if n * m ≤ N then F n m else 0 :=
        sum_congr rfl fun m hm => hpair n m hn2 hm
      _ = ∑ m ∈ Icc 1 (N / n), if n * m ≤ N then F n m else 0 := by
        symm
        apply sum_subset hsub
        intro m hm hmn
        have hnm : ¬ n * m ≤ N := by
          intro h
          apply hmn
          exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
            (Nat.le_div_iff_mul_le hn0).mpr (by simpa only [Nat.mul_comm] using h)⟩
        simp [hnm]
      _ = _ := sum_congr rfl fun m hm => if_pos (by
        have h := (Nat.le_div_iff_mul_le hn0).mp (mem_Icc.mp hm).2
        simpa only [Nat.mul_comm] using h)
  have hconv (k : ℕ) : LSeries.convolution (WeilHerglotz.lamC lam) a k =
      z⁻¹ * (Real.log k : ℂ) * a k := by
    have h := congrArg (fun v : ℂ => z⁻¹ * v) (powerCoeff_log_convolution hW z k)
    simpa only [← mul_assoc, inv_mul_cancel₀ hz, one_mul] using h
  have hdiag (k : ℕ) : (∑ p ∈ k.divisorsAntidiagonal, F p.1 p.2) =
      z⁻¹.re * (Real.log k * ‖a k‖ ^ 2 / k) := by
    have hr := congrArg Complex.re (hconv k)
    have hi := congrArg Complex.im (hconv k)
    simp only [LSeries.convolution_def, WeilHerglotz.lamC, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
    simp only [LSeries.convolution_def, WeilHerglotz.lamC, Complex.im_sum,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hi
    calc
      _ = (a k).re / k * ∑ p ∈ k.divisorsAntidiagonal,
            (if 2 ≤ p.1 then lam p.1 else 0) * (a p.2).re +
          (a k).im / k * ∑ p ∈ k.divisorsAntidiagonal,
            (if 2 ≤ p.1 then lam p.1 else 0) * (a p.2).im := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro p hp
        have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
        dsimp [F]
        rw [hp']
        ring
      _ = _ := by
        rw [hr, hi, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
  have hleft : (∑ n ∈ Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Icc 1 N, c (n * m) * conj (c m)).re) =
      z⁻¹.re * ∑ k ∈ Icc 1 N, Real.log k * ‖a k‖ ^ 2 / k := by
    calc
      _ = ∑ n ∈ Icc 2 N, ∑ m ∈ Icc 1 (N / n), F n m :=
        sum_congr rfl fun n hn => hrow n hn
      _ = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / n), F n m := by
        apply sum_subset
        · intro n hn
          have h := mem_Icc.mp hn
          exact mem_Icc.mpr ⟨by omega, h.2⟩
        · intro n hn hn'
          have hn1 : n = 1 := by
            simp only [mem_Icc, not_and, not_le] at hn hn'
            omega
          subst n
          simp [F]
      _ = ∑ k ∈ Icc 1 N, ∑ p ∈ k.divisorsAntidiagonal, F p.1 p.2 :=
        (Sieve.sum_Icc_divisorsAntidiagonal_swap F N).symm
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun k _ => hdiag k
  have ht := hC N hN c hcN
  rw [hleft, sum_congr rfl hcnorm, ← mul_assoc] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right
    (add_le_add_right (le_max_left C 0) _) (sum_nonneg fun m _ =>
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg m)))

/-- Original full positivity gives critical square energy throughout the open
power disk, with no sign, multiplicativity or spectral hypothesis. -/
theorem exists_powerCoeff_critical_energy_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {z : ℂ} (hz : (1 / 2 : ℝ) < z⁻¹.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, ‖powerCoeff lam z n‖ ^ 2 / n ≤
        K * (1 + Real.log N) ^ (1 / (2 * z⁻¹.re - 1)) := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  obtain ⟨C, hC, hb⟩ := exists_powerCoeff_log_moment_le hW hz0
  apply sum_le_log_rpow_of_log_moment
    (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) hC (by linarith : 1 < 2 * z⁻¹.re)
  intro N hN
  simpa only [mul_div_assoc] using hb N hN

end RHTower.WeilWorkSettledPhase
