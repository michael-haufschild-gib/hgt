import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Field

/-!
# The generating function of the probabilists' Hermite polynomials

**Theorem** (`hasSum_aeval_hermite_mul_pow_div_factorial`).  For real `x, u`,

  `Σ_N He_N(x) u^N / N! = e^{xu − u²/2}`,

and the absolute series is dominated: `Σ_N |He_N(x)| |u|^N / N! ≤ e^{|x||u| + u²/2}`
(`hasSum_abs_coeff_hermite_bound`).

Proof.  `e^{−u²/2} = Σ_m a_m u^m` with `a_{2k} = (−½)^k/k!` and `a_{2k+1} = 0`.  The Cauchy product with
`e^{xu} = Σ_j (xu)^j/j!` has `u^N`-coefficient `Σ_{j ≤ N} x^j a_{N−j}/j!`, and the explicit
coefficients `coeff_j He_N = (−1)^n (2n−1)!! C(N, j)` (`N − j = 2n`) give
`coeff_j He_N / N! = a_{N−j}/j!` (`coeff_hermite_div_factorial`), since `(2n)! = 2ⁿ n! (2n−1)!!`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficients of `e^{−u²/2} = Σ_m a_m u^m`. -/
def gaussSeriesCoeff (m : ℕ) : ℝ :=
  if Even m then (-1 / 2 : ℝ) ^ (m / 2) / ((m / 2).factorial : ℝ) else 0

theorem hasSum_exp_series (y : ℝ) : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

theorem gaussSeriesCoeff_two_mul (k : ℕ) (u : ℝ) :
    gaussSeriesCoeff (2 * k) * u ^ (2 * k) = (-(u ^ 2 / 2)) ^ k / (k.factorial : ℝ) := by
  unfold gaussSeriesCoeff
  rw [if_pos (even_two_mul k), Nat.mul_div_cancel_left k (by norm_num), pow_mul]
  rw [show (-(u ^ 2 / 2)) ^ k = (-1 / 2) ^ k * (u ^ 2) ^ k by rw [← mul_pow]; ring_nf]
  ring

theorem gaussSeriesCoeff_odd {m : ℕ} (hm : ¬ Even m) : gaussSeriesCoeff m = 0 := by
  unfold gaussSeriesCoeff; rw [if_neg hm]

theorem hasSum_gaussSeriesCoeff (u : ℝ) :
    HasSum (fun m : ℕ => gaussSeriesCoeff m * u ^ m) (Real.exp (-(u ^ 2 / 2))) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k), gaussSeriesCoeff m * u ^ m = 0 := by
    intro m hm
    have : ¬ Even m := fun he => hm (by obtain ⟨k, hk⟩ := he; exact ⟨k, show 2 * k = m by omega⟩)
    rw [gaussSeriesCoeff_odd this, zero_mul]
  rw [← hinj.hasSum_iff hzero]
  simp only [Function.comp_def, gaussSeriesCoeff_two_mul]
  exact hasSum_exp_series _

theorem hasSum_abs_gaussSeriesCoeff (u : ℝ) :
    HasSum (fun m : ℕ => |gaussSeriesCoeff m| * |u| ^ m) (Real.exp (u ^ 2 / 2)) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k), |gaussSeriesCoeff m| * |u| ^ m = 0 := by
    intro m hm
    have : ¬ Even m := fun he => hm (by obtain ⟨k, hk⟩ := he; exact ⟨k, show 2 * k = m by omega⟩)
    rw [gaussSeriesCoeff_odd this, abs_zero, zero_mul]
  rw [← hinj.hasSum_iff hzero]
  have e : ∀ k : ℕ, |gaussSeriesCoeff (2 * k)| * |u| ^ (2 * k) = (u ^ 2 / 2) ^ k / k.factorial := by
    intro k
    have h := gaussSeriesCoeff_two_mul k u
    rw [← abs_pow, ← abs_mul, h, abs_div, abs_pow, Nat.abs_cast, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ u ^ 2 / 2)]
  simp only [Function.comp_def, e]
  exact hasSum_exp_series _

/-- `coeff_j He_N / N! = a_{N−j}/j!` for `j ≤ N`. -/
theorem coeff_hermite_div_factorial {N j : ℕ} (hj : j ≤ N) :
    ((hermite N).coeff j : ℝ) / (N.factorial : ℝ) = gaussSeriesCoeff (N - j) / (j.factorial : ℝ) := by
  by_cases hev : Even (N - j)
  · obtain ⟨n, hn⟩ := hev
    have hN : N = j + 2 * n := by omega
    have hevadd : Even (N + j) := ⟨j + n, by omega⟩
    rw [coeff_hermite_of_even_add hevadd]
    have h1 : (N - j) / 2 = n := by omega
    have h2 : N - j - 1 = 2 * n - 1 := by omega
    rw [h1, h2]
    unfold gaussSeriesCoeff
    rw [if_pos ⟨n, hn⟩, show (N - j) / 2 = n by omega]
    have hchoose : ((N.choose j : ℕ) : ℝ) * j.factorial * (N - j).factorial = N.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    have hfac2 : ((2 * n).factorial : ℝ) = 2 ^ n * n.factorial * (2 * n - 1).doubleFactorial := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp
      · have h := Nat.factorial_eq_mul_doubleFactorial (2 * n - 1)
        rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.doubleFactorial_two_mul] at h
        rw [h]; push_cast; ring
    rw [show N - j = 2 * n by omega] at hchoose
    have hNf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    have hjf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hdf : (0 : ℝ) < (2 * n - 1).doubleFactorial := by
      exact_mod_cast Nat.doubleFactorial_pos _
    rw [hfac2] at hchoose
    push_cast
    rw [div_eq_div_iff hNf.ne' hjf.ne', ← hchoose]
    rw [show (-1 / 2 : ℝ) ^ n = (-1) ^ n / 2 ^ n by rw [div_pow]]
    field_simp
  · have hodd : Odd (N + j) := by
      rw [Nat.not_even_iff_odd] at hev
      obtain ⟨k, hk⟩ := hev
      exact ⟨k + j, by omega⟩
    rw [coeff_hermite_of_odd_add hodd, gaussSeriesCoeff_odd hev]
    simp

/-- **The Hermite generating function.**  `Σ_N He_N(x) u^N/N! = e^{xu − u²/2}`. -/
theorem hasSum_aeval_hermite_mul_pow_div_factorial (x u : ℝ) :
    HasSum (fun N : ℕ => aeval x (hermite N) * u ^ N / (N.factorial : ℝ))
      (Real.exp (x * u - u ^ 2 / 2)) := by
  set f : ℕ → ℝ := fun j => (x * u) ^ j / (j.factorial : ℝ) with hf
  set g : ℕ → ℝ := fun m => gaussSeriesCoeff m * u ^ m with hg
  have hfn : Summable fun j => ‖f j‖ := by
    have := (hasSum_exp_series (|x * u|)).summable
    refine this.congr fun j => ?_
    simp only [hf, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  have hgn : Summable fun m => ‖g m‖ := by
    refine (hasSum_abs_gaussSeriesCoeff u).summable.congr fun m => ?_
    simp only [hg, Real.norm_eq_abs, abs_mul, abs_pow]
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have hterm : ∀ N : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, f kl.1 * g kl.2
      = aeval x (hermite N) * u ^ N / (N.factorial : ℝ) := by
    intro N
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, aeval_eq_sum_range, natDegree_hermite,
      Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hc := coeff_hermite_div_factorial hjN
    simp only [hf, hg, zsmul_eq_mul]
    have hpow : u ^ N = u ^ j * u ^ (N - j) := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    have hNf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    have hjf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    calc (x * u) ^ j / (j.factorial : ℝ) * (gaussSeriesCoeff (N - j) * u ^ (N - j))
        = x ^ j * (u ^ j * u ^ (N - j)) * (gaussSeriesCoeff (N - j) / (j.factorial : ℝ)) := by
          rw [mul_pow]; ring
      _ = x ^ j * (u ^ j * u ^ (N - j)) * (((hermite N).coeff j : ℝ) / (N.factorial : ℝ)) := by
          rw [hc]
      _ = ((hermite N).coeff j : ℝ) * x ^ j * (u ^ j * u ^ (N - j)) / (N.factorial : ℝ) := by ring
  have hexp : (∑' j, f j) * (∑' m, g m) = Real.exp (x * u - u ^ 2 / 2) := by
    rw [(hasSum_exp_series (x * u)).tsum_eq, (hasSum_gaussSeriesCoeff u).tsum_eq, ← Real.exp_add]
    ring_nf
  rw [← hexp, hprod]
  simp only [← hterm]
  exact hsum.hasSum

/-- **The absolute generating function.**  `Σ_N (Σ_j |coeff_j He_N| |x|^j) |u|^N / N! = e^{|x||u| + u²/2}`;
in particular `Σ_N |He_N(x)| |u|^N/N!` converges and is at most `e^{|x||u| + u²/2}`. -/
theorem summable_abs_aeval_hermite_le (x u : ℝ) :
    Summable (fun N : ℕ => |aeval x (hermite N)| * |u| ^ N / (N.factorial : ℝ)) ∧
      ∑' N : ℕ, |aeval x (hermite N)| * |u| ^ N / (N.factorial : ℝ)
        ≤ Real.exp (|x| * |u| + u ^ 2 / 2) := by
  set f : ℕ → ℝ := fun j => (|x| * |u|) ^ j / (j.factorial : ℝ) with hf
  set g : ℕ → ℝ := fun m => |gaussSeriesCoeff m| * |u| ^ m with hg
  have hfn : Summable fun j => ‖f j‖ := by
    refine (hasSum_exp_series (|x| * |u|)).summable.congr fun j => ?_
    rw [Real.norm_of_nonneg (show 0 ≤ f j by simp only [hf]; positivity)]
  have hgn : Summable fun m => ‖g m‖ := by
    refine (hasSum_abs_gaussSeriesCoeff u).summable.congr fun m => ?_
    rw [Real.norm_of_nonneg (show 0 ≤ g m by simp only [hg]; positivity)]
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have hle : ∀ N : ℕ, |aeval x (hermite N)| * |u| ^ N / (N.factorial : ℝ)
      ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, f kl.1 * g kl.2 := by
    intro N
    have hNf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, aeval_eq_sum_range, natDegree_hermite]
    calc |∑ i ∈ Finset.range (N + 1), (hermite N).coeff i • x ^ i| * |u| ^ N / (N.factorial : ℝ)
        ≤ (∑ i ∈ Finset.range (N + 1), |((hermite N).coeff i : ℝ)| * |x| ^ i) * |u| ^ N
            / (N.factorial : ℝ) := by
          gcongr
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [zsmul_eq_mul, abs_mul, abs_pow]
      _ = ∑ k ∈ Finset.range N.succ, f (k, N - k).1 * g (k, N - k).2 := by
          rw [Finset.sum_mul, Finset.sum_div]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hc := coeff_hermite_div_factorial hjN
          have hjf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
          have hca : |((hermite N).coeff j : ℝ)| / (N.factorial : ℝ)
              = |gaussSeriesCoeff (N - j)| / (j.factorial : ℝ) := by
            rw [← abs_of_pos hNf, ← abs_div, hc, abs_div, abs_of_pos hjf]
          simp only [hf, hg]
          have hpow : |u| ^ N = |u| ^ j * |u| ^ (N - j) := by rw [← pow_add]; congr 1; omega
          rw [hpow]
          calc |((hermite N).coeff j : ℝ)| * |x| ^ j * (|u| ^ j * |u| ^ (N - j)) / (N.factorial : ℝ)
              = |x| ^ j * (|u| ^ j * |u| ^ (N - j))
                  * (|((hermite N).coeff j : ℝ)| / (N.factorial : ℝ)) := by ring
            _ = |x| ^ j * (|u| ^ j * |u| ^ (N - j))
                  * (|gaussSeriesCoeff (N - j)| / (j.factorial : ℝ)) := by rw [hca]
            _ = (|x| * |u|) ^ j / (j.factorial : ℝ) * (|gaussSeriesCoeff (N - j)| * |u| ^ (N - j)) := by
                rw [mul_pow]; ring
  have hexp : (∑' j, f j) * (∑' m, g m) = Real.exp (|x| * |u| + u ^ 2 / 2) := by
    rw [(hasSum_exp_series (|x| * |u|)).tsum_eq, (hasSum_abs_gaussSeriesCoeff u).tsum_eq,
      ← Real.exp_add]
  have hnn : ∀ N, 0 ≤ |aeval x (hermite N)| * |u| ^ N / (N.factorial : ℝ) := fun N => by positivity
  have hs : Summable (fun N : ℕ => |aeval x (hermite N)| * |u| ^ N / (N.factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hle hsum
  refine ⟨hs, ?_⟩
  rw [← hexp, hprod]
  exact hs.tsum_le_tsum hle hsum

end

end GaloisForLFunctions.HTGeometry
