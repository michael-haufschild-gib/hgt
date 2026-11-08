import GaloisForLFunctions.InfiniteRankWeilTheory.ReturnsFreezeSmoothPolynomials

/-!
# The precision cost of forced vanishing

Moment conditions force a smooth Dirichlet polynomial `A` to be small to order `J` at every return
(`ReturnsFreezeSmoothPolynomials`). A Stepanov count needs more: the zero of order `J` at `s₀` must be
copied to the return, and the Rouché route to that copy needs the freezing error to stay below `|A|`
on a circle `|w| = r`. This file prices that requirement.

* `exp_sub_sum_le`: the `J`-th exponential tail is at most `x^J e^x/J!` for `x ≥ 0`.
* `norm_dpoly_le_flat`: a polynomial on `[2, N]` with `J` vanishing logarithmic moments at `s₀` has
  `|A(s₀ + w)| ≤ m (|w| log N)^J N^{|w|}/J!`, `m = Σ|c_n n^{−s₀}|`.
* `factorial_mul_lt_of_rouche`: if at one point `|w| = r` of the circle the freezing error bound
  `δ Σ|c_n n^{−(s₀+w)}| Ω(n)` is below `|A(s₀ + w)|`, then `δ J! < (r log N)^J N^{2r}`.
* `order_le_of_rouche`: hence `J ≤ e² r log N + log(1/δ)` for `0 < δ ≤ 1`.

So at constant precision the order of a zero that forced vanishing can copy to a return is
`O(r log N)`: the auxiliary polynomial gains at most `O(r)` zeros per unit of `log`-length per return.
Since a Dirichlet polynomial of length `N` has about `(T/2π) log N` zeros up to height `T`, the
resulting Stepanov count of `r`-separated returns is `≳ T/r`, the trivial separation bound. Over `𝔽_q`
the Frobenius makes the order of vanishing at the points as large as the degree allows; over `ℤ` the
order is capped by the precision. This is the exact form of "no Frobenius substitute".
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- `e^x − Σ_{j<J} x^j/j! ≤ x^J e^x/J!` for `x ≥ 0`. -/
theorem exp_sub_sum_le {x : ℝ} (hx : 0 ≤ x) (J : ℕ) :
    Real.exp x - ∑ j ∈ range J, x ^ j / (j.factorial : ℝ) ≤
      x ^ J / (J.factorial : ℝ) * Real.exp x := by
  have hs := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := hs.sum_add_tsum_nat_add J
  have htail : Summable fun k : ℕ => x ^ (k + J) / ((k + J).factorial : ℝ) :=
    hs.comp_injective (add_left_injective J)
  calc Real.exp x - ∑ j ∈ range J, x ^ j / (j.factorial : ℝ)
      = ∑' k : ℕ, x ^ (k + J) / ((k + J).factorial : ℝ) := by
        rw [hexp, ← hsplit, add_sub_cancel_left]
    _ ≤ ∑' k : ℕ, x ^ J / (J.factorial : ℝ) * (x ^ k / (k.factorial : ℝ)) := by
        refine htail.tsum_le_tsum (fun k => ?_) (hs.mul_left _)
        have hf : ((k.factorial : ℕ) : ℝ) * (J.factorial : ℝ) ≤ ((k + J).factorial : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
            (Nat.factorial_mul_factorial_dvd_factorial_add k J)
        rw [pow_add, show x ^ J / (J.factorial : ℝ) * (x ^ k / (k.factorial : ℝ)) =
          x ^ k * x ^ J / ((k.factorial : ℝ) * (J.factorial : ℝ)) by ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = x ^ J / (J.factorial : ℝ) * Real.exp x := by rw [tsum_mul_left, ← hexp]

/-- **Flatness of a zero of order `J`.** For a polynomial on `[2, N]` with `J` vanishing logarithmic
moments at `s₀`: `|A(s₀ + w)| ≤ m (|w| log N)^J e^{|w| log N}/J!`, `m = Σ|c_n n^{−s₀}|`. -/
theorem norm_dpoly_le_flat {S : Finset ℕ} {N : ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n) (hSN : ∀ n ∈ S, n ≤ N)
    {c : ℕ → ℂ} {s₀ : ℂ} {J : ℕ} (hmom : ∀ j < J, logMoment S c s₀ j = 0) (w : ℂ) :
    ‖dpoly S c (s₀ + w)‖ ≤ (∑ n ∈ S, ‖c n * (n : ℂ) ^ (-s₀)‖) *
      ((‖w‖ * Real.log N) ^ J / (J.factorial : ℝ) * Real.exp (‖w‖ * Real.log N)) := by
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn => by have := hS2 n hn; omega
  refine (norm_dpoly_le_expTail hS0 hmom w).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := hS2 n hn; omega)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast hSN n hn)
  have hx : ‖w‖ * Real.log n ≤ ‖w‖ * Real.log N := mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
  refine (exp_sub_sum_le (by positivity) J).trans ?_
  gcongr

/-- **The precision cost of a Rouché copy.** If at one point `|w| = r` the freezing error bound at
precision `δ` is below `|A(s₀ + w)|`, then `δ J! < (r log N)^J e^{2r log N}`. -/
theorem factorial_mul_lt_of_rouche {S : Finset ℕ} {N : ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n)
    (hSN : ∀ n ∈ S, n ≤ N) {c : ℕ → ℂ} {s₀ : ℂ} {J : ℕ}
    (hmom : ∀ j < J, logMoment S c s₀ j = 0) {δ : ℝ} (hδ : 0 ≤ δ) {w : ℂ}
    (hcopy : δ * ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-(s₀ + w))‖ * n.primeFactorsList.length <
      ‖dpoly S c (s₀ + w)‖) :
    δ * J.factorial < (‖w‖ * Real.log N) ^ J * Real.exp (2 * (‖w‖ * Real.log N)) := by
  set m := ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-s₀)‖ with hm
  set L := ‖w‖ * Real.log N with hL
  have hflat := norm_dpoly_le_flat hS2 hSN hmom w
  rw [← hm, ← hL] at hflat
  -- the freezing error bound is at least `δ m e^{−L}`
  have hmass : m * Real.exp (-L) ≤
      ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-(s₀ + w))‖ * n.primeFactorsList.length := by
    rw [hm, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 := hS2 n hn
    have hnpos : 0 < n := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hΩ : (1 : ℝ) ≤ n.primeFactorsList.length := by
      have : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 (by omega)
      exact_mod_cast List.length_pos_of_ne_nil this
    have hsplit : ‖c n * (n : ℂ) ^ (-(s₀ + w))‖ =
        ‖c n * (n : ℂ) ^ (-s₀)‖ * (n : ℝ) ^ (-w).re := by
      rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hnpos.ne'), ← mul_assoc, norm_mul,
        Complex.norm_natCast_cpow_of_pos hnpos]
    have hpow : Real.exp (-L) ≤ (n : ℝ) ^ (-w).re := by
      rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, hL]
      have hre : -‖w‖ ≤ (-w).re := by
        rw [Complex.neg_re]; linarith [Complex.re_le_norm w]
      have hlog : Real.log n ≤ Real.log N :=
        Real.log_le_log (by linarith) (by exact_mod_cast hSN n hn)
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
      nlinarith [norm_nonneg w]
    rw [hsplit]
    have h0 := norm_nonneg (c n * (n : ℂ) ^ (-s₀))
    calc ‖c n * (n : ℂ) ^ (-s₀)‖ * Real.exp (-L)
        ≤ ‖c n * (n : ℂ) ^ (-s₀)‖ * (n : ℝ) ^ (-w).re := mul_le_mul_of_nonneg_left hpow h0
      _ ≤ ‖c n * (n : ℂ) ^ (-s₀)‖ * (n : ℝ) ^ (-w).re * n.primeFactorsList.length :=
          le_mul_of_one_le_right (by positivity) hΩ
  have hchain : δ * (m * Real.exp (-L)) < m * (L ^ J / (J.factorial : ℝ) * Real.exp L) :=
    (mul_le_mul_of_nonneg_left hmass hδ).trans_lt (hcopy.trans_le hflat)
  have hm0 : 0 < m := by
    by_contra h
    push Not at h
    have hm0' : m = 0 := le_antisymm h (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    rw [hm0'] at hchain
    simp at hchain
  have hfac : (0 : ℝ) < J.factorial := by exact_mod_cast Nat.factorial_pos J
  have he : Real.exp (-L) * Real.exp (2 * L) = Real.exp L := by
    rw [← Real.exp_add]; ring_nf
  have key : δ * J.factorial * (m * Real.exp (-L)) <
      L ^ J * Real.exp (2 * L) * (m * Real.exp (-L)) := by
    calc δ * J.factorial * (m * Real.exp (-L)) = J.factorial * (δ * (m * Real.exp (-L))) := by
          ring
      _ < J.factorial * (m * (L ^ J / (J.factorial : ℝ) * Real.exp L)) :=
          mul_lt_mul_of_pos_left hchain hfac
      _ = L ^ J * Real.exp (2 * L) * (m * Real.exp (-L)) := by
          rw [← he]; field_simp
  exact lt_of_mul_lt_mul_right key (by positivity)

/-- `(J/e)^J ≤ J!`. -/
theorem pow_div_exp_le_factorial (J : ℕ) : ((J : ℝ) / Real.exp 1) ^ J ≤ J.factorial := by
  have h := Real.pow_div_factorial_le_exp (J : ℝ) (Nat.cast_nonneg J) J
  have hfac : (0 : ℝ) < J.factorial := by exact_mod_cast Nat.factorial_pos J
  rw [div_le_iff₀ hfac] at h
  rw [div_pow, ← Real.exp_nat_mul, mul_one, div_le_iff₀ (Real.exp_pos _)]
  linarith [mul_comm (Real.exp (J : ℝ)) (J.factorial : ℝ)]

/-- **The order of a copyable zero.** If a Rouché copy at precision `0 < δ ≤ 1` is possible on the
circle `|w| = r`, the order satisfies `J ≤ e² r log N + log(1/δ)`. -/
theorem order_le_of_rouche {S : Finset ℕ} {N : ℕ} (hS2 : ∀ n ∈ S, 2 ≤ n)
    (hSN : ∀ n ∈ S, n ≤ N) {c : ℕ → ℂ} {s₀ : ℂ} {J : ℕ}
    (hmom : ∀ j < J, logMoment S c s₀ j = 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {w : ℂ}
    (hcopy : δ * ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-(s₀ + w))‖ * n.primeFactorsList.length <
      ‖dpoly S c (s₀ + w)‖) :
    (J : ℝ) ≤ Real.exp 2 * (‖w‖ * Real.log N) + Real.log (1 / δ) := by
  have h := factorial_mul_lt_of_rouche hS2 hSN hmom hδ0.le hcopy
  set L := ‖w‖ * Real.log N with hL
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hL, hN, Nat.cast_zero, Real.log_zero, mul_zero]
    · exact mul_nonneg (norm_nonneg _) (Real.log_natCast_nonneg N)
  have hlogδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  by_contra hgt
  push Not at hgt
  have hJL : Real.exp 2 * L < J := by linarith
  have hJpos : (0 : ℝ) < J := lt_of_le_of_lt (by positivity) hJL
  -- `(J/e)^J ≤ J!` and `L ≤ J/e²` give `δ e^J < e^{2L}`
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hLJ : L ≤ (J : ℝ) / Real.exp 2 := by
    rw [le_div_iff₀ (Real.exp_pos 2)]; linarith
  have h1 : δ * ((J : ℝ) / Real.exp 1) ^ J ≤ δ * J.factorial :=
    mul_le_mul_of_nonneg_left (pow_div_exp_le_factorial J) hδ0.le
  have h2 : L ^ J * Real.exp (2 * L) ≤ ((J : ℝ) / Real.exp 2) ^ J * Real.exp (2 * L) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0 hLJ J) (Real.exp_pos _).le
  have h3 : δ * ((J : ℝ) / Real.exp 1) ^ J < ((J : ℝ) / Real.exp 2) ^ J * Real.exp (2 * L) :=
    (h1.trans_lt h).trans_le h2
  -- divide by `(J/e²)^J`: `δ e^J < e^{2L}`
  have hratio : ((J : ℝ) / Real.exp 1) ^ J = ((J : ℝ) / Real.exp 2) ^ J * Real.exp J := by
    have hJexp : Real.exp (J : ℝ) = Real.exp 1 ^ J := by rw [← Real.exp_nat_mul, mul_one]
    rw [hJexp, he2, div_pow, div_pow, mul_pow]
    field_simp
  rw [hratio] at h3
  have hq : 0 < ((J : ℝ) / Real.exp 2) ^ J := pow_pos (div_pos hJpos (Real.exp_pos 2)) J
  have h4 : δ * Real.exp J < Real.exp (2 * L) := by
    have := h3
    rw [show δ * (((J : ℝ) / Real.exp 2) ^ J * Real.exp J) =
      ((J : ℝ) / Real.exp 2) ^ J * (δ * Real.exp J) by ring] at this
    exact lt_of_mul_lt_mul_left this hq.le
  -- take logarithms: `log δ + J < 2L`
  have h5 : Real.log δ + J < 2 * L := by
    have := Real.log_lt_log (by positivity) h4
    rwa [Real.log_mul hδ0.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
  have h6 : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  have h7 : 2 * L ≤ Real.exp 2 * L := by
    have : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2; linarith
    nlinarith
  linarith

end GaloisForLFunctions.InfiniteRankWeilTheory
