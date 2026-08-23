import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorHalfIntegerBound
import GaloisForLFunctions.RHTower.Sieve.ShiftedPolylogTransfer
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# `RH ⟹ ψ(x) − x = O(x^{1/2+ε})`

The closed-form bound at a half-integer cutoff carries a shifted power and two logarithms; both
are absorbed by any larger power, so the Chebyshev error is subpower above the square root.  The
statement is then transferred from the natural-number cutoff to the real-variable `ψ`.
-/

namespace RHTower.Sieve

open Filter Asymptotics ArithmeticFunction

noncomputable section

/-- A shifted power times a power of `1 + log` is dominated by any larger power. -/
theorem isBigO_shift_rpow_one_add_log {a b : ℝ} (hab : a < b) (hb : 0 ≤ b) (k : ℕ) :
    (fun N : ℕ => ((N : ℝ) + 1 / 2) ^ a * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ k)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ b := by
  refine Asymptotics.IsBigO.trans ?_ (isBigO_shift_rpow_log hab hb k)
  refine Asymptotics.IsBigO.of_bound (2 ^ k) ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) := by
    have hexp : Real.exp 1 ≤ (N : ℝ) + 1 / 2 := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hxa : (0 : ℝ) < ((N : ℝ) + 1 / 2) ^ a := Real.rpow_pos_of_pos (by linarith) a
  have hL : (1 + Real.log ((N : ℝ) + 1 / 2)) ^ k
      ≤ 2 ^ k * (Real.log ((N : ℝ) + 1 / 2)) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) k
  have hLnn : (0 : ℝ) ≤ (1 + Real.log ((N : ℝ) + 1 / 2)) ^ k := by positivity
  have hLnn' : (0 : ℝ) ≤ (Real.log ((N : ℝ) + 1 / 2)) ^ k := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((N : ℝ) + 1 / 2) ^ a
      * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ k),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((N : ℝ) + 1 / 2) ^ a
      * (Real.log ((N : ℝ) + 1 / 2)) ^ k)]
  nlinarith [mul_le_mul_of_nonneg_left hL hxa.le]

/-- **The Chebyshev error is subpower above the square root, under RH.** -/
theorem chebyshev_error_isBigO_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ))
      =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Cst, hCst0, hCst⟩ := exists_chebyshev_error_halfInt_bound hRH
    (ε := min ε (1 / 4)) (lt_min hε (by norm_num)) (min_le_right _ _)
  have hmin : min ε (1 / 4) ≤ ε := min_le_left _ _
  have hmin0 : (0 : ℝ) < min ε (1 / 4) := lt_min hε (by norm_num)
  have hstep : (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ))
      =O[atTop] fun N : ℕ => ((N : ℝ) + 1 / 2) ^ (1 / 2 + min ε (1 / 4) / 2)
        * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
    refine Asymptotics.IsBigO.of_bound Cst ?_
    filter_upwards [eventually_ge_atTop 7] with N hN
    have hb := hCst N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((N : ℝ) + 1 / 2) ^ (1 / 2 + min ε (1 / 4) / 2)
        * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2)]
    exact hb
  refine hstep.trans (isBigO_shift_rpow_one_add_log ?_ (by linarith) 2)
  linarith

/-- Turning a natural-number `IsBigO` against a nonnegative power into a bound valid from `1` on. -/
theorem exists_bound_of_isBigO_natRpow {f : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : f =O[atTop] fun N : ℕ => (N : ℝ) ^ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → |f N| ≤ C * (N : ℝ) ^ b := by
  obtain ⟨c, hc0, hc⟩ := h.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨N₀, hN₀⟩ := hc
  refine ⟨c + (∑ n ∈ Finset.range N₀, |f n|) + 1, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hb
  have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ b := by linarith
  have hsum0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N₀, |f n| :=
    Finset.sum_nonneg fun n _ => abs_nonneg _
  rcases le_or_gt N₀ N with hle | hgt
  · have hb' := hN₀ N hle
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow0] at hb'
    nlinarith [hb', hpow, hsum0, hc0.le]
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.2 hgt
    have hsingle : |f N| ≤ ∑ n ∈ Finset.range N₀, |f n| :=
      Finset.single_le_sum (fun n _ => abs_nonneg (f n)) hmem
    nlinarith [hsingle, hpow, hsum0, hc0.le, abs_nonneg (f N)]

/-- **`RH ⟹ |ψ(N) − N| ≤ C N^{1/2+ε}` for every `N ≥ 1`.** -/
theorem exists_chebyshev_error_power_bound (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)| ≤ C * (N : ℝ) ^ (1 / 2 + ε) :=
  exists_bound_of_isBigO_natRpow (by linarith)
    (chebyshev_error_isBigO_of_riemannHypothesis hRH hε)

/-- **`RH ⟹ |ψ(t) − t| ≤ C t^{1/2+ε}` for every real `t ≥ 1`.** -/
theorem exists_chebyshevPsiReal_error_power_bound (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |chebyshevPsiReal t - t| ≤ C * t ^ (1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshev_error_power_bound hRH hε
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hfl : 1 ≤ ⌊t⌋₊ := Nat.one_le_floor_iff t |>.2 ht
  have hflle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hfllt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hfl1 : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfl
  have hpsi : chebyshevPsiReal t = ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Λ n : ℝ) := by
    rw [chebyshevPsiReal_eq_sum_range, sum_range_succ_vonMangoldt_eq_sum_Icc]
  have hb := hC ⌊t⌋₊ hfl
  have hmono : ((⌊t⌋₊ : ℕ) : ℝ) ^ (1 / 2 + ε) ≤ t ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow (by linarith) hflle (by linarith)
  have hone : (1 : ℝ) ≤ t ^ (1 / 2 + ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht (show (0:ℝ) ≤ 1 / 2 + ε by linarith)
  have htri : |chebyshevPsiReal t - t|
      ≤ |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Λ n : ℝ)) - ((⌊t⌋₊ : ℕ) : ℝ)|
        + |((⌊t⌋₊ : ℕ) : ℝ) - t| := by
    rw [hpsi]
    exact abs_sub_le _ _ _
  have hgap : |((⌊t⌋₊ : ℕ) : ℝ) - t| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  nlinarith [htri, hb, hgap, hmono, hone, hC0]

end

end RHTower.Sieve
