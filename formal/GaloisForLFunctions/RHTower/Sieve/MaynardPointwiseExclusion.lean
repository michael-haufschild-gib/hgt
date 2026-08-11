import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicPointwise
import GaloisForLFunctions.RHTower.Sieve.MaynardWeakLargeValues

/-!
# Pointwise exclusion of near-maximal Heath--Brown factors

Maynard labels a dyadic factor of length `N` by an exponent `α` when its value is at least
`N^(-c+α)`.  A pointwise saving

`|S(c+it)| ≤ C N^(1-c) N^(-δ)`

therefore forces

`α ≤ 1-δ + log C/log N`.

This file proves that implication, instantiates it for the exact zeta and logarithm blocks of the
finite Heath--Brown packet, and proves the global aggregation law: one factor of relative length
at least `x^λ` with exponent deficit `Δ` forces the product exponent to be at most `1-λΔ`.

Together these statements formalize the power bookkeeping in Maynard's near-one derivative-test
case without importing a large-values theorem.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction
open scoped zeta

/-- A pointwise power saving becomes an explicit ceiling for the large-value exponent. -/
theorem exponent_le_of_pointwise_power_saving
    {N c α C δ V : ℝ} (hN : 1 < N) (hC : 0 < C)
    (hlower : N ^ (-c + α) ≤ V)
    (hupper : V ≤ C * N ^ (1 - c) * N ^ (-δ)) :
    α ≤ 1 - δ + Real.log C / Real.log N := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hleft0 : 0 < N ^ (-c + α) := Real.rpow_pos_of_pos hN0 _
  have hright0 : 0 < C * N ^ (1 - c) * N ^ (-δ) := by positivity
  have hle : N ^ (-c + α) ≤ C * N ^ (1 - c) * N ^ (-δ) :=
    hlower.trans hupper
  have hlogs := Real.log_le_log hleft0 hle
  have hcollapse : N ^ (1 - c) * N ^ (-δ) = N ^ (1 - c - δ) := by
    rw [← Real.rpow_add hN0]
    congr 1
  have hrightcollapse : C * N ^ (1 - c) * N ^ (-δ) = C * N ^ (1 - c - δ) := by
    rw [mul_assoc, hcollapse]
  rw [hrightcollapse, Real.log_rpow hN0, Real.log_mul hC.ne'
    (ne_of_gt (Real.rpow_pos_of_pos hN0 _)), Real.log_rpow hN0] at hlogs
  have hdiv : α - (1 - δ) ≤ Real.log C / Real.log N := by
    rw [le_div_iff₀ hlogN]
    nlinarith [hlogs]
  linarith

/-- Once the harmless constant is absorbed by half the power saving, a genuine fixed deficit
remains. -/
theorem exponent_le_one_sub_half_of_pointwise_power_saving
    {N c α C δ V : ℝ} (hN : 1 < N) (hC : 1 ≤ C)
    (hsize : 2 * Real.log C ≤ δ * Real.log N)
    (hlower : N ^ (-c + α) ≤ V)
    (hupper : V ≤ C * N ^ (1 - c) * N ^ (-δ)) :
    α ≤ 1 - δ / 2 := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hbase := exponent_le_of_pointwise_power_saving hN hC0 hlower hupper
  have hlogC : Real.log C / Real.log N ≤ δ / 2 := by
    rw [div_le_iff₀ hlogN]
    nlinarith
  linarith

/-- A large zeta block in the derivative-test window has an explicit exponent ceiling. -/
theorem zetaDyadicBlock_largeValue_exponent_le
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X) (hq1 : 1 ≤ q)
    {c t α : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hlarge : ((2 ^ q : ℕ) : ℝ) ^ (-c + α) ≤
      ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((c : ℂ) + (t : ℂ) * Complex.I)‖) :
    α ≤ 1 - 1 / (3 * (2 : ℝ) ^ k₀) +
      Real.log 2560 / Real.log (((2 ^ q : ℕ) : ℝ)) := by
  have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq1)
  exact exponent_le_of_pointwise_power_saving hN (by norm_num) hlarge
    (norm_LSeries_zetaDyadicBlock_le hX hq hc ht hk₀ hfac hlow hhigh)

/-- A large logarithm block has the same power deficit; its coefficient costs only the displayed
logarithmic constant. -/
theorem logDyadicBlock_largeValue_exponent_le
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X) (hq1 : 1 ≤ q)
    {c t α : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hlarge : ((2 ^ q : ℕ) : ℝ) ^ (-c + α) ≤
      ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((c : ℂ) + (t : ℂ) * Complex.I)‖) :
    α ≤ 1 - 1 / (3 * (2 : ℝ) ^ k₀) +
      Real.log (5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ)) /
        Real.log (((2 ^ q : ℕ) : ℝ)) := by
  have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq1)
  have htop : 2 ≤ heathBrownDyadicFactorTop X q := by
    have hpow : 2 ≤ 2 ^ q := by
      calc
        2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq1
    exact hpow.trans (pow_le_heathBrownDyadicFactorTop hX hq)
  have hC : 0 < 5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ) := by
    have : 0 < Real.log (heathBrownDyadicFactorTop X q : ℝ) :=
      Real.log_pos (by exact_mod_cast htop)
    positivity
  refine exponent_le_of_pointwise_power_saving hN hC hlarge ?_
  convert norm_LSeries_logDyadicBlock_le hX hq hc ht hk₀ hfac hlow hhigh using 1 <;> ring

/-- **One-factor deficit aggregation.**  If `x=NM`, the complementary factor is no larger than
its trivial exponent, and `N` occupies at least the relative length `x^λ`, then a deficit `Δ` on
the first factor forces a global deficit `λΔ`. -/
theorem maynard_one_factor_deficit
    {x N M σ α β ell Δ : ℝ}
    (hx : 1 < x) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hΔ : 0 ≤ Δ) (hprod : x = N * M)
    (hscale : x ^ σ = N ^ α * M ^ β)
    (hlength : x ^ ell ≤ N) (hα : α ≤ 1 - Δ) (hβ : β ≤ 1) :
    σ ≤ 1 - ell * Δ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogs : σ * Real.log x = α * Real.log N + β * Real.log M := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hN0,
      Real.rpow_def_of_pos hM0, ← Real.exp_add] at hscale
    have h := Real.exp_injective hscale
    nlinarith
  have hlogprod : Real.log x = Real.log N + Real.log M := by
    rw [hprod, Real.log_mul hN0.ne' hM0.ne']
  have hloglength : ell * Real.log x ≤ Real.log N := by
    have hpow0 : 0 < x ^ ell := Real.rpow_pos_of_pos hx0 _
    have h := Real.log_le_log hpow0 hlength
    rwa [Real.log_rpow hx0] at h
  have hweighted : α * Real.log N + β * Real.log M
      ≤ (1 - Δ) * Real.log N + Real.log M := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right hα hlogN)
      (by simpa using mul_le_mul_of_nonneg_right hβ hlogM)
  have hdeficit : Δ * (ell * Real.log x) ≤ Δ * Real.log N :=
    mul_le_mul_of_nonneg_left hloglength hΔ
  have hgoal : σ * Real.log x ≤ (1 - ell * Δ) * Real.log x := by
    calc
      σ * Real.log x = α * Real.log N + β * Real.log M := hlogs
      _ ≤ (1 - Δ) * Real.log N + Real.log M := hweighted
      _ = Real.log N + Real.log M - Δ * Real.log N := by ring
      _ ≤ Real.log N + Real.log M - Δ * (ell * Real.log x) :=
        sub_le_sub_left hdeficit _
      _ = (1 - ell * Δ) * Real.log x := by rw [hlogprod]; ring
  exact le_of_mul_le_mul_right hgoal hlogx

/-- Contrapositive form used by the large-value classification: a product exponent above
`1-λΔ` excludes every factor satisfying the stated length and deficit conditions. -/
theorem maynard_no_long_deficient_factor
    {x N M σ α β ell Δ : ℝ}
    (hx : 1 < x) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hΔ : 0 ≤ Δ) (hprod : x = N * M)
    (hscale : x ^ σ = N ^ α * M ^ β)
    (hlength : x ^ ell ≤ N) (hβ : β ≤ 1)
    (hσ : 1 - ell * Δ < σ) :
    ¬ α ≤ 1 - Δ := by
  intro hα
  exact (not_le_of_gt hσ)
    (maynard_one_factor_deficit hx hN hM hΔ hprod hscale hlength hα hβ)

/-- **Concrete global exclusion from one long zeta factor.**  After the constant `2560` is
absorbed, the exact derivative-test saving on that factor propagates to the full product exponent. -/
theorem maynard_global_deficit_of_long_zetaDyadicBlock
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X) (hq1 : 1 ≤ q)
    {x M c t α β σ ell : ℝ} (hx : 1 < x) (hM : 1 ≤ M)
    (hc : 0 ≤ c) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hsize : 2 * Real.log 2560 ≤
      (1 / (3 * (2 : ℝ) ^ k₀)) * Real.log (((2 ^ q : ℕ) : ℝ)))
    (hprod : x = (((2 ^ q : ℕ) : ℝ)) * M)
    (hscale : x ^ σ = (((2 ^ q : ℕ) : ℝ)) ^ α * M ^ β)
    (hlength : x ^ ell ≤ (((2 ^ q : ℕ) : ℝ))) (hβ : β ≤ 1)
    (hlarge : ((2 ^ q : ℕ) : ℝ) ^ (-c + α) ≤
      ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
        ((c : ℂ) + (t : ℂ) * Complex.I)‖) :
    σ ≤ 1 - ell * (1 / (3 * (2 : ℝ) ^ k₀) / 2) := by
  have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq1)
  have hα : α ≤ 1 - (1 / (3 * (2 : ℝ) ^ k₀)) / 2 :=
    exponent_le_one_sub_half_of_pointwise_power_saving hN (by norm_num) hsize hlarge
      (norm_LSeries_zetaDyadicBlock_le hX hq hc ht hk₀ hfac hlow hhigh)
  exact maynard_one_factor_deficit hx hN.le hM (by positivity) hprod hscale hlength hα hβ

/-- Concrete global exclusion from one long logarithm factor.  Increasing-weight Abel summation
shows that its only extra cost is `5120 log M_q`, absorbed explicitly by `hsize`. -/
theorem maynard_global_deficit_of_long_logDyadicBlock
    {X q k₀ : ℕ} (hX : 1 ≤ X) (hq : q ≤ Nat.log 2 X) (hq1 : 1 ≤ q)
    {x M c t α β σ ell : ℝ} (hx : 1 < x) (hM : 1 ≤ M)
    (hc : 0 ≤ c) (ht : 0 < t) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ 2 ^ q)
    (hlow : 8 * Real.pi * ((2 ^ q : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * ((2 ^ q : ℕ) : ℝ) ^ (k₀ - 1) *
      ((2 ^ q : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hsize : 2 * Real.log
        (5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ)) ≤
      (1 / (3 * (2 : ℝ) ^ k₀)) * Real.log (((2 ^ q : ℕ) : ℝ)))
    (hprod : x = (((2 ^ q : ℕ) : ℝ)) * M)
    (hscale : x ^ σ = (((2 ^ q : ℕ) : ℝ)) ^ α * M ^ β)
    (hlength : x ^ ell ≤ (((2 ^ q : ℕ) : ℝ))) (hβ : β ≤ 1)
    (hlarge : ((2 ^ q : ℕ) : ℝ) ^ (-c + α) ≤
      ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((c : ℂ) + (t : ℂ) * Complex.I)‖) :
    σ ≤ 1 - ell * (1 / (3 * (2 : ℝ) ^ k₀) / 2) := by
  have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq1)
  have htop : 2 ≤ heathBrownDyadicFactorTop X q := by
    have hpow : 2 ≤ 2 ^ q := by
      calc
        2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq1
    exact hpow.trans (pow_le_heathBrownDyadicFactorTop hX hq)
  have hC : 1 ≤ 5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ) := by
    have hlog : Real.log 2 ≤ Real.log (heathBrownDyadicFactorTop X q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast htop)
    have hlog2 := Real.log_two_gt_d9
    nlinarith
  have hupper := norm_LSeries_logDyadicBlock_le hX hq hc ht hk₀ hfac hlow hhigh
  have hupper' : ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
        ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ)) *
        ((2 ^ q : ℕ) : ℝ) ^ (1 - c) *
          ((2 ^ q : ℕ) : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    convert hupper using 1 <;> ring
  have hα : α ≤ 1 - (1 / (3 * (2 : ℝ) ^ k₀)) / 2 :=
    exponent_le_one_sub_half_of_pointwise_power_saving hN hC hsize hlarge hupper'
  exact maynard_one_factor_deficit hx hN.le hM (by positivity) hprod hscale hlength hα hβ

end RHTower.Sieve
