import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeScaledBound
import GaloisForLFunctions.RHTower.Sieve.ScaledEnvelopeEstimate
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowPaperScale

/-!
# Twisted sums over short prime blocks at the Matomäki–Teräväinen scale

For primes in `(Q, Q(1+δ)]` with `z₀ = exp(log X/(log log X)³) ≤ Q ≤ X` and a frequency
`exp(c√log X) ≤ |t| ≤ 4X`, the sum `∑ p^{-1-it}` is at most `exp(-(log X)^{1/30})`.  The input is
the Route-T twisted prime estimate at a free smoothing width `D = exp((log X)^{1/25})`: its
zero-free width `≫ (log X)^{-9/10}(log log X)^{-2}` against `log Q ≥ log X/(log log X)³` gives the
saving `exp(-c(log X)^{2/25})`.
-/

namespace RHTower.Sieve

open Filter Topology Complex

noncomputable section

/-- **Exponential dominance.**  For `α < β`, `0 < β`, `b > 0`:
`C L^k exp(a L^α) ≤ exp(b L^β)` for all large `L`. -/
theorem eventually_mul_pow_mul_exp_rpow_le_exp_rpow {α β a b C : ℝ} (k : ℕ) (hαβ : α < β)
    (hβ : 0 < β) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, C * L ^ k * Real.exp (a * L ^ α) ≤ Real.exp (b * L ^ β) := by
  have hLβ : Tendsto (fun L : ℝ => L ^ β) atTop atTop := tendsto_rpow_atTop hβ
  have h1 : ∀ᶠ L : ℝ in atTop, Real.log (max C 1) ≤ b / 3 * L ^ β :=
    (hLβ.const_mul_atTop (by positivity)).eventually_ge_atTop _
  have hlo := isLittleO_log_rpow_atTop hβ
  have h2 : ∀ᶠ L : ℝ in atTop, (k : ℝ) * Real.log L ≤ b / 3 * L ^ β := by
    have hc : (0 : ℝ) < b / (3 * ((k : ℝ) + 1)) := by positivity
    filter_upwards [hlo.bound hc, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hLb : 0 ≤ L ^ β := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hLb] at hL
    have hk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    calc (k : ℝ) * Real.log L ≤ ((k : ℝ) + 1) * (b / (3 * ((k : ℝ) + 1)) * L ^ β) :=
          mul_le_mul hk hL hlog (by positivity)
      _ = b / 3 * L ^ β := by field_simp
  have h3 : ∀ᶠ L : ℝ in atTop, a * L ^ α ≤ b / 3 * L ^ β := by
    have hgap : Tendsto (fun L : ℝ => L ^ (β - α)) atTop atTop := tendsto_rpow_atTop (by linarith)
    filter_upwards [hgap.eventually_ge_atTop (3 * |a| / b), eventually_gt_atTop (0 : ℝ)]
      with L hL hL0
    have hsplit : L ^ β = L ^ (β - α) * L ^ α := by
      rw [← Real.rpow_add hL0]; ring_nf
    have hLα : 0 < L ^ α := Real.rpow_pos_of_pos hL0 _
    rw [hsplit]
    calc a * L ^ α ≤ |a| * L ^ α := mul_le_mul_of_nonneg_right (le_abs_self a) hLα.le
      _ = b / 3 * (3 * |a| / b) * L ^ α := by field_simp
      _ ≤ b / 3 * (L ^ (β - α) * L ^ α) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity))
            hLα.le
  filter_upwards [h1, h2, h3, eventually_gt_atTop (0 : ℝ)] with L h1 h2 h3 hL0
  have hC : C ≤ max C 1 := le_max_left _ _
  have hC1 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLk : 0 ≤ L ^ k := by positivity
  calc C * L ^ k * Real.exp (a * L ^ α) ≤ max C 1 * L ^ k * Real.exp (a * L ^ α) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hLk) (Real.exp_pos _).le
    _ = Real.exp (Real.log (max C 1) + (k : ℝ) * Real.log L + a * L ^ α) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hC1, ← Real.rpow_natCast,
          Real.rpow_def_of_pos hL0]
        ring_nf
    _ ≤ Real.exp (b * L ^ β) := Real.exp_le_exp.2 (by linarith)

/-- The twisted harmonic prime sum is the negative of Menon's harmonic prime polynomial at
`w = -t/(2π)`. -/
theorem sum_prime_cpow_eq_neg_harmonicPrimeBlockPoly {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime)
    (t : ℝ) :
    ∑ p ∈ B, (p : ℂ) ^ (-(1 + (t : ℂ) * Complex.I)) = -harmonicPrimeBlockPoly B (-t / (2 * Real.pi)) := by
  unfold harmonicPrimeBlockPoly
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := hB p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  unfold harmonicMoebiusPhase moebiusPhase unitLogPhase
  rw [ArithmeticFunction.moebius_apply_prime hpp, Complex.cpow_def_of_ne_zero hp0, hlog]
  have hexp : Complex.exp (((Real.log p : ℝ) : ℂ)) = (p : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hpr, Complex.ofReal_natCast]
  have hsplit : ((Real.log p : ℝ) : ℂ) * (-(1 + (t : ℂ) * Complex.I)) =
      -((Real.log p : ℝ) : ℂ) + ((2 * Real.pi * (-t / (2 * Real.pi) * Real.log p) : ℝ) : ℂ) * Complex.I := by
    push_cast; field_simp; ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, hexp]
  push_cast
  field_simp

/-- The seven terms bounding a short prime block twist, as functions of `L = log X`. -/
def primeBlockTwistMajorant (c Ctot CA L : ℝ) : ℝ :=
  12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25)) * (4 * L ^ 2 * Real.exp (-(c * L ^ ((1 : ℝ) / 2))))
      / (2 * Real.pi)
    + 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25)) * (2 * Real.exp (-(c * L ^ ((1 : ℝ) / 2))))
      / (2 * Real.pi)
    + 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25))
        * (60 * CA * L ^ 3 * Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25)))) / (2 * Real.pi)
    + 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25))
        * (60 * CA * L ^ 3 * Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2)))) / (2 * Real.pi)
    + 24 * L * Real.exp (-(L ^ ((1 : ℝ) / 25)))
    + 48 * (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100)))
    + 84 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100)))

/-- One term `C L^k exp(a L^α - b L^β)`, `α < β`, is eventually `≤ exp(-L^{1/30})/7`. -/
theorem eventually_term_le_exp_neg_rpow {α β a b C : ℝ} (k : ℕ) (hα : (1 : ℝ) / 30 ≤ α)
    (hαβ : α < β) (hβ : 0 < β) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) ≤
      Real.exp (-(L ^ ((1 : ℝ) / 30))) / 8 := by
  filter_upwards [eventually_mul_pow_mul_exp_rpow_le_exp_rpow (C := 8 * C) (a := a + 1) k hαβ hβ hb,
    eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hL0 : 0 < L := by linarith
  have h30 : L ^ ((1 : ℝ) / 30) ≤ L ^ α := Real.rpow_le_rpow_of_exponent_le hL1 hα
  have hexp : Real.exp (a * L ^ α) * Real.exp (L ^ ((1 : ℝ) / 30)) ≤ Real.exp ((a + 1) * L ^ α) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hpos : 0 < Real.exp (L ^ ((1 : ℝ) / 30)) := Real.exp_pos _
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have key : C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) * 8 *
      Real.exp (L ^ ((1 : ℝ) / 30)) ≤ 1 := by
    have h1 : 8 * C * L ^ k * Real.exp ((a + 1) * L ^ α) * Real.exp (-(b * L ^ β)) ≤ 1 := by
      calc 8 * C * L ^ k * Real.exp ((a + 1) * L ^ α) * Real.exp (-(b * L ^ β))
          ≤ Real.exp (b * L ^ β) * Real.exp (-(b * L ^ β)) :=
            mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rcases le_or_gt 0 C with hC | hC
    · calc C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) * 8 *
            Real.exp (L ^ ((1 : ℝ) / 30))
          = 8 * C * L ^ k * (Real.exp (a * L ^ α) * Real.exp (L ^ ((1 : ℝ) / 30))) *
            Real.exp (-(b * L ^ β)) := by ring
        _ ≤ 8 * C * L ^ k * Real.exp ((a + 1) * L ^ α) * Real.exp (-(b * L ^ β)) := by
            gcongr
        _ ≤ 1 := h1
    · have : C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) * 8 *
          Real.exp (L ^ ((1 : ℝ) / 30)) ≤ 0 := by
        have hLk : 0 ≤ L ^ k := by positivity
        have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC.le hLk)
          (Real.exp_pos (a * L ^ α)).le
        have h2 := mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos (-(b * L ^ β))).le
        have h3 := mul_nonpos_of_nonpos_of_nonneg h2 (by norm_num : (0 : ℝ) ≤ 8)
        exact mul_nonpos_of_nonpos_of_nonneg h3 hpos.le
      linarith
  calc C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) * 8
      = C * L ^ k * Real.exp (a * L ^ α) * Real.exp (-(b * L ^ β)) * 8 *
          Real.exp (L ^ ((1 : ℝ) / 30)) * Real.exp (-(L ^ ((1 : ℝ) / 30))) := by
        rw [mul_assoc _ (Real.exp (L ^ ((1 : ℝ) / 30))), ← Real.exp_add]; simp
    _ ≤ 1 * Real.exp (-(L ^ ((1 : ℝ) / 30))) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = Real.exp (-(L ^ ((1 : ℝ) / 30))) := one_mul _

/-- The majorant is eventually at most `exp(-L^{1/30})`. -/
theorem eventually_primeBlockTwistMajorant_le {c Ctot CA : ℝ} (hc : 0 < c) (hCA : 0 < CA) :
    ∀ᶠ L : ℝ in atTop, primeBlockTwistMajorant c Ctot CA L ≤ Real.exp (-(L ^ ((1 : ℝ) / 30))) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have e1 := eventually_term_le_exp_neg_rpow (C := 12 * Ctot * 4 / (2 * Real.pi)) 2
    (α := 1 / 25) (β := 1 / 2) (a := 2) (b := c) (by norm_num) (by norm_num) (by norm_num) hc
  have e2 := eventually_term_le_exp_neg_rpow (C := 12 * Ctot * 2 / (2 * Real.pi)) 0
    (α := 1 / 25) (β := 1 / 2) (a := 2) (b := c) (by norm_num) (by norm_num) (by norm_num) hc
  have e3 := eventually_term_le_exp_neg_rpow (C := 12 * Ctot * (60 * CA) / (2 * Real.pi)) 3
    (α := 1 / 25) (β := 2 / 25) (a := 2) (b := 1 / (120 * CA)) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  have e4 := eventually_term_le_exp_neg_rpow (C := 12 * Ctot * (60 * CA) / (2 * Real.pi)) 3
    (α := 1 / 25) (β := 1 / 2) (a := 2) (b := 2 * c) (by norm_num) (by norm_num) (by norm_num)
    (by positivity)
  have e5 := eventually_term_le_exp_neg_rpow (C := 24) 1
    (α := 1 / 30) (β := 1 / 25) (a := 0) (b := 1) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  have e6a := eventually_term_le_exp_neg_rpow (C := 48) 1
    (α := 1 / 30) (β := 99 / 100) (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  have e6b := eventually_term_le_exp_neg_rpow (C := 48) 0
    (α := 1 / 30) (β := 99 / 100) (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  have e7 := eventually_term_le_exp_neg_rpow (C := 84 * Real.exp 9) 0
    (α := 1 / 30) (β := 99 / 100) (a := 0) (b := 1) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  filter_upwards [e1, e2, e3, e4, e5, e6a, e6b, e7] with L h1 h2 h3 h4 h5 h6a h6b h7
  simp only [pow_zero, mul_one, pow_one, zero_mul, Real.exp_zero, one_mul] at h1 h2 h3 h4 h5 h6a h6b h7
  unfold primeBlockTwistMajorant
  have r1 : 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
      (4 * L ^ 2 * Real.exp (-(c * L ^ ((1 : ℝ) / 2)))) / (2 * Real.pi) =
      12 * Ctot * 4 / (2 * Real.pi) * L ^ 2 * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
        Real.exp (-(c * L ^ ((1 : ℝ) / 2))) := by ring
  have r2 : 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
      (2 * Real.exp (-(c * L ^ ((1 : ℝ) / 2)))) / (2 * Real.pi) =
      12 * Ctot * 2 / (2 * Real.pi) * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
        Real.exp (-(c * L ^ ((1 : ℝ) / 2))) := by ring
  have r3 : 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25))
        * (60 * CA * L ^ 3 * Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25)))) /
          (2 * Real.pi) =
      12 * Ctot * (60 * CA) / (2 * Real.pi) * L ^ 3 * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
        Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25))) := by ring
  have r4 : 12 * Ctot * Real.exp (2 * L ^ ((1 : ℝ) / 25))
        * (60 * CA * L ^ 3 * Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2)))) / (2 * Real.pi) =
      12 * Ctot * (60 * CA) / (2 * Real.pi) * L ^ 3 * Real.exp (2 * L ^ ((1 : ℝ) / 25)) *
        Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2))) := by ring
  have r6 : 48 * (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) =
      48 * L * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) +
        48 * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := by ring
  rw [r1, r2, r3, r4, r6]
  linarith

/-- The Route-T width surrogate at heights up to `4X`, as a function of `L = log X`. -/
def primeBlockWidthLower (CA L : ℝ) : ℝ :=
  1 / (10 * CA * (3 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (3 * L)) ^ 2)

theorem primeBlockWidthLower_le {A τ X : ℝ} (hX : 60 ≤ Real.log X)
    (hτ : 16 * Real.pi / 3 ≤ |τ|) (hτX : |τ| ≤ 4 * X) :
    primeBlockWidthLower (routeTZeroFreeDeltaEnvelopeConstant A) (Real.log X) ≤
      routeTWidthPolylogLower A τ := by
  have hX0 : 0 < X := by
    have : 0 < 16 * Real.pi / 3 := by positivity
    linarith
  have hX1 : 1 ≤ X := ((Real.log_pos_iff hX0.le).1 (by linarith)).le
  set E : ℝ := routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) with hE
  have hE1 : 1 ≤ E := routeTLogHeightEnvelope_one_le (by positivity)
  have hE3 : E ≤ 3 * Real.log X := by
    rw [hE, routeTLogHeightEnvelope]
    have h1 : 4 * (3 * |τ| / 2 + 1) + 2 ≤ 30 * X := by linarith
    have h2 : Real.log (4 * (3 * |τ| / 2 + 1) + 2) ≤ Real.log (30 * X) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hX0.ne'] at h2
    have h3 : Real.log 30 ≤ 30 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hCA := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hpow : E ^ ((9 : ℝ) / 10) ≤ (3 * Real.log X) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow (by linarith) hE3 (by norm_num)
  have hlog : (1 + Real.log E) ^ 2 ≤ (1 + Real.log (3 * Real.log X)) ^ 2 := by
    have := Real.log_le_log (by linarith) hE3
    have h0 : 0 ≤ Real.log E := Real.log_nonneg hE1
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [primeBlockWidthLower, routeTWidthPolylogLower, ← hE]
  have hEp : 0 < E ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE1
  refine one_div_le_one_div_of_le (by positivity) ?_
  have := mul_le_mul hpow hlog (by positivity) (by positivity)
  calc 10 * routeTZeroFreeDeltaEnvelopeConstant A * E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2
      = 10 * routeTZeroFreeDeltaEnvelopeConstant A * (E ^ ((9 : ℝ) / 10) * (1 + Real.log E) ^ 2) := by
        ring
    _ ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * ((3 * Real.log X) ^ ((9 : ℝ) / 10) *
          (1 + Real.log (3 * Real.log X)) ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- `1/ℓ ≤ 30 C L^{91/100}` once `(1 + log 3L)² ≤ L^{1/100}`. -/
theorem inv_primeBlockWidthLower_le {CA L : ℝ} (hCA : 0 < CA) (hL : 1 ≤ L)
    (hlog : (1 + Real.log (3 * L)) ^ 2 ≤ L ^ ((1 : ℝ) / 100)) :
    1 / primeBlockWidthLower CA L ≤ 30 * CA * L ^ ((91 : ℝ) / 100) := by
  have hL0 : 0 < L := by linarith
  rw [primeBlockWidthLower, one_div_one_div]
  have h3 : (3 * L) ^ ((9 : ℝ) / 10) ≤ 3 * L ^ ((9 : ℝ) / 10) := by
    rw [Real.mul_rpow (by norm_num) hL0.le]
    have : (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ 3 := by
      calc (3 : ℝ) ^ ((9 : ℝ) / 10) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hL0.le _)
  have hsplit : L ^ ((91 : ℝ) / 100) = L ^ ((9 : ℝ) / 10) * L ^ ((1 : ℝ) / 100) := by
    rw [← Real.rpow_add hL0]; norm_num
  rw [hsplit]
  have hlog0 : 0 ≤ (1 + Real.log (3 * L)) ^ 2 := sq_nonneg _
  calc 10 * CA * (3 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (3 * L)) ^ 2
      ≤ 10 * CA * (3 * L ^ ((9 : ℝ) / 10)) * L ^ ((1 : ℝ) / 100) := by
        gcongr
    _ = 30 * CA * (L ^ ((9 : ℝ) / 10) * L ^ ((1 : ℝ) / 100)) := by ring

/-- The eventual scalar conditions behind the short prime block bound. -/
theorem eventually_primeBlock_scalar_conditions {c Ctot CA delta τ₀ : ℝ} (hc : 0 < c)
    (hCA : 0 < CA) (hdelta : 0 < delta) :
    ∀ᶠ L : ℝ in atTop,
      primeBlockTwistMajorant c Ctot CA L ≤ Real.exp (-(L ^ ((1 : ℝ) / 30))) ∧ 60 ≤ L ∧
      (Real.log L) ^ 3 ≤ L ^ ((1 : ℝ) / 100) ∧
      (1 + Real.log (3 * L)) ^ 2 ≤ L ^ ((1 : ℝ) / 100) ∧
      primeBlockWidthLower CA L ≤ delta ∧
      max τ₀ (16 * Real.pi / 3) ≤ Real.exp (c * L ^ ((1 : ℝ) / 2)) ∧
      2 * Real.log 2 ≤ L ^ ((99 : ℝ) / 100) := by
  have hlo3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 100)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hlo2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 100)).bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  have hwidth : Tendsto (fun L : ℝ => (3 * L) ^ ((9 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_id.const_mul_atTop (by norm_num))
  have hsq : Tendsto (fun L : ℝ => Real.exp (c * L ^ ((1 : ℝ) / 2))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).const_mul_atTop hc)
  have h99 : Tendsto (fun L : ℝ => L ^ ((99 : ℝ) / 100)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_primeBlockTwistMajorant_le (Ctot := Ctot) hc hCA,
    eventually_ge_atTop (60 : ℝ), hlo3, hlo2, hwidth.eventually_ge_atTop (1 / (10 * CA * delta)),
    hsq.eventually_ge_atTop (max τ₀ (16 * Real.pi / 3)), h99.eventually_ge_atTop (2 * Real.log 2)]
    with L hmaj h60 h3 h2 hw hτ h99'
  have hL0 : 0 < L := by linarith
  have hlogL : 2 ≤ Real.log L := by
    rw [← Real.log_exp 2]
    refine Real.log_le_log (Real.exp_pos 2) ?_
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hLp : 0 ≤ L ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hL0.le _
  refine ⟨hmaj, h60, ?_, ?_, ?_, hτ, h99'⟩
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg hLp, one_mul] at h3
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h3
    exact h3
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg hLp] at h2
    have hl3 : 1 + Real.log (3 * L) ≤ 3 * Real.log L := by
      rw [Real.log_mul (by norm_num) hL0.ne']
      have : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have h2' : Real.log L ^ (2 : ℕ) ≤ 1 / 9 * L ^ ((1 : ℝ) / 100) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h2
      exact h2
    calc (1 + Real.log (3 * L)) ^ 2 ≤ (3 * Real.log L) ^ 2 :=
          pow_le_pow_left₀ (by
            have : 0 ≤ Real.log (3 * L) := Real.log_nonneg (by linarith)
            linarith) hl3 2
      _ = 9 * Real.log L ^ 2 := by ring
      _ ≤ 9 * (1 / 9 * L ^ ((1 : ℝ) / 100)) := mul_le_mul_of_nonneg_left h2' (by norm_num)
      _ = L ^ ((1 : ℝ) / 100) := by ring
  · rw [primeBlockWidthLower]
    have hlog0 : 1 ≤ (1 + Real.log (3 * L)) ^ 2 := by
      have : 0 ≤ Real.log (3 * L) := Real.log_nonneg (by linarith)
      nlinarith
    have hpos : 0 < (3 * L) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ delta * (10 * CA * (3 * L) ^ ((9 : ℝ) / 10)) := by
      rw [div_le_iff₀ (by positivity)] at hw
      linarith
    calc (1 : ℝ) ≤ delta * (10 * CA * (3 * L) ^ ((9 : ℝ) / 10)) := this
      _ ≤ delta * (10 * CA * (3 * L) ^ ((9 : ℝ) / 10) * (1 + Real.log (3 * L)) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hlog0) hdelta.le

/-- The arithmetic of the short prime block bound: twelve times the relative Route-T envelope
is dominated by the majorant's first six terms. -/
theorem twelve_relScaled_le_majorant {L c Ctot CA D T Hm em xb : ℝ} (hL : 1 ≤ L) (hc : 0 < c)
    (hCA : 0 < CA) (hCtot : 0 < Ctot)
    (hD : D = Real.exp (L ^ ((1 : ℝ) / 25))) (hT0 : 0 < T)
    (h1t : 1 / T ≤ Real.exp (-(c * L ^ ((1 : ℝ) / 2))))
    (h1t2 : 1 / T ^ 2 ≤ Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2))))
    (hHm : Hm ≤ Real.exp (-(c * L ^ ((1 : ℝ) / 2))) + 60 * CA * L ^ 3)
    (hem0 : 0 ≤ em) (hem : em ≤ Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25))))
    (hlog2 : Real.log (2 * xb) / D ≤ 2 * L * Real.exp (-(L ^ ((1 : ℝ) / 25))))
    (hsq : 2 * Real.log xb / Real.sqrt xb ≤ 3 * (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100)))) :
    12 * (Ctot * D ^ 2 * ((2 * L) ^ 2 / T + Hm * (em + 1 / T ^ 2)) / (2 * Real.pi)
        + Real.log (2 * xb) / D + 2 * Real.log xb / Real.sqrt xb)
      + 84 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) ≤
      primeBlockTwistMajorant c Ctot CA L := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hL0 : 0 < L := by linarith
  have hD2 : D ^ 2 = Real.exp (2 * L ^ ((1 : ℝ) / 25)) := by
    rw [hD, ← Real.exp_nat_mul]; norm_num
  obtain ⟨E1, hE1⟩ : ∃ E1, E1 = Real.exp (-(c * L ^ ((1 : ℝ) / 2))) := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2, E2 = Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2))) := ⟨_, rfl⟩
  obtain ⟨E3, hE3⟩ : ∃ E3, E3 = Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25))) := ⟨_, rfl⟩
  rw [← hE1] at h1t hHm
  rw [← hE2] at h1t2
  rw [← hE3] at hem
  have hE10 : 0 ≤ E1 := by rw [hE1]; exact (Real.exp_pos _).le
  have hE20 : 0 ≤ E2 := by rw [hE2]; exact (Real.exp_pos _).le
  have hE11 : E1 ≤ 1 := by
    rw [hE1, Real.exp_le_one_iff]
    have : 0 ≤ c * L ^ ((1 : ℝ) / 2) := by positivity
    linarith
  have hE21 : E2 ≤ 1 := by
    rw [hE2, Real.exp_le_one_iff]
    have : 0 ≤ 2 * c * L ^ ((1 : ℝ) / 2) := by positivity
    linarith
  have hE31 : E3 ≤ 1 := by
    rw [hE3, Real.exp_le_one_iff]
    have : 0 ≤ 1 / (120 * CA) * L ^ ((2 : ℝ) / 25) := by positivity
    linarith
  have hE30 : 0 ≤ E3 := by rw [hE3]; exact (Real.exp_pos _).le
  have hA : (2 * L) ^ 2 / T ≤ 4 * L ^ 2 * E1 := by
    calc (2 * L) ^ 2 / T = (2 * L) ^ 2 * (1 / T) := by ring
      _ ≤ (2 * L) ^ 2 * E1 := mul_le_mul_of_nonneg_left h1t (by positivity)
      _ = 4 * L ^ 2 * E1 := by ring
  have hB : Hm * (em + 1 / T ^ 2) ≤
      2 * E1 + 60 * CA * L ^ 3 * E3 + 60 * CA * L ^ 3 * E2 := by
    have h1 : Hm * (em + 1 / T ^ 2) ≤ (E1 + 60 * CA * L ^ 3) * (E3 + E2) :=
      mul_le_mul hHm (add_le_add hem h1t2) (by positivity) (by positivity)
    have h2 : E1 * E3 ≤ E1 := mul_le_of_le_one_right hE10 hE31
    have h3 : E1 * E2 ≤ E1 := mul_le_of_le_one_right hE10 hE21
    nlinarith
  have hsum : (2 * L) ^ 2 / T + Hm * (em + 1 / T ^ 2) ≤
      4 * L ^ 2 * E1 + (2 * E1 + 60 * CA * L ^ 3 * E3 + 60 * CA * L ^ 3 * E2) :=
    add_le_add hA hB
  have hmain : 12 * (Ctot * D ^ 2 * ((2 * L) ^ 2 / T + Hm * (em + 1 / T ^ 2)) / (2 * Real.pi)) ≤
      12 * (Ctot * D ^ 2 * (4 * L ^ 2 * E1 + (2 * E1 + 60 * CA * L ^ 3 * E3 +
        60 * CA * L ^ 3 * E2)) / (2 * Real.pi)) := by
    have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ Ctot * D ^ 2)
    have := div_le_div_of_nonneg_right this hπ.le
    linarith
  have hexp : 0 ≤ Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := (Real.exp_pos _).le
  have hsq' : 12 * (2 * Real.log xb / Real.sqrt xb) ≤
      48 * (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := by
    have : 0 ≤ (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := by positivity
    nlinarith
  unfold primeBlockTwistMajorant
  rw [← hD2, ← hE1, ← hE2, ← hE3]
  have hsplit : 12 * (Ctot * D ^ 2 * (4 * L ^ 2 * E1 + (2 * E1 + 60 * CA * L ^ 3 * E3 +
        60 * CA * L ^ 3 * E2)) / (2 * Real.pi)) =
      12 * Ctot * D ^ 2 * (4 * L ^ 2 * E1) / (2 * Real.pi)
        + 12 * Ctot * D ^ 2 * (2 * E1) / (2 * Real.pi)
        + 12 * Ctot * D ^ 2 * (60 * CA * L ^ 3 * E3) / (2 * Real.pi)
        + 12 * Ctot * D ^ 2 * (60 * CA * L ^ 3 * E2) / (2 * Real.pi) := by ring
  linarith

/-- The component bounds of the short prime block estimate, collected into the majorant. -/
theorem primeBlock_envelope_le_majorant {A c CA Ctot X L D ℓ t : ℝ} {b : ℕ} (hc : 0 < c)
    (hCA : 0 < CA) (hCtot : 0 < Ctot) (h60 : 60 ≤ L) (hL : L = Real.log X) (hX0 : 0 < X)
    (hD : D = Real.exp (L ^ ((1 : ℝ) / 25)))
    (ht1 : Real.exp (c * L ^ ((1 : ℝ) / 2)) ≤ |t|) (ht2 : |t| ≤ 4 * X)
    (ht1' : (1 : ℝ) ≤ |t|) (hℓpos : 0 < ℓ) (hℓle : ℓ ≤ routeTWidthPolylogLower A t)
    (hinvℓ : 1 / ℓ ≤ 30 * CA * L ^ ((91 : ℝ) / 100)) (hb1 : (1 : ℝ) ≤ b)
    (hlogb : Real.log b ≤ L + 1) (hbz : Real.exp (L ^ ((99 : ℝ) / 100)) / 2 ≤ (b : ℝ)) :
    12 * (Ctot * D ^ 2 * ((2 * L) ^ 2 / |t| + scaledHeightMajorant A t *
            (Real.exp (-(ℓ / 2 * (L ^ ((99 : ℝ) / 100) / 2))) + 1 / |t| ^ 2)) / (2 * Real.pi)
          + Real.log (2 * (b : ℝ)) / D + 2 * Real.log b / Real.sqrt b)
          + 84 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) ≤
      primeBlockTwistMajorant c Ctot CA L := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hexpc : 0 < Real.exp (c * L ^ ((1 : ℝ) / 2)) := Real.exp_pos _
  have ht0 : 0 < |t| := lt_of_lt_of_le hexpc ht1
  -- component bounds
  have hE1 : 1 / |t| ≤ Real.exp (-(c * L ^ ((1 : ℝ) / 2))) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hexpc ht1
  have hE2 : 1 / |t| ^ 2 ≤ Real.exp (-(2 * c * L ^ ((1 : ℝ) / 2))) := by
    have h := mul_le_mul hE1 hE1 (by positivity) (Real.exp_pos _).le
    rw [← Real.exp_add] at h
    calc 1 / |t| ^ 2 = 1 / |t| * (1 / |t|) := by ring
      _ ≤ _ := h
      _ = _ := by ring_nf
  have hHm0 : 0 ≤ scaledHeightMajorant A t := scaledHeightMajorant_nonneg ht1'
  have hlog3t : Real.log (3 * |t| / 2) ≤ 2 * L := by
    have h1 : 3 * |t| / 2 ≤ 6 * X := by linarith only [ht2]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hX0.ne', ← hL] at h2
    have h6 : Real.log 6 ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith only [h2, h6, h60]
  have hlog3t0 : 0 ≤ Real.log (3 * |t| / 2) := Real.log_nonneg (by linarith only [ht1'])
  have hHm : scaledHeightMajorant A t ≤ Real.exp (-(c * L ^ ((1 : ℝ) / 2))) + 60 * CA * L ^ 3 := by
    rw [scaledHeightMajorant]
    have hw0 : 0 < routeTWidthPolylogLower A t := routeTWidthPolylogLower_pos A t
    have hinv : 1 / routeTWidthPolylogLower A t ≤ 1 / ℓ := one_div_le_one_div_of_le hℓpos hℓle
    have hL91 : L ^ ((91 : ℝ) / 100) ≤ L ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2 : Real.log (3 * |t| / 2) / routeTWidthPolylogLower A t ≤ 60 * CA * L ^ 3 := by
      calc Real.log (3 * |t| / 2) / routeTWidthPolylogLower A t
          = Real.log (3 * |t| / 2) * (1 / routeTWidthPolylogLower A t) := by ring
        _ ≤ (2 * L) * (30 * CA * L ^ (2 : ℕ)) :=
            mul_le_mul hlog3t (hinv.trans (hinvℓ.trans (mul_le_mul_of_nonneg_left hL91
              (by positivity)))) (by positivity) (by positivity)
        _ = 60 * CA * L ^ 3 := by ring
    linarith only [hE1, h2]
  have hem : Real.exp (-(ℓ / 2 * (L ^ ((99 : ℝ) / 100) / 2))) ≤
      Real.exp (-(1 / (120 * CA) * L ^ ((2 : ℝ) / 25))) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hℓlow : 1 / (30 * CA * L ^ ((91 : ℝ) / 100)) ≤ ℓ := by
      have h := one_div_le_one_div_of_le (by positivity) hinvℓ
      rwa [one_div_one_div] at h
    have hsplit : L ^ ((99 : ℝ) / 100) = L ^ ((91 : ℝ) / 100) * L ^ ((2 : ℝ) / 25) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hp91 : 0 < L ^ ((91 : ℝ) / 100) := Real.rpow_pos_of_pos hL0 _
    calc 1 / (120 * CA) * L ^ ((2 : ℝ) / 25)
        = 1 / (30 * CA * L ^ ((91 : ℝ) / 100)) / 2 * (L ^ ((99 : ℝ) / 100) / 2) := by
          rw [hsplit]; field_simp; ring
      _ ≤ ℓ / 2 * (L ^ ((99 : ℝ) / 100) / 2) := by
          have h99 : 0 ≤ L ^ ((99 : ℝ) / 100) / 2 := by positivity
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hℓlow (by norm_num)) h99
  have hlog2b : Real.log (2 * (b : ℝ)) / D ≤ 2 * L * Real.exp (-(L ^ ((1 : ℝ) / 25))) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hb1])), hD, Real.exp_neg,
      div_eq_mul_inv]
    have h2le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    exact mul_le_mul_of_nonneg_right (by linarith only [h2le, hlogb, h60]) (by positivity)
  have hsqb : 2 * Real.log b / Real.sqrt b ≤
      3 * (L + 1) * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := by
    have hsb : Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)) / Real.sqrt 2 ≤ Real.sqrt b := by
      have h := Real.sqrt_le_sqrt hbz
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)] at h
      have he : Real.sqrt (Real.exp (L ^ ((99 : ℝ) / 100))) = Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)) := by
        rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
      rwa [he] at h
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hsbpos : 0 < Real.sqrt b := Real.sqrt_pos.2 (by linarith only [hb1])
    have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hinvs : 1 / Real.sqrt b ≤ 3 / 2 * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100))) := by
      rw [Real.exp_neg]
      have hep := Real.exp_pos (1 / 2 * L ^ ((99 : ℝ) / 100))
      rw [div_le_iff₀ hsbpos]
      have h2 := mul_le_mul_of_nonneg_left hsb (by positivity :
        (0 : ℝ) ≤ 3 / 2 * (Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)))⁻¹)
      calc (1 : ℝ) = 3 / 2 * (Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)))⁻¹ *
            (Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)) / (3 / 2)) := by field_simp
        _ ≤ 3 / 2 * (Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)))⁻¹ *
            (Real.exp (1 / 2 * L ^ ((99 : ℝ) / 100)) / Real.sqrt 2) := by
            gcongr
        _ ≤ _ := h2
    calc 2 * Real.log b / Real.sqrt b = 2 * Real.log b * (1 / Real.sqrt b) := by ring
      _ ≤ 2 * (L + 1) * (3 / 2 * Real.exp (-(1 / 2 * L ^ ((99 : ℝ) / 100)))) :=
          mul_le_mul (by linarith only [hlogb]) hinvs (by positivity) (by positivity)
      _ = _ := by ring
  have h12 := twelve_relScaled_le_majorant (xb := (b : ℝ)) hL1 hc hCA hCtot hD ht0 hE1 hE2
    hHm (Real.exp_pos _).le hem hlog2b hsqb
  exact h12

/-- The last step of the short prime block estimate, in the variables `r` (the relative
envelope) and `R` (its explicit majorant). -/
theorem primeBlock_final_chain {a b : ℕ} {r R L : ℝ} (hb2a : (b : ℝ) ≤ 2 * ((a : ℝ) + 1))
    (hr0 : 0 ≤ r) (ha : Real.exp (L ^ ((99 : ℝ) / 100)) ≤ (a : ℝ) + 1) (hr : r ≤ R) :
    4 / Real.log 2 * ((b : ℝ) * r + 7 * Real.exp 9) / ((a : ℝ) + 1) ≤
      12 * R + 84 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) := by
  have ha1pos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hlog2 : 4 / Real.log 2 ≤ 6 := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    have h2 := Real.log_two_gt_d9; linarith only [h2]
  have hinva : 7 * Real.exp 9 / ((a : ℝ) + 1) ≤
      7 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) := by
    rw [Real.exp_neg, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) ha) (by positivity)
  have hstep : ((b : ℝ) * r + 7 * Real.exp 9) / ((a : ℝ) + 1) ≤
      2 * r + 7 * Real.exp 9 / ((a : ℝ) + 1) := by
    rw [div_le_iff₀ ha1pos, add_mul, div_mul_cancel₀ _ ha1pos.ne']
    have hbr := mul_le_mul_of_nonneg_right hb2a hr0
    linarith only [hbr]
  have hnn : 0 ≤ ((b : ℝ) * r + 7 * Real.exp 9) / ((a : ℝ) + 1) := by positivity
  have he9 : 0 ≤ Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) := by positivity
  calc 4 / Real.log 2 * ((b : ℝ) * r + 7 * Real.exp 9) / ((a : ℝ) + 1)
      = 4 / Real.log 2 * (((b : ℝ) * r + 7 * Real.exp 9) / ((a : ℝ) + 1)) := by ring
    _ ≤ 6 * (2 * r + 7 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100)))) :=
        mul_le_mul hlog2 (hstep.trans (add_le_add le_rfl hinva)) hnn (by norm_num)
    _ ≤ 12 * R + 84 * Real.exp 9 * Real.exp (-(L ^ ((99 : ℝ) / 100))) := by
        linarith only [hr, he9]

/-- **Twisted sums over short prime blocks at the paper scale.**  For every `c > 0`, for all large
`X`: if `z₀ ≤ Q ≤ X`, `0 ≤ δ ≤ 1`, and `exp(c√log X) ≤ |t| ≤ 4X`, then
`|∑_{Q < p ≤ Q(1+δ)} p^{-1-it}| ≤ exp(-(log X)^{1/30})`. -/
theorem eventually_norm_sum_primeBlock_cpow_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : Finset ℕ) (Q δ t : ℝ),
      mtLowerCutoff X ≤ Q → Q ≤ X → 0 ≤ δ → δ ≤ 1 →
      (∀ p, p ∈ B ↔ p.Prime ∧ Q < p ∧ (p : ℝ) ≤ Q * (1 + δ)) →
      Real.exp (c * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ |t| → |t| ≤ 4 * X →
      ‖∑ p ∈ B, (p : ℂ) ^ (-(1 + (t : ℂ) * Complex.I))‖ ≤
        Real.exp (-(Real.log X) ^ ((1 : ℝ) / 30)) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hH⟩ := exists_norm_harmonicPrimeBlockPoly_scaled_le
  obtain ⟨CA, hCAdef⟩ : ∃ CA : ℝ, CA = routeTZeroFreeDeltaEnvelopeConstant A := ⟨_, rfl⟩
  have hCA : 0 < CA := by rw [hCAdef]; exact routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hev := Real.tendsto_log_atTop.eventually
    (eventually_primeBlock_scalar_conditions (Ctot := Ctot) (τ₀ := τ₀) hc hCA hdelta)
  filter_upwards [hev] with X ⟨hmaj, h60, hlogL3, hlog3L, hℓδ, hτbig, hq2⟩
  intro B Q δ t hQlo hQhi hδ0 hδ1 hB ht1 ht2
  clear hev
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hL] at hmaj h60 hlogL3 hlog3L hℓδ hτbig hq2 ht1 ⊢
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hexpc : 0 < Real.exp (c * L ^ ((1 : ℝ) / 2)) := Real.exp_pos _
  have ht0 : 0 < |t| := lt_of_lt_of_le hexpc ht1
  have hX0 : 0 < X := by linarith
  have hπ3 : 16 * Real.pi / 3 ≤ |t| := le_trans (le_max_right _ _) (hτbig.trans ht1)
  have hτ₀t : τ₀ ≤ |t| := le_trans (le_max_left _ _) (hτbig.trans ht1)
  -- the lower cutoff
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hz0 : Real.exp (L ^ ((99 : ℝ) / 100)) ≤ mtLowerCutoff X := by
    rw [mtLowerCutoff, mtLowerLogCutoff, ← hL]
    refine Real.exp_le_exp.2 ?_
    rw [le_div_iff₀ (by positivity)]
    calc L ^ ((99 : ℝ) / 100) * Real.log L ^ 3 ≤ L ^ ((99 : ℝ) / 100) * L ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_left hlogL3 (Real.rpow_nonneg hL0.le _)
      _ = L := by rw [← Real.rpow_add hL0]; norm_num
  have hz4 : 4 ≤ Real.exp (L ^ ((99 : ℝ) / 100)) := by
    have h := Real.exp_le_exp.2 hq2
    rwa [show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)] at h
  have hQ4 : 4 ≤ Q := hz4.trans (hz0.trans hQlo)
  have hQ0 : 0 ≤ Q := by linarith
  -- the integer endpoints
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌊Q⌋₊ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊Q * (1 + δ)⌋₊ := ⟨_, rfl⟩
  have haQ : (a : ℝ) ≤ Q := by rw [ha]; exact Nat.floor_le hQ0
  have hQa : Q < (a : ℝ) + 1 := by rw [ha]; exact Nat.lt_floor_add_one Q
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hQδ : Q ≤ Q * (1 + δ) := by nlinarith
  have hab : a ≤ b := by rw [ha, hb]; exact Nat.floor_mono hQδ
  have hbQ : (b : ℝ) ≤ Q * (1 + δ) := by rw [hb]; exact Nat.floor_le (by positivity)
  have hB' : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b) := by
    intro p
    rw [hB p, ha, hb, Nat.floor_lt hQ0, Nat.le_floor_iff (by positivity)]
  have hBprime : ∀ p ∈ B, p.Prime := fun p hp => ((hB' p).1 hp).1
  -- the Route-T estimate
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.exp (L ^ ((1 : ℝ) / 25)) := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; exact Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hD0 : 0 < D := by linarith
  have hw : -(2 * Real.pi * (-t / (2 * Real.pi))) = t := by field_simp
  have hHB := hH B a b D (-t / (2 * Real.pi)) ha1 hab hB' hD1 (by rw [hw]; exact hτ₀t)
  rw [hw] at hHB
  clear hH
  rw [sum_prime_cpow_eq_neg_harmonicPrimeBlockPoly hBprime, norm_neg]
  refine hHB.trans ?_
  have hb1 : (1 : ℝ) ≤ b := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  rw [max_eq_left hb1, scaledTwistEnvelope_eq_mul (by linarith)]
  -- the relative envelope
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = primeBlockWidthLower CA L := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by
    rw [hℓ, primeBlockWidthLower]
    have h3L : 0 < (3 * L) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
    have hlog3 : 0 < (1 + Real.log (3 * L)) ^ 2 := by
      have : 0 ≤ Real.log (3 * L) := Real.log_nonneg (by linarith)
      positivity
    exact div_pos one_pos (mul_pos (mul_pos (by positivity) h3L) hlog3)
  have hℓle : ℓ ≤ routeTWidthPolylogLower A t := by
    rw [hℓ, hCAdef, hL]; exact primeBlockWidthLower_le (by rw [← hL]; exact h60) hπ3 ht2
  have hinvℓ : 1 / ℓ ≤ 30 * CA * L ^ ((91 : ℝ) / 100) := by
    rw [hℓ]; exact inv_primeBlockWidthLower_le hCA hL1 hlog3L
  have hbX : (b : ℝ) ≤ 2 * X := by nlinarith
  have hlogb : Real.log b ≤ L + 1 := by
    have := Real.log_le_log (by linarith) hbX
    rw [Real.log_mul (by norm_num) hX0.ne', ← hL] at this
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hbz : Real.exp (L ^ ((99 : ℝ) / 100)) / 2 ≤ (b : ℝ) := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have : Q ≤ (a : ℝ) + 1 := hQa.le
    have : Q / 2 ≤ (a : ℝ) := by linarith
    have : Real.exp (L ^ ((99 : ℝ) / 100)) ≤ Q := hz0.trans hQlo
    linarith
  have hq : L ^ ((99 : ℝ) / 100) / 2 ≤ Real.log b := by
    have h := Real.log_le_log (by positivity) hbz
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h
    have h2 : Real.log 2 ≤ L ^ ((99 : ℝ) / 100) / 2 := by linarith
    linarith
  have hμ : ℓ / 2 ≤ min delta (routeTWidthPolylogLower A t) / 2 := by
    have := le_min (hℓ ▸ hℓδ) hℓle
    linarith
  have hrel := relScaledEnvelope_le (A := A) (delta := delta) (Ctot := Ctot) (D := D) (τ := t)
    (x := (b : ℝ)) (Lx := 2 * L) (q := L ^ ((99 : ℝ) / 100) / 2) (μ := ℓ / 2)
    hCtot.le hD0 hπ3 hb1 (by linarith) (by positivity) hq (by linarith) hμ
  -- the relative envelope is nonnegative
  have ht1' : (1 : ℝ) ≤ |t| := by have := Real.pi_gt_three; linarith
  have hrel0 : 0 ≤ relScaledEnvelope A delta Ctot D t (b : ℝ) := by
    have h := scaledTwistEnvelope_nonneg (A := A) (delta := delta) (τ := t) hCtot.le hD0 ht1' hb1
    rw [scaledTwistEnvelope_eq_mul (by linarith)] at h
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact h) (by linarith : (0 : ℝ) < b)
  have h12 := primeBlock_envelope_le_majorant (A := A) (Ctot := Ctot) hc hCA hCtot h60 hL hX0 hD
    ht1 ht2 ht1' hℓpos hℓle hinvℓ hb1 hlogb hbz
  -- assembling
  have hb2a : (b : ℝ) ≤ 2 * ((a : ℝ) + 1) := by
    have hQd : Q * δ ≤ Q := mul_le_of_le_one_right hQ0 hδ1
    linarith only [hbQ, hQd, hQa]
  have ha1big : Real.exp (L ^ ((99 : ℝ) / 100)) ≤ (a : ℝ) + 1 := by
    linarith only [hz0.trans hQlo, hQa]
  have hfin := primeBlock_final_chain hb2a hrel0 ha1big hrel
  push_cast
  exact hfin.trans (h12.trans hmaj)

end

end RHTower.Sieve
