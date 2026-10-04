import GaloisForLFunctions.RHTower.NicolasInequalityQuasiRiemannConverse
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.RHTower.WeilLagLocalWorkHuxley

/-!
# Prime lags bounded below force the Riemann hypothesis

With `a_n = Φ(log n)`, if `a_p ≥ -M` for every large prime `p`, the Riemann hypothesis holds.
Together with the upper criterion (`riemannHypothesis_iff_primeLag_bddAbove`): RH holds iff the
prime lags are bounded above, iff they are bounded below.

The lag primitive `v(T) = γ + 1 - ∫_0^T (e^s - ψ(e^s))e^{-s} ds` satisfies
`Φ(T) = e^{T/2} v(T) - (log 2π - S(e^T)) e^{-T/2}`, so a lower bound at `T₂` transfers to `T₁ ≥ T₂`
with loss `e^{T₁/2}(T₁ - T₂) sup_{[T₂,T₁]} |e^s - ψ(e^s)|e^{-s}`.  A prime in `(x - x^{3/5}, x]`
(Huxley) gives `T₁ - T₂ ≤ 2x^{-2/5}`.

* With the trivial bound `|ψ(x) - x| ≤ Cx` the loss is `O(x^{1/10})`, so `Φ(L) ≥ -M' e^{L/10}` and
  every zero has real part at most `3/5`.
* Then `|ψ(x) - x| ≤ C x^{13/20}` makes the loss `O(x^{-1/4})`, so `Φ` is bounded below and every
  zero lies on the critical line.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **Transfer of a lower lag bound.**  If `0 < T₂ ≤ T₁`, `|g| ≤ A` on `[T₂, T₁]` and
`Φ(T₂) ≥ -M`, then `Φ(T₁) ≥ -(M e^{(T₁-T₂)/2} + A(T₁ - T₂)e^{T₁/2} + 2)`. -/
theorem weilLagFunctionReal_ge_of_transfer {T₁ T₂ A M : ℝ} (hT₂ : 0 < T₂) (hT : T₂ ≤ T₁)
    (hA : ∀ s ∈ Icc T₂ T₁, |mertensLagDensity s| ≤ A)
    (hΦ : -M ≤ weilLagFunctionReal T₂) :
    -(M * Real.exp ((T₁ - T₂) / 2) + A * (T₁ - T₂) * Real.exp (T₁ / 2) + 2)
      ≤ weilLagFunctionReal T₁ := by
  have hT₁ : 0 < T₁ := lt_of_lt_of_le hT₂ hT
  have h1 := weilLagFunctionReal_eq_lagPrimitive hT₁
  have h2 := weilLagFunctionReal_eq_lagPrimitive hT₂
  -- `v(T₁) - v(T₂) = -∫_{T₂}^{T₁} g`
  have hdiff : mertensLagPrimitive T₁ - mertensLagPrimitive T₂
      = -∫ s in T₂..T₁, mertensLagDensity s := by
    unfold mertensLagPrimitive
    rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_mertensLagDensity 0 T₁)
      (intervalIntegrable_mertensLagDensity 0 T₂)]
    ring
  have hint : |∫ s in T₂..T₁, mertensLagDensity s| ≤ A * (T₁ - T₂) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T₂) (b := T₁)
      (f := mertensLagDensity) (C := A) fun s hs => by
        rw [uIoc_of_le hT] at hs
        rw [Real.norm_eq_abs]; exact hA s ⟨hs.1.le, hs.2⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hT)] at this
  have hX1 : (1 : ℝ) ≤ Real.exp T₁ := Real.one_le_exp hT₁.le
  have hX2 : (1 : ℝ) ≤ Real.exp T₂ := Real.one_le_exp hT₂.le
  have hS1 := trivialZeroSeriesReal_nonneg hX1
  have hS1' := trivialZeroSeriesReal_le_one hX1
  have hS2 := trivialZeroSeriesReal_nonneg hX2
  have hS2' := trivialZeroSeriesReal_le_one hX2
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 1 < Real.log (2 * Real.pi) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  -- `v(T₂) ≥ -M e^{-T₂/2}`
  have hhalf2 : Real.exp (T₂ / 2) * Real.exp (-T₂ / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hv2 : -(M * Real.exp (-T₂ / 2)) ≤ mertensLagPrimitive T₂ := by
    have hE := Real.exp_pos (T₂ / 2)
    have hE' := Real.exp_pos (-T₂ / 2)
    have hd : 0 ≤ (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T₂))
        * Real.exp (-T₂ / 2) := mul_nonneg (by linarith) hE'.le
    have : Real.exp (T₂ / 2) * mertensLagPrimitive T₂ ≥ -M := by linarith
    have h3 : mertensLagPrimitive T₂
        = Real.exp (-T₂ / 2) * (Real.exp (T₂ / 2) * mertensLagPrimitive T₂) := by
      rw [← mul_assoc, mul_comm (Real.exp (-T₂ / 2)), hhalf2, one_mul]
    rw [h3]
    have := mul_le_mul_of_nonneg_left this hE'.le
    linarith
  have hv1 : -(M * Real.exp (-T₂ / 2)) - A * (T₁ - T₂) ≤ mertensLagPrimitive T₁ := by
    have := (abs_le.mp hint).2
    linarith
  have hE1 := Real.exp_pos (T₁ / 2)
  have hprod : Real.exp (T₁ / 2) * Real.exp (-T₂ / 2) = Real.exp ((T₁ - T₂) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hlast : (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T₁))
      * Real.exp (-T₁ / 2) ≤ 2 := by
    have : Real.exp (-T₁ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h0 : 0 ≤ Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T₁) := by linarith
    nlinarith
  have := mul_le_mul_of_nonneg_left hv1 hE1.le
  rw [h1]
  have e : Real.exp (T₁ / 2) * (-(M * Real.exp (-T₂ / 2)) - A * (T₁ - T₂))
      = -(M * Real.exp ((T₁ - T₂) / 2)) - A * (T₁ - T₂) * Real.exp (T₁ / 2) := by
    rw [← hprod]; ring
  linarith

/-- Primes just below `e^L`: for large `L` there is a prime `p` with
`L - 2e^{-2L/5} ≤ log p ≤ L`. -/
theorem eventually_exists_prime_log_near :
    ∀ᶠ L : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ L - 2 * Real.exp (-(2 / 5) * L) ≤ Real.log p ∧
      Real.log p ≤ L := by
  have hprime := eventually_exists_prime_short_interval_seven_twelfths (α := 3 / 5)
    (by norm_num) (by norm_num)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hprime
  -- `x^{3/5} ≤ x/2` for large `x`
  have hsmall : ∀ᶠ x : ℝ in atTop, 2 * x ^ (3 / 5 : ℝ) ≤ x := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 / 5 by norm_num)
    filter_upwards [h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have e : x ^ (3 / 5 : ℝ) = x * x ^ (-(2 / 5) : ℝ) := by
      rw [← Real.rpow_one_add' hx0.le (by norm_num)]; norm_num
    rw [e]; nlinarith
  have hev := Real.tendsto_exp_atTop.eventually ((hsmall.and (eventually_ge_atTop (2 * Y + 2))))
  filter_upwards [hev] with L ⟨hs, hYx⟩
  set x := Real.exp L with hx
  have hx0 : 0 < x := Real.exp_pos L
  have hxp : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  set y := x - x ^ (3 / 5 : ℝ) with hy
  have hyY : Y ≤ y := by rw [hy]; linarith
  have hy0 : 0 < y := by rw [hy]; linarith
  obtain ⟨p, hp, hyp, hpy⟩ := hY y hyY
  have hyx : y ^ (3 / 5 : ℝ) ≤ x ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow hy0.le (by rw [hy]; linarith) (by norm_num)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpx : (p : ℝ) ≤ x := by rw [hy] at hpy; linarith
  refine ⟨p, hp, ?_, ?_⟩
  · -- `log x - log p ≤ x/p - 1 ≤ 2 x^{-2/5}`
    have h1 : Real.log x - Real.log p ≤ x / p - 1 := by
      rw [← Real.log_div hx0.ne' hp0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hx0 hp0)
    have hpx2 : x / 2 ≤ (p : ℝ) := by rw [hy] at hyp; linarith
    have h2 : x / p - 1 ≤ 2 * x ^ (-(2 / 5) : ℝ) := by
      rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
      have e : x ^ (-(2 / 5) : ℝ) * x = x ^ (3 / 5 : ℝ) := by
        rw [← Real.rpow_add_one hx0.ne']; norm_num
      have hxm : x - p ≤ x ^ (3 / 5 : ℝ) := by rw [hy] at hyp; linarith
      have hneg : 0 ≤ x ^ (-(2 / 5) : ℝ) := Real.rpow_nonneg hx0.le _
      nlinarith
    have h3 : x ^ (-(2 / 5) : ℝ) = Real.exp (-(2 / 5) * L) := by
      rw [hx, ← Real.exp_mul]; ring_nf
    rw [hx, Real.log_exp] at h1
    rw [← h3]
    linarith
  · rw [← Real.log_exp L]
    exact Real.log_le_log hp0 hpx

/-- `|g(s)| = |e^s - ψ(e^s)| e^{-s} ≤ log 4 + 4`. -/
theorem abs_mertensLagDensity_le (s : ℝ) :
    |mertensLagDensity s| ≤ Real.log 4 + 4 := by
  unfold mertensLagDensity
  have hx := Real.exp_pos s
  have hψ := Chebyshev.psi_le_const_mul_self hx.le
  have hψ0 := Chebyshev.psi_nonneg (Real.exp s)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hprod : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.exp s - Chebyshev.psi (Real.exp s)| ≤ (Real.log 4 + 4) * Real.exp s := by
    rw [abs_le]; constructor <;> nlinarith
  calc |Real.exp s - Chebyshev.psi (Real.exp s)| * Real.exp (-s)
      ≤ (Real.log 4 + 4) * Real.exp s * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.log 4 + 4 := by rw [mul_assoc, hprod, mul_one]

/-- Exponent-law bound: if `Θ < b`, then `|g(s)| ≤ C e^{(b-1)s}` for `s ≥ 0`. -/
theorem exists_abs_mertensLagDensity_le_exp {b : ℝ} (hb : zeroReSup < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → |mertensLagDensity s| ≤ C * Real.exp ((b - 1) * s) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_chebyshevPsi_sub_le_rpow hb
  refine ⟨C, hC0, fun s hs => ?_⟩
  unfold mertensLagDensity
  have h1 := hC (Real.exp s) (Real.one_le_exp hs)
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]
  have h2 : Real.exp s ^ b = Real.exp (b * s) := by rw [← Real.exp_mul, mul_comm]
  rw [h2] at h1
  have h3 : Real.exp (b * s) * Real.exp (-s) = Real.exp ((b - 1) * s) := by
    rw [← Real.exp_add]; ring_nf
  calc |Chebyshev.psi (Real.exp s) - Real.exp s| * Real.exp (-s)
      ≤ C * Real.exp (b * s) * Real.exp (-s) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = C * Real.exp ((b - 1) * s) := by rw [mul_assoc, h3]


theorem exp_one_half_le_two_lag : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- A lower bound `Φ ≥ -K e^{aL}` beyond `L₀` extends to all `L ≥ 0`. -/
theorem weilLagFunctionReal_lower_of_eventually {a K L₀ : ℝ} (ha : 0 ≤ a) (hK0 : 0 ≤ K)
    (hK : ∀ L, L₀ ≤ L → -(K * Real.exp (a * L)) ≤ weilLagFunctionReal L) :
    ∀ L, 0 ≤ L → -((K + Real.exp (L₀ / 2) * lagWeightTotal) * Real.exp (a * L))
      ≤ weilLagFunctionReal L := by
  intro L hL
  have hW := lagWeightTotal_nonneg
  have hea : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha hL)
  have hEW : 0 ≤ Real.exp (L₀ / 2) * lagWeightTotal := mul_nonneg (Real.exp_pos _).le hW
  rcases le_or_gt L₀ L with h | h
  · have h1 := hK L h
    have h2 : K * Real.exp (a * L) ≤ (K + Real.exp (L₀ / 2) * lagWeightTotal) * Real.exp (a * L) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith
  · have hb := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at hb
    have h1 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (L₀ / 2) * lagWeightTotal :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hW
    have h2 : Real.exp (L₀ / 2) * lagWeightTotal
        ≤ (K + Real.exp (L₀ / 2) * lagWeightTotal) * Real.exp (a * L) :=
      le_trans (by linarith) (le_mul_of_one_le_right (by linarith) hea)
    have := (abs_le.mp hb).1
    linarith

/-- **Prime lags bounded below force the Riemann hypothesis.** -/
theorem riemannHypothesis_of_primeLag_ge {M : ℝ}
    (hM : ∀ᶠ p : ℕ in atTop, p.Prime → -M ≤ integerLag p) : RiemannHypothesis := by
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hM
  have hlow : ∀ p : ℕ, p.Prime → (P₀ : ℝ) ≤ p → -M' ≤ weilLagFunctionReal (Real.log p) := by
    intro p hp hpP
    have := hP₀ p (by exact_mod_cast hpP) hp
    unfold integerLag at this
    linarith [le_max_left M 0]
  -- primes just below `e^L`, beyond `P₀`
  have hnear : ∀ᶠ L : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ (P₀ : ℝ) ≤ p ∧
      L - 2 * Real.exp (-(2 / 5) * L) ≤ Real.log p ∧ Real.log p ≤ L ∧ L - 1 ≤ Real.log p := by
    have hsm : ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-(2 / 5) * L) ≤ 1 := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (show -(2 / 5 : ℝ) < 0 by norm_num))).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by
          norm_num))
      filter_upwards [this] with L hL
      simp only [Function.comp, id] at hL
      linarith
    filter_upwards [eventually_exists_prime_log_near, hsm,
      eventually_ge_atTop (Real.log (max (P₀ : ℝ) 1) + 1)] with L ⟨p, hp, h1, h2⟩ hL hLP
    refine ⟨p, hp, ?_, h1, h2, by linarith⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have : Real.log (max (P₀ : ℝ) 1) ≤ Real.log p := by linarith
    have h3 : max (P₀ : ℝ) 1 ≤ p :=
      (Real.log_le_log_iff (lt_of_lt_of_le one_pos (le_max_right _ _)) hp0).mp this
    exact le_trans (le_max_left _ _) h3
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hnear
  -- Step 1: `Φ(L) ≥ -M₁ e^{L/10}`, hence every zero has real part at most `3/5`
  set A : ℝ := Real.log 4 + 4 with hA
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); linarith
  have hstep1 : ∀ L, max L₁ 1 ≤ L →
      -((2 * M' + 2 + 2 * A) * Real.exp (1 / 10 * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    obtain ⟨p, hp, hpP, h1, h2, h3⟩ := hL₁ L (le_trans (le_max_left _ _) hL)
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hT₂ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have htr := weilLagFunctionReal_ge_of_transfer hT₂ h2
      (fun s _ => abs_mertensLagDensity_le s) (hlow p hp hpP)
    have hd : L - Real.log p ≤ 2 * Real.exp (-(2 / 5) * L) := by linarith
    have hd1 : L - Real.log p ≤ 1 := by linarith
    have he1 : Real.exp ((L - Real.log p) / 2) ≤ 2 := by
      have : Real.exp ((L - Real.log p) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith [exp_one_half_le_two_lag]
    have he2 : A * (L - Real.log p) * Real.exp (L / 2) ≤ 2 * A * Real.exp (1 / 10 * L) := by
      have h4 : (L - Real.log p) * Real.exp (L / 2)
          ≤ 2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      have h5 : Real.exp (-(2 / 5) * L) * Real.exp (L / 2) = Real.exp (1 / 10 * L) := by
        rw [← Real.exp_add]; ring_nf
      have := mul_le_mul_of_nonneg_left h4 hA0
      nlinarith
    have hea : 1 ≤ Real.exp (1 / 10 * L) := Real.one_le_exp (by linarith)
    have hM2 : M' * Real.exp ((L - Real.log p) / 2) ≤ 2 * M' * Real.exp (1 / 10 * L) := by
      have := mul_le_mul_of_nonneg_left he1 hM'0
      nlinarith
    nlinarith
  have hall1 := weilLagFunctionReal_lower_of_eventually (by norm_num) (by positivity) hstep1
  have hre1 := re_le_half_add_of_neg_exp_le_weilLagFunctionReal (by norm_num) (by norm_num) hall1
  have hΘ35 : zeroReSup ≤ 3 / 5 := by
    have := zeroReSup_le_of_forall_re_le hre1; linarith
  -- Step 2: `Φ` is bounded below
  obtain ⟨C, hC0, hC⟩ := exists_abs_mertensLagDensity_le_exp (b := 13 / 20) (by linarith)
  have hdecay : ∀ᶠ L : ℝ in atTop, 2 * C * Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) ≤ 1 := by
    have := ((Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (show -(1 / 4 : ℝ) < 0 by norm_num))).const_mul (2 * C * Real.exp (7 / 20))).eventually
        (ge_mem_nhds (show (2 * C * Real.exp (7 / 20)) * 0 < 1 by norm_num))
    filter_upwards [this] with L hL
    simpa [Function.comp] using hL
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp hdecay
  have hstep2 : ∀ L, max (max L₁ 1) L₂ ≤ L →
      -((2 * M' + 3) * Real.exp (0 * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hLa : max L₁ 1 ≤ L := le_trans (le_max_left _ _) hL
    obtain ⟨p, hp, hpP, h1, h2, h3⟩ := hL₁ L (le_trans (le_max_left _ _) hLa)
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hLa
    have hT₂ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    set A' : ℝ := C * Real.exp ((13 / 20 - 1) * (L - 1)) with hA'
    have hA'b : ∀ s ∈ Icc (Real.log p) L, |mertensLagDensity s| ≤ A' := by
      intro s hs
      have hs0 : 0 ≤ s := le_trans hT₂.le hs.1
      refine (hC s hs0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
      nlinarith [hs.1]
    have htr := weilLagFunctionReal_ge_of_transfer hT₂ h2 hA'b (hlow p hp hpP)
    have hd : L - Real.log p ≤ 2 * Real.exp (-(2 / 5) * L) := by linarith
    have hd1 : L - Real.log p ≤ 1 := by
      have := hL₁ L (le_trans (le_max_left _ _) hLa)
      linarith
    have he1 : Real.exp ((L - Real.log p) / 2) ≤ 2 := by
      have : Real.exp ((L - Real.log p) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith [exp_one_half_le_two_lag]
    have hA'0 : 0 ≤ A' := by rw [hA']; positivity
    have he2 : A' * (L - Real.log p) * Real.exp (L / 2) ≤ 1 := by
      have h4 : (L - Real.log p) * Real.exp (L / 2)
          ≤ 2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      have h5 : Real.exp ((13 / 20 - 1) * (L - 1)) * (Real.exp (-(2 / 5) * L) * Real.exp (L / 2))
          = Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have h6 := hL₂ L (le_trans (le_max_right _ _) hL)
      have := mul_le_mul_of_nonneg_left h4 hA'0
      calc A' * (L - Real.log p) * Real.exp (L / 2)
          ≤ A' * (2 * Real.exp (-(2 / 5) * L) * Real.exp (L / 2)) := by nlinarith
        _ = 2 * C * (Real.exp ((13 / 20 - 1) * (L - 1))
              * (Real.exp (-(2 / 5) * L) * Real.exp (L / 2))) := by rw [hA']; ring
        _ = 2 * C * Real.exp (7 / 20) * Real.exp (-(1 / 4) * L) := by rw [h5]; ring
        _ ≤ 1 := h6
    have hM2 : M' * Real.exp ((L - Real.log p) / 2) ≤ 2 * M' :=
      by have := mul_le_mul_of_nonneg_left he1 hM'0; linarith
    rw [zero_mul, Real.exp_zero, mul_one]
    linarith
  have hall2 := weilLagFunctionReal_lower_of_eventually (le_refl 0) (by positivity) hstep2
  have hre2 := re_le_half_add_of_neg_exp_le_weilLagFunctionReal (le_refl 0) (by norm_num) hall2
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have := hre2 q
  linarith

/-- **RH ⟺ prime lags bounded below.** -/
theorem riemannHypothesis_iff_primeLag_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ p : ℕ, p.Prime → -M ≤ integerLag p := by
  constructor
  · intro h
    refine ⟨poleSharpConstant, fun p _ => ?_⟩
    have := abs_integerLag_le_of_riemannHypothesis h p
    linarith [neg_abs_le (integerLag p)]
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_primeLag_ge (M := M) (Filter.Eventually.of_forall hM)


/-- **Transfer of an upper lag bound downwards.**  If `0 < T₂ ≤ T₁`, `|g| ≤ A` on `[T₂, T₁]` and
`Φ(T₁) ≤ -η`, then `Φ(T₂) ≤ e^{T₂/2}(-η e^{-T₁/2} + 2e^{-T₁} + A(T₁ - T₂))`. -/
theorem weilLagFunctionReal_le_of_transfer {T₁ T₂ A η : ℝ} (hT₂ : 0 < T₂) (hT : T₂ ≤ T₁)
    (hA : ∀ s ∈ Icc T₂ T₁, |mertensLagDensity s| ≤ A) (hΦ : weilLagFunctionReal T₁ ≤ -η) :
    weilLagFunctionReal T₂
      ≤ Real.exp (T₂ / 2) * (-(η * Real.exp (-T₁ / 2)) + 2 * Real.exp (-T₁) + A * (T₁ - T₂)) := by
  have hT₁ : 0 < T₁ := lt_of_lt_of_le hT₂ hT
  have hdiff : mertensLagPrimitive T₁ - mertensLagPrimitive T₂
      = -∫ s in T₂..T₁, mertensLagDensity s := by
    unfold mertensLagPrimitive
    rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_mertensLagDensity 0 T₁)
      (intervalIntegrable_mertensLagDensity 0 T₂)]
    ring
  have hint : |∫ s in T₂..T₁, mertensLagDensity s| ≤ A * (T₁ - T₂) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T₂) (b := T₁)
      (f := mertensLagDensity) (C := A) fun s hs => by
        rw [uIoc_of_le hT] at hs
        rw [Real.norm_eq_abs]; exact hA s ⟨hs.1.le, hs.2⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hT)] at this
  have hX1 : (1 : ℝ) ≤ Real.exp T₁ := Real.one_le_exp hT₁.le
  have hX2 : (1 : ℝ) ≤ Real.exp T₂ := Real.one_le_exp hT₂.le
  have hS1 := trivialZeroSeriesReal_nonneg hX1
  have hS2 := trivialZeroSeriesReal_le_one hX2
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 1 < Real.log (2 * Real.pi) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  -- `v(T₁) ≤ -η e^{-T₁/2} + 2 e^{-T₁}`
  have hid1 := exp_mul_mertensLagPrimitive_eq hT₁
  have hhalf : Real.exp (-T₁) * Real.exp (T₁ / 2) = Real.exp (-T₁ / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hv1 : mertensLagPrimitive T₁ ≤ -(η * Real.exp (-T₁ / 2)) + 2 * Real.exp (-T₁) := by
    have hv : mertensLagPrimitive T₁ = Real.exp (-T₁) * (Real.exp (T₁ / 2) * weilLagFunctionReal T₁
        + Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T₁)) := by
      rw [← hid1, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hv]
    have hE := Real.exp_pos (-T₁)
    have hE2 := Real.exp_pos (T₁ / 2)
    have h1 : Real.exp (T₁ / 2) * weilLagFunctionReal T₁ ≤ Real.exp (T₁ / 2) * (-η) :=
      mul_le_mul_of_nonneg_left hΦ hE2.le
    have h2 : Real.exp (T₁ / 2) * weilLagFunctionReal T₁ + Real.log (2 * Real.pi)
        - trivialZeroSeriesReal (Real.exp T₁) ≤ Real.exp (T₁ / 2) * (-η) + 2 := by linarith
    have := mul_le_mul_of_nonneg_left h2 hE.le
    calc _ ≤ Real.exp (-T₁) * (Real.exp (T₁ / 2) * (-η) + 2) := this
      _ = -(η * (Real.exp (-T₁) * Real.exp (T₁ / 2))) + 2 * Real.exp (-T₁) := by ring
      _ = -(η * Real.exp (-T₁ / 2)) + 2 * Real.exp (-T₁) := by rw [hhalf]
  have hv2 : mertensLagPrimitive T₂ ≤ -(η * Real.exp (-T₁ / 2)) + 2 * Real.exp (-T₁)
      + A * (T₁ - T₂) := by
    have := (abs_le.mp hint).2
    linarith
  rw [weilLagFunctionReal_eq_lagPrimitive hT₂]
  have hd : 0 ≤ (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T₂))
      * Real.exp (-T₂ / 2) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left hv2 (Real.exp_pos (T₂ / 2)).le
  linarith

/-- **Low prime lags.**  Unconditionally, some `η > 0` has `a_p ≤ -η` for infinitely many primes. -/
theorem exists_frequently_prime_integerLag_le_neg :
    ∃ η : ℝ, 0 < η ∧ ∃ᶠ p : ℕ in atTop, p.Prime ∧ integerLag p ≤ -η := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨η, hη, hL⟩ := exists_weilLagFunctionReal_le_neg_of_riemannHypothesis hRH
    refine ⟨η / 4, by positivity, ?_⟩
    have hΘ : zeroReSup < 3 / 5 := by
      have h := zeroReSup_le_of_forall_re_le (b := 1 / 2) fun q =>
        (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
      linarith
    obtain ⟨C, hC0, hC⟩ := exists_abs_mertensLagDensity_le_exp hΘ
    -- the loss terms vanish
    have hloss : ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-L / 2)
        + 2 * C * Real.exp (2 / 5) * Real.exp (-(3 / 10) * L) ≤ η / 4 := by
      have h1 : Tendsto (fun L : ℝ => 2 * Real.exp (-L / 2)
          + 2 * C * Real.exp (2 / 5) * Real.exp (-(3 / 10) * L)) atTop (𝓝 0) := by
        have ha : Tendsto (fun L : ℝ => Real.exp (-L / 2)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (by
            have := tendsto_id.const_mul_atTop_of_neg (show -(1 / 2 : ℝ) < 0 by norm_num)
            refine this.congr fun L => ?_; simp; ring)
        have hb : Tendsto (fun L : ℝ => Real.exp (-(3 / 10) * L)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
        simpa using (ha.const_mul 2).add (hb.const_mul (2 * C * Real.exp (2 / 5)))
      exact h1.eventually (ge_mem_nhds (by positivity))
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_exists_prime_log_near.and
      (hloss.and (eventually_ge_atTop (max (Real.log (N + 1) + 1) 3))))
    obtain ⟨L, hLL₀, hΦL⟩ := hL L₀
    obtain ⟨⟨p, hp, h1, h2⟩, hlossL, hLbig⟩ := hL₀ L hLL₀
    have hL2 : 3 ≤ L := le_trans (le_max_right _ _) hLbig
    have hT₂ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hsm : 2 * Real.exp (-(2 / 5) * L) ≤ 1 := by
      have : Real.exp (-(2 / 5) * L) ≤ Real.exp (-(6 / 5)) := Real.exp_le_exp.mpr (by linarith)
      have h45 : Real.exp (-(6 / 5)) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.add_one_le_exp (6 / 5 : ℝ); linarith
      linarith
    have hT21 : L - 1 ≤ Real.log p := by linarith
    set A : ℝ := C * Real.exp ((3 / 5 - 1) * (L - 1)) with hA
    have hAb : ∀ s ∈ Icc (Real.log p) L, |mertensLagDensity s| ≤ A := by
      intro s hs
      refine (hC s (le_trans hT₂.le hs.1)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr ?_) hC0)
      nlinarith [hs.1]
    have htr := weilLagFunctionReal_le_of_transfer hT₂ h2 hAb hΦL
    refine ⟨p, ?_, hp, ?_⟩
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have : Real.log (N + 1) ≤ Real.log p := by
        have := le_trans (le_max_left _ _) hLbig; linarith
      have h3 : ((N : ℝ) + 1) ≤ p := (Real.log_le_log_iff (by positivity) hp0).mp this
      exact_mod_cast (show (N : ℝ) ≤ p by linarith)
    · unfold integerLag
      -- bound the three terms
      have hE := Real.exp_pos (Real.log p / 2)
      have he1 : Real.exp (Real.log p / 2) * Real.exp (-L / 2) ≥ 1 / 2 := by
        rw [← Real.exp_add]
        have : -(1 / 2 : ℝ) ≤ Real.log p / 2 + -L / 2 := by linarith
        have h := Real.exp_le_exp.mpr this
        have h12 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
          rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
          linarith [exp_one_half_le_two_lag]
        linarith
      have he2 : Real.exp (Real.log p / 2) * Real.exp (-L) ≤ Real.exp (-L / 2) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      have he3 : Real.exp (Real.log p / 2) * (A * (L - Real.log p))
          ≤ 2 * C * Real.exp (2 / 5) * Real.exp (-(3 / 10) * L) := by
        have hd : L - Real.log p ≤ 2 * Real.exp (-(2 / 5) * L) := by linarith
        have hA0 : 0 ≤ A := by rw [hA]; positivity
        have hpL : Real.exp (Real.log p / 2) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
        have h5 : Real.exp (L / 2) * Real.exp ((3 / 5 - 1) * (L - 1)) * Real.exp (-(2 / 5) * L)
            = Real.exp (2 / 5) * Real.exp (-(3 / 10) * L) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        calc Real.exp (Real.log p / 2) * (A * (L - Real.log p))
            ≤ Real.exp (L / 2) * (A * (2 * Real.exp (-(2 / 5) * L))) := by
              apply mul_le_mul hpL _ (by nlinarith) (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left hd hA0
          _ = 2 * C * (Real.exp (L / 2) * Real.exp ((3 / 5 - 1) * (L - 1))
                * Real.exp (-(2 / 5) * L)) := by rw [hA]; ring
          _ = 2 * C * Real.exp (2 / 5) * Real.exp (-(3 / 10) * L) := by rw [h5]; ring
      have hexp : Real.exp (Real.log p / 2) * (-(η * Real.exp (-L / 2)) + 2 * Real.exp (-L)
          + A * (L - Real.log p))
          = -(η * (Real.exp (Real.log p / 2) * Real.exp (-L / 2)))
            + 2 * (Real.exp (Real.log p / 2) * Real.exp (-L))
            + Real.exp (Real.log p / 2) * (A * (L - Real.log p)) := by ring
      rw [hexp] at htr
      have h6 : η * (1 / 2) ≤ η * (Real.exp (Real.log p / 2) * Real.exp (-L / 2)) :=
        mul_le_mul_of_nonneg_left he1 hη.le
      linarith
  · refine ⟨1, one_pos, ?_⟩
    by_contra hno
    rw [Filter.not_frequently] at hno
    apply hRH
    refine riemannHypothesis_of_primeLag_ge (M := 1) (hno.mono fun p hp hpr => ?_)
    by_contra h
    exact hp ⟨hpr, by linarith [not_le.mp h]⟩

/-- **Prime lags oscillate.**  Unconditionally `a_p > a₁ - ε` for infinitely many primes (every
`ε > 0`) and `a_p ≤ -η` for infinitely many primes (some `η > 0`). -/
theorem prime_integerLag_oscillation :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ p : ℕ in atTop, p.Prime ∧ poleSharpConstant - ε < integerLag p) ∧
      ∃ η : ℝ, 0 < η ∧ ∃ᶠ p : ℕ in atTop, p.Prime ∧ integerLag p ≤ -η :=
  ⟨fun _ hε => frequently_prime_integerLag_gt hε, exists_frequently_prime_integerLag_le_neg⟩

end

end RHTower
