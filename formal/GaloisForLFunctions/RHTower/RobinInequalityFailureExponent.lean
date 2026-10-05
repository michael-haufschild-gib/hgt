import GaloisForLFunctions.RHTower.MertensRemainderExponentLaw
import GaloisForLFunctions.RHTower.RobinSharpConstant

/-!
# Robin's inequality fails with a power margin when RH fails

If `Θ > ½` then for every `½ ≤ b < Θ` there are infinitely many `n` with
`log(σ(n)/n) > γ + log log log n + (log n)^{b-1}`.

At the extremal number `N_x` the Robin defect is at least `G(log x) - 11/(√x log x)` for large `x`:
the tangent bound for `log log` removes the second-order term, the prime tails and `ψ - θ` are
nonnegative, and `θ((3/2)√x)`, the exponent deficit and the higher exponents are
`O(1/(√x log x))`.  At the points where `G(T) > e^{(b'-1)T}`, `b < b' < Θ`, this beats
`(log N_x)^{b-1} ≤ 2x^{b-1}`.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (sigma)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **The Robin defect at `N_x` dominates the Mertens remainder**: for large `x`,
`D(N_x) √x log x ≥ G(log x) √x log x - 11`. -/
theorem eventually_robinExtremalDefect_scaled_ge_remainder :
    ∀ᶠ x : ℝ in atTop, mertensErrorRemainder (Real.log x) * (Real.sqrt x * Real.log x) - 11
      ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x) := by
  have E6 := (tendsto_order.1 (tendsto_theta_mul_sqrt_div (c := 3 / 2) (by norm_num))).2
    (3 / 2 + 1) (by norm_num)
  have E7 := (tendsto_order.1 tendsto_two_log_mul_cube_root_div_sqrt).2 1 (by norm_num)
  have E8 := eventually_sum_prime_inv_sq_scaled_le (c := 5 / 4) (δ := 1) (by norm_num)
    (by norm_num)
  have E9 := (tendsto_order.1 tendsto_eight_div_cube_root_sq_mul).2 1 (by norm_num)
  filter_upwards [eventually_two_le_robinExponent, eventually_ge_atTop (10000 : ℝ),
    E6, E7, E8, E9, eventually_two_fifths_le_theta] with x h2 hx e6 e7 e8 e9 e10
  have hx0 : 0 < x := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx : 3 / 2 ≤ Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hyx : 3 / 2 * Real.sqrt x ≤ x :=
    calc 3 / 2 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsx hsx0.le
      _ = x := Real.mul_self_sqrt hx0.le
  have hb := robinExtremalDefect_scaled_ge (c₁ := 5 / 4) (c₂ := 3 / 2) hx (by norm_num) h2
    (by norm_num) (by nlinarith) hyx e10
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hD0 : 0 < Real.sqrt x * Real.log x := mul_pos hsx0 hL0
  have hΔ : 0 ≤ (mertensProductError x - mertensError x) * (Real.sqrt x * Real.log x) :=
    mul_nonneg (mertensProductError_sub_mem (by linarith)).1 hD0.le
  have hψθ : 0 ≤ (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x :=
    div_nonneg (by linarith [Chebyshev.theta_le_psi x]) hsx0.le
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
    (fun p : ℕ => 5 / 4 * Real.sqrt x < p), 1 / (p : ℝ) ^ 2 with hS
  have hS0 : 0 ≤ S * (Real.sqrt x * Real.log x) := by
    have : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
    positivity
  have hfac : 1 + 2 / ((5 / 4) ^ 2 * x) ≤ 2 := by
    have : 2 / ((5 / 4) ^ 2 * x) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hprod : (1 + 2 / ((5 / 4) ^ 2 * x)) * S * (Real.sqrt x * Real.log x) ≤ 6 := by
    have h1 : (1 + 2 / ((5 / 4) ^ 2 * x)) * S * (Real.sqrt x * Real.log x)
        = (1 + 2 / ((5 / 4) ^ 2 * x)) * (S * (Real.sqrt x * Real.log x)) := by ring
    rw [h1]
    have h3 : S * (Real.sqrt x * Real.log x) ≤ 2 / (5 / 4) + 1 := e8
    have h4 : (1 + 2 / ((5 / 4) ^ 2 * x)) * (S * (Real.sqrt x * Real.log x))
        ≤ 2 * (2 / (5 / 4) + 1) := mul_le_mul hfac h3 hS0 (by norm_num)
    norm_num at h4
    linarith
  linarith only [hb, hΔ, hψθ, e6, e7, hprod, e9]

/-- **Robin's inequality fails with a power margin.**  If `½ ≤ b < Θ`, then
`D(n) > (log n)^{b-1}` for infinitely many `n`. -/
theorem frequently_rpow_lt_robinDefectOf {b : ℝ} (hb : 1 / 2 ≤ b) (hbΘ : b < zeroReSup) :
    ∃ᶠ n : ℕ in atTop, Real.log n ^ (b - 1) < robinDefectOf n := by
  have hb1 : b < 1 := lt_of_lt_of_le hbΘ zeroReSup_le_one
  set b' := (b + zeroReSup) / 2 with hb'
  have hbb' : b < b' := by rw [hb']; linarith
  have hb'Θ : b' < zeroReSup := by rw [hb']; linarith
  have hgrow : ∀ᶠ T : ℝ in atTop, 13 ≤ Real.exp ((b' - b) * T) := by
    have : Tendsto (fun T : ℝ => Real.exp ((b' - b) * T)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
    exact this.eventually (eventually_ge_atTop 13)
  have hlow := Real.tendsto_exp_atTop.eventually
    (eventually_robinExtremalDefect_scaled_ge_remainder.and
      ((eventually_ge_atTop (16 : ℝ)).and eventually_two_fifths_le_theta))
  have hfreq := ((frequently_exp_lt_mertensErrorRemainder (by linarith) hb'Θ).and_eventually
    (hlow.and (hgrow.and (eventually_ge_atTop (1 : ℝ)))))
  -- `N_x → ∞` along `x = e^T`
  have hN : Tendsto (fun T : ℝ => robinExtremalAt (Real.exp T)) atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine tendsto_atTop_mono' atTop ?_ (Real.tendsto_exp_atTop.atTop_mul_const
      (show (0 : ℝ) < 2 / 5 by norm_num))
    filter_upwards [Real.tendsto_exp_atTop.eventually
      ((eventually_ge_atTop (16 : ℝ)).and eventually_two_fifths_le_theta)] with T ⟨hT16, hθT⟩
    have h1 := theta_le_log_robinExtremalAt (x := Real.exp T) (by linarith)
    have hNpos : (0 : ℝ) < robinExtremalAt (Real.exp T) := by exact_mod_cast robinExtremal_pos _ _
    have h2 := Real.log_le_sub_one_of_pos hNpos
    linarith
  refine hN.frequently (hfreq.mono fun T ⟨hG, ⟨hD, hx16, hθx⟩, hg, hT1⟩ => ?_)
  set x := Real.exp T with hxdef
  have hx0 : 0 < x := Real.exp_pos T
  have hlogx : Real.log x = T := Real.log_exp T
  rw [hlogx] at hD
  have hT0 : 0 < T := by linarith
  have hsx : Real.sqrt x = Real.exp (T / 2) := by rw [hxdef, Real.exp_half]
  have hD0 : 0 < Real.sqrt x * T := by rw [hsx]; positivity
  -- `D(N_x) > e^{(b'-1)T} - 11 e^{-T/2}/T`
  have hDx : Real.exp ((b' - 1) * T) - 11 / (Real.sqrt x * T) < robinExtremalDefect x := by
    have h1 : (mertensErrorRemainder T - 11 / (Real.sqrt x * T)) * (Real.sqrt x * T)
        = mertensErrorRemainder T * (Real.sqrt x * T) - 11 := by field_simp
    have h2 : mertensErrorRemainder T - 11 / (Real.sqrt x * T) ≤ robinExtremalDefect x := by
      have := (mul_le_mul_iff_of_pos_right hD0).mp (h1 ▸ hD)
      exact this
    linarith
  -- the target is at most `2 e^{(b-1)T}`
  have hu := theta_le_log_robinExtremalAt (x := x) (by linarith)
  have hu0 : 2 / 5 * x ≤ Real.log (robinExtremalAt x : ℝ) := le_trans hθx hu
  have htarget : Real.log (robinExtremalAt x : ℝ) ^ (b - 1) ≤ 2 * Real.exp ((b - 1) * T) := by
    have h1 : Real.log (robinExtremalAt x : ℝ) ^ (b - 1) ≤ (2 / 5 * x) ^ (b - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hu0 (by linarith)
    have h2 : (2 / 5 * x) ^ (b - 1) = (2 / 5 : ℝ) ^ (b - 1) * Real.exp ((b - 1) * T) := by
      rw [Real.mul_rpow (by norm_num) hx0.le, rpow_sub_one_eq_exp_log hx0, hlogx]
    have h3 : (2 / 5 : ℝ) ^ (b - 1) ≤ 2 := by
      have h4 : (2 / 5 : ℝ) ^ (b - 1) ≤ (2 / 5 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      have h5 : (2 / 5 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity)
          (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_right h3 (Real.exp_pos ((b - 1) * T)).le
    linarith
  -- comparison of the exponentials
  have hcmp : 2 * Real.exp ((b - 1) * T) + 11 / (Real.sqrt x * T)
      ≤ Real.exp ((b' - 1) * T) := by
    have h1 : Real.exp ((b' - 1) * T) = Real.exp ((b' - b) * T) * Real.exp ((b - 1) * T) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 11 / (Real.sqrt x * T) ≤ 11 * Real.exp ((b - 1) * T) := by
      rw [div_le_iff₀ hD0, hsx]
      have h3 : Real.exp (-(T / 2)) ≤ Real.exp ((b - 1) * T) := Real.exp_le_exp.mpr (by nlinarith)
      have h4 : Real.exp (-(T / 2)) * Real.exp (T / 2) = 1 := by rw [← Real.exp_add]; simp
      have h5 : 1 ≤ Real.exp ((b - 1) * T) * (Real.exp (T / 2) * T) := by
        have := mul_le_mul_of_nonneg_right h3 (show 0 ≤ Real.exp (T / 2) * T by positivity)
        nlinarith [Real.exp_pos (T / 2)]
      linarith
    rw [h1]
    have := mul_le_mul_of_nonneg_right hg (Real.exp_pos ((b - 1) * T)).le
    linarith
  show Real.log (robinExtremalAt x : ℝ) ^ (b - 1) < robinDefectOf (robinExtremalAt x)
  have e : robinDefectOf (robinExtremalAt x) = robinExtremalDefect x := rfl
  rw [e]
  linarith

end

end RHTower
