import GaloisForLFunctions.ArithmeticPositiveDuality.ADiscreteBeurlingOneOff

/-!
# A discrete Beurling one-off that crosses the critical line

The discrete one-off of `ADiscreteBeurlingOneOff` takes the quantiles of the continuous count `W`
(`#{k : t_k ≤ x} = ⌊W(x)⌋`); its prime squares then blow the Euler product up at `s = 1/2`.
Here the quantiles are taken of the count with Riemann's prime-square correction,

`V(x) = W(x) − W(x/2)/2 + W(min(x, u₀)/2)/2`,

the correction `−W(x/2)/2` switched on beyond a threshold `u₀`, where the corrected density
`w(u) − w(u/2)/4` is positive (`correctedDensity_pos`).

* **Positive discrete primes** (`V_lt`, `catom_strictMono`, `catomCount_eq`). `V` is strictly
  increasing, so `t_k` with `V(t_k) = k + 1` are distinct positive atoms with `#{t_k ≤ x} = ⌊V(x)⌋`;
  the discrete primes are `p_k = e^{t_k} > 1`.
* **The count carries the prime squares** (`abs_cerror_le`). `|N(x) − (W(x) − W(x/2)/2)| ≤ M`.
* **Euler logarithm** (`cEulerLog_eq`). On `Re s > 1`,
  `Σ_k −log(1 − p_k^{-s}) = L(s) − L(4s)/4 + sΛ(s) + sΛ(2s) + R₃(s)`, `L(z) = ∫ e^{-zu} w(u) du`,
  `Λ` the Laplace transform of the bounded discrepancy, `R₃` the prime-cube remainder.
* **Continuation across the critical line** (`differentiableOn_cContinuation`,
  `cContinuation_eq_zero_iff`, `cZeros_right_eq_pair`). The Euler product equals
  `ζ_c(s) exp(−L(4s)/4 + sΛ(s) + sΛ(2s) + R₃(s))`, holomorphic on `Re s > 1/3`, `s ≠ 1`, where its
  zeros are exactly the off-line pair `(1 − μ) ± iγ`. It is holomorphic and zero-free on the whole
  critical line (`cContinuation_critical_line`), and finite at `s = 1/2`
  (`tendsto_norm_cContinuation_half`), where the uncorrected one-off diverges.

So a discrete Euler product with positive prime atoms can carry a finite off-line layer and continue
holomorphically, without zeros, across `Re s = 1/2`: the obstruction in the uncorrected one-off is
the prime squares, and the second Möbius term of Riemann's prime count removes it.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

noncomputable section

open GaloisForLFunctions.HTGeometry RHTower.BeurlingOverRegularIntegers

/-! ### General lemmas -/

/-- The Laplace transform of a function bounded by `M` is holomorphic on `Re s > 0`. -/
theorem differentiableOn_boundedLaplace_of_le {E : ℝ → ℝ} (hEm : Measurable E) {M : ℝ}
    (hM : 0 < M) (hE : ∀ x, |E x| ≤ M) :
    DifferentiableOn ℂ (boundedLaplace E) {s : ℂ | 0 < s.re} := by
  have hE' : ∀ x, |E x / M| ≤ 1 := fun x => by
    rw [abs_div, abs_of_pos hM, div_le_one hM]; exact hE x
  have h := differentiableOn_boundedLaplace (hEm.div_const M) hE'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have heq : boundedLaplace E = fun s => (M : ℂ) * boundedLaplace (fun x => E x / M) s := by
    funext s
    unfold boundedLaplace
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    push_cast
    field_simp
  rw [heq]
  exact h.const_mul _

/-- If `k + 1 ≤ C_b e^{b t_k}` for every `b > 1`, then `Σ_k e^{-a t_k} < ∞` for every `a > 1`. -/
theorem summable_exp_of_count {t : ℕ → ℝ}
    (hC : ∀ b : ℝ, 1 < b → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * Real.exp (b * t k))
    {a : ℝ} (ha : 1 < a) : Summable fun k => Real.exp (-(a * t k)) := by
  set b := (1 + a) / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  have hab : 1 < a / b := by rw [lt_div_iff₀ (by linarith)]; linarith
  obtain ⟨C, hC0, hCk⟩ := hC b hb1
  have hk : ∀ k : ℕ, Real.exp (-(b * t k)) ≤ C / ((k : ℝ) + 1) := by
    intro k
    have h := hCk k
    rw [le_div_iff₀ (by positivity)]
    have he : Real.exp (-(b * t k)) * Real.exp (b * t k) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(b * t k))]
  have hsum : Summable fun k : ℕ => C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith : -(a / b) < -1))
    refine (h.mul_left (C ^ (a / b))).congr fun k => ?_
    push_cast
    rfl
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hsum
  have hexp : Real.exp (-(a * t k)) = Real.exp (-(b * t k)) ^ (a / b) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [hexp]
  calc Real.exp (-(b * t k)) ^ (a / b) ≤ (C / ((k : ℝ) + 1)) ^ (a / b) :=
        Real.rpow_le_rpow (Real.exp_pos _).le (hk k) (by positivity)
    _ = C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
        rw [Real.div_rpow hC0 (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- The cubic Taylor remainder of `−log(1 − x)`. -/
theorem norm_neg_log_sub_sub_le {x : ℂ} (hx : ‖x‖ < 1) :
    ‖-Complex.log (1 - x) - x - x ^ 2 / 2‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ / 3 := by
  have hx' : ‖-x‖ < 1 := by rwa [norm_neg]
  have h := Complex.norm_log_sub_logTaylor_le 2 hx'
  have hT : Complex.logTaylor (2 + 1) (-x) = -x - x ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hT, norm_neg] at h
  have h' : -Complex.log (1 - x) - x - x ^ 2 / 2 =
      -(Complex.log (1 + -x) - (-x - x ^ 2 / 2)) := by
    rw [← sub_eq_add_neg]; ring
  rw [h', norm_neg]
  refine h.trans (le_of_eq ?_)
  norm_num

/-- The prime-cube part `R₃(s) = Σ_k (−log(1 − x_k) − x_k − x_k²/2)`, `x_k = e^{-st_k}`. -/
def primeCubeRemainder (t : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' k, (-Complex.log (1 - cexp (-(s * t k))) - cexp (-(s * t k)) - cexp (-(s * t k)) ^ 2 / 2)

theorem norm_primeCubeTerm_le {t : ℝ} (ht : 0 < t) {σ₀ : ℝ} {z : ℂ}
    (hz : σ₀ ≤ z.re) {q : ℝ} (hq : Real.exp (-(σ₀ * t)) ≤ q) (hq1 : q < 1) :
    ‖-Complex.log (1 - cexp (-(z * t))) - cexp (-(z * t)) - cexp (-(z * t)) ^ 2 / 2‖ ≤
      Real.exp (-(3 * σ₀ * t)) * (1 - q)⁻¹ / 3 := by
  set x := cexp (-(z * t)) with hx
  have hxn : ‖x‖ = Real.exp (-(z.re * t)) := norm_cexp_neg_mul z t
  have hxle : ‖x‖ ≤ Real.exp (-(σ₀ * t)) := by
    rw [hxn]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hx1 : ‖x‖ < 1 := by linarith
  refine (norm_neg_log_sub_sub_le hx1).trans ?_
  have hq0 : 0 < 1 - q := by linarith
  have hcube : ‖x‖ ^ 3 ≤ Real.exp (-(3 * σ₀ * t)) := by
    calc ‖x‖ ^ 3 ≤ Real.exp (-(σ₀ * t)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hxle 3
      _ = Real.exp (-(3 * σ₀ * t)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : (1 - ‖x‖)⁻¹ ≤ (1 - q)⁻¹ := inv_anti₀ hq0 (by linarith)
  have hn1 : 0 ≤ (1 - ‖x‖)⁻¹ := inv_nonneg.mpr (by linarith)
  calc ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ / 3 ≤ Real.exp (-(3 * σ₀ * t)) * (1 - q)⁻¹ / 3 := by
        gcongr

/-- **The prime-cube remainder is holomorphic on `Re s > 1/3`.** -/
theorem differentiableOn_primeCubeRemainder {t : ℕ → ℝ} (ht : ∀ k, 0 < t k)
    (hmono : ∀ k, t 0 ≤ t k) (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) :
    DifferentiableOn ℂ (primeCubeRemainder t) {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have hs' : 1 / 3 < s.re := hs
  set σ₀ : ℝ := (1 / 3 + s.re) / 2 with hσ₀
  have hσ₀0 : 0 < σ₀ := by linarith
  set q : ℝ := Real.exp (-(σ₀ * t 0)) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := ht 0
    nlinarith
  set U : Set ℂ := {z : ℂ | σ₀ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by show σ₀ < s.re; linarith
  have hdiff : ∀ k, DifferentiableOn ℂ (fun z : ℂ => -Complex.log (1 - cexp (-(z * t k))) -
      cexp (-(z * t k)) - cexp (-(z * t k)) ^ 2 / 2) U := by
    intro k z hz
    have hz' : σ₀ < z.re := hz
    have hre : 0 < (1 - cexp (-(z * t k))).re := by
      have h1 : (cexp (-(z * t k))).re ≤ ‖cexp (-(z * t k))‖ := Complex.re_le_norm _
      have h2 : ‖cexp (-(z * t k))‖ < 1 := by
        rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
        have := ht k
        nlinarith
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hexp : DifferentiableAt ℂ (fun z : ℂ => cexp (-(z * t k))) z := by fun_prop
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_const _ |>.sub hexp).clog
      (Complex.mem_slitPlane_iff.mpr (Or.inl hre))).neg.sub hexp).sub ((hexp.pow 2).div_const 2)
  have hbound : ∀ k (z : ℂ), z ∈ U →
      ‖-Complex.log (1 - cexp (-(z * t k))) - cexp (-(z * t k)) - cexp (-(z * t k)) ^ 2 / 2‖ ≤
        Real.exp (-(3 * σ₀ * t k)) * (1 - q)⁻¹ / 3 := by
    intro k z hz
    have hz' : σ₀ < z.re := hz
    refine norm_primeCubeTerm_le (ht k) hz'.le ?_ hq1
    rw [hq]
    exact Real.exp_le_exp.mpr (by nlinarith [hmono k])
  have hsumU : Summable fun k => Real.exp (-(3 * σ₀ * t k)) * (1 - q)⁻¹ / 3 :=
    ((hsum (3 * σ₀) (by linarith)).mul_right _).div_const _
  have hD := differentiableOn_tsum_of_summable_norm hsumU hdiff hUo hbound
  exact (hD.differentiableAt (hUo.mem_nhds hsU)).differentiableWithinAt

/-- **The Euler logarithm splits** into primes, prime squares and the prime-cube remainder on
`Re s > 1`. -/
theorem tsum_neg_log_eq_cube {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) (hmono : ∀ k, t 0 ≤ t k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) {s : ℂ} (hs : 1 < s.re) :
    ∑' k, -Complex.log (1 - cexp (-(s * t k))) =
      ∑' k, cexp (-(s * t k)) + (∑' k, cexp (-((2 * s) * t k))) / 2 +
        primeCubeRemainder t s := by
  have h1 : Summable fun k => cexp (-(s * t k)) := by
    refine Summable.of_norm ?_
    simp_rw [norm_cexp_neg_mul]
    exact hsum s.re hs
  have h2 : Summable fun k => cexp (-((2 * s) * t k)) := by
    refine Summable.of_norm ?_
    simp_rw [norm_cexp_neg_mul]
    have : (2 * s).re = 2 * s.re := by simp
    rw [this]
    exact hsum _ (by linarith)
  have hsq : ∀ k, cexp (-(s * t k)) ^ 2 / 2 = cexp (-((2 * s) * t k)) / 2 := fun k => by
    rw [← Complex.exp_nat_mul]; congr 2; push_cast; ring
  have h2' : Summable fun k => cexp (-(s * t k)) ^ 2 / 2 :=
    (h2.div_const 2).congr fun k => (hsq k).symm
  set q : ℝ := Real.exp (-(s.re * t 0)) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := ht 0
    nlinarith
  have h3 : Summable fun k => -Complex.log (1 - cexp (-(s * t k))) - cexp (-(s * t k)) -
      cexp (-(s * t k)) ^ 2 / 2 := by
    refine Summable.of_norm_bounded
      (((hsum (3 * s.re) (by linarith)).mul_right ((1 - q)⁻¹)).div_const 3) fun k => ?_
    have hle : Real.exp (-(s.re * t k)) ≤ q := by
      rw [hq]
      exact Real.exp_le_exp.mpr (by nlinarith [hmono k])
    have h := norm_primeCubeTerm_le (ht k) le_rfl hle hq1
    simpa only [mul_assoc] using h
  rw [primeCubeRemainder, ← tsum_div_const, ← tsum_congr hsq, ← h1.tsum_add h2',
    ← (h1.add h2').tsum_add h3]
  congr 1
  funext k
  ring

namespace Params

variable (P : Params)

/-! ### The density -/

theorem continuousOn_w : ContinuousOn P.w (Ioi 0) := by
  unfold w primeDensity primeNumerator
  exact ContinuousOn.div (Continuous.continuousOn (by fun_prop)) continuousOn_id
    fun t ht => ne_of_gt ht

/-- **Upper bound.** `w(t) ≤ 5e^t/t` for `t > 0`. -/
theorem w_le {t : ℝ} (ht : 0 < t) : P.w t ≤ 5 * Real.exp t / t := by
  have hμ0 : 0 < P.μ := by linarith [P.hμ1]
  have e1 : Real.exp ((1 - P.μ) * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (-((3 * P.μ - 1 - P.ν) * t)) ≤ Real.exp t :=
    Real.exp_le_exp.mpr (by nlinarith [P.hlow])
  have e3 : Real.exp (-((3 * P.μ - 1 + P.ν) * t)) ≤ Real.exp t :=
    Real.exp_le_exp.mpr (by nlinarith [P.hhigh])
  have e4 : 0 ≤ Real.exp (-((4 * P.μ - 1) * t)) := (Real.exp_pos _).le
  have e5 : -(2 * Real.exp ((1 - P.μ) * t) * Real.cos (P.γ * t)) ≤ 2 * Real.exp t := by
    have hc : 0 ≤ 1 + Real.cos (P.γ * t) := by linarith [Real.neg_one_le_cos (P.γ * t)]
    nlinarith [mul_nonneg (Real.exp_pos ((1 - P.μ) * t)).le hc]
  have hN : primeNumerator P.μ P.ν P.γ t ≤ 5 * Real.exp t := by
    unfold primeNumerator
    linarith
  unfold w primeDensity
  exact div_le_div_of_nonneg_right hN ht.le

theorem c₀_le_one : (1 - Real.exp (-P.μ)) ^ 3 ≤ 1 := by
  have h0 : 0 ≤ 1 - Real.exp (-P.μ) := by
    have := Real.exp_le_one_iff.mpr (by linarith [P.hμ1] : -P.μ ≤ 0)
    linarith
  exact pow_le_one₀ h0 (by linarith [Real.exp_pos (-P.μ)])

/-- The threshold `u₀ = 2 log(3/c₀) + 2`, beyond which `w(u) > w(u/2)/4`. -/
def u₀ : ℝ := 2 * Real.log (3 / (1 - Real.exp (-P.μ)) ^ 3) + 2

theorem two_le_u₀ : 2 ≤ P.u₀ := by
  have h : 1 ≤ 3 / (1 - Real.exp (-P.μ)) ^ 3 := by
    rw [le_div_iff₀ P.c₀_pos]; linarith [P.c₀_le_one]
  have := Real.log_nonneg h
  unfold u₀
  linarith

/-- **The corrected density is positive beyond `u₀`.** -/
theorem correctedDensity_pos {u : ℝ} (hu : P.u₀ ≤ u) : 0 < P.w u - P.w (u / 2) / 4 := by
  set c := (1 - Real.exp (-P.μ)) ^ 3 with hc
  have hc0 : 0 < c := P.c₀_pos
  have hu2 : 2 ≤ u := le_trans P.two_le_u₀ hu
  have hu0 : 0 < u := by linarith
  set y := Real.exp (u / 2) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hyy : Real.exp u = y * y := by rw [hy, ← Real.exp_add]; congr 1; ring
  have hcy : 3 ≤ c * y := by
    have h3 : 3 / c ≤ y := by
      have hlog : Real.log (3 / c) ≤ u / 2 := by unfold u₀ at hu; rw [← hc] at hu; linarith
      calc 3 / c = Real.exp (Real.log (3 / c)) := (Real.exp_log (by positivity)).symm
        _ ≤ y := Real.exp_le_exp.mpr hlog
    rwa [div_le_iff₀ hc0, mul_comm] at h3
  have hlow := P.w_ge (t := u) (by linarith)
  have hup := P.w_le (t := u / 2) (by linarith)
  rw [← hc, hyy] at hlow
  rw [← hy] at hup
  have key : 5 * y / (u / 2) / 4 < c * (y * y) / u := by
    rw [div_div, div_lt_div_iff₀ (by positivity) hu0]
    nlinarith [mul_le_mul_of_nonneg_left hcy (mul_pos hy0 hu0).le, mul_pos hy0 hu0]
  linarith

/-! ### The corrected count -/

/-- **The corrected count** `V(x) = W(x) − W(x/2)/2 + W(min(x,u₀)/2)/2`. -/
def V (x : ℝ) : ℝ := P.W x - P.W (x / 2) / 2 + P.W (min x P.u₀ / 2) / 2

theorem V_of_le {x : ℝ} (hx : x ≤ P.u₀) : P.V x = P.W x := by
  rw [V, min_eq_left hx]; ring

theorem V_of_ge {x : ℝ} (hx : P.u₀ ≤ x) :
    P.V x = P.W x - P.W (x / 2) / 2 + P.W (P.u₀ / 2) / 2 := by
  rw [V, min_eq_right hx]

theorem W_half_le (x : ℝ) : P.W (x / 2) ≤ P.W x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [P.W_of_nonpos (by linarith), P.W_of_nonpos hx]
  · exact P.W_le_W (by linarith)

theorem half_W_le_V (x : ℝ) : P.W x / 2 ≤ P.V x := by
  have h1 := P.W_half_le x
  have h2 := P.W_nonneg (min x P.u₀ / 2)
  rw [V]; linarith

theorem V_le_W (x : ℝ) : P.V x ≤ P.W x := by
  have h1 : P.W (min x P.u₀ / 2) ≤ P.W (x / 2) := P.W_le_W (by linarith [min_le_left x P.u₀])
  rw [V]; linarith

theorem V_nonneg (x : ℝ) : 0 ≤ P.V x := by
  have := P.half_W_le_V x
  have := P.W_nonneg x
  linarith

theorem V_of_nonpos {x : ℝ} (hx : x ≤ 0) : P.V x = 0 := by
  rw [P.V_of_le (by linarith [P.two_le_u₀]), P.W_of_nonpos hx]

/-- `W(b) − W(a) = ∫_a^b w` for `0 < a ≤ b`. -/
theorem W_sub_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    P.W b - P.W a = ∫ u in a..b, P.w u := by
  rw [P.W_eq_intervalIntegral (by linarith), P.W_eq_intervalIntegral ha.le,
    intervalIntegral.integral_interval_sub_left (P.intervalIntegrable_wt le_rfl (by linarith))
      (P.intervalIntegrable_wt le_rfl ha.le)]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hab] at hu
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from lt_of_lt_of_le ha hu.1)]

/-- **Beyond `u₀`, `V` grows by the corrected density**: `V(b) − V(a) = ∫_a^b (w(u) − w(u/2)/4)`. -/
theorem V_sub_of_ge {a b : ℝ} (ha : P.u₀ ≤ a) (hab : a ≤ b) :
    P.V b - P.V a = ∫ u in a..b, (P.w u - P.w (u / 2) / 4) := by
  have ha0 : 0 < a := by linarith [P.two_le_u₀]
  have hcw : ContinuousOn P.w (uIcc a b) :=
    P.continuousOn_w.mono fun u hu => by
      rw [uIcc_of_le hab] at hu; exact lt_of_lt_of_le ha0 hu.1
  have hcw2 : ContinuousOn (fun u => P.w (u / 2)) (uIcc a b) :=
    P.continuousOn_w.comp (continuousOn_id.div_const 2) fun u hu => by
      rw [uIcc_of_le hab] at hu; show 0 < u / 2; linarith [hu.1]
  have hi1 : IntervalIntegrable P.w volume a b := hcw.intervalIntegrable
  have hi2 : IntervalIntegrable (fun u => P.w (u / 2) / 4) volume a b :=
    (hcw2.div_const 4).intervalIntegrable
  have hhalf : P.W (b / 2) - P.W (a / 2) = (∫ u in a..b, P.w (u / 2)) / 2 := by
    rw [P.W_sub_eq (by linarith) (by linarith), intervalIntegral.integral_comp_div
      (fun u => P.w u) (two_ne_zero : (2 : ℝ) ≠ 0), smul_eq_mul]
    ring
  rw [P.V_of_ge (le_trans ha hab), P.V_of_ge ha, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_div, ← P.W_sub_eq ha0 hab]
  linarith

/-- **`V` is strictly increasing on `[0, ∞)`.** -/
theorem V_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : P.V a < P.V b := by
  have hlow : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ P.u₀ → P.V a < P.V b := by
    intro a b ha hab hb
    rw [P.V_of_le (by linarith), P.V_of_le hb]
    exact P.W_lt ha hab
  have hhigh : ∀ {a b : ℝ}, P.u₀ ≤ a → a < b → P.V a < P.V b := by
    intro a b ha hab
    have h := P.V_sub_of_ge ha hab.le
    have hpos : 0 < ∫ u in a..b, (P.w u - P.w (u / 2) / 4) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_
        (fun u hu => P.correctedDensity_pos (by linarith [hu.1])) hab
      have ha0 : 0 < a := by linarith [P.two_le_u₀]
      have hc : ContinuousOn (fun u => P.w u - P.w (u / 2) / 4) (uIcc a b) := by
        refine (P.continuousOn_w.mono fun u hu => ?_).sub
          ((P.continuousOn_w.comp (continuousOn_id.div_const 2) fun u hu => ?_).div_const 4)
        · rw [uIcc_of_le hab.le] at hu; exact lt_of_lt_of_le ha0 hu.1
        · rw [uIcc_of_le hab.le] at hu; show 0 < u / 2; linarith [hu.1]
      exact hc.intervalIntegrable
    linarith
  by_cases hb : b ≤ P.u₀
  · exact hlow ha hab hb
  · push Not at hb
    by_cases ha' : P.u₀ ≤ a
    · exact hhigh ha' hab
    · push Not at ha'
      exact (hlow ha ha' le_rfl).trans (hhigh le_rfl hb)

theorem V_le_V {a b : ℝ} (hab : a ≤ b) : P.V a ≤ P.V b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [P.V_of_nonpos ha]; exact P.V_nonneg b
  · rcases hab.lt_or_eq with h | h
    · exact (P.V_lt ha.le h).le
    · rw [h]

theorem continuousOn_V {M : ℝ} (hM : 0 ≤ M) : ContinuousOn P.V (Icc 0 M) := by
  have hW := P.continuousOn_W hM
  have h2 : ContinuousOn (fun x => P.W (x / 2)) (Icc 0 M) :=
    hW.comp (continuousOn_id.div_const 2) fun x hx =>
      ⟨by show 0 ≤ x / 2; linarith [hx.1], by show x / 2 ≤ M; linarith [hx.1, hx.2]⟩
  have h3 : ContinuousOn (fun x => P.W (min x P.u₀ / 2)) (Icc 0 M) :=
    hW.comp ((continuous_id.min continuous_const).continuousOn.div_const 2) fun x hx => by
      have hu := P.two_le_u₀
      have h1 : min x P.u₀ ≤ x := min_le_left _ _
      have h0 : 0 ≤ min x P.u₀ := le_min hx.1 (by linarith)
      exact ⟨by show 0 ≤ min x P.u₀ / 2; linarith,
        by show min x P.u₀ / 2 ≤ M; linarith [hx.2]⟩
  exact (hW.sub (h2.div_const 2)).add (h3.div_const 2)

/-! ### The corrected atoms -/

theorem exists_catom (k : ℕ) : ∃ x, 0 < x ∧ P.V x = k + 1 := by
  set c := (1 - Real.exp (-P.μ)) ^ 3 with hc
  have hc0 : 0 < c := P.c₀_pos
  set M : ℝ := 1 + 2 * (k + 1) / c with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 2 * ((k : ℝ) + 1) / c := by positivity
    linarith
  have hVM : (k : ℝ) + 1 ≤ P.V M := by
    have h := P.W_ge hM1
    have h2 := P.half_W_le_V M
    have : c * (M - 1) = 2 * ((k : ℝ) + 1) := by rw [hM]; field_simp; ring
    linarith
  obtain ⟨x, hx, hVx⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ M)
    (P.continuousOn_V (by linarith)) ⟨by rw [P.V_of_nonpos le_rfl]; positivity, hVM⟩
  refine ⟨x, ?_, hVx⟩
  rcases hx.1.lt_or_eq with h | h
  · exact h
  · rw [← h, P.V_of_nonpos le_rfl] at hVx
    have : (0 : ℝ) < k + 1 := by positivity
    linarith

/-- The `k`-th corrected discrete prime in logarithmic coordinate: `V(t_k) = k + 1`. -/
def catom (k : ℕ) : ℝ := (P.exists_catom k).choose

theorem catom_pos (k : ℕ) : 0 < P.catom k := (P.exists_catom k).choose_spec.1

theorem V_catom (k : ℕ) : P.V (P.catom k) = k + 1 := (P.exists_catom k).choose_spec.2

theorem catom_le_iff (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : P.catom k ≤ x ↔ (k : ℝ) + 1 ≤ P.V x := by
  constructor
  · intro h
    rw [← P.V_catom k]
    exact P.V_le_V h
  · intro h
    by_contra hlt
    push Not at hlt
    have := P.V_lt hx hlt
    rw [P.V_catom] at this
    linarith

theorem catom_strictMono : StrictMono P.catom := by
  intro j k hjk
  by_contra hle
  push Not at hle
  have h := P.V_le_V hle
  rw [P.V_catom, P.V_catom] at h
  have : (j : ℝ) < k := by exact_mod_cast hjk
  linarith

theorem catom_zero_le (k : ℕ) : P.catom 0 ≤ P.catom k :=
  P.catom_strictMono.monotone (Nat.zero_le k)

/-- **The corrected primes follow `V`**: `#{k : t_k ≤ x} = ⌊V(x)⌋`. -/
theorem catomCount_eq (x : ℝ) : atomCount P.catom x = (⌊P.V x⌋₊ : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [P.V_of_nonpos hx.le, atomCount]
    simp only [Nat.floor_zero, Nat.cast_zero]
    convert tsum_zero with k
    rw [if_neg (not_le.mpr (lt_trans hx (P.catom_pos k)))]
  · have hiff : ∀ k : ℕ, P.catom k ≤ x ↔ k < ⌊P.V x⌋₊ := fun k => by
      rw [P.catom_le_iff k hx, Nat.lt_iff_add_one_le, Nat.le_floor_iff (P.V_nonneg x)]
      push_cast
      rfl
    rw [atomCount, tsum_eq_sum (s := Finset.range ⌊P.V x⌋₊) fun k hk => by
      rw [if_neg (by rw [hiff]; simpa using hk)]]
    rw [Finset.sum_congr rfl fun k hk => if_pos ((hiff k).mpr (Finset.mem_range.mp hk))]
    simp

/-- The corrected primes have `Σ_k e^{-a t_k} < ∞` for `a > 1`. -/
theorem summable_exp_catom {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * P.catom k)) := by
  refine summable_exp_of_count (fun b hb => ?_) ha
  refine ⟨∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u,
    setIntegral_nonneg measurableSet_Ioi fun u hu => mul_nonneg (Real.exp_pos _).le (P.w_pos hu).le,
    fun k => ?_⟩
  have h := P.W_le_exp hb (P.catom k)
  have h2 := P.V_le_W (P.catom k)
  rw [P.V_catom] at h2
  linarith

/-! ### The discrepancy of the corrected count -/

/-- The discrepancy `N(x) − (W(x) − W(x/2)/2)` between the corrected discrete count and the
continuous count with its prime-square term. -/
def cerror (x : ℝ) : ℝ := atomCount P.catom x - (P.W x - P.W (x / 2) / 2)

/-- The bound `M = 1 + W(u₀/2)/2` of the discrepancy. -/
def cbound : ℝ := 1 + P.W (P.u₀ / 2) / 2

theorem cbound_pos : 0 < P.cbound := by
  have := P.W_nonneg (P.u₀ / 2)
  unfold cbound; linarith

/-- **The corrected count carries the prime squares**: `|N(x) − (W(x) − W(x/2)/2)| ≤ M`. -/
theorem abs_cerror_le (x : ℝ) : |P.cerror x| ≤ P.cbound := by
  have h1 := Nat.floor_le (P.V_nonneg x)
  have h2 := Nat.lt_floor_add_one (P.V x)
  have h3 := P.W_nonneg (min x P.u₀ / 2)
  have h4 : P.W (min x P.u₀ / 2) ≤ P.W (P.u₀ / 2) :=
    P.W_le_W (by linarith [min_le_right x P.u₀])
  have hV : P.V x = P.W x - P.W (x / 2) / 2 + P.W (min x P.u₀ / 2) / 2 := rfl
  rw [cerror, P.catomCount_eq, cbound, abs_le]
  constructor <;> linarith

theorem measurable_cerror : Measurable P.cerror := by
  have hW : Monotone P.W := fun a b h => P.W_le_W h
  have hW2 : Monotone fun x => P.W (x / 2) := fun a b h => P.W_le_W (by linarith)
  have hF : Monotone fun x => (⌊P.V x⌋₊ : ℝ) := fun a b h =>
    Nat.cast_le.mpr (Nat.floor_le_floor (P.V_le_V h))
  have heq : P.cerror = fun x => (⌊P.V x⌋₊ : ℝ) - (P.W x - P.W (x / 2) / 2) := by
    funext x
    rw [cerror, P.catomCount_eq]
  rw [heq]
  exact hF.measurable.sub (hW.measurable.sub (hW2.measurable.div_const 2))

/-! ### The continuous Laplace transform -/

/-- `L(z) = ∫_{u>0} e^{-zu} w(u) du`, the logarithm of `ζ_c` on `Re z > 1`. -/
def logZeta (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), cexp (-(z * u)) * (P.w u : ℂ)

/-- `L(z) = z ∫ e^{-zx} W(x) dx` on `Re z > 1`, the integrand integrable. -/
theorem logZeta_eq {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (P.W x : ℂ)) (Ioi 0) ∧
      P.logZeta z = z * ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (P.W x : ℂ) :=
  integral_cexp_density P.measurable_w (fun u hu => (P.w_pos hu).le) (by linarith)
    (P.integrableOn_exp_mul_w hz)

theorem measurable_W : Measurable P.W := Monotone.measurable fun _ _ h => P.W_le_W h

/-- **`L` is holomorphic on `Re z > 1`.** -/
theorem differentiableOn_logZeta : DifferentiableOn ℂ P.logZeta {z : ℂ | 1 < z.re} := by
  intro z₀ hz₀
  have hz₀' : 1 < z₀.re := hz₀
  set b : ℝ := (1 + z₀.re) / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  set C := ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u with hC
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.exp_pos _).le (P.w_pos hu).le
  set E : ℝ → ℝ := fun x => P.W x * Real.exp (-(b * x)) with hE
  have hEm : Measurable E := P.measurable_W.mul (by fun_prop)
  have hEb : ∀ x, |E x| ≤ C + 1 := by
    intro x
    have h := P.W_le_exp hb1 x
    have he : Real.exp (b * x) * Real.exp (-(b * x)) = 1 := by rw [← Real.exp_add]; simp
    have hW0 := P.W_nonneg x
    have hEx : E x ≤ C := by
      simp only [hE]
      nlinarith [Real.exp_pos (-(b * x)), Real.exp_pos (b * x)]
    rw [abs_of_nonneg (mul_nonneg hW0 (Real.exp_pos _).le)]
    linarith
  set g : ℂ → ℂ := fun z => z * boundedLaplace E (z - b) with hg
  have hU : IsOpen {z : ℂ | b < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀U : z₀ ∈ {z : ℂ | b < z.re} := by show b < z₀.re; linarith
  have heq : P.logZeta =ᶠ[𝓝 z₀] g := by
    filter_upwards [hU.mem_nhds hz₀U] with z hz
    have hz' : b < z.re := hz
    rw [(P.logZeta_eq (by linarith)).2, hg]
    congr 1
    unfold boundedLaplace
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hE]
    push_cast
    have hsp : cexp (-(z * x)) = cexp (-((z - b) * x)) * cexp (-(b * x)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hsp]; ring
  have hgd : DifferentiableAt ℂ g z₀ := by
    have hL := (differentiableOn_boundedLaplace_of_le hEm (by linarith : (0 : ℝ) < C + 1)
      hEb).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (z₀ - (b : ℂ)).re by simp; linarith))
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - (b : ℂ)) z₀ := differentiableAt_id.sub_const _
    have hcomp := DifferentiableAt.comp (𝕜 := ℂ) (g := boundedLaplace E)
      (f := fun z : ℂ => z - (b : ℂ)) z₀ hL hsub
    exact differentiableAt_id.mul hcomp
  exact (hgd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- **Half-scale Laplace transform.** `∫ e^{-zx} W(x/2) dx = 2 ∫ e^{-2zy} W(y) dy`. -/
theorem integral_cexp_W_half (z : ℂ) :
    ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (P.W (x / 2) : ℂ) =
      2 * ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (P.W y : ℂ) := by
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => cexp (-((2 * z) * y)) * (P.W y : ℂ)) 0 (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [mul_zero] at h
  rw [show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  rw [show (2 : ℂ) * ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (P.W y : ℂ) =
      (2 : ℝ) • ∫ y in Ioi (0 : ℝ), cexp (-((2 * z) * y)) * (P.W y : ℂ) by
    rw [Complex.real_smul]; push_cast; ring, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show (1 / 2 * x : ℝ) = x / 2 by ring]
  push_cast
  rw [show -(2 * z * ((x : ℂ) / 2)) = -(z * x) by ring]

/-- **The Laplace transform of the corrected count.** On `Re z > 1`,
`z ∫ e^{-zx} N(x) dx = zΛ(z) + L(z) − L(2z)/2`. -/
theorem mul_integral_cexp_catomCount {z : ℂ} (hz : 1 < z.re) :
    z * ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (atomCount P.catom x : ℂ) =
      z * boundedLaplace P.cerror z + P.logZeta z - P.logZeta (2 * z) / 2 := by
  obtain ⟨hWint, hL1⟩ := P.logZeta_eq hz
  have hz2 : 1 < (2 * z).re := by simp; linarith
  obtain ⟨-, hL2⟩ := P.logZeta_eq hz2
  have hEint : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (P.cerror x : ℂ)) (Ioi 0) := by
    have hb : IntegrableOn (fun x : ℝ => P.cbound * Real.exp (-z.re * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
    refine hb.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(z * x))).measurable.mul
        (Complex.measurable_ofReal.comp P.measurable_cerror)).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        show -z.re * x = -(z.re * x) by ring, mul_comm]
      exact mul_le_mul_of_nonneg_right (P.abs_cerror_le x) (Real.exp_pos _).le
  have hW2int : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (P.W (x / 2) : ℂ)) (Ioi 0) := by
    refine hWint.norm.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(z * x))).measurable.mul
        (Complex.measurable_ofReal.comp (P.measurable_W.comp
          (measurable_id.div_const 2)))).aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (P.W_nonneg _), abs_of_nonneg (P.W_nonneg _)]
      exact mul_le_mul_of_nonneg_left (P.W_half_le x) (norm_nonneg _)
  have hsplit : ∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (atomCount P.catom x : ℂ) =
      boundedLaplace P.cerror z + (∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (P.W x : ℂ)) -
        (∫ x in Ioi (0 : ℝ), cexp (-(z * x)) * (P.W (x / 2) : ℂ)) / 2 := by
    have hAB : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (P.cerror x : ℂ) +
        cexp (-(z * x)) * (P.W x : ℂ)) (Ioi 0) := hEint.add hWint
    have hC : IntegrableOn (fun x : ℝ => cexp (-(z * x)) * (P.W (x / 2) : ℂ) / 2) (Ioi 0) :=
      hW2int.div_const 2
    have hpt : (fun x : ℝ => cexp (-(z * x)) * (atomCount P.catom x : ℂ)) = fun x : ℝ =>
        (cexp (-(z * x)) * (P.cerror x : ℂ) + cexp (-(z * x)) * (P.W x : ℂ)) -
          cexp (-(z * x)) * (P.W (x / 2) : ℂ) / 2 := by
      funext x
      simp only [cerror]
      push_cast
      ring
    rw [hpt, integral_sub hAB hC, integral_add hEint hWint, integral_div, boundedLaplace]
  rw [hsplit, P.integral_cexp_W_half, hL1, hL2]
  ring

/-! ### The corrected discrete one-off -/

/-- The Euler logarithm `Σ_k −log(1 − p_k^{-s})` of the corrected discrete primes. -/
def cEulerLog (s : ℂ) : ℂ := ∑' k, -Complex.log (1 - cexp (-(s * P.catom k)))

/-- **The zeta function of the corrected discrete primes**, `exp` of the Euler logarithm. -/
def correctedZeta (s : ℂ) : ℂ := cexp (P.cEulerLog s)

/-- **It is the Euler product** `Π_k (1 − p_k^{-s})^{-1}` on `Re s > 1`. -/
theorem correctedZeta_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    P.correctedZeta s = ∏' k, (1 - cexp (-(s * P.catom k)))⁻¹ := by
  have hre : ∀ k, 0 < (1 - cexp (-(s * P.catom k))).re := by
    intro k
    have h1 : (cexp (-(s * P.catom k))).re ≤ ‖cexp (-(s * P.catom k))‖ := Complex.re_le_norm _
    have h2 : ‖cexp (-(s * P.catom k))‖ < 1 := by
      rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
      have := P.catom_pos k
      nlinarith
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hlog : ∀ k, Complex.log (1 - cexp (-(s * P.catom k)))⁻¹ =
      -Complex.log (1 - cexp (-(s * P.catom k))) := by
    intro k
    refine Complex.log_inv _ fun h => ?_
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [hre k]
  have hne : ∀ k, (1 - cexp (-(s * P.catom k)))⁻¹ ≠ 0 := by
    intro k
    refine inv_ne_zero fun h => ?_
    have := hre k
    rw [h] at this
    simp at this
  obtain ⟨h1, h2⟩ := summable_neg_log P.catom_pos P.catom_zero_le
    (fun a ha => P.summable_exp_catom ha) hs
  have hsum : Summable fun k => Complex.log (1 - cexp (-(s * P.catom k)))⁻¹ := by
    simp_rw [hlog]
    exact (h1.add h2).congr fun k => by ring
  rw [correctedZeta, cEulerLog, ← Complex.cexp_tsum_eq_tprod hne hsum]
  simp_rw [hlog]

/-- **The Euler logarithm of the corrected primes.** On `Re s > 1`,
`Σ_k −log(1 − p_k^{-s}) = L(s) − L(4s)/4 + sΛ(s) + sΛ(2s) + R₃(s)`. -/
theorem cEulerLog_eq {s : ℂ} (hs : 1 < s.re) :
    P.cEulerLog s = P.logZeta s + (-(P.logZeta (4 * s)) / 4 + s * boundedLaplace P.cerror s +
      s * boundedLaplace P.cerror (2 * s) + primeCubeRemainder P.catom s) := by
  have hs0 : 0 < s.re := by linarith
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hsplit := tsum_neg_log_eq_cube P.catom_pos P.catom_zero_le
    (fun a ha => P.summable_exp_catom ha) hs
  have hd1 := tsum_cexp_atoms P.catom_pos hs0 (P.summable_exp_catom hs)
  have hd2 := tsum_cexp_atoms P.catom_pos (by linarith : 0 < (2 * s).re)
    (P.summable_exp_catom hs2)
  have hN1 := P.mul_integral_cexp_catomCount hs
  have hN2 := P.mul_integral_cexp_catomCount hs2
  rw [show 2 * (2 * s) = 4 * s by ring] at hN2
  rw [cEulerLog, hsplit, hd1, hd2, hN1, hN2]
  ring

/-- **The corrected continuation** `ζ_c(s) exp(−L(4s)/4 + sΛ(s) + sΛ(2s) + R₃(s))`. -/
def cContinuation (s : ℂ) : ℂ :=
  overRegularZeta P.μ P.ν P.γ s *
    cexp (-(P.logZeta (4 * s)) / 4 + s * boundedLaplace P.cerror s +
      s * boundedLaplace P.cerror (2 * s) + primeCubeRemainder P.catom s)

/-- **The corrected Euler product is the continuation on `Re s > 1`.** -/
theorem correctedZeta_eq_cContinuation {s : ℂ} (hs : 1 < s.re) :
    P.correctedZeta s = P.cContinuation s := by
  rw [correctedZeta, P.cEulerLog_eq hs, Complex.exp_add, cContinuation]
  congr 1
  exact cexp_integral_primeDensity P.hlow P.hhigh P.h4 hs

/-- **The continuation is holomorphic on `Re s > 1/3`, away from the pole `s = 1`.** -/
theorem differentiableOn_cContinuation :
    DifferentiableOn ℂ P.cContinuation {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} := by
  rintro s ⟨hs, hs1⟩
  have hs' : 1 / 3 < s.re := hs
  have hopen : ∀ c : ℝ, ∀ z : ℂ, c < z.re → {w : ℂ | c < w.re} ∈ 𝓝 z := fun c z hz =>
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hζ : DifferentiableAt ℂ (overRegularZeta P.μ P.ν P.γ) s := by
    unfold overRegularZeta
    exact DifferentiableAt.div (by fun_prop) (by fun_prop)
      (overRegularZeta_denom_ne_zero (μ := P.μ) P.hν0.le (by linarith [P.hlow]) hs1)
  have hL : DifferentiableAt ℂ (fun s : ℂ => P.logZeta (4 * s)) s := by
    have h := P.differentiableOn_logZeta.differentiableAt
      (hopen 1 (4 * s) (by simp; linarith))
    exact h.comp s (differentiableAt_id.const_mul 4)
  have hM := P.cbound_pos
  have hΛ := differentiableOn_boundedLaplace_of_le P.measurable_cerror hM P.abs_cerror_le
  have hΛ1 : DifferentiableAt ℂ (boundedLaplace P.cerror) s :=
    hΛ.differentiableAt (hopen 0 s (by linarith))
  have hΛ2 : DifferentiableAt ℂ (fun s : ℂ => boundedLaplace P.cerror (2 * s)) s :=
    (hΛ.differentiableAt (hopen 0 (2 * s) (by simp; linarith))).comp s
      (differentiableAt_id.const_mul 2)
  have hR : DifferentiableAt ℂ (primeCubeRemainder P.catom) s :=
    (differentiableOn_primeCubeRemainder P.catom_pos P.catom_zero_le
      (fun a ha => P.summable_exp_catom ha)).differentiableAt (hopen (1 / 3) s hs')
  exact (hζ.mul ((((hL.neg.div_const 4).add (differentiableAt_id.mul hΛ1)).add
    (differentiableAt_id.mul hΛ2)).add hR).cexp).differentiableWithinAt

/-- **The zeros right of `1/3` are exactly the off-line pair `(1 − μ) ± iγ`.** -/
theorem cContinuation_eq_zero_iff {s : ℂ} (hs : 1 / 3 < s.re) (hs1 : s ≠ 1) :
    P.cContinuation s = 0 ↔
      s = ((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I ∨ s = ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I := by
  have hden := overRegularZeta_denom_ne_zero (μ := P.μ) P.hν0.le (by linarith [P.hlow]) hs1
  have h4 : s + (4 * P.μ - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [P.hμ1]
  have hfac : (s - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2 =
      (s - (((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I)) *
        (s - (((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I)) := by
    push_cast
    linear_combination ((P.γ : ℂ) ^ 2) * Complex.I_sq
  rw [cContinuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), overRegularZeta,
    div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_left h4, hfac, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]

/-- **The one-off across the line.** The zeros of the continuation with real part `> 1/3` are
exactly the pair `(1 − μ) ± iγ`. -/
theorem cZeros_right_eq_pair :
    {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1 ∧ P.cContinuation s = 0} =
      {((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I, ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I} := by
  ext s
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hs, hs1, hz⟩
    exact (P.cContinuation_eq_zero_iff hs hs1).mp hz
  · intro hz
    have hre : s.re = 1 - P.μ := by rcases hz with rfl | rfl <;> simp
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hre
      simp at hre
      linarith [P.hμ1]
    have h3 : 1 / 3 < s.re := by rw [hre]; linarith [P.hμ2]
    exact ⟨h3, hs1, (P.cContinuation_eq_zero_iff h3 hs1).mpr hz⟩

/-- **The critical line.** The continuation is holomorphic and zero-free at every point of
`Re s = 1/2`. -/
theorem cContinuation_critical_line {s : ℂ} (hs : s.re = 1 / 2) :
    DifferentiableAt ℂ P.cContinuation s ∧ P.cContinuation s ≠ 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : {z : ℂ | 1 / 3 < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by show 1 / 3 < s.re; rw [hs]; norm_num)
  have h2 : {z : ℂ | z ≠ 1} ∈ 𝓝 s := isOpen_ne.mem_nhds hs1
  have hU : {z : ℂ | 1 / 3 < z.re ∧ z ≠ 1} ∈ 𝓝 s :=
    Filter.mem_of_superset (Filter.inter_mem h1 h2) fun z hz => ⟨hz.1, hz.2⟩
  refine ⟨P.differentiableOn_cContinuation.differentiableAt hU, fun h0 => ?_⟩
  have hre : s.re = 1 - P.μ := by
    rcases (P.cContinuation_eq_zero_iff (by rw [hs]; norm_num) hs1).mp h0 with rfl | rfl <;> simp
  linarith [P.hμ2]

/-- **No blow-up at `1/2`.** As `σ → 1/2⁺` the corrected continuation tends to its finite, nonzero
value at `1/2`; the uncorrected one-off diverges there (`tendsto_norm_continuation_half`). -/
theorem tendsto_norm_cContinuation_half :
    Tendsto (fun σ : ℝ => ‖P.cContinuation σ‖) (𝓝[>] (1 / 2))
      (𝓝 ‖P.cContinuation (1 / 2)‖) ∧ P.cContinuation (1 / 2) ≠ 0 := by
  obtain ⟨hd, hne⟩ := P.cContinuation_critical_line (s := 1 / 2) (by norm_num)
  refine ⟨?_, hne⟩
  have hc : ContinuousAt (fun σ : ℝ => P.cContinuation σ) (1 / 2) := by
    have h := hd.continuousAt
    have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rw [← hcast] at h
    exact h.comp Complex.continuous_ofReal.continuousAt
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have h := hc.norm.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))
  simpa only [hcast] using h

end Params

end

end GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
