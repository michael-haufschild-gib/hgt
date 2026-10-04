import GaloisForLFunctions.RHTower.NicolasPrimorialInequalityRH
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowthLower

/-!
# Nicolas's inequality forces the Riemann hypothesis unless `Θ = 1`

Let `Θ` be the supremum of the real parts of the zeros of `ζ`.  If Nicolas's inequality
`N_n/φ(N_n) > e^γ log log N_n` holds for every large primorial `N_n` and `Θ < 1`, then the Riemann
hypothesis holds.  Equivalently: under `¬RH`, Nicolas's inequality fails infinitely often or
`Θ = 1`.

The proof runs through the Mertens remainder `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)` and the lag
primitive `v`, linked by `G(T) - G(U) = h(T)v(T) - h(U)v(U) - ∫_T^U k v`, `h = (1+s)/s²`,
`k = (s+2)/s³`.

* **Upper bound for the defect.**  With `ε = (θ(x) - x)/x`,
  `Nic(x) ≤ G(log x) + C₁/(√x log x) + (35/4) ε²/log x`, from `log log θ ≥ log log x +
  (θ - x)/(θ log θ)`, `ψ - θ ≤ C√x` and the prime-tail bound `P - A ≤ 8 log 4/(√x log x)`.
* **Inversion.**  `v(T) = v(U) - G(U)/h(U) + G(T)/h(T) + ∫_T^U G·s(s+2)/(1+s)² ds`, so a lower bound
  for `G` on `[T, ∞)` gives one for `v(T)`; the term at `U` is removed with `|v(s)| ≤ W e^{(Θ-1)s} +
  2e^{-s}` (from `|Φ(L)| ≤ W e^{(Θ-1/2)L}`) and the sign changes of `R`.
* **Landau.**  For `Θ < b < 1` the exponent law gives `ε² ≤ C x^{2b-2}`; hence
  `Φ(L) ≥ -M e^{aL}`, `a = max(0, 2b - 3/2) < 1/2`, and every zero has real part at most
  `max(1/2, 2b - 1)`.  Taking `b` close to `Θ` forces `Θ ≤ 1/2`.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Growth of the lag function and of the lag primitive in terms of `Θ` -/

theorem abs_weilLagFunctionReal_le_exp_zeroReSup {L : ℝ} (hL : 0 ≤ L) :
    |weilLagFunctionReal L| ≤ Real.exp ((zeroReSup - 1 / 2) * L) * lagWeightTotal := by
  have h1 : |weilLagFunctionReal L| = ‖weilLagFunction L‖ := by
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  have hterm : ∀ q : XiZeroCopy,
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
        ≤ Real.exp ((zeroReSup - 1 / 2) * L) * ‖lagWeight q‖ := by
    intro q
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp, lagWeight]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hre : (↑L * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by simp
    rw [hre]
    have := re_le_zeroReSup q
    nlinarith
  have hs : Summable (fun q : XiZeroCopy =>
      ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (summable_norm_lagWeight.mul_left _)
  unfold weilLagFunction lagWeightTotal
  calc ‖∑' q : XiZeroCopy, Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
      ≤ ∑' q : XiZeroCopy,
          ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q : XiZeroCopy, Real.exp ((zeroReSup - 1 / 2) * L) * ‖lagWeight q‖ :=
        hs.tsum_le_tsum hterm (summable_norm_lagWeight.mul_left _)
    _ = Real.exp ((zeroReSup - 1 / 2) * L) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := tsum_mul_left

/-- `|v(L)| ≤ W e^{(Θ-1)L} + 2 e^{-L}` for `L > 0`. -/
theorem abs_mertensLagPrimitive_le_exp_zeroReSup {L : ℝ} (hL : 0 < L) :
    |mertensLagPrimitive L|
      ≤ lagWeightTotal * Real.exp ((zeroReSup - 1) * L) + 2 * Real.exp (-L) := by
  have hΦ := abs_weilLagFunctionReal_le_exp_zeroReSup hL.le
  have hX1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL.le
  have hS0 := trivialZeroSeriesReal_nonneg hX1
  have hS1 := trivialZeroSeriesReal_le_one hX1
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hid := exp_mul_mertensLagPrimitive_eq hL
  have hv : mertensLagPrimitive L = Real.exp (-L) * (Real.exp (L / 2) * weilLagFunctionReal L
      + Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) := by
    rw [← hid, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hW := lagWeightTotal_nonneg
  have h3 : |Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |Real.exp (L / 2) * weilLagFunctionReal L|
      ≤ Real.exp (L / 2) * (Real.exp ((zeroReSup - 1 / 2) * L) * lagWeightTotal) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le
  have he1 : Real.exp (-L) * (Real.exp (L / 2) * Real.exp ((zeroReSup - 1 / 2) * L))
      = Real.exp ((zeroReSup - 1) * L) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hv, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-L) * |Real.exp (L / 2) * weilLagFunctionReal L + Real.log (2 * Real.pi)
        - trivialZeroSeriesReal (Real.exp L)|
      ≤ Real.exp (-L) * (Real.exp (L / 2) * (Real.exp ((zeroReSup - 1 / 2) * L)
          * lagWeightTotal) + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        calc _ = |Real.exp (L / 2) * weilLagFunctionReal L
                + (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))| := by ring_nf
          _ ≤ |Real.exp (L / 2) * weilLagFunctionReal L|
                + |Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)| := abs_add_le _ _
          _ ≤ _ := add_le_add h2 h3
    _ = lagWeightTotal * (Real.exp (-L) * (Real.exp (L / 2)
          * Real.exp ((zeroReSup - 1 / 2) * L))) + 2 * Real.exp (-L) := by ring
    _ = lagWeightTotal * Real.exp ((zeroReSup - 1) * L) + 2 * Real.exp (-L) := by rw [he1]


/-! ## An upper bound for the Nicolas defect -/

/-- `log log θ ≥ log log x + (θ - x)/(θ log θ)` for `x > 1`, `θ > 1`. -/
theorem log_log_ge_add {x θ : ℝ} (hx : 1 < x) (hθ : 1 < θ) :
    Real.log (Real.log x) + (θ - x) / (θ * Real.log θ) ≤ Real.log (Real.log θ) := by
  have hx0 : 0 < x := by linarith
  have hθ0 : 0 < θ := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlθ : 0 < Real.log θ := Real.log_pos hθ
  have h1 : 1 - (Real.log θ / Real.log x)⁻¹ ≤ Real.log (Real.log θ / Real.log x) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hlθ hlx)
  rw [Real.log_div hlθ.ne' hlx.ne', inv_div] at h1
  have h2 : 1 - (θ / x)⁻¹ ≤ Real.log (θ / x) := Real.one_sub_inv_le_log_of_pos (div_pos hθ0 hx0)
  rw [Real.log_div hθ0.ne' hx0.ne', inv_div] at h2
  have h3 : 1 - Real.log x / Real.log θ = (Real.log θ - Real.log x) / Real.log θ := by field_simp
  have h4 : 1 - x / θ = (θ - x) / θ := by field_simp
  rw [h3] at h1
  rw [h4] at h2
  have h5 : (θ - x) / θ / Real.log θ ≤ (Real.log θ - Real.log x) / Real.log θ :=
    div_le_div_of_nonneg_right h2 hlθ.le
  rw [div_div] at h5
  linarith

/-- The second-order term: `(θ - x)/(x log x) - (θ - x)/(θ log θ) ≤ (35/4)(θ - x)²/(x² log x)` when
`θ ≥ 2x/5` and `log θ ≥ 1`. -/
theorem sub_div_sub_le_sq {x θ : ℝ} (hx : 1 < x) (hθ25 : 2 / 5 * x ≤ θ)
    (hlθ1 : 1 ≤ Real.log θ) :
    (θ - x) / (x * Real.log x) - (θ - x) / (θ * Real.log θ)
      ≤ 35 / 4 * ((θ - x) ^ 2 / (x ^ 2 * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hθ0 : 0 < θ := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlθ : 0 < Real.log θ := by linarith
  -- `log θ - log x` lies between `(θ - x)/θ` and `(θ - x)/x`
  have hup : Real.log θ - Real.log x ≤ (θ - x) / x := by
    rw [← Real.log_div hθ0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hθ0 hx0)
    rw [sub_div, div_self hx0.ne']; linarith
  have hlo : (θ - x) / θ ≤ Real.log θ - Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hθ0 hx0)
    rw [Real.log_div hθ0.ne' hx0.ne', inv_div] at this
    rw [sub_div, div_self hθ0.ne']; linarith
  have hkey : (θ - x) * (x * (Real.log θ - Real.log x)) ≤ 5 / 2 * (θ - x) ^ 2 := by
    rcases le_total x θ with h | h
    · have h1 : x * (Real.log θ - Real.log x) ≤ θ - x := by
        have := mul_le_mul_of_nonneg_left hup hx0.le
        rwa [mul_div_cancel₀ _ hx0.ne'] at this
      have := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr h)
      nlinarith [sq_nonneg (θ - x)]
    · have h1 : x * ((θ - x) / θ) ≤ x * (Real.log θ - Real.log x) :=
        mul_le_mul_of_nonneg_left hlo hx0.le
      have h2 : (θ - x) * (x * (Real.log θ - Real.log x)) ≤ (θ - x) * (x * ((θ - x) / θ)) :=
        mul_le_mul_of_nonpos_left h1 (by linarith)
      have h3 : (θ - x) * (x * ((θ - x) / θ)) = (θ - x) ^ 2 * (x / θ) := by field_simp
      have h4 : x / θ ≤ 5 / 2 := by rw [div_le_iff₀ hθ0]; linarith
      have h5 : (θ - x) ^ 2 * (x / θ) ≤ (θ - x) ^ 2 * (5 / 2) :=
        mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      linarith
  have hnum : (θ - x) * (θ * Real.log θ - x * Real.log x)
      ≤ (θ - x) ^ 2 * (Real.log θ + 5 / 2) := by
    have e : (θ - x) * (θ * Real.log θ - x * Real.log x)
        = (θ - x) ^ 2 * Real.log θ + (θ - x) * (x * (Real.log θ - Real.log x)) := by ring
    rw [e]; nlinarith
  have hlhs : (θ - x) / (x * Real.log x) - (θ - x) / (θ * Real.log θ)
      = (θ - x) * (θ * Real.log θ - x * Real.log x) / (x * θ * Real.log x * Real.log θ) := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  have hD : 0 < x * θ * Real.log x * Real.log θ := by positivity
  -- `(log θ + 5/2) ≤ (7/2) log θ` and `θ ≥ 2x/5`
  have hA : (θ - x) ^ 2 * (Real.log θ + 5 / 2) ≤ (θ - x) ^ 2 * (7 / 2 * Real.log θ) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hB : 35 / 4 * ((θ - x) ^ 2 / (x ^ 2 * Real.log x)) * (x * θ * Real.log x * Real.log θ)
      = 35 / 4 * (θ - x) ^ 2 * (θ / x) * Real.log θ := by field_simp
  rw [hB]
  have hθx : 2 / 5 ≤ θ / x := by rw [le_div_iff₀ hx0]; linarith
  have hC : (θ - x) ^ 2 * (7 / 2 * Real.log θ) ≤ 35 / 4 * (θ - x) ^ 2 * (θ / x) * Real.log θ := by
    have h0 : 0 ≤ (θ - x) ^ 2 * Real.log θ := mul_nonneg (sq_nonneg _) hlθ.le
    have : 7 / 2 ≤ 35 / 4 * (θ / x) := by linarith
    nlinarith
  linarith

/-- **Upper bound for the Nicolas defect.**  For `x ≥ 4` with `θ(x) ≥ 2x/5`, `log θ(x) ≥ 1` and
`ψ(t) - θ(t) ≤ C√t`:
`Nic(x) ≤ G(log x) + (8 log 4 + C)/(√x log x) + (35/4)(θ(x) - x)²/(x² log x)`. -/
theorem nicolasDefect_le {x C : ℝ} (hx : 4 ≤ x) (hθ25 : 2 / 5 * x ≤ Chebyshev.theta x)
    (hlθ1 : 1 ≤ Real.log (Chebyshev.theta x))
    (hC : Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    nicolasDefect x ≤ mertensErrorRemainder (Real.log x)
      + (8 * Real.log 4 + C) / (Real.sqrt x * Real.log x)
      + 35 / 4 * ((Chebyshev.theta x - x) ^ 2 / (x ^ 2 * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hθ1 : 1 < Chebyshev.theta x := by
    by_contra h
    have : Real.log (Chebyshev.theta x) ≤ 0 := Real.log_nonpos (Chebyshev.theta_nonneg x)
      (not_lt.mp h)
    linarith
  have h1 := log_log_ge_add (by linarith : (1 : ℝ) < x) hθ1
  have h2 := (mertensProductError_sub_mem hx).2
  have hG : mertensErrorRemainder (Real.log x)
      = mertensError x - (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [mertensErrorRemainder, Real.exp_log hx0]
  have h3 := sub_div_sub_le_sq (by linarith : (1 : ℝ) < x) hθ25 hlθ1
  have hψθ : (Chebyshev.psi x - Chebyshev.theta x) / (x * Real.log x)
      ≤ C / (Real.sqrt x * Real.log x) := by
    have hxx : x * Real.log x = Real.sqrt x * (Real.sqrt x * Real.log x) := by
      rw [← mul_assoc, Real.mul_self_sqrt hx0.le]
    rw [hxx, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ Real.sqrt x * Real.log x)
    nlinarith
  have hsplit : (Chebyshev.psi x - x) / (x * Real.log x)
      = (Chebyshev.psi x - Chebyshev.theta x) / (x * Real.log x)
        + (Chebyshev.theta x - x) / (x * Real.log x) := by
    rw [← add_div]; ring_nf
  have hsum : (8 * Real.log 4 + C) / (Real.sqrt x * Real.log x)
      = 8 * Real.log 4 / (Real.sqrt x * Real.log x) + C / (Real.sqrt x * Real.log x) := by
    rw [add_div]
  unfold nicolasDefect
  unfold mertensProductError at h2
  linarith


/-! ## Inverting the remainder -/

/-- `G(s) - G(U) = h(s)v(s) - h(U)v(U) - ∫_s^U k v` for `1 ≤ s ≤ U`. -/
theorem mertensErrorRemainder_sub_eq_lag {s U : ℝ} (hs : 1 ≤ s) (hsU : s ≤ U) :
    mertensErrorRemainder s - mertensErrorRemainder U
      = (1 + s) / s ^ 2 * mertensLagPrimitive s - (1 + U) / U ^ 2 * mertensLagPrimitive U
        - ∫ t in s..U, (t + 2) / t ^ 3 * mertensLagPrimitive t := by
  have hl2 : Real.log 2 ≤ s := by have := Real.log_two_lt_d9; linarith
  rw [mertensErrorRemainder_sub_eq hl2 hsU, integral_deficit_mertensAbelWeight_eq (by linarith) hsU]

/-- **The inversion identity.**  For `1 ≤ T ≤ U`, with `r(s) = s²/(1+s)` and
`q(s) = s(s+2)/(1+s)²`: `v(T) = v(U) - G(U) r(U) + G(T) r(T) + ∫_T^U G q`. -/
theorem mertensLagPrimitive_eq_inversion {T U : ℝ} (hT : 1 ≤ T) (hTU : T ≤ U) :
    mertensLagPrimitive T = mertensLagPrimitive U - mertensErrorRemainder U * (U ^ 2 / (1 + U))
      + mertensErrorRemainder T * (T ^ 2 / (1 + T))
      + ∫ s in T..U, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) := by
  set v := mertensLagPrimitive with hv
  set G := mertensErrorRemainder with hGdef
  set kv : ℝ → ℝ := fun t => (t + 2) / t ^ 3 * v t with hkv
  set Ψ : ℝ → ℝ := fun s => ∫ t in s..U, kv t with hΨ
  set c : ℝ := G U - (1 + U) / U ^ 2 * v U with hc
  have hpos : ∀ s ∈ uIcc T U, 0 < s := fun s hs => by
    rw [uIcc_of_le hTU] at hs; linarith [hs.1]
  have hvc := continuous_mertensLagPrimitive
  have hkvc : ContinuousOn kv (Ioi 0) :=
    ((continuousOn_id.add continuousOn_const).div (continuousOn_id.pow 3) fun t ht =>
      pow_ne_zero 3 (ne_of_gt ht)).mul hvc.continuousOn
  have hkvi : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable kv volume a b := fun a b ha hb =>
    (hkvc.mono fun t ht => by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; exact lt_of_lt_of_le ha ht.1
      · rw [uIcc_of_ge h] at ht; exact lt_of_lt_of_le hb ht.1).intervalIntegrable
  -- `G = c + h v - Ψ` on `[T, U]`
  have hGs : ∀ s ∈ uIcc T U, G s = c + (1 + s) / s ^ 2 * v s - Ψ s := by
    intro s hs
    rw [uIcc_of_le hTU] at hs
    have := mertensErrorRemainder_sub_eq_lag (by linarith [hs.1]) hs.2
    simp only [hΨ, hc]
    linarith
  -- derivative of `Ψ`
  have hΨd : ∀ s ∈ uIcc T U, HasDerivAt Ψ (-kv s) s := by
    intro s hs
    have hs0 := hpos s hs
    exact intervalIntegral.integral_hasDerivAt_left (hkvi s U hs0 (by linarith))
      (hkvc.stronglyMeasurableAtFilter isOpen_Ioi s hs0)
      (hkvc.continuousAt (isOpen_Ioi.mem_nhds hs0))
  -- derivative of `r`
  have hrd : ∀ s ∈ uIcc T U, HasDerivAt (fun s : ℝ => s ^ 2 / (1 + s))
      (s * (s + 2) / (1 + s) ^ 2) s := by
    intro s hs
    have hs0 := hpos s hs
    have h1 : (1 + s) ≠ 0 := by linarith
    have := (hasDerivAt_pow 2 s).div ((hasDerivAt_id s).const_add 1) h1
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hqc : ContinuousOn (fun s : ℝ => s * (s + 2) / (1 + s) ^ 2) (uIcc T U) :=
    (continuousOn_id.mul (continuousOn_id.add continuousOn_const)).div
      ((continuousOn_const.add continuousOn_id).pow 2) fun s hs => by
        have := hpos s hs; positivity
  have hΨc : ContinuousOn Ψ (uIcc T U) := fun s hs => (hΨd s hs).continuousAt.continuousWithinAt
  have hkvcU : ContinuousOn kv (uIcc T U) := hkvc.mono fun s hs => hpos s hs
  have hrc : ContinuousOn (fun s : ℝ => s ^ 2 / (1 + s)) (uIcc T U) :=
    (continuousOn_id.pow 2).div (continuousOn_const.add continuousOn_id) fun s hs => by
      have := hpos s hs; positivity
  -- `∫ G q = c ∫ q + ∫ k v r - ∫ Ψ q`
  have hcong : ∫ s in T..U, G s * (s * (s + 2) / (1 + s) ^ 2)
      = ∫ s in T..U, (c * (s * (s + 2) / (1 + s) ^ 2) + kv s * (s ^ 2 / (1 + s))
          - Ψ s * (s * (s + 2) / (1 + s) ^ 2)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hGs s hs]
    have hs0 := hpos s hs
    simp only [hkv]
    field_simp
  have i1 : IntervalIntegrable (fun s => c * (s * (s + 2) / (1 + s) ^ 2)) volume T U :=
    (hqc.intervalIntegrable).const_mul c
  have i2 : IntervalIntegrable (fun s => kv s * (s ^ 2 / (1 + s))) volume T U :=
    (hkvcU.mul hrc).intervalIntegrable
  have i3 : IntervalIntegrable (fun s => Ψ s * (s * (s + 2) / (1 + s) ^ 2)) volume T U :=
    (hΨc.mul hqc).intervalIntegrable
  have hq : ∫ s in T..U, s * (s + 2) / (1 + s) ^ 2 = U ^ 2 / (1 + U) - T ^ 2 / (1 + T) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hrd hqc.intervalIntegrable
  -- by parts for `∫ Ψ q`
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hΨd hrd
    ((hkvcU.neg).intervalIntegrable) hqc.intervalIntegrable
  have hΨU : Ψ U = 0 := by simp [hΨ]
  rw [hΨU, zero_mul, zero_sub] at hparts
  have hneg : ∫ s in T..U, -kv s * (s ^ 2 / (1 + s)) = -∫ s in T..U, kv s * (s ^ 2 / (1 + s)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun s _ => by ring
  rw [hneg] at hparts
  rw [hcong, intervalIntegral.integral_sub (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, hq, hparts]
  have hGT := hGs T (by rw [uIcc_of_le hTU]; exact ⟨le_rfl, hTU⟩)
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith
  have hrT : (1 + T) / T ^ 2 * (T ^ 2 / (1 + T)) = 1 := by field_simp
  have hrU : (1 + U) / U ^ 2 * (U ^ 2 / (1 + U)) = 1 := by field_simp
  rw [hGT]
  simp only [hc]
  linear_combination (-(v T)) * hrT + v U * hrU


/-- The Mertens remainder is continuous on `[1, U]`. -/
theorem continuousOn_mertensErrorRemainder (U : ℝ) :
    ContinuousOn mertensErrorRemainder (Icc 1 U) := by
  set kv : ℝ → ℝ := fun t => (t + 2) / t ^ 3 * mertensLagPrimitive t with hkv
  have hkvc : ContinuousOn kv (Ioi 0) :=
    ((continuousOn_id.add continuousOn_const).div (continuousOn_id.pow 3) fun t ht =>
      pow_ne_zero 3 (ne_of_gt ht)).mul continuous_mertensLagPrimitive.continuousOn
  have hΨ : ContinuousOn (fun s => ∫ t in s..U, kv t) (Icc 1 U) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hi : IntervalIntegrable kv volume s U := (hkvc.mono fun t ht => by
      rw [uIcc_of_le hs.2] at ht; exact lt_of_lt_of_le hs0 ht.1).intervalIntegrable
    exact (intervalIntegral.integral_hasDerivAt_left hi
      (hkvc.stronglyMeasurableAtFilter isOpen_Ioi s hs0)
      (hkvc.continuousAt (isOpen_Ioi.mem_nhds hs0))).continuousAt.continuousWithinAt
  have hrep : ∀ s ∈ Icc 1 U, mertensErrorRemainder s
      = mertensErrorRemainder U + (1 + s) / s ^ 2 * mertensLagPrimitive s
        - (1 + U) / U ^ 2 * mertensLagPrimitive U - ∫ t in s..U, kv t := by
    intro s hs
    have := mertensErrorRemainder_sub_eq_lag hs.1 hs.2
    simp only [hkv]
    linarith
  refine ContinuousOn.congr ?_ hrep
  refine ((continuousOn_const.add ?_).sub continuousOn_const).sub hΨ
  exact ((continuousOn_const.add continuousOn_id).div (continuousOn_pow 2)
    fun s (hs : s ∈ Icc 1 U) =>
    pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < s by linarith [hs.1]))).mul
      continuous_mertensLagPrimitive.continuousOn

/-- If `Θ < 1`, then `(ψ(x) - x)/(x log x) → 0`. -/
theorem tendsto_chebyshevError_div_of_zeroReSup_lt_one (hΘ : zeroReSup < 1) :
    Tendsto (fun x => (Chebyshev.psi x - x) / (x * Real.log x)) atTop (𝓝 0) := by
  set b := (zeroReSup + 1) / 2 with hb
  obtain ⟨C, hC0, hC⟩ := exists_abs_chebyshevPsi_sub_le_rpow (b := b) (by rw [hb]; linarith)
  have hb1 : b - 1 < 0 := by rw [hb]; linarith
  have h0 : Tendsto (fun x : ℝ => C * x ^ (b - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < -(b - 1) by linarith)).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlx : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hxl : 0 < x * Real.log x := mul_pos hx0 (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hxl]
  have h1 := hC x hx1
  rw [div_le_iff₀ hxl]
  have hxb : x ^ (b - 1) * x = x ^ b := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  calc |Chebyshev.psi x - x| ≤ C * x ^ b := h1
    _ = C * x ^ (b - 1) * x := by rw [mul_assoc, hxb]
    _ ≤ C * x ^ (b - 1) * (x * Real.log x) := by
        have hCx : 0 ≤ C * x ^ (b - 1) := mul_nonneg hC0 (Real.rpow_nonneg hx0.le _)
        refine mul_le_mul_of_nonneg_left ?_ hCx
        nlinarith

/-- The tail beyond `U`: `|r(U) ∫_U^W k v| ≤ K₀/U`, `K₀ = 3(W + 2)/(1 - Θ)`. -/
theorem abs_mul_integral_lag_tail_le (hΘ : zeroReSup < 1) {U W : ℝ} (hU1 : 1 ≤ U) (hUW : U ≤ W) :
    |U ^ 2 / (1 + U) * ∫ t in U..W, (t + 2) / t ^ 3 * mertensLagPrimitive t|
      ≤ 3 * (lagWeightTotal + 2) / (1 - zeroReSup) / U := by
  have hΘh := half_le_zeroReSup
  have hU0 : 0 < U := by linarith
  have hW0 := lagWeightTotal_nonneg
  set A : ℝ := lagWeightTotal + 2 with hA
  have hA0 : 0 < A := by rw [hA]; linarith
  have hvb : ∀ s, 1 ≤ s → |mertensLagPrimitive s| ≤ A * Real.exp ((zeroReSup - 1) * s) := by
    intro s hs
    have h := abs_mertensLagPrimitive_le_exp_zeroReSup (by linarith : (0 : ℝ) < s)
    have he : Real.exp (-s) ≤ Real.exp ((zeroReSup - 1) * s) := Real.exp_le_exp.mpr (by nlinarith)
    have hE := Real.exp_pos ((zeroReSup - 1) * s)
    rw [hA]; nlinarith
  have hpt : ∀ᵐ t ∂volume, t ∈ Ioc U W → ‖(t + 2) / t ^ 3 * mertensLagPrimitive t‖
      ≤ 3 * A / U ^ 2 * Real.exp ((zeroReSup - 1) * t) := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have htU : U ≤ t := ht.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have h1 := hvb t (by linarith)
    have hk : (t + 2) / t ^ 3 ≤ 3 / U ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : U ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hU0.le htU 2
      nlinarith
    calc (t + 2) / t ^ 3 * |mertensLagPrimitive t|
        ≤ 3 / U ^ 2 * (A * Real.exp ((zeroReSup - 1) * t)) :=
          mul_le_mul hk h1 (abs_nonneg _) (by positivity)
      _ = 3 * A / U ^ 2 * Real.exp ((zeroReSup - 1) * t) := by ring
  have hgi : IntervalIntegrable (fun t => 3 * A / U ^ 2 * Real.exp ((zeroReSup - 1) * t))
      volume U W := Continuous.intervalIntegrable (by fun_prop) U W
  have hle := intervalIntegral.norm_integral_le_of_norm_le hUW hpt hgi
  rw [Real.norm_eq_abs] at hle
  have hne : zeroReSup - 1 ≠ 0 := by linarith
  have hd : ∀ t ∈ uIcc U W, HasDerivAt
      (fun t : ℝ => Real.exp ((zeroReSup - 1) * t) / (zeroReSup - 1))
      (Real.exp ((zeroReSup - 1) * t)) t := by
    intro t _
    have := (((hasDerivAt_id' t).const_mul (zeroReSup - 1)).exp).div_const (zeroReSup - 1)
    refine this.congr_deriv ?_
    field_simp
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) U W)
  have hEU : Real.exp ((zeroReSup - 1) * U) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hEW := Real.exp_pos ((zeroReSup - 1) * W)
  have hint : ∫ t in U..W, 3 * A / U ^ 2 * Real.exp ((zeroReSup - 1) * t)
      ≤ 3 * A / U ^ 2 / (1 - zeroReSup) := by
    rw [intervalIntegral.integral_const_mul, hI]
    have e1 : Real.exp ((zeroReSup - 1) * W) / (zeroReSup - 1)
        - Real.exp ((zeroReSup - 1) * U) / (zeroReSup - 1)
        = (Real.exp ((zeroReSup - 1) * U) - Real.exp ((zeroReSup - 1) * W))
          / (1 - zeroReSup) := by
      have hne' : 1 - zeroReSup ≠ 0 := by linarith
      field_simp
      ring
    rw [e1, mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 ≤ 3 * A / U ^ 2 := by positivity
    nlinarith
  have hrUle : U ^ 2 / (1 + U) ≤ U := by rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [abs_mul, abs_of_pos (by positivity)]
  calc U ^ 2 / (1 + U) * |∫ t in U..W, (t + 2) / t ^ 3 * mertensLagPrimitive t|
      ≤ U * (3 * A / U ^ 2 / (1 - zeroReSup)) :=
        mul_le_mul hrUle (hle.trans hint) (abs_nonneg _) hU0.le
    _ = 3 * A / (1 - zeroReSup) / U := by field_simp

/-- If `Θ < 1`, the remainder is below any `ε > 0` for arbitrarily large `W`. -/
theorem frequently_mertensErrorRemainder_lt (hΘ : zeroReSup < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ W : ℝ in atTop, mertensErrorRemainder W < ε := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hE := tendsto_chebyshevError_div_of_zeroReSup_lt_one hΘ
  have hev : ∀ᶠ x : ℝ in atTop, -ε < (Chebyshev.psi x - x) / (x * Real.log x) :=
    hE.eventually (lt_mem_nhds (by linarith))
  refine Real.tendsto_log_atTop.frequently ?_
  refine ((frequently_mertensError_lt_neg_rpow hb).and_eventually
    (hev.and (eventually_gt_atTop 0))).mono fun x hxx => ?_
  obtain ⟨h, hs, hx⟩ := hxx
  rw [mertensErrorRemainder, Real.exp_log hx]
  have := Real.rpow_nonneg hx.le (1 / 4 - 1)
  linarith

/-- `c · h(W)|v(W)| → 0`. -/
theorem eventually_mul_lag_boundary_lt (hΘ : zeroReSup < 1) {c ε : ℝ} (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ W : ℝ in atTop, c * ((1 + W) / W ^ 2 * |mertensLagPrimitive W|) < ε := by
  have hΘh := half_le_zeroReSup
  have hW0 := lagWeightTotal_nonneg
  filter_upwards [eventually_ge_atTop (max 1 (2 * c * (lagWeightTotal + 2) / ε + 1))] with W hW
  have hW1 : 1 ≤ W := le_trans (le_max_left _ _) hW
  have hW0' : 0 < W := by linarith
  have hWl : 2 * c * (lagWeightTotal + 2) / ε < W :=
    lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hW)
  have h1 := abs_mertensLagPrimitive_le_exp_zeroReSup hW0'
  have he1 : Real.exp ((zeroReSup - 1) * W) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he2 : Real.exp (-W) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : |mertensLagPrimitive W| ≤ lagWeightTotal + 2 := by nlinarith
  have h3 : (1 + W) / W ^ 2 ≤ 2 / W := by
    rw [div_le_div_iff₀ (by positivity) hW0']; nlinarith
  have h4 : (1 + W) / W ^ 2 * |mertensLagPrimitive W| ≤ 2 / W * (lagWeightTotal + 2) :=
    mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
  calc c * ((1 + W) / W ^ 2 * |mertensLagPrimitive W|)
      ≤ c * (2 / W * (lagWeightTotal + 2)) := mul_le_mul_of_nonneg_left h4 hc
    _ = 2 * c * (lagWeightTotal + 2) / W := by ring
    _ < ε := by
        rw [div_lt_iff₀ hW0']
        rw [div_lt_iff₀ hε] at hWl
        linarith

/-- The bracket at `U` expressed through a later point `W`. -/
theorem mertensLag_bracket_eq {U W : ℝ} (hU1 : 1 ≤ U) (hUW : U ≤ W) :
    mertensLagPrimitive U - mertensErrorRemainder U * (U ^ 2 / (1 + U))
      = -(U ^ 2 / (1 + U) * mertensErrorRemainder W)
        + U ^ 2 / (1 + U) * ((1 + W) / W ^ 2 * mertensLagPrimitive W)
        + U ^ 2 / (1 + U) * ∫ t in U..W, (t + 2) / t ^ 3 * mertensLagPrimitive t := by
  have hU0 : 0 < U := by linarith
  have hrUh : U ^ 2 / (1 + U) * ((1 + U) / U ^ 2) = 1 := by field_simp
  have hI2 := mertensErrorRemainder_sub_eq_lag hU1 hUW
  have : mertensErrorRemainder U = mertensErrorRemainder W
      + ((1 + U) / U ^ 2 * mertensLagPrimitive U - (1 + W) / W ^ 2 * mertensLagPrimitive W
        - ∫ t in U..W, (t + 2) / t ^ 3 * mertensLagPrimitive t) := by linarith
  rw [this]
  linear_combination (-(mertensLagPrimitive U)) * hrUh

/-- `∫_T^U G q ≥ -B` from `G ≥ -g`, `0 ≤ q ≤ 1`, `∫_T^U g ≤ B`. -/
theorem integral_remainder_weight_ge {T₀ T U B : ℝ} {g : ℝ → ℝ} (hgc : Continuous g)
    (hgnn : ∀ s, 0 ≤ g s) (hg : ∀ s, T₀ ≤ s → -g s ≤ mertensErrorRemainder s) (hT : T₀ ≤ T)
    (hT1 : 1 ≤ T) (hTU : T ≤ U) (hB : ∫ s in T..U, g s ≤ B) :
    -B ≤ ∫ s in T..U, mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2) := by
  have hGcont := continuousOn_mertensErrorRemainder U
  have hqc : ContinuousOn (fun s : ℝ => s * (s + 2) / (1 + s) ^ 2) (uIcc T U) :=
    (continuousOn_id.mul (continuousOn_id.add continuousOn_const)).div
      ((continuousOn_const.add continuousOn_id).pow 2) fun s hs => by
        rw [uIcc_of_le hTU] at hs
        have : 0 < s := by linarith [hs.1]
        positivity
  have hGq : IntervalIntegrable (fun s => mertensErrorRemainder s * (s * (s + 2) / (1 + s) ^ 2))
      volume T U := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (hGcont.mono ?_) hqc
    intro s hs; rw [uIcc_of_le hTU] at hs; exact ⟨le_trans hT1 hs.1, hs.2⟩
  have hmono : ∫ s in T..U, -g s ≤ ∫ s in T..U, mertensErrorRemainder s
      * (s * (s + 2) / (1 + s) ^ 2) := by
    refine intervalIntegral.integral_mono_on hTU (hgc.neg.intervalIntegrable _ _) hGq
      fun s hs => ?_
    have hs0 : 0 < s := by linarith [hs.1]
    have hq0 : 0 ≤ s * (s + 2) / (1 + s) ^ 2 := by positivity
    have hq1 : s * (s + 2) / (1 + s) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h1 := hg s (le_trans hT hs.1)
    have h2 := hgnn s
    have h3 := mul_le_mul_of_nonneg_right h1 hq0
    have h4 : g s * (s * (s + 2) / (1 + s) ^ 2) ≤ g s := mul_le_of_le_one_right h2 hq1
    linarith
  rw [intervalIntegral.integral_neg] at hmono
  linarith

/-- **Lower bounds pass from the remainder to the lag primitive** (`Θ < 1`).  If
`G(s) ≥ -g(s)` for `s ≥ T₀` with `g ≥ 0` continuous and `∫_T^U g ≤ B` for every `U ≥ T`, then
`v(T) ≥ -(g(T) T²/(1+T) + B)`. -/
theorem mertensLagPrimitive_ge_of_remainder_ge (hΘ : zeroReSup < 1) {T₀ : ℝ} (hT₀ : 4 ≤ T₀)
    {g : ℝ → ℝ} (hgc : Continuous g) (hgnn : ∀ s, 0 ≤ g s)
    (hg : ∀ s, T₀ ≤ s → -g s ≤ mertensErrorRemainder s) {T B : ℝ} (hT : T₀ ≤ T)
    (hB : ∀ U, T ≤ U → ∫ s in T..U, g s ≤ B) :
    -(g T * (T ^ 2 / (1 + T)) + B) ≤ mertensLagPrimitive T := by
  have hT1 : 1 ≤ T := by linarith
  have hK0 : 0 ≤ 3 * (lagWeightTotal + 2) / (1 - zeroReSup) :=
    div_nonneg (by linarith [lagWeightTotal_nonneg]) (by linarith)
  set K₀ := 3 * (lagWeightTotal + 2) / (1 - zeroReSup) with hK₀
  refine le_of_forall_pos_lt_add fun η hη => ?_
  set U : ℝ := max T (3 * K₀ / η + 1) with hU
  have hTU : T ≤ U := le_max_left _ _
  have hU1 : 1 ≤ U := le_trans hT1 hTU
  have hU0 : 0 < U := by linarith
  have hUK : 3 * K₀ / η < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hrU0 : 0 < U ^ 2 / (1 + U) := by positivity
  have hKU : K₀ / U ≤ η / 3 := by
    rw [div_le_div_iff₀ hU0 (by norm_num)]
    rw [div_lt_iff₀ hη] at hUK
    linarith
  obtain ⟨W, hGW, hvWW, hUW⟩ := ((frequently_mertensErrorRemainder_lt hΘ
    (show 0 < η / 3 / (U ^ 2 / (1 + U)) by positivity)).and_eventually
    ((eventually_mul_lag_boundary_lt hΘ hrU0.le (show 0 < η / 3 by positivity)).and
      (eventually_ge_atTop U))).exists
  have hinv := mertensLagPrimitive_eq_inversion hT1 hTU
  have hbr := mertensLag_bracket_eq hU1 hUW
  have hb1 : -(η / 3) < -(U ^ 2 / (1 + U) * mertensErrorRemainder W) := by
    have := mul_lt_mul_of_pos_left hGW hrU0
    rw [mul_div_cancel₀ _ hrU0.ne'] at this
    linarith
  have hb2 : -(η / 3) ≤ U ^ 2 / (1 + U) * ((1 + W) / W ^ 2 * mertensLagPrimitive W) := by
    have hW0' : 0 < W := by linarith
    have h := neg_abs_le ((1 + W) / W ^ 2 * mertensLagPrimitive W)
    rw [abs_mul, abs_of_pos (div_pos (by linarith) (pow_pos hW0' 2))] at h
    have := mul_le_mul_of_nonneg_left h hrU0.le
    linarith
  have hb3 := neg_abs_le (U ^ 2 / (1 + U) * ∫ t in U..W, (t + 2) / t ^ 3 * mertensLagPrimitive t)
  have hb3' := (abs_mul_integral_lag_tail_le hΘ hU1 hUW).trans hKU
  have hrT0 : 0 ≤ T ^ 2 / (1 + T) := by positivity
  have hGT : -(g T * (T ^ 2 / (1 + T))) ≤ mertensErrorRemainder T * (T ^ 2 / (1 + T)) := by
    have := mul_le_mul_of_nonneg_right (hg T hT) hrT0; linarith
  have hint := integral_remainder_weight_ge hgc hgnn hg hT hT1 hTU (hB U hTU)
  rw [hinv, hbr]
  linarith only [hb1, hb2, hb3, hb3', hGT, hint]


/-! ## Assembly -/

/-- Nicolas's inequality at all large primorials gives `Nic(x) ≥ 0` for all large real `x`. -/
theorem eventually_nicolasDefect_nonneg_of_nicolas
    (hNic : ∀ᶠ n : ℕ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial n : ℕ) : ℝ))
      < ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ)) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ nicolasDefect x := by
  have hθ := eventually_two_fifths_le_theta
  have h1 : ∀ᶠ x : ℝ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial ⌊x⌋₊ : ℕ) : ℝ))
      < ((primorial ⌊x⌋₊ : ℕ) : ℝ) / ((primorial ⌊x⌋₊).totient : ℝ) :=
    tendsto_nat_floor_atTop.eventually hNic
  have h2 : ∀ᶠ x : ℝ in atTop, 2 / 5 * (⌊x⌋₊ : ℝ) ≤ Chebyshev.theta (⌊x⌋₊ : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).eventually hθ
  filter_upwards [h1, h2, eventually_ge_atTop (5 : ℝ)] with x hx hθx hx5
  have hn : (4 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : (4 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast this
  have hθ1 : 1 < Chebyshev.theta (⌊x⌋₊ : ℝ) := by linarith
  have hlθ : 0 < Real.log (Chebyshev.theta (⌊x⌋₊ : ℝ)) := Real.log_pos hθ1
  rw [primorial_div_totient_eq, log_primorial_eq_theta] at hx
  have hP := mertensPrimeProduct_pos ⌊x⌋₊
  have hR : 0 < Real.exp Real.eulerMascheroniConstant
      * Real.log (Chebyshev.theta (⌊x⌋₊ : ℝ)) := by positivity
  rw [← Real.log_lt_log_iff hR (inv_pos.mpr hP), Real.log_inv,
    Real.log_mul (Real.exp_pos _).ne' hlθ.ne', Real.log_exp] at hx
  unfold nicolasDefect
  rw [Chebyshev.theta_eq_theta_coe_floor x]
  linarith

/-- Under Nicolas's inequality and `Θ < b < 1`, `b ≥ 1/2`: for some `T₀ ≥ 4` and `c₁, c₂ ≥ 0`,
`G(T) ≥ -(c₁ e^{-T/2} + c₂ e^{(2b-2)T})/T` for every `T ≥ T₀`. -/
theorem exists_mertensErrorRemainder_lower_of_nicolas
    (hNic : ∀ᶠ x : ℝ in atTop, 0 ≤ nicolasDefect x) {b : ℝ} (hb : zeroReSup < b)
    (hb12 : 1 / 2 ≤ b) :
    ∃ T₀ c₁ c₂ : ℝ, 4 ≤ T₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ T, T₀ ≤ T →
      -((c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T)) / T)
        ≤ mertensErrorRemainder T := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_chebyshevPsi_sub_le_rpow hb
  obtain ⟨C₁, hC₁⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set D : ℝ := C₀ + |C₁| with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hev := hNic.and (eventually_two_fifths_le_theta.and (eventually_ge_atTop (Real.exp 4)))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hev
  refine ⟨max 4 (Real.log (max X₁ 1)), 8 * Real.log 4 + |C₁|, 35 / 4 * D ^ 2, le_max_left _ _,
    by positivity, by positivity, fun T hT => ?_⟩
  have hT4 : 4 ≤ T := le_trans (le_max_left _ _) hT
  set x := Real.exp T with hx
  have hx0 : 0 < x := Real.exp_pos T
  have hxX : X₁ ≤ x := by
    have h1 : Real.log (max X₁ 1) ≤ T := le_trans (le_max_right _ _) hT
    have h2 : max X₁ 1 ≤ x := by
      rw [hx, ← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X₁ 1))]
      exact Real.exp_le_exp.mpr h1
    exact le_trans (le_max_left _ _) h2
  obtain ⟨hN, hθ, hx4⟩ := hX₁ x hxX
  have hx4' : 4 ≤ x := by
    have := Real.add_one_le_exp (4 : ℝ); linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogx : Real.log x = T := Real.log_exp T
  have hlθ1 : 1 ≤ Real.log (Chebyshev.theta x) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 ≤ 2 / 5 * x := by
      have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h4 : 49 ≤ x := by
        have := Real.add_one_le_exp (4 : ℝ)
        have h5 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
        have h6 : 7 ≤ Real.exp 2 := by
          have h7 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          have := Real.exp_one_gt_d9
          nlinarith
        nlinarith
      linarith
    linarith
  have hC : Chebyshev.psi x - Chebyshev.theta x ≤ |C₁| * Real.sqrt x :=
    (hC₁ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  have hup := nicolasDefect_le hx4' hθ hlθ1 hC
  -- the square term
  have hsqrt_le : Real.sqrt x ≤ x ^ b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hb12
  have hθx : |Chebyshev.theta x - x| ≤ D * x ^ b := by
    have h1 := hC₀ x hx1
    have h2 := Chebyshev.theta_le_psi x
    have h3 : Chebyshev.psi x - Chebyshev.theta x ≤ |C₁| * x ^ b :=
      hC.trans (mul_le_mul_of_nonneg_left hsqrt_le (abs_nonneg _))
    rw [hD, add_mul]
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [abs_nonneg C₁, Real.rpow_nonneg hx0.le b]
  have hsq : (Chebyshev.theta x - x) ^ 2 / (x ^ 2 * Real.log x)
      ≤ D ^ 2 * Real.exp ((2 * b - 2) * T) / T := by
    rw [hlogx]
    have h1 : (Chebyshev.theta x - x) ^ 2 ≤ (D * x ^ b) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθx 2
    have h2 : (D * x ^ b) ^ 2 / x ^ 2 = D ^ 2 * Real.exp ((2 * b - 2) * T) := by
      have hxb : x ^ b = Real.exp (b * T) := by rw [hx, ← Real.exp_mul, mul_comm]
      have e1 : Real.exp (b * T) ^ 2 = Real.exp (2 * b * T) := by
        rw [sq, ← Real.exp_add]; ring_nf
      have e2 : x ^ 2 = Real.exp (2 * T) := by rw [hx, sq, ← Real.exp_add]; ring_nf
      rw [hxb, mul_pow, e1, e2, mul_div_assoc, ← Real.exp_sub]
      ring_nf
    have hT0 : 0 < T := by linarith
    calc (Chebyshev.theta x - x) ^ 2 / (x ^ 2 * T) ≤ (D * x ^ b) ^ 2 / (x ^ 2 * T) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = (D * x ^ b) ^ 2 / x ^ 2 / T := by rw [div_div]
      _ = D ^ 2 * Real.exp ((2 * b - 2) * T) / T := by rw [h2]
  have hfirst : (8 * Real.log 4 + |C₁|) / (Real.sqrt x * Real.log x)
      = (8 * Real.log 4 + |C₁|) * Real.exp (-T / 2) / T := by
    rw [hlogx, hx, sqrt_exp_eq_exp_half_mul,
      show Real.exp (-T / 2) = (Real.exp (1 / 2 * T))⁻¹ by
        rw [← Real.exp_neg]; ring_nf]
    have : 0 < T := by linarith
    field_simp
  have hGx : mertensErrorRemainder (Real.log x) = mertensErrorRemainder T := by rw [hlogx]
  rw [hGx, hfirst] at hup
  have hT0 : 0 < T := by linarith
  have e : (8 * Real.log 4 + |C₁|) * Real.exp (-T / 2) / T + 35 / 4 * (D ^ 2
      * Real.exp ((2 * b - 2) * T) / T)
      = ((8 * Real.log 4 + |C₁|) * Real.exp (-T / 2) + 35 / 4 * D ^ 2
        * Real.exp ((2 * b - 2) * T)) / T := by field_simp
  have := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 35 / 4 by norm_num)
  linarith


/-- The integral of the comparison weight: for `b < 1`,
`∫_T^U (c₁ e^{-s/2} + c₂ e^{(2b-2)s}) ds ≤ 2c₁ e^{-T/2} + c₂ e^{(2b-2)T}/(2 - 2b)`. -/
theorem integral_exp_weight_le {c₁ c₂ b : ℝ} (T U : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hb : b < 1) :
    ∫ s in T..U, (c₁ * Real.exp (-s / 2) + c₂ * Real.exp ((2 * b - 2) * s))
      ≤ 2 * c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) / (2 - 2 * b) := by
  have hne : 2 * b - 2 ≠ 0 := by linarith
  have hd : ∀ s ∈ uIcc T U, HasDerivAt
      (fun s : ℝ => -2 * c₁ * Real.exp (-s / 2) + c₂ * Real.exp ((2 * b - 2) * s) / (2 * b - 2))
      (c₁ * Real.exp (-s / 2) + c₂ * Real.exp ((2 * b - 2) * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => -2 * c₁ * Real.exp (-s / 2)) (c₁ * Real.exp (-s / 2)) s :=
      (((hasDerivAt_neg s).div_const 2).exp.const_mul (-2 * c₁)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun s : ℝ => c₂ * Real.exp ((2 * b - 2) * s) / (2 * b - 2))
        (c₂ * Real.exp ((2 * b - 2) * s)) s := by
      have := (((hasDerivAt_id' s).const_mul (2 * b - 2)).exp.const_mul c₂).div_const (2 * b - 2)
      refine this.congr_deriv ?_
      generalize Real.exp ((2 * b - 2) * s) = E
      have hb' : b - 1 ≠ 0 := by linarith
      field_simp
    exact h1.add h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable
    (by fun_prop) T U)]
  have hU1 := Real.exp_pos (-U / 2)
  have hU2 := Real.exp_pos ((2 * b - 2) * U)
  have hT2 := Real.exp_pos ((2 * b - 2) * T)
  generalize Real.exp ((2 * b - 2) * U) = EU at hU2 ⊢
  generalize Real.exp ((2 * b - 2) * T) = ET at hT2 ⊢
  have h2b : 0 < 2 - 2 * b := by linarith
  have e : c₂ * EU / (2 * b - 2) - c₂ * ET / (2 * b - 2) = c₂ * ET / (2 - 2 * b)
      - c₂ * EU / (2 - 2 * b) := by
    rw [show 2 * b - 2 = -(2 - 2 * b) by ring, div_neg, div_neg]; ring
  have h3 : 0 ≤ c₂ * EU / (2 - 2 * b) := div_nonneg (by positivity) h2b.le
  have h4 : 0 ≤ c₁ * Real.exp (-U / 2) := by positivity
  linarith

/-- From the remainder bound to a lag-primitive bound (`Θ < 1`, `b < 1`). -/
theorem mertensLagPrimitive_lower_of_remainder_lower (hΘ : zeroReSup < 1) {T₀ c₁ c₂ b : ℝ}
    (hT₀ : 4 ≤ T₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hb1 : b < 1)
    (hG : ∀ T, T₀ ≤ T → -((c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T)) / T)
        ≤ mertensErrorRemainder T) :
    ∀ T, T₀ ≤ T → -(3 * c₁ * Real.exp (-T / 2)
      + c₂ * (1 + 1 / (2 - 2 * b)) * Real.exp ((2 * b - 2) * T)) ≤ mertensLagPrimitive T := by
  set g : ℝ → ℝ := fun s => (c₁ * Real.exp (-s / 2) + c₂ * Real.exp ((2 * b - 2) * s))
    / max s 1 with hg
  have hmax : ∀ s : ℝ, 0 < max s 1 := fun s => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hgc : Continuous g := Continuous.div (by fun_prop) (by fun_prop) fun s => (hmax s).ne'
  have hgnn : ∀ s, 0 ≤ g s := fun s => div_nonneg (by positivity) (hmax s).le
  have hgG : ∀ s, T₀ ≤ s → -g s ≤ mertensErrorRemainder s := by
    intro s hs
    have hs1 : max s 1 = s := max_eq_left (by linarith)
    simp only [hg, hs1]
    exact hG s hs
  intro T hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set B : ℝ := (2 * c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) / (2 - 2 * b)) / T
    with hB
  have hBint : ∀ U, T ≤ U → ∫ s in T..U, g s ≤ B := by
    intro U hTU
    have hmono : ∫ s in T..U, g s ≤ ∫ s in T..U,
        (c₁ * Real.exp (-s / 2) + c₂ * Real.exp ((2 * b - 2) * s)) / T := by
      refine intervalIntegral.integral_mono_on hTU (hgc.intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
      have hs1 : max s 1 = s := max_eq_left (by linarith [hs.1])
      simp only [hg, hs1]
      exact div_le_div_of_nonneg_left (by positivity) hT0 hs.1
    rw [intervalIntegral.integral_div] at hmono
    refine hmono.trans ?_
    rw [hB]
    exact div_le_div_of_nonneg_right (integral_exp_weight_le T U hc₁ hc₂ hb1) hT0.le
  have htr := mertensLagPrimitive_ge_of_remainder_ge hΘ hT₀ hgc hgnn hgG hT hBint
  have hT1' : max T 1 = T := max_eq_left hT1
  have hgT : g T * (T ^ 2 / (1 + T))
      ≤ c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) := by
    simp only [hg, hT1']
    have hr : T ^ 2 / (1 + T) ≤ T := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hnum : 0 ≤ c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) := by positivity
    calc (c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T)) / T * (T ^ 2 / (1 + T))
        ≤ (c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T)) / T * T :=
          mul_le_mul_of_nonneg_left hr (div_nonneg hnum hT0.le)
      _ = c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) := by field_simp
  have hBle : B ≤ 2 * c₁ * Real.exp (-T / 2)
      + c₂ * Real.exp ((2 * b - 2) * T) / (2 - 2 * b) := by
    rw [hB, div_le_iff₀ hT0]
    have : 0 ≤ 2 * c₁ * Real.exp (-T / 2) + c₂ * Real.exp ((2 * b - 2) * T) / (2 - 2 * b) :=
      add_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
    nlinarith
  have e : c₂ * (1 + 1 / (2 - 2 * b)) * Real.exp ((2 * b - 2) * T)
      = c₂ * Real.exp ((2 * b - 2) * T) + c₂ * Real.exp ((2 * b - 2) * T) / (2 - 2 * b) := by
    have : 2 - 2 * b ≠ 0 := by linarith
    field_simp
  linarith

/-- `Φ(L) = e^{L/2} v(L) - (log 2π - S(e^L)) e^{-L/2}` for `L > 0`. -/
theorem weilLagFunctionReal_eq_lagPrimitive {L : ℝ} (hL : 0 < L) :
    weilLagFunctionReal L = Real.exp (L / 2) * mertensLagPrimitive L
      - (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) * Real.exp (-L / 2) := by
  have hid := exp_mul_mertensLagPrimitive_eq hL
  have hhalf : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hEL : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : weilLagFunctionReal L
      = Real.exp (-L / 2) * (Real.exp (L / 2) * weilLagFunctionReal L) := by
    rw [← mul_assoc, mul_comm (Real.exp (-L / 2)), hhalf, one_mul]
  rw [h2]
  have h1 : Real.exp (L / 2) * weilLagFunctionReal L
      = Real.exp L * mertensLagPrimitive L - Real.log (2 * Real.pi)
        + trivialZeroSeriesReal (Real.exp L) := by linarith
  rw [h1, hEL]
  linear_combination (Real.exp (L / 2) * mertensLagPrimitive L) * (by
    rw [mul_comm]; exact hhalf : Real.exp (-L / 2) * Real.exp (L / 2) = 1)

/-- A lag-primitive lower bound gives an exponential lower bound for `Φ` beyond `T₀`. -/
theorem weilLagFunctionReal_lower_of_lagPrimitive_lower {A₁ A₂ b L : ℝ} (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hL0 : 0 < L)
    (hv : -(A₁ * Real.exp (-L / 2) + A₂ * Real.exp ((2 * b - 2) * L)) ≤ mertensLagPrimitive L) :
    -((A₁ + A₂ + 2) * Real.exp (max 0 (2 * b - 3 / 2) * L)) ≤ weilLagFunctionReal L := by
  rw [weilLagFunctionReal_eq_lagPrimitive hL0]
  have hX1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL0.le
  have hS0 := trivialZeroSeriesReal_nonneg hX1
  have hlog := log_two_mul_pi_lt_two
  have he1 : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have he2 : Real.exp (L / 2) * Real.exp ((2 * b - 2) * L)
      = Real.exp ((2 * b - 3 / 2) * L) := by rw [← Real.exp_add]; ring_nf
  have he3 : Real.exp ((2 * b - 3 / 2) * L) ≤ Real.exp (max 0 (2 * b - 3 / 2) * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL0.le)
  have he0 : 1 ≤ Real.exp (max 0 (2 * b - 3 / 2) * L) :=
    Real.one_le_exp (mul_nonneg (le_max_left _ _) hL0.le)
  have he4 : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEh := Real.exp_pos (L / 2)
  have hv' := mul_le_mul_of_nonneg_left hv hEh.le
  rw [mul_neg, mul_add, mul_left_comm, he1, mul_one, mul_left_comm, he2] at hv'
  have hterm : (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))
      * Real.exp (-L / 2) ≤ 2 := by
    have h0 : Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L) ≤ 2 := by linarith
    have h0' : 0 ≤ Real.exp (-L / 2) := (Real.exp_pos _).le
    have h0'' : 0 ≤ Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L) := by
      have := trivialZeroSeriesReal_le_one hX1
      have : 1 < Real.log (2 * Real.pi) := by
        rw [Real.lt_log_iff_exp_lt (by positivity)]
        have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
      linarith
    nlinarith
  have h5 : A₂ * Real.exp ((2 * b - 3 / 2) * L) ≤ A₂ * Real.exp (max 0 (2 * b - 3 / 2) * L) :=
    mul_le_mul_of_nonneg_left he3 hA₂
  nlinarith

/-- **Nicolas's inequality forces the Riemann hypothesis when `Θ < 1`.**  If
`N_n/φ(N_n) > e^γ log log N_n` for every large `n` and the zeros of `ζ` have real parts bounded away
from `1`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_nicolas_of_zeroReSup_lt_one
    (hNic : ∀ᶠ n : ℕ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial n : ℕ) : ℝ))
      < ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ))
    (hΘ : zeroReSup < 1) : RiemannHypothesis := by
  have hΘh := half_le_zeroReSup
  set b : ℝ := (2 * zeroReSup + 1) / 3 with hbdef
  have hb : zeroReSup < b := by rw [hbdef]; linarith
  have hb1 : b < 1 := by rw [hbdef]; linarith
  have hb12 : 1 / 2 ≤ b := by rw [hbdef]; linarith
  obtain ⟨T₀, c₁, c₂, hT₀, hc₁, hc₂, hG⟩ :=
    exists_mertensErrorRemainder_lower_of_nicolas (eventually_nicolasDefect_nonneg_of_nicolas hNic)
      hb hb12
  have hv := mertensLagPrimitive_lower_of_remainder_lower hΘ hT₀ hc₁ hc₂ hb1 hG
  set A₂ : ℝ := c₂ * (1 + 1 / (2 - 2 * b)) with hA₂
  have hA₂0 : 0 ≤ A₂ := mul_nonneg hc₂ (add_nonneg zero_le_one (div_nonneg zero_le_one
    (by linarith)))
  set a : ℝ := max 0 (2 * b - 3 / 2) with ha
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha12 : a < 1 / 2 := max_lt (by norm_num) (by linarith)
  have hW := lagWeightTotal_nonneg
  set M : ℝ := (3 * c₁ + A₂ + 2) + Real.exp (T₀ / 2) * lagWeightTotal with hM
  have hEW : 0 ≤ Real.exp (T₀ / 2) * lagWeightTotal := mul_nonneg (Real.exp_pos _).le hW
  have hΦ : ∀ L, 0 ≤ L → -(M * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hea : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    rcases le_or_gt T₀ L with hLT | hLT
    · have hL0 : 0 < L := by linarith
      have h1 := weilLagFunctionReal_lower_of_lagPrimitive_lower (by positivity) hA₂0 hL0
        (hv L hLT)
      have h2 : (3 * c₁ + A₂ + 2) * Real.exp (a * L) ≤ M * Real.exp (a * L) :=
        mul_le_mul_of_nonneg_right (by rw [hM]; linarith) (Real.exp_pos _).le
      linarith
    · have hb' := abs_weilLagFunctionReal_le L
      rw [abs_of_nonneg hL] at hb'
      have h1 : Real.exp (L / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (T₀ / 2) * lagWeightTotal :=
        mul_le_mul_of_nonneg_right h1 hW
      have hM0 : 0 ≤ M := by rw [hM]; linarith
      have h3 : Real.exp (T₀ / 2) * lagWeightTotal ≤ M := by rw [hM]; linarith
      have h4 : M ≤ M * Real.exp (a * L) := le_mul_of_one_le_right hM0 hea
      have := (abs_le.mp hb').1
      linarith
  have hre := re_le_half_add_of_neg_exp_le_weilLagFunctionReal ha0 ha12 hΦ
  have hΘa : zeroReSup ≤ 1 / 2 + a := zeroReSup_le_of_forall_re_le hre
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hqΘ := re_le_zeroReSup q
  rcases le_total (2 * b - 3 / 2) 0 with h | h
  · have : a = 0 := by rw [ha]; exact max_eq_left h
    rw [this] at hΘa
    linarith
  · have : a = 2 * b - 3 / 2 := by rw [ha]; exact max_eq_right h
    rw [this, hbdef] at hΘa
    linarith

end

end RHTower
