import GaloisForLFunctions.RHTower.MertensProductDiamondPintz
import GaloisForLFunctions.RHTower.NicolasTotientLandau
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier

/-!
# The sharp Mertens remainder and Nicolas's inequality under the Riemann hypothesis

Put `g(s) = (e^s - ψ(e^s)) e^{-s}` and `v(T) = γ + 1 - ∫_0^T g`.  Abel summation gives
`v(T) = Σ_{n ≤ e^T} Λ(n)/n - ψ(e^T)e^{-T} - T + γ + 1`, and the prime side of the lag function
`Φ(L) = Σ_ρ e^{L(ρ - 1/2)}/(ρ(1 - ρ))` reads

```text
e^L v(L) = e^{L/2} Φ(L) + log 2π - S(e^L),        0 ≤ S ≤ 1.
```

Under the Riemann hypothesis `|Φ| ≤ a₁ = 2 + γ - log 4π < 3/10`, so
`|v(L)| ≤ a₁ e^{-L/2} + 2e^{-L}`.
Integrating the Mertens remainder `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)` by parts against `v`
gives the sharp bound

```text
|R(x) - (ψ(x) - x)/(x log x)| ≤ (a₁ + 10/log x)/(√x log x)        (x ≥ e⁴, RH).
```

Consequently, with `N_n = ∏_{p ≤ n} p`, Nicolas's inequality `N_n/φ(N_n) > e^γ log log N_n` holds
for every large `n`: its defect is at least `(θ(√x)/√x - a₁ - 10/log x)/(√x log x)`, because
`ψ - θ ≥ θ(√x)`, the prime tails `P - A` are nonnegative and `log log θ(x) ≤ log log x +
(θ(x) - x)/(x log x)`.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The lag primitive -/

/-- `g(s) = (e^s - ψ(e^s)) e^{-s}`. -/
def mertensLagDensity (s : ℝ) : ℝ := (Real.exp s - Chebyshev.psi (Real.exp s)) * Real.exp (-s)

theorem intervalIntegrable_mertensLagDensity (a b : ℝ) :
    IntervalIntegrable mertensLagDensity volume a b :=
  (intervalIntegrable_chebyshevDeficit a b).mul_continuousOn
    (Real.continuous_exp.comp continuous_neg).continuousOn

/-- `v(T) = γ + 1 - ∫_0^T g`. -/
def mertensLagPrimitive (T : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + 1 - ∫ s in (0 : ℝ)..T, mertensLagDensity s

theorem continuous_mertensLagPrimitive : Continuous mertensLagPrimitive :=
  continuous_const.sub (intervalIntegral.continuous_primitive
    (fun a b => intervalIntegrable_mertensLagDensity a b) 0)

/-- `∫_1^{e^T} E(t)/t² dt = -∫_0^T g`. -/
theorem integral_chebyshevError_div_sq_eq_log_variable {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (1 : ℝ)..Real.exp T, chebyshevError t / t ^ 2
      = -∫ s in (0 : ℝ)..T, mertensLagDensity s := by
  have h1 : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
  rw [intervalIntegral.integral_of_le h1, intervalIntegral.integral_of_le hT,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, ← integral_neg]
  have himg : Icc (1 : ℝ) (Real.exp T) = Real.exp '' Icc 0 T := by
    rw [Real.image_exp_Icc, Real.exp_zero]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, mertensLagDensity, chebyshevError, Real.exp_neg]
  have he := (Real.exp_pos s).ne'
  field_simp
  ring

/-- **Abel summation for the lag primitive.** -/
theorem mertensLagPrimitive_eq {T : ℝ} (hT : 0 ≤ T) :
    mertensLagPrimitive T = (∑ k ∈ Finset.Icc 0 ⌊Real.exp T⌋₊, vonMangoldt k / k)
      - Chebyshev.psi (Real.exp T) / Real.exp T - T + Real.eulerMascheroniConstant + 1 := by
  have h1 : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
  have hkey := mertens_key h1
  rw [integral_chebyshevError_div_sq_eq_log_variable hT, Real.log_exp] at hkey
  unfold mertensLagPrimitive
  unfold chebyshevError at hkey
  have he := (Real.exp_pos T).ne'
  rw [sub_div, div_self he] at hkey
  linarith

/-- **The lag identity.**  `e^L v(L) = e^{L/2} Φ(L) + log 2π - S(e^L)` for `L > 0`. -/
theorem exp_mul_mertensLagPrimitive_eq {L : ℝ} (hL : 0 < L) :
    Real.exp L * mertensLagPrimitive L = Real.exp (L / 2) * weilLagFunctionReal L
      + Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L) := by
  rw [weilLagFunctionReal_eq_prime_side hL, mertensLagPrimitive_eq hL.le, mertensSum_eq_Icc_zero]
  have hexp : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have he := (Real.exp_pos L).ne'
  rw [← mul_assoc, hexp, one_mul]
  field_simp
  ring

theorem poleSharpConstant_lt_three_tenths : poleSharpConstant < 3 / 10 := by
  unfold poleSharpConstant
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have h12 : (12 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hlog12 : Real.log 12 ≤ Real.log (4 * Real.pi) := Real.log_le_log (by norm_num) h12
  have h12' : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ (2 : ℕ) * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have hlog2 := Real.log_two_gt_d9
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  linarith

/-- Under RH, `|v(L)| ≤ a₁ e^{-L/2} + 2 e^{-L}` for `L > 0`. -/
theorem abs_mertensLagPrimitive_le_of_riemannHypothesis (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 0 < L) :
    |mertensLagPrimitive L| ≤ poleSharpConstant * Real.exp (-L / 2) + 2 * Real.exp (-L) := by
  have hΦ : |weilLagFunctionReal L| ≤ poleSharpConstant := by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH L
    rwa [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  have hX1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp hL.le
  have hS0 := trivialZeroSeriesReal_nonneg hX1
  have hS1 := trivialZeroSeriesReal_le_one hX1
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hid := exp_mul_mertensLagPrimitive_eq hL
  have he := Real.exp_pos L
  have hv : mertensLagPrimitive L = Real.exp (-L) * (Real.exp (L / 2) * weilLagFunctionReal L
      + Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)) := by
    rw [← hid, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hhalf : Real.exp (-L) * Real.exp (L / 2) = Real.exp (-L / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hv, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.exp (L / 2) * weilLagFunctionReal L + Real.log (2 * Real.pi)
      - trivialZeroSeriesReal (Real.exp L)|
      ≤ Real.exp (L / 2) * poleSharpConstant + 2 := by
    have h2 : |Real.exp (L / 2) * weilLagFunctionReal L|
        ≤ Real.exp (L / 2) * poleSharpConstant := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left hΦ (Real.exp_pos _).le
    have h3 : |Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    calc _ = |Real.exp (L / 2) * weilLagFunctionReal L
            + (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L))| := by ring_nf
      _ ≤ |Real.exp (L / 2) * weilLagFunctionReal L|
            + |Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp L)| := abs_add_le _ _
      _ ≤ _ := add_le_add h2 h3
  calc Real.exp (-L) * |Real.exp (L / 2) * weilLagFunctionReal L + Real.log (2 * Real.pi)
        - trivialZeroSeriesReal (Real.exp L)|
      ≤ Real.exp (-L) * (Real.exp (L / 2) * poleSharpConstant + 2) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = poleSharpConstant * (Real.exp (-L) * Real.exp (L / 2)) + 2 * Real.exp (-L) := by ring
    _ = poleSharpConstant * Real.exp (-L / 2) + 2 * Real.exp (-L) := by rw [hhalf]


/-! ## The sharp remainder -/

/-- **Integration by parts against the lag primitive.**  With `h(s) = (1 + s)/s²`,
`∫_T^U (e^s - ψ(e^s)) w(s) ds = h(T)v(T) - h(U)v(U) - ∫_T^U (s + 2)/s³ · v(s) ds`. -/
theorem integral_deficit_mertensAbelWeight_eq {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    ∫ s in T..U, (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s
      = (1 + T) / T ^ 2 * mertensLagPrimitive T - (1 + U) / U ^ 2 * mertensLagPrimitive U
        - ∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s := by
  set Q : ℝ → ℝ := fun s => ∫ r in T..s, mertensLagDensity r with hQ
  have hi : IntervalIntegrable mertensLagDensity volume T U :=
    intervalIntegrable_mertensLagDensity T U
  have hQac : AbsolutelyContinuousOnInterval Q T U :=
    hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hQv : ∀ s, Q s = mertensLagPrimitive T - mertensLagPrimitive s := by
    intro s
    simp only [hQ, mertensLagPrimitive]
    rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_mertensLagDensity 0 s)
      (intervalIntegrable_mertensLagDensity 0 T)]
    ring
  set h : ℝ → ℝ := fun s => (1 + s) / s ^ 2 with hh
  have hpos : ∀ s ∈ uIcc T U, 0 < s := fun s hs => by
    rw [uIcc_of_le hTU] at hs; linarith [hs.1]
  have hhd : ∀ s ∈ uIcc T U, HasDerivAt h (-((s + 2) / s ^ 3)) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    have := ((hasDerivAt_id s).const_add 1).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcd : ContDiffOn ℝ 1 h (uIcc T U) :=
    (contDiffOn_const.add contDiffOn_id).div (contDiffOn_id.pow 2) fun s hs =>
      pow_ne_zero 2 (hpos s hs).ne'
  have hparts := hcd.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hQac
  have hleft : (∫ s in T..U, h s * deriv Q s)
      = ∫ s in T..U, (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt Q (mertensLagDensity s) s := hs (uIoc_subset_uIcc hmem) T left_mem_uIcc
    rw [hd.deriv, hh, mertensLagDensity, mertensAbelWeight]
    ring
  have hright : (∫ s in T..U, deriv h s * Q s)
      = ∫ s in T..U, -((s + 2) / s ^ 3) * (mertensLagPrimitive T - mertensLagPrimitive s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [(hhd s hs).deriv, hQv]
  have hQT : Q T = 0 := by simp [hQ]
  rw [hleft, hright, hQT, mul_zero, sub_zero, hQv U] at hparts
  have hc : ContinuousOn (fun s : ℝ => (s + 2) / s ^ 3) (uIcc T U) :=
    (continuousOn_id.add continuousOn_const).div (continuousOn_id.pow 3) fun s hs =>
      pow_ne_zero 3 (hpos s hs).ne'
  have hint1 : IntervalIntegrable (fun s : ℝ => (s + 2) / s ^ 3) volume T U := hc.intervalIntegrable
  have hint2 : IntervalIntegrable (fun s => (s + 2) / s ^ 3 * mertensLagPrimitive s) volume T U :=
    (hc.mul continuous_mertensLagPrimitive.continuousOn).intervalIntegrable
  have hFTC : ∫ s in T..U, (s + 2) / s ^ 3 = h T - h U := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hhd hc.neg.intervalIntegrable
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hsplit : ∫ s in T..U, -((s + 2) / s ^ 3) * (mertensLagPrimitive T - mertensLagPrimitive s)
      = -(mertensLagPrimitive T * ∫ s in T..U, (s + 2) / s ^ 3)
        + ∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s := by
    rw [show (∫ s in T..U, -((s + 2) / s ^ 3) * (mertensLagPrimitive T - mertensLagPrimitive s))
        = ∫ s in T..U, ((-mertensLagPrimitive T) * ((s + 2) / s ^ 3)
          + (s + 2) / s ^ 3 * mertensLagPrimitive s) from
        intervalIntegral.integral_congr fun s _ => by ring,
      intervalIntegral.integral_add (hint1.const_mul _) hint2, intervalIntegral.integral_const_mul]
    ring
  rw [hparts, hsplit, hFTC]
  simp only [hh]
  ring

/-- The pieces of the by-parts identity are small under RH. -/
theorem abs_mertensLagPrimitive_terms_le (hRH : RiemannHypothesis) {T U : ℝ} (hT : 4 ≤ T)
    (hTU : T ≤ U) :
    |(1 + T) / T ^ 2 * mertensLagPrimitive T|
        + |∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s|
      ≤ (poleSharpConstant + 10 / T) * (Real.exp (-T / 2) / T) := by
  have hT0 : 0 < T := by linarith
  have ha := poleSharpConstant_pos
  have ha3 := poleSharpConstant_lt_three_tenths
  set a := poleSharpConstant with hadef
  set A := Real.exp (-T / 2) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have hAA : Real.exp (-T) = A * A := by rw [hA, ← Real.exp_add]; ring_nf
  have hA2 : A * (T + 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (T / 2)
    have h2 : Real.exp (T / 2) * A = 1 := by rw [hA, ← Real.exp_add]; ring_nf; exact Real.exp_zero
    nlinarith
  -- the boundary term
  have hb : |(1 + T) / T ^ 2 * mertensLagPrimitive T|
      ≤ (1 + T) / T ^ 2 * (a * A + 2 * (A * A)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_mertensLagPrimitive_le_of_riemannHypothesis hRH hT0
    rwa [← hA, hAA] at this
  -- the interior term
  have hi : |∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s|
      ≤ 2 / T ^ 2 * (2 * a * A + 2 * (A * A)) := by
    have hg : IntervalIntegrable (fun s => 2 / T ^ 2 * (a * Real.exp (-s / 2) + 2 * Real.exp (-s)))
        volume T U := by
      refine (Continuous.intervalIntegrable ?_ _ _)
      exact continuous_const.mul ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_neg.div_const 2))).add (continuous_const.mul
          (Real.continuous_exp.comp continuous_neg)))
    have hpt : ∀ᵐ s ∂volume, s ∈ Ioc T U → ‖(s + 2) / s ^ 3 * mertensLagPrimitive s‖
        ≤ 2 / T ^ 2 * (a * Real.exp (-s / 2) + 2 * Real.exp (-s)) := by
      refine Filter.Eventually.of_forall fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hsT : T ≤ s := hs.1.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      have h1 := abs_mertensLagPrimitive_le_of_riemannHypothesis hRH hs0
      have hk : (s + 2) / s ^ 3 ≤ 2 / T ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (s + 2) * T ^ 2 ≤ (s + 2) * s ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0.le hsT 2) (by linarith)
        nlinarith
      calc (s + 2) / s ^ 3 * |mertensLagPrimitive s|
          ≤ (s + 2) / s ^ 3 * (a * Real.exp (-s / 2) + 2 * Real.exp (-s)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 2 / T ^ 2 * (a * Real.exp (-s / 2) + 2 * Real.exp (-s)) :=
            mul_le_mul_of_nonneg_right hk (by positivity)
    have hle := intervalIntegral.norm_integral_le_of_norm_le hTU hpt hg
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    have hd1 : ∀ s ∈ uIcc T U, HasDerivAt (fun s : ℝ => -2 * Real.exp (-s / 2))
        (Real.exp (-s / 2)) s := by
      intro s _
      have := ((hasDerivAt_neg s).div_const 2).exp.const_mul (-2)
      refine this.congr_deriv ?_
      ring
    have hd2 : ∀ s ∈ uIcc T U, HasDerivAt (fun s : ℝ => -Real.exp (-s)) (Real.exp (-s)) s := by
      intro s _
      have := (hasDerivAt_neg s).exp.neg
      refine this.congr_deriv ?_
      ring
    have hI1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd1
      ((Real.continuous_exp.comp (continuous_neg.div_const 2)).intervalIntegrable T U)
    have hI2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd2
      ((Real.continuous_exp.comp continuous_neg).intervalIntegrable T U)
    have i1 : IntervalIntegrable (fun x : ℝ => a * Real.exp (-x / 2)) volume T U :=
      Continuous.intervalIntegrable (by fun_prop) T U
    have i2 : IntervalIntegrable (fun x : ℝ => 2 * Real.exp (-x)) volume T U :=
      Continuous.intervalIntegrable (by fun_prop) T U
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI1, hI2]
    have hU1 := Real.exp_pos (-U / 2)
    have hU2 := Real.exp_pos (-U)
    have hTA : Real.exp (-T / 2) = A := rfl
    rw [hTA, hAA]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  -- the final arithmetic
  have hA3 : A ≤ 1 / 3 := by
    have : 6 ≤ T + 2 := by linarith
    nlinarith
  have hkey : 5 * a * A + A * A * (2 * T + 6) ≤ 10 * A := by
    have h1 : A * (2 * T + 6) ≤ 5 := by nlinarith
    have h2 : 5 * a + A * (2 * T + 6) ≤ 10 := by linarith
    nlinarith
  have hsum : (1 + T) / T ^ 2 * (a * A + 2 * (A * A)) + 2 / T ^ 2 * (2 * a * A + 2 * (A * A))
      = (a * T * A + (5 * a * A + A * A * (2 * T + 6))) / T ^ 2 := by
    field_simp; ring
  have hgoal : (a + 10 / T) * (A / T) = (a * T * A + 10 * A) / T ^ 2 := by field_simp
  calc _ ≤ (1 + T) / T ^ 2 * (a * A + 2 * (A * A)) + 2 / T ^ 2 * (2 * a * A + 2 * (A * A)) :=
        add_le_add hb hi
    _ = (a * T * A + (5 * a * A + A * A * (2 * T + 6))) / T ^ 2 := hsum
    _ ≤ (a * T * A + 10 * A) / T ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity); linarith
    _ = (a + 10 / T) * (A / T) := hgoal.symm

/-- Sign changes of the remainder under RH: `G(U) > -η` and `G(U) < η` for arbitrarily large `U`. -/
theorem frequently_mertensErrorRemainder_near_zero (hRH : RiemannHypothesis) {η : ℝ}
    (hη : 0 < η) :
    (∃ᶠ U : ℝ in atTop, -η < mertensErrorRemainder U) ∧
      ∃ᶠ U : ℝ in atTop, mertensErrorRemainder U < η := by
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hsm := eventually_abs_chebyshevError_div_lt_of_riemannHypothesis hRH hη
  have hG : ∀ x : ℝ, 0 < x → mertensErrorRemainder (Real.log x)
      = mertensError x - (Chebyshev.psi x - x) / (x * Real.log x) := fun x hx => by
    rw [mertensErrorRemainder, Real.exp_log hx]
  constructor
  · refine Real.tendsto_log_atTop.frequently ?_
    refine (((frequently_rpow_lt_mertensError hb).and_eventually
      (hsm.and (eventually_gt_atTop 0)))).mono fun x ⟨h, hs, hx⟩ => ?_
    rw [hG x hx]
    have := Real.rpow_nonneg hx.le (1 / 4 - 1)
    have := (abs_lt.mp hs).2
    linarith
  · refine Real.tendsto_log_atTop.frequently ?_
    refine (((frequently_mertensError_lt_neg_rpow hb).and_eventually
      (hsm.and (eventually_gt_atTop 0)))).mono fun x ⟨h, hs, hx⟩ => ?_
    rw [hG x hx]
    have := Real.rpow_nonneg hx.le (1 / 4 - 1)
    have := (abs_lt.mp hs).1
    linarith

/-- **The sharp Mertens remainder under RH.**  For `T ≥ 4`,
`|G(T)| ≤ (a₁ + 10/T) e^{-T/2}/T`, i.e.
`|R(x) - (ψ(x) - x)/(x log x)| ≤ (a₁ + 10/log x)/(√x log x)`. -/
theorem abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis (hRH : RiemannHypothesis) {T : ℝ}
    (hT : 4 ≤ T) :
    |mertensErrorRemainder T| ≤ (poleSharpConstant + 10 / T) * (Real.exp (-T / 2) / T) := by
  have hT0 : 0 < T := by linarith
  set M := (poleSharpConstant + 10 / T) * (Real.exp (-T / 2) / T) with hM
  have hl2 : Real.log 2 ≤ T := by have := Real.log_two_lt_d9; linarith
  -- `G(T) - G(U)` is the by-parts expression
  have hdiff : ∀ U, T ≤ U → mertensErrorRemainder T - mertensErrorRemainder U
      = (1 + T) / T ^ 2 * mertensLagPrimitive T - (1 + U) / U ^ 2 * mertensLagPrimitive U
        - ∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s := fun U hU => by
    rw [mertensErrorRemainder_sub_eq hl2 hU, integral_deficit_mertensAbelWeight_eq hT0 hU]
  -- the `U`-boundary term tends to zero
  have hUterm : ∀ η > 0, ∀ᶠ U : ℝ in atTop, |(1 + U) / U ^ 2 * mertensLagPrimitive U| < η := by
    intro η hη
    filter_upwards [eventually_ge_atTop (max 1 (7 / η))] with U hU
    have hU1 : 1 ≤ U := le_trans (le_max_left _ _) hU
    have hU0 : 0 < U := by linarith
    have hUη : 7 / η ≤ U := le_trans (le_max_right _ _) hU
    have hv := abs_mertensLagPrimitive_le_of_riemannHypothesis hRH hU0
    have he1 : Real.exp (-U / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he2 : Real.exp (-U) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have ha3 := poleSharpConstant_lt_three_tenths
    have ha0 := poleSharpConstant_pos
    have hv3 : |mertensLagPrimitive U| ≤ 3 := by nlinarith
    rw [abs_mul, abs_of_pos (by positivity)]
    have h1 : (1 + U) / U ^ 2 ≤ 2 / U := by
      rw [div_le_div_iff₀ (by positivity) hU0]; nlinarith
    calc (1 + U) / U ^ 2 * |mertensLagPrimitive U| ≤ 2 / U * 3 :=
          mul_le_mul h1 hv3 (abs_nonneg _) (by positivity)
      _ = 6 / U := by ring
      _ < η := by
          rw [div_lt_iff₀ hU0]
          have := (div_le_iff₀ hη).mp hUη
          linarith
  have hterms := fun U (hU : T ≤ U) => abs_mertensLagPrimitive_terms_le hRH hT hU
  rw [abs_le]
  constructor
  · refine neg_le.mpr (le_of_forall_pos_lt_add fun η hη => ?_)
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨U, hGU, hUt, hTU⟩ :=
      (((frequently_mertensErrorRemainder_near_zero hRH hη2).1.and_eventually
      ((hUterm (η / 2) hη2).and (eventually_ge_atTop T))).exists)
    have h1 := hdiff U hTU
    have h2 := hterms U hTU
    have h3 := neg_abs_le ((1 + T) / T ^ 2 * mertensLagPrimitive T)
    have h4 := le_abs_self (∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s)
    have h5 := le_abs_self ((1 + U) / U ^ 2 * mertensLagPrimitive U)
    linarith
  · refine le_of_forall_pos_lt_add fun η hη => ?_
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨U, hGU, hUt, hTU⟩ :=
      (((frequently_mertensErrorRemainder_near_zero hRH hη2).2.and_eventually
      ((hUterm (η / 2) hη2).and (eventually_ge_atTop T))).exists)
    have h1 := hdiff U hTU
    have h2 := hterms U hTU
    have h3 := le_abs_self ((1 + T) / T ^ 2 * mertensLagPrimitive T)
    have h4 := neg_abs_le (∫ s in T..U, (s + 2) / s ^ 3 * mertensLagPrimitive s)
    have h5 := neg_abs_le ((1 + U) / U ^ 2 * mertensLagPrimitive U)
    linarith


/-! ## Nicolas's inequality -/

/-- The Nicolas defect `-log ∏_{p ≤ x}(1 - 1/p) - γ - log log θ(x)`. -/
def nicolasDefect (x : ℝ) : ℝ :=
  -Real.log (mertensPrimeProduct ⌊x⌋₊) - Real.eulerMascheroniConstant
    - Real.log (Real.log (Chebyshev.theta x))

/-- `log log θ(x) ≤ log log x + (θ(x) - x)/(x log x)` when `θ(x) > 1` and `x > 1`. -/
theorem log_log_theta_le {x : ℝ} (hx : 1 < x) (hθ : 1 < Chebyshev.theta x) :
    Real.log (Real.log (Chebyshev.theta x))
      ≤ Real.log (Real.log x) + (Chebyshev.theta x - x) / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hθ0 : 0 < Chebyshev.theta x := by linarith
  have hlθ : 0 < Real.log (Chebyshev.theta x) := Real.log_pos hθ
  have h1 : Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)
      ≤ Real.log (Chebyshev.theta x) / Real.log x - 1 := by
    rw [← Real.log_div hlθ.ne' hlx.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hlθ hlx)
  have h2 : Real.log (Chebyshev.theta x) - Real.log x ≤ Chebyshev.theta x / x - 1 := by
    rw [← Real.log_div hθ0.ne' hx0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hθ0 hx0)
  have h3 : Real.log (Chebyshev.theta x) / Real.log x - 1
      = (Real.log (Chebyshev.theta x) - Real.log x) / Real.log x := by field_simp
  have h4 : (Real.log (Chebyshev.theta x) - Real.log x) / Real.log x
      ≤ (Chebyshev.theta x / x - 1) / Real.log x := div_le_div_of_nonneg_right h2 hlx.le
  have h5 : (Chebyshev.theta x / x - 1) / Real.log x
      = (Chebyshev.theta x - x) / (x * Real.log x) := by field_simp
  linarith

/-- `ψ(x) - θ(x) ≥ θ(√x)` for `x ≥ 4`. -/
theorem theta_sqrt_le_psi_sub_theta {x : ℝ} (hx : 4 ≤ x) :
    Chebyshev.theta (Real.sqrt x) ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith
  rw [Chebyshev.psi_eq_theta_add_sum_theta (by linarith), add_sub_cancel_left]
  have h2 : 2 ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊ := by
    simp only [Finset.mem_Icc, le_refl, true_and]
    apply Nat.le_floor
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hl2]
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hx
    push_cast
    linarith
  have h := Finset.single_le_sum (f := fun n : ℕ => Chebyshev.theta (x ^ ((1 : ℝ) / n)))
    (fun n _ => Chebyshev.theta_nonneg _) h2
  rwa [Real.sqrt_eq_rpow, show ((1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 / 2 by norm_num] at *

/-- Chebyshev's lower bound in the form `θ(y) ≥ (2/5) y` for large `y`. -/
theorem eventually_two_fifths_le_theta :
    ∀ᶠ y : ℝ in atTop, 2 / 5 * y ≤ Chebyshev.theta y := by
  filter_upwards [(isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 100 by norm_num), eventually_ge_atTop (10000 : ℝ)] with y hy hy1
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hly,
    abs_of_nonneg (Real.rpow_nonneg hy0.le _), ← Real.sqrt_eq_rpow] at hy
  have hθ := Chebyshev.theta_ge' (by linarith : (1 : ℝ) ≤ y)
  have hl2 := Real.log_two_gt_d9
  have hsy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hs100 : 100 ≤ Real.sqrt y := by
    rw [show (100 : ℝ) = Real.sqrt 10000 by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy1
  have hsqrt : Real.sqrt y ≤ y / 100 := by nlinarith
  have hlog2y : Real.log (y + 2) ≤ Real.log 2 + Real.log y := by
    rw [← Real.log_mul (by norm_num) hy0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h1 : 2 * Real.sqrt y * Real.log y ≤ y / 50 := by
    have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt y)
    nlinarith
  have h2 : Real.log (y + 2) ≤ 1 + y / 10000 := by nlinarith
  nlinarith

/-- **The Nicolas defect dominates the Mertens remainder.**  For `x ≥ 4` with `θ(x) > 1`,
`nicolasDefect x ≥ G(log x) + θ(√x)/(x log x)`. -/
theorem nicolasDefect_ge {x : ℝ} (hx : 4 ≤ x) (hθ : 1 < Chebyshev.theta x) :
    mertensErrorRemainder (Real.log x) + Chebyshev.theta (Real.sqrt x) / (x * Real.log x)
      ≤ nicolasDefect x := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := log_log_theta_le (by linarith) hθ
  have h2 := (mertensProductError_sub_mem hx).1
  have h3 := theta_sqrt_le_psi_sub_theta hx
  have h4 : Chebyshev.theta (Real.sqrt x) / (x * Real.log x)
      ≤ (Chebyshev.psi x - Chebyshev.theta x) / (x * Real.log x) :=
    div_le_div_of_nonneg_right h3 (by positivity)
  have hG : mertensErrorRemainder (Real.log x)
      = mertensError x - (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [mertensErrorRemainder, Real.exp_log hx0]
  have hsplit : (Chebyshev.psi x - Chebyshev.theta x) / (x * Real.log x)
      = (Chebyshev.psi x - x) / (x * Real.log x) - (Chebyshev.theta x - x) / (x * Real.log x) := by
    rw [← sub_div]; ring_nf
  unfold nicolasDefect
  unfold mertensProductError at h2
  linarith

/-- **Nicolas's inequality holds eventually under RH (real form).** -/
theorem eventually_nicolasDefect_pos_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, 0 < nicolasDefect x := by
  have ha3 := poleSharpConstant_lt_three_tenths
  have hθs : ∀ᶠ x : ℝ in atTop, 2 / 5 * Real.sqrt x ≤ Chebyshev.theta (Real.sqrt x) :=
    Real.tendsto_sqrt_atTop.eventually eventually_two_fifths_le_theta
  filter_upwards [hθs, eventually_two_fifths_le_theta, eventually_ge_atTop (Real.exp 101)]
    with x hθx hθ hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hl101 : 101 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hx4 : 4 ≤ x := by
    have := Real.add_one_le_exp (101 : ℝ); linarith
  have hθ1 : 1 < Chebyshev.theta x := by linarith
  have hlx : 0 < Real.log x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hND := nicolasDefect_ge hx4 hθ1
  have hG := abs_mertensErrorRemainder_le_sharp_of_riemannHypothesis hRH
    (by linarith : 4 ≤ Real.log x)
  have he : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [show -Real.log x / 2 = -(1 / 2 * Real.log x) by ring, Real.exp_neg,
      ← sqrt_exp_eq_exp_half_mul, Real.exp_log hx0]
  rw [he] at hG
  have hxx : x * Real.log x = Real.sqrt x * (Real.sqrt x * Real.log x) := by
    rw [← mul_assoc, Real.mul_self_sqrt hx0.le]
  have hD : 0 < Real.sqrt x * Real.log x := mul_pos hsx hlx
  have hlow : (2 / 5) / (Real.sqrt x * Real.log x)
      ≤ Chebyshev.theta (Real.sqrt x) / (x * Real.log x) := by
    rw [hxx, div_le_div_iff₀ hD (mul_pos hsx hD)]
    nlinarith
  have hGv : (poleSharpConstant + 10 / Real.log x) * ((Real.sqrt x)⁻¹ / Real.log x)
      = (poleSharpConstant + 10 / Real.log x) / (Real.sqrt x * Real.log x) := by
    field_simp
  rw [hGv] at hG
  have h10 : 10 / Real.log x < 1 / 10 := by
    rw [div_lt_div_iff₀ hlx (by norm_num)]; linarith
  have hm : (poleSharpConstant + 10 / Real.log x) / (Real.sqrt x * Real.log x)
      < (2 / 5) / (Real.sqrt x * Real.log x) :=
    div_lt_div_of_pos_right (by linarith) hD
  have := (abs_le.mp hG).1
  linarith

/-! ## Primorials -/

theorem primorial_div_totient_eq (n : ℕ) :
    ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ) = (mertensPrimeProduct n)⁻¹ := by
  rw [div_totient_eq_prod (primorial_ne_zero n), primeFactors_primorial,
    Nat.primesLE_eq_filter_Icc_zero, mertensPrimeProduct, ← Finset.prod_filter,
    Finset.prod_inv_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun p _ => ?_)
  rw [one_div]

theorem log_primorial_eq_theta (n : ℕ) :
    Real.log ((primorial n : ℕ) : ℝ) = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]

/-- **Nicolas's inequality for all large primorials under the Riemann hypothesis.**  With
`N_n = ∏_{p ≤ n} p`: `N_n/φ(N_n) > e^γ log log N_n` for every sufficiently large `n`. -/
theorem eventually_nicolas_inequality_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop, Real.exp Real.eulerMascheroniConstant
        * Real.log (Real.log ((primorial n : ℕ) : ℝ))
      < ((primorial n : ℕ) : ℝ) / ((primorial n).totient : ℝ) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    ((eventually_nicolasDefect_pos_of_riemannHypothesis hRH).and eventually_two_fifths_le_theta)
  filter_upwards [h, eventually_ge_atTop 4] with n ⟨hpos, hθ⟩ hn4
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hθ1 : 1 < Chebyshev.theta n := by linarith
  have hlθ : 0 < Real.log (Chebyshev.theta n) := Real.log_pos hθ1
  rw [primorial_div_totient_eq, log_primorial_eq_theta]
  have hP := mertensPrimeProduct_pos n
  have hR : 0 < Real.exp Real.eulerMascheroniConstant * Real.log (Chebyshev.theta n) := by
    positivity
  rw [← Real.log_lt_log_iff hR (inv_pos.mpr hP), Real.log_inv,
    Real.log_mul (Real.exp_pos _).ne' hlθ.ne', Real.log_exp]
  unfold nicolasDefect at hpos
  rw [Nat.floor_natCast] at hpos
  linarith

end

end RHTower
