import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheWallSeenFromTheLeft
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The leading term of the prime head in averaged form

The prime head `ŜF(−t)` is a sum of Abel integrals of `F` just right of the prime points `−log n`.
Point values of `F` there need not exist; right averages are enough.

* **Laplace transform of a primitive** (`integral_exp_mul_primitive`). For `g` of exponential type
  `b` and `σ > b`, `∫_0^∞ e^{−σv} g(v) dv = σ ∫_0^∞ e^{−σT} P(T) dT` with `P(T) = ∫_0^T g`:
  integration by parts against the absolutely continuous primitive
  (`integral_exp_mul_primitive_of_integrableOn`). For integrable `g` no growth bound is needed
  (`integral_exp_mul_primitive_of_integrable`).
* **Abelian theorem** (`tendsto_mul_laplace_of_average`). If `P(h)/h → ℓ` as `h → 0⁺` then
  `t ∫_0^∞ e^{−tv} g(v) dv → ℓ`: after `T = s/t` the transform is `∫_0^∞ s e^{−s} · P(s/t)/(s/t) ds`,
  and dominated convergence applies.
* **The prime head** (`tendsto_mul_primeHead_neg_of_average`). If `|F(u)| ≤ C e^{cu}` with `c > ½` and
  the right averages `h⁻¹ ∫_{−log n}^{−log n + h} F` converge to `ℓ(n)` at every prime power, then
  `t · ŜF(−t) → Σ_n Λ(n) n^{−½} ℓ(n)`. Right-continuity at the prime points is the special case
  `ℓ(n) = F(−log n)`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem atom_nonneg_avg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-! ## Laplace transform of a primitive -/

/-- Integration by parts on `[0, R]` against the primitive `P(T) = ∫_0^T g`. -/
theorem integral_exp_mul_primitive_interval {g : ℝ → ℝ}
    (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b) {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
    ∫ T in (0 : ℝ)..R, Real.exp (-σ * T) * (∫ v in (0 : ℝ)..T, g v) =
      -(Real.exp (-σ * R) / σ) * (∫ v in (0 : ℝ)..R, g v) +
        (1 / σ) * ∫ T in (0 : ℝ)..R, Real.exp (-σ * T) * g T := by
  let G : ℝ → ℝ := fun T => -(Real.exp (-σ * T) / σ)
  let P : ℝ → ℝ := fun T => ∫ v in (0 : ℝ)..T, g v
  have hi : IntervalIntegrable g volume 0 R := hgi 0 R
  have hPac : AbsolutelyContinuousOnInterval P 0 R :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (show (0 : ℝ) ∈ uIcc 0 R by simp [hR])
  have hGcd : ContDiff ℝ 1 G := by dsimp [G]; fun_prop
  have hGac : AbsolutelyContinuousOnInterval G 0 R := hGcd.contDiffOn.absolutelyContinuousOnInterval
  have hparts := hGac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ t in (0 : ℝ)..R, G t * deriv P t) = ∫ t in (0 : ℝ)..R, G t * g t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt P (g t) t := ht (uIoc_subset_uIcc hmem) 0 (by simp [hR])
    rw [hd.deriv]
  have hderivG : ∀ t, deriv G t = Real.exp (-σ * t) := by
    intro t
    have h1 : HasDerivAt (fun T : ℝ => -σ * T) (-σ) t := by
      simpa using (hasDerivAt_id t).const_mul (-σ)
    have h2 : HasDerivAt (fun T : ℝ => Real.exp (-σ * T)) (Real.exp (-σ * t) * -σ) t := h1.exp
    have h3 : HasDerivAt G (-(Real.exp (-σ * t) * -σ / σ)) t := (h2.div_const σ).neg
    have hval : -(Real.exp (-σ * t) * -σ / σ) = Real.exp (-σ * t) := by
      rw [mul_neg, neg_div, neg_neg, mul_div_assoc, div_self hσ.ne', mul_one]
    rw [hval] at h3
    exact h3.deriv
  have hright : (∫ t in (0 : ℝ)..R, deriv G t * P t) =
      ∫ t in (0 : ℝ)..R, Real.exp (-σ * t) * ∫ v in (0 : ℝ)..t, g v := by
    apply intervalIntegral.integral_congr
    intro t _
    show deriv G t * P t = Real.exp (-σ * t) * P t
    rw [hderivG]
  have hP0 : P 0 = 0 := by simp [P]
  rw [hleft, hright, hP0, mul_zero, sub_zero] at hparts
  have hGf : (∫ t in (0 : ℝ)..R, G t * g t) =
      -(1 / σ) * ∫ t in (0 : ℝ)..R, Real.exp (-σ * t) * g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [G]
    ring
  rw [hGf] at hparts
  dsimp only [G, P] at hparts
  linarith

/-- **Laplace transform of a primitive, general form.** If `e^{−σT} g` and `e^{−σT} P` are integrable
on `(0, ∞)` and the boundary term `e^{−σR} P(R)/σ` vanishes at infinity, then
`∫_0^∞ e^{−σv} g = σ ∫_0^∞ e^{−σT} P(T) dT`. -/
theorem integral_exp_mul_primitive_of_integrableOn {g : ℝ → ℝ}
    (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b) {σ : ℝ} (hσ : 0 < σ)
    (hint1 : IntegrableOn (fun T => Real.exp (-σ * T) * g T) (Ioi 0))
    (hint2 : IntegrableOn (fun T => Real.exp (-σ * T) * ∫ v in (0 : ℝ)..T, g v) (Ioi 0))
    (hB : Tendsto (fun R : ℝ => -(Real.exp (-σ * R) / σ) * ∫ v in (0 : ℝ)..R, g v)
      atTop (𝓝 0)) :
    ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * g T =
      σ * ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * (∫ v in (0 : ℝ)..T, g v) := by
  have hL := intervalIntegral_tendsto_integral_Ioi 0 hint2 tendsto_id
  have hR := (intervalIntegral_tendsto_integral_Ioi 0 hint1 tendsto_id).const_mul (1 / σ)
  have hsum := hB.add hR
  rw [zero_add] at hsum
  have heq : (fun R : ℝ => ∫ T in (0 : ℝ)..id R, Real.exp (-σ * T) * ∫ v in (0 : ℝ)..T, g v)
      =ᶠ[atTop] fun R => -(Real.exp (-σ * R) / σ) * (∫ v in (0 : ℝ)..R, g v) +
        (1 / σ) * ∫ T in (0 : ℝ)..id R, Real.exp (-σ * T) * g T := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact integral_exp_mul_primitive_interval hgi hσ hR
  rw [tendsto_nhds_unique (hL.congr' heq) hsum, ← mul_assoc, mul_one_div_cancel hσ.ne', one_mul]

/-- **Laplace transform of a primitive.** For `g` of exponential type `b < σ` on `[0, ∞)` (together
with its primitive), `∫_0^∞ e^{−σv} g = σ ∫_0^∞ e^{−σT} ∫_0^T g`. -/
theorem integral_exp_mul_primitive {g : ℝ → ℝ} (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hgm : Measurable g) {K b σ : ℝ} (hbσ : b < σ) (hσ : 0 < σ)
    (hgb : ∀ v, 0 ≤ v → |g v| ≤ K * Real.exp (b * v))
    (hPb : ∀ T, 0 ≤ T → |∫ v in (0 : ℝ)..T, g v| ≤ K * Real.exp (b * T)) :
    ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * g T =
      σ * ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * (∫ v in (0 : ℝ)..T, g v) := by
  have hmaj := (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ - b)).const_mul K
  have hexp : ∀ T : ℝ, Real.exp (-σ * T) * (K * Real.exp (b * T)) =
      K * Real.exp (-(σ - b) * T) := fun T => by
    rw [show -(σ - b) * T = -σ * T + b * T by ring, Real.exp_add]; ring
  have hint1 : IntegrableOn (fun T => Real.exp (-σ * T) * g T) (Ioi 0) := by
    refine hmaj.mono' ((by fun_prop : Measurable fun T : ℝ => Real.exp (-σ * T)).mul
      hgm).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← hexp]
    exact mul_le_mul_of_nonneg_left (hgb T (le_of_lt hT)) (Real.exp_pos _).le
  have hint2 : IntegrableOn (fun T => Real.exp (-σ * T) * ∫ v in (0 : ℝ)..T, g v) (Ioi 0) := by
    refine hmaj.mono' ((by fun_prop : Continuous fun T : ℝ => Real.exp (-σ * T)).mul
      (intervalIntegral.continuous_primitive hgi 0)).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← hexp]
    exact mul_le_mul_of_nonneg_left (hPb T (le_of_lt hT)) (Real.exp_pos _).le
  -- the boundary term decays
  have hB : Tendsto (fun R : ℝ => -(Real.exp (-σ * R) / σ) * ∫ v in (0 : ℝ)..R, g v)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => Real.exp (-((σ - b) * R))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < σ - b))
    have hdecay : Tendsto (fun R : ℝ => K / σ * Real.exp (-((σ - b) * R))) atTop (𝓝 0) := by
      simpa using h0.const_mul (K / σ)
    refine squeeze_zero_norm' ?_ hdecay
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hσ]
    calc Real.exp (-σ * R) / σ * |∫ v in (0 : ℝ)..R, g v|
        ≤ Real.exp (-σ * R) / σ * (K * Real.exp (b * R)) :=
          mul_le_mul_of_nonneg_left (hPb R hR) (div_nonneg (Real.exp_pos _).le hσ.le)
      _ = K / σ * Real.exp (-((σ - b) * R)) := by
          rw [show -((σ - b) * R) = -σ * R + b * R by ring, Real.exp_add]; ring
  exact integral_exp_mul_primitive_of_integrableOn hgi hσ hint1 hint2 hB

/-- **Laplace transform of the primitive of an integrable function.** For integrable `g` and
`σ > 0`, `∫_0^∞ e^{−σv} g = σ ∫_0^∞ e^{−σT} ∫_0^T g`; the primitive is bounded by `‖g‖₁`. -/
theorem integral_exp_mul_primitive_of_integrable {g : ℝ → ℝ} (hg : Integrable g) {σ : ℝ}
    (hσ : 0 < σ) :
    ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * g T =
      σ * ∫ T in Ioi (0 : ℝ), Real.exp (-σ * T) * (∫ v in (0 : ℝ)..T, g v) := by
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable
  have hPb : ∀ T : ℝ, |∫ v in (0 : ℝ)..T, g v| ≤ ∫ v, ‖g v‖ := fun T => by
    rw [← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral hg.norm (Eventually.of_forall fun _ => norm_nonneg _))
  have hexp : Continuous fun T : ℝ => Real.exp (-σ * T) := by fun_prop
  have hint1 : IntegrableOn (fun T => Real.exp (-σ * T) * g T) (Ioi 0) := by
    refine hg.norm.integrableOn.mono'
      (hexp.aestronglyMeasurable.mul hg.aestronglyMeasurable).restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((Real.exp_le_exp.mpr
      (by nlinarith [mul_pos hσ (show (0 : ℝ) < T from hT)] : -σ * T ≤ 0)).trans_eq Real.exp_zero)
  have hint2 : IntegrableOn (fun T => Real.exp (-σ * T) * ∫ v in (0 : ℝ)..T, g v) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hσ).const_mul (∫ v, ‖g v‖)).mono'
      (hexp.mul (intervalIntegral.continuous_primitive hgi 0)).aestronglyMeasurable ?_
    filter_upwards with T
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right (hPb T) (Real.exp_pos _).le
  have hB : Tendsto (fun R : ℝ => -(Real.exp (-σ * R) / σ) * ∫ v in (0 : ℝ)..R, g v)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => Real.exp (-σ * R)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hσ)).congr fun R => ?_
      simp only [Function.comp_apply, id_eq, neg_mul]
    have hdecay : Tendsto (fun R : ℝ => (∫ v, ‖g v‖) / σ * Real.exp (-σ * R)) atTop (𝓝 0) := by
      simpa using h0.const_mul ((∫ v, ‖g v‖) / σ)
    refine squeeze_zero_norm' (Eventually.of_forall fun R => ?_) hdecay
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_pos (Real.exp_pos _), abs_of_pos hσ]
    calc Real.exp (-σ * R) / σ * |∫ v in (0 : ℝ)..R, g v|
        ≤ Real.exp (-σ * R) / σ * ∫ v, ‖g v‖ :=
          mul_le_mul_of_nonneg_left (hPb R) (div_nonneg (Real.exp_pos _).le hσ.le)
      _ = (∫ v, ‖g v‖) / σ * Real.exp (-σ * R) := by ring
  exact integral_exp_mul_primitive_of_integrableOn hgi hσ hint1 hint2 hB

/-! ## The Abelian theorem -/

theorem integral_Ioi_mul_exp_neg_eq_one :
    ∫ s in Ioi (0 : ℝ), s * Real.exp (-s) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := 1) (by norm_num) one_pos
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul, div_one, Real.one_rpow,
    Real.Gamma_two] at h
  exact h

/-- **Abel means of a right average.** If `g = O(e^{bv})` on `[0, ∞)` and `h⁻¹ ∫_0^h g → ℓ` as
`h → 0⁺`, then `t ∫_0^∞ e^{−tv} g(v) dv → ℓ` as `t → ∞`. -/
theorem tendsto_mul_laplace_of_average {g : ℝ → ℝ}
    (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b) (hgm : Measurable g) {K b : ℝ} (hb : 0 < b)
    (hgb : ∀ v, 0 ≤ v → |g v| ≤ K * Real.exp (b * v)) {ℓ : ℝ}
    (hav : Tendsto (fun h => (∫ v in (0 : ℝ)..h, g v) / h) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun t : ℝ => t * ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * g v) atTop (𝓝 ℓ) := by
  have hK : 0 ≤ K := by
    have h0 := hgb 0 le_rfl
    rw [mul_zero, Real.exp_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  -- the primitive grows at most like `K T e^{bT}`
  have hP : ∀ T, 0 ≤ T → |∫ v in (0 : ℝ)..T, g v| ≤ K * Real.exp (b * T) * T := by
    intro T hT
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (f := g)
      (C := K * Real.exp (b * T)) (fun v hv => by
        rw [uIoc_of_le hT] at hv
        rw [Real.norm_eq_abs]
        exact (hgb v hv.1.le).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.2 hb.le)) hK))
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at h
  have hP' : ∀ T, 0 ≤ T → |∫ v in (0 : ℝ)..T, g v| ≤ K * Real.exp ((b + 1) * T) := by
    intro T hT
    have h1 : T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
    calc |∫ v in (0 : ℝ)..T, g v| ≤ K * Real.exp (b * T) * T := hP T hT
      _ ≤ K * Real.exp (b * T) * Real.exp T :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (Real.exp_pos _).le)
      _ = K * Real.exp ((b + 1) * T) := by
          rw [mul_assoc, ← Real.exp_add, show b * T + T = (b + 1) * T by ring]
  have hgb' : ∀ v, 0 ≤ v → |g v| ≤ K * Real.exp ((b + 1) * v) := fun v hv =>
    (hgb v hv).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hK)
  -- the scaled transform is the exponential average of `t P(s/t)`
  have hrep : ∀ t : ℝ, b + 1 < t → t * ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * g v =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) * (t * ∫ v in (0 : ℝ)..s / t, g v) := by
    intro t ht
    have htpos : 0 < t := by linarith
    have h1 := integral_exp_mul_primitive hgi hgm ht htpos hgb' hP'
    simp only [neg_mul] at h1
    have h2 := integral_comp_mul_left_Ioi
      (fun s => Real.exp (-s) * ∫ v in (0 : ℝ)..s / t, g v) 0 htpos
    simp only [mul_zero, smul_eq_mul, mul_div_cancel_left₀ _ htpos.ne'] at h2
    have h3 : ∫ s in Ioi (0 : ℝ), Real.exp (-s) * (t * ∫ v in (0 : ℝ)..s / t, g v) =
        t * ∫ s in Ioi (0 : ℝ), Real.exp (-s) * ∫ v in (0 : ℝ)..s / t, g v := by
      rw [← integral_const_mul]; congr 1; funext s; ring
    rw [h1, h2, h3, mul_inv_cancel_left₀ htpos.ne']
  -- pointwise limit: `t P(s/t) = s · P(s/t)/(s/t) → s ℓ`
  have hlim : ∀ s : ℝ, 0 < s → Tendsto (fun t : ℝ =>
      Real.exp (-s) * (t * ∫ v in (0 : ℝ)..s / t, g v)) atTop (𝓝 (Real.exp (-s) * (s * ℓ))) := by
    intro s hs
    have h0 : Tendsto (fun t : ℝ => s / t) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, (eventually_gt_atTop 0).mono fun t ht => div_pos hs ht⟩
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    refine (((hav.comp h0).const_mul s).const_mul (Real.exp (-s))).congr'
      ((eventually_gt_atTop 0).mono fun t ht => ?_)
    show Real.exp (-s) * (s * ((∫ v in (0 : ℝ)..s / t, g v) / (s / t))) = _
    rw [div_div_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hs.ne',
      mul_comm (∫ v in (0 : ℝ)..s / t, g v) t]
  -- domination by `4K e^{−s/4}`
  have hbound : ∀ t : ℝ, 2 * b ≤ t → ∀ s : ℝ, 0 < s →
      ‖Real.exp (-s) * (t * ∫ v in (0 : ℝ)..s / t, g v)‖ ≤ 4 * K * Real.exp (-(1 / 4) * s) := by
    intro t ht s hs
    have htpos : 0 < t := by linarith
    have hst : 0 ≤ s / t := (div_pos hs htpos).le
    have h2 : b * (s / t) ≤ s / 2 := by
      rw [mul_div_assoc', div_le_iff₀ htpos]; nlinarith
    have h3 : s ≤ 4 * Real.exp (s / 4) := by linarith [Real.add_one_le_exp (s / 4)]
    have hcalc : t * |∫ v in (0 : ℝ)..s / t, g v| ≤
        K * Real.exp (s / 2) * (4 * Real.exp (s / 4)) := by
      calc t * |∫ v in (0 : ℝ)..s / t, g v|
          ≤ t * (K * Real.exp (b * (s / t)) * (s / t)) :=
            mul_le_mul_of_nonneg_left (hP _ hst) htpos.le
        _ = K * Real.exp (b * (s / t)) * (s / t * t) := by ring
        _ = K * Real.exp (b * (s / t)) * s := by rw [div_mul_cancel₀ s htpos.ne']
        _ ≤ K * Real.exp (s / 2) * s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hK) hs.le
        _ ≤ K * Real.exp (s / 2) * (4 * Real.exp (s / 4)) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hK (Real.exp_pos _).le)
    have he : Real.exp (-(1 / 4) * s) = Real.exp (-s) * Real.exp (s / 2) * Real.exp (s / 4) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos htpos, he]
    calc Real.exp (-s) * (t * |∫ v in (0 : ℝ)..s / t, g v|)
        ≤ Real.exp (-s) * (K * Real.exp (s / 2) * (4 * Real.exp (s / 4))) :=
          mul_le_mul_of_nonneg_left hcalc (Real.exp_pos _).le
      _ = 4 * K * (Real.exp (-s) * Real.exp (s / 2) * Real.exp (s / 4)) := by ring
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := atTop) (F := fun t s => Real.exp (-s) * (t * ∫ v in (0 : ℝ)..s / t, g v))
    (f := fun s => Real.exp (-s) * (s * ℓ))
    (fun s => 4 * K * Real.exp (-(1 / 4) * s))
    (Eventually.of_forall fun t => ((Real.continuous_exp.comp continuous_neg).mul
      (continuous_const.mul ((intervalIntegral.continuous_primitive hgi 0).comp
        (continuous_id.div_const t)))).aestronglyMeasurable)
    ((eventually_ge_atTop (2 * b)).mono fun t ht => (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => hbound t ht s hs))
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => hlim s hs))
  have hval : ∫ s in Ioi (0 : ℝ), Real.exp (-s) * (s * ℓ) = ℓ := by
    rw [show (fun s : ℝ => Real.exp (-s) * (s * ℓ)) = fun s => ℓ * (s * Real.exp (-s)) by
      funext s; ring, integral_const_mul, integral_Ioi_mul_exp_neg_eq_one, mul_one]
  rw [hval] at h
  exact h.congr' ((eventually_gt_atTop (b + 1)).mono fun t ht => (hrep t ht).symm)

/-! ## The prime head -/

theorem abelHead_eq_shift (F : ℝ → ℝ) (t L : ℝ) :
    abelHead F t L = ∫ v in Ioi (0 : ℝ), Real.exp (-(t * v)) * F (v - L) := by
  unfold abelHead
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self ((Ioi (-L)).indicator
      fun u => Real.exp (-(t * (L + u))) * F u) L]
  congr 1
  funext v
  simp only [Set.indicator_apply, mem_Ioi, show L + (v - L) = v by ring]
  by_cases hv : 0 < v
  · rw [if_pos (show -L < v - L by linarith), if_pos hv]
  · rw [if_neg (show ¬ -L < v - L by intro h; exact hv (by linarith)), if_neg hv]

/-- **An Abel integral at a right Lebesgue–Cesàro point.** If `h⁻¹ ∫_{−L}^{−L+h} F → ℓ` then
`t ∫_{u > −L} e^{−t(L+u)} F(u) du → ℓ`. -/
theorem tendsto_mul_abelHead_of_average {F : ℝ → ℝ} (hFm : Measurable F) {C c : ℝ} (hc : 0 < c)
    (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u)) {L ℓ : ℝ}
    (hav : Tendsto (fun h => (∫ u in (-L)..(-L + h), F u) / h) (𝓝[>] 0) (𝓝 ℓ)) :
    Tendsto (fun t : ℝ => t * abelHead F t L) atTop (𝓝 ℓ) := by
  have hgm : Measurable fun v => F (v - L) := hFm.comp (measurable_id.sub_const L)
  have hgb : ∀ v, |F (v - L)| ≤ C * Real.exp (-(c * L)) * Real.exp (c * v) := fun v => by
    calc |F (v - L)| ≤ C * Real.exp (c * (v - L)) := hbd _
      _ = C * Real.exp (-(c * L)) * Real.exp (c * v) := by
          rw [show c * (v - L) = -(c * L) + c * v by ring, Real.exp_add]; ring
  have hcont : Continuous fun v : ℝ => C * Real.exp (-(c * L)) * Real.exp (c * v) := by fun_prop
  have hgi : ∀ a b : ℝ, IntervalIntegrable (fun v => F (v - L)) volume a b := fun a b =>
    (hcont.intervalIntegrable a b).mono_fun' hgm.aestronglyMeasurable
      (Eventually.of_forall fun v => by
        show ‖F (v - L)‖ ≤ C * Real.exp (-(c * L)) * Real.exp (c * v)
        rw [Real.norm_eq_abs]; exact hgb v)
  have hav' : Tendsto (fun h => (∫ v in (0 : ℝ)..h, F (v - L)) / h) (𝓝[>] 0) (𝓝 ℓ) := by
    refine hav.congr fun h => ?_
    rw [intervalIntegral.integral_comp_sub_right F L, zero_sub, sub_eq_neg_add]
  refine (tendsto_mul_laplace_of_average hgi hgm hc (fun v _ => hgb v) hav').congr fun t => ?_
  rw [abelHead_eq_shift]

/-- **The leading term of the prime head, averaged.** If `|F(u)| ≤ C e^{cu}` with `c > ½` and at every
prime power `n` the right averages `h⁻¹ ∫_{−log n}^{−log n + h} F` tend to `ℓ(n)`, then
`t · ŜF(−t) → Σ_n Λ(n) n^{−½} ℓ(n)`. -/
theorem tendsto_mul_primeHead_neg_of_average {F : ℝ → ℝ} (hFm : Measurable F) {C c : ℝ}
    (hc : 1 / 2 < c) (hbd : ∀ u, |F u| ≤ C * Real.exp (c * u)) {ℓ : ℕ → ℝ}
    (hav : ∀ n : ℕ, vonMangoldtAtom n ≠ 0 → Tendsto
      (fun h => (∫ u in (-Real.log n)..(-Real.log n + h), F u) / h) (𝓝[>] 0) (𝓝 (ℓ n))) :
    Tendsto (fun t : ℝ => (t : ℂ) * primeHead F (-(t : ℂ))) atTop
      (𝓝 (∑' n : ℕ, ((vonMangoldtAtom n * ℓ n : ℝ) : ℂ))) := by
  have hc0 : 0 < c := by linarith
  have hpt : ∀ n : ℕ, Tendsto (fun t : ℝ =>
      ((vonMangoldtAtom n * (t * abelHead F t (Real.log n)) : ℝ) : ℂ))
      atTop (𝓝 ((vonMangoldtAtom n * ℓ n : ℝ) : ℂ)) := by
    intro n
    by_cases h0 : vonMangoldtAtom n = 0
    · simp only [h0, zero_mul]
      exact tendsto_const_nhds
    · exact (Complex.continuous_ofReal.tendsto _).comp
        ((tendsto_mul_abelHead_of_average hFm hc0 hbd (hav n h0)).const_mul (vonMangoldtAtom n))
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (n : ℕ) => ((vonMangoldtAtom n * (t * abelHead F t (Real.log n)) : ℝ) : ℂ))
    (bound := fun n : ℕ => vonMangoldtAtom n * Real.exp (-c * Real.log n) *
      (C * ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2) * s)))
    ((summable_primeHead_damping hc).mul_right _) hpt
    ((eventually_ge_atTop (2 * c)).mono fun t ht n => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (atom_nonneg_avg n)]
      calc vonMangoldtAtom n * |t * abelHead F t (Real.log n)|
          ≤ vonMangoldtAtom n * (C * Real.exp (-(c * Real.log n)) *
              ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2) * s)) :=
            mul_le_mul_of_nonneg_left (abs_mul_abelHead_le hc0 hbd ht _) (atom_nonneg_avg n)
        _ = _ := by rw [neg_mul]; ring)
  refine hlim.congr fun t => ?_
  rw [primeHead_neg_ofReal, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  push_cast
  ring

#print axioms tendsto_mul_primeHead_neg_of_average

end GaloisForLFunctions.ExclusionOfTheCriticalState
