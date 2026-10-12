import GaloisForLFunctions.HTGeometry.PolynomialGaussianPositionMoments
import GaloisForLFunctions.HTGeometry.GaussianPolynomialCoordinateEnergy

/-!
# Polynomial–Gaussians of arbitrary width: tails, derivatives and exponential weights

For a real polynomial `Q` of degree `d` and `β > 0` let `w(x) = Q(x) e^{-βx²}` (`gaussPolyFun`).

* **Tail** (`setIntegral_tail_gaussPolyFun_sq_le`).  For every `k`,
  `∫_{|x| ≥ X} w² ≤ ((d + k)/(β X²))^k ∫ w²`.
* **Derivative** (`integral_gaussPolyFun_derivPoly_sq_le`).  `∫ w'² ≤ 4β(d + 1) ∫ w²`, where
  `w' = (Q' − 2βxQ) e^{-βx²}`.
* **Exponential weight** (`integral_gaussPolyFun_sq_mul_exp_le`).  If `β > ½` and
  `r = ((d + k)/((β − ½) X²))^k < 1`, then `(1 − r) ∫ w² e^{x²} ≤ e^{X²} ∫ w²`, and the part of
  `∫ w² e^{x²}` beyond `|x| = X` is at most `r` times the whole.
* **Strip weight** (`sq_setIntegral_abs_mul_exp_half_le`).
  `(∫_S |f| e^{|x|/2})² ≤ 2eπ ∫_S f² e^{x²}`.

Proof.  The substitution `x = s y`, `s = (π/β)^{1/2}`, turns `w` into the unit-width
polynomial–Gaussian `Q(s y) e^{-πy²}`, where the oscillator bounds on position moments and on the
derivative hold.  The product of the moment constants `(√(d+i) + √(d+i+1))²/(4π)`, `i < k`, is at
most `((d + k)/π)^k`.  The strip weight follows from `t ≤ (ε/2) t² c + 1/(2εc)` with `c = 1 + x²`
and `e^{|x|}(1 + x²) ≤ 2e · e^{x²}`.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- The polynomial–Gaussian `Q(x) e^{-βx²}`. -/
def gaussPolyFun (Q : ℝ[X]) (β x : ℝ) : ℝ := Q.eval x * Real.exp (-(β * x ^ 2))

/-- The polynomial factor `Q' − 2βxQ` of the derivative of `Q(x) e^{-βx²}`. -/
def gaussPolyDerivPoly (Q : ℝ[X]) (β : ℝ) : ℝ[X] := derivative Q - C (2 * β) * X * Q

theorem continuous_gaussPolyFun (Q : ℝ[X]) (β : ℝ) : Continuous (gaussPolyFun Q β) :=
  Q.continuous.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_pow 2)).neg))

theorem hasDerivAt_gaussPolyFun (Q : ℝ[X]) (β x : ℝ) :
    HasDerivAt (gaussPolyFun Q β) (gaussPolyFun (gaussPolyDerivPoly Q β) β x) x := by
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(β * y ^ 2)))
      (Real.exp (-(β * x ^ 2)) * (-(β * (2 * x)))) x := by
    have e : (fun y : ℝ => Real.exp (-(β * y ^ 2))) = fun y => Real.exp ((-β) * y ^ 2) := by
      funext y; ring_nf
    rw [e]
    refine (((hasDerivAt_pow 2 x).const_mul (-β))).exp.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring_nf
  refine ((Q.hasDerivAt x).mul h2).congr_deriv ?_
  simp only [gaussPolyFun, gaussPolyDerivPoly, eval_sub, eval_mul, eval_C, eval_X]
  ring

theorem gaussPolyFun_neg_of_even (Q : ℝ[X]) (hQ : Q.comp (-X) = Q) (β x : ℝ) :
    gaussPolyFun Q β (-x) = gaussPolyFun Q β x := by
  have h := congrArg (fun R : ℝ[X] => R.eval x) hQ
  simp only [eval_comp, eval_neg, eval_X] at h
  simp only [gaussPolyFun, h, neg_sq]

/-! ## Change of scale -/

theorem integral_comp_mul_pos (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, f x = s * ∫ y, f (s * y) := by
  rw [Measure.integral_comp_mul_left f s, smul_eq_mul, abs_inv, abs_of_pos hs, ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul]

theorem setIntegral_tail_comp_mul_pos (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (X : ℝ) :
    ∫ x in {x : ℝ | X ≤ |x|}, f x = s * ∫ y in {y : ℝ | X / s ≤ |y|}, f (s * y) := by
  have hm : ∀ c : ℝ, MeasurableSet {x : ℝ | c ≤ |x|} := fun c =>
    measurableSet_le measurable_const continuous_abs.measurable
  rw [← integral_indicator (hm X), ← integral_indicator (hm (X / s)),
    integral_comp_mul_pos _ hs]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hiff : X ≤ |s * y| ↔ X / s ≤ |y| := by
    rw [abs_mul, abs_of_pos hs, div_le_iff₀ hs, mul_comm]
  by_cases hy : X / s ≤ |y|
  · rw [Set.indicator_of_mem (show s * y ∈ {x : ℝ | X ≤ |x|} from hiff.2 hy),
      Set.indicator_of_mem (show y ∈ {y : ℝ | X / s ≤ |y|} from hy)]
  · rw [Set.indicator_of_notMem (show s * y ∉ {x : ℝ | X ≤ |x|} from fun h => hy (hiff.1 h)),
      Set.indicator_of_notMem (show y ∉ {y : ℝ | X / s ≤ |y|} from hy)]

/-- The unit-width form of `Q(x) e^{-βx²}` under `x = s y`, `s = (π/β)^{1/2}`. -/
theorem gaussPolyFun_scale (Q : ℝ[X]) {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    gaussPolyFun Q β (Real.sqrt (π / β) * y) =
      (Q.comp (C (Real.sqrt (π / β)) * X)).eval y * gaussReal y := by
  have hs2 : Real.sqrt (π / β) ^ 2 = π / β := Real.sq_sqrt (by positivity)
  have hexp : β * (Real.sqrt (π / β) * y) ^ 2 = π * y ^ 2 := by
    rw [mul_pow, hs2]; field_simp
  simp only [gaussPolyFun, gaussReal, eval_comp, eval_mul, eval_C, eval_X, hexp]

theorem natDegree_comp_C_mul_X_of_ne (Q : ℝ[X]) {s : ℝ} (hs : s ≠ 0) :
    (Q.comp (C s * X)).natDegree = Q.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]

theorem norm_polyGaussSchwartz_sq (P : ℝ[X]) (y : ℝ) :
    ‖polyGaussSchwartz P y‖ ^ 2 = (P.eval y * gaussReal y) ^ 2 := by
  rw [polyGaussSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integrable_gaussPolyFun_sq (Q : ℝ[X]) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x => gaussPolyFun Q β x ^ 2) := by
  set s := Real.sqrt (π / β)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hv : Integrable (fun y => ‖polyGaussSchwartz (Q.comp (C s * X)) y‖ ^ 2) :=
    ((polyGaussSchwartz (Q.comp (C s * X))).memLp 2 (volume : Measure ℝ)).integrable_norm_pow
      (by norm_num)
  refine (hv.comp_mul_left' (inv_ne_zero hs.ne')).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_polyGaussSchwartz_sq, ← gaussPolyFun_scale Q hβ, ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul]

/-! ## The moment product -/

theorem prod_momentConstant_sq_le (d k : ℕ) :
    (∏ i ∈ Finset.range k, (Real.sqrt (d + i) + Real.sqrt (d + i + 1)) / (2 * Real.sqrt π)) ^ 2 ≤
      ((d + k) / π) ^ k := by
  rw [← Finset.prod_pow]
  calc ∏ i ∈ Finset.range k, ((Real.sqrt (d + i) + Real.sqrt (d + i + 1)) /
        (2 * Real.sqrt π)) ^ 2
      ≤ ∏ _i ∈ Finset.range k, ((d + k : ℝ) / π) :=
        Finset.prod_le_prod (fun _ _ => by positivity) fun i hi => by
          have hik : (i : ℝ) + 1 ≤ k := by
            have := Finset.mem_range.1 hi; exact_mod_cast this
          have hm : (0 : ℝ) ≤ d + i := by positivity
          have h1 := Real.sq_sqrt hm
          have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ d + i + 1 by positivity)
          have hπ := Real.sq_sqrt Real.pi_pos.le
          have hsum : (Real.sqrt (d + i) + Real.sqrt (d + i + 1)) ^ 2 ≤ 2 * (2 * (d + i) + 1) := by
            nlinarith [sq_nonneg (Real.sqrt (d + i) - Real.sqrt (d + i + 1))]
          rw [div_pow, mul_pow, hπ, div_le_div_iff₀ (by positivity) Real.pi_pos]
          nlinarith [Real.pi_pos]
    _ = ((d + k : ℝ) / π) ^ k := by rw [Finset.prod_const, Finset.card_range]

/-! ## Tails -/

/-- **Tail bound.**  `∫_{|x| ≥ X} (Q e^{-βx²})² ≤ ((d + k)/(βX²))^k ∫ (Q e^{-βx²})²`. -/
theorem setIntegral_tail_gaussPolyFun_sq_le (Q : ℝ[X]) {β L : ℝ} (hβ : 0 < β) (hL : 0 < L)
    (k : ℕ) :
    ∫ x in {x : ℝ | L ≤ |x|}, gaussPolyFun Q β x ^ 2 ≤
      ((Q.natDegree + k) / (β * L ^ 2)) ^ k * ∫ x, gaussPolyFun Q β x ^ 2 := by
  set s := Real.sqrt (π / β) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = π / β := Real.sq_sqrt (by positivity)
  set P := Q.comp (C s * X) with hP
  have hdeg : P.natDegree = Q.natDegree := natDegree_comp_C_mul_X_of_ne Q hs.ne'
  have hpt : ∀ y, gaussPolyFun Q β (s * y) ^ 2 = ‖polyGaussSchwartz P y‖ ^ 2 := fun y => by
    rw [norm_polyGaussSchwartz_sq, gaussPolyFun_scale Q hβ]
  rw [setIntegral_tail_comp_mul_pos _ hs, integral_comp_mul_pos _ hs]
  simp_rw [hpt]
  have hR : 0 < L / s := by positivity
  have hunit := setIntegral_tail_polyGauss_le_moment P k hR
  rw [norm_toLp_sq_eq_integral, hdeg] at hunit
  have hprod := prod_momentConstant_sq_le Q.natDegree k
  set V := ∫ y, ‖polyGaussSchwartz P y‖ ^ 2
  have hV : 0 ≤ V := integral_nonneg fun _ => by positivity
  have hRk : (L / s) ^ (2 * k) = (L ^ 2 * β / π) ^ k := by
    rw [pow_mul, div_pow, hs2, div_div_eq_mul_div]
  have hratio : (∏ i ∈ Finset.range k, (Real.sqrt (Q.natDegree + i) +
      Real.sqrt (Q.natDegree + i + 1)) / (2 * Real.sqrt π)) ^ 2 / (L / s) ^ (2 * k) ≤
      ((Q.natDegree + k) / (β * L ^ 2)) ^ k := by
    rw [hRk, div_le_iff₀ (by positivity), ← mul_pow]
    have he : (Q.natDegree + k : ℝ) / (β * L ^ 2) * (L ^ 2 * β / π) = (Q.natDegree + k) / π := by
      field_simp
    rw [he]
    exact hprod
  calc s * ∫ y in {y : ℝ | L / s ≤ |y|}, ‖polyGaussSchwartz P y‖ ^ 2
      ≤ s * ((∏ i ∈ Finset.range k, (Real.sqrt (Q.natDegree + i) +
          Real.sqrt (Q.natDegree + i + 1)) / (2 * Real.sqrt π)) ^ 2 * V / (L / s) ^ (2 * k)) := by
        gcongr
    _ = s * ((∏ i ∈ Finset.range k, (Real.sqrt (Q.natDegree + i) +
          Real.sqrt (Q.natDegree + i + 1)) / (2 * Real.sqrt π)) ^ 2 / (L / s) ^ (2 * k) * V) := by
        ring
    _ ≤ s * (((Q.natDegree + k) / (β * L ^ 2)) ^ k * V) := by gcongr
    _ = ((Q.natDegree + k) / (β * L ^ 2)) ^ k * (s * V) := by ring

/-! ## The derivative -/

theorem hasDerivAt_gaussPolyFun_comp_mul (Q : ℝ[X]) (β s y : ℝ) :
    HasDerivAt (fun y => gaussPolyFun Q β (s * y))
      (gaussPolyFun (gaussPolyDerivPoly Q β) β (s * y) * s) y := by
  have h := (hasDerivAt_gaussPolyFun Q β (s * y)).comp y ((hasDerivAt_id y).const_mul s)
  refine h.congr_deriv ?_
  simp

/-- **Derivative bound.**  `∫ ((Q' − 2βxQ) e^{-βx²})² ≤ 4β(d + 1) ∫ (Q e^{-βx²})²`. -/
theorem integral_gaussPolyFun_derivPoly_sq_le (Q : ℝ[X]) {β : ℝ} (hβ : 0 < β) :
    ∫ x, gaussPolyFun (gaussPolyDerivPoly Q β) β x ^ 2 ≤
      4 * β * (Q.natDegree + 1) * ∫ x, gaussPolyFun Q β x ^ 2 := by
  set s := Real.sqrt (π / β) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = π / β := Real.sq_sqrt (by positivity)
  set P := Q.comp (C s * X) with hP
  have hdeg : P.natDegree = Q.natDegree := natDegree_comp_C_mul_X_of_ne Q hs.ne'
  have hfun : (polyGaussSchwartz P : ℝ → ℂ) = fun y => ((gaussPolyFun Q β (s * y) : ℝ) : ℂ) := by
    funext y
    rw [polyGaussSchwartz_apply, gaussPolyFun_scale Q hβ]
  have hderiv : ∀ y, ‖derivSCLM (polyGaussSchwartz P) y‖ ^ 2 =
      s ^ 2 * gaussPolyFun (gaussPolyDerivPoly Q β) β (s * y) ^ 2 := fun y => by
    rw [derivSCLM_apply, hfun, (hasDerivAt_gaussPolyFun_comp_mul Q β s y).ofReal_comp.deriv,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hunit := gaussianPolynomialFullDerivativeNorm_le P
  rw [hdeg] at hunit
  have hsq : ‖(derivSCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      4 * π * ((Q.natDegree : ℝ) + 1) * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hunit 2
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at h
  have hv : ∀ y, ‖polyGaussSchwartz P y‖ ^ 2 = gaussPolyFun Q β (s * y) ^ 2 := fun y => by
    rw [norm_polyGaussSchwartz_sq, gaussPolyFun_scale Q hβ]
  rw [norm_toLp_sq_eq_integral, norm_toLp_sq_eq_integral] at hsq
  simp_rw [hderiv, hv] at hsq
  rw [integral_const_mul] at hsq
  rw [integral_comp_mul_pos _ hs, integral_comp_mul_pos (fun x => gaussPolyFun Q β x ^ 2) hs]
  set D := ∫ y, gaussPolyFun (gaussPolyDerivPoly Q β) β (s * y) ^ 2
  set V := ∫ y, gaussPolyFun Q β (s * y) ^ 2
  have hV : 0 ≤ V := integral_nonneg fun _ => by positivity
  have hD : D ≤ 4 * β * ((Q.natDegree : ℝ) + 1) * V := by
    have hβs : π = β * s ^ 2 := by rw [hs2]; field_simp
    rw [hβs] at hsq
    have hs2pos : 0 < s ^ 2 := by positivity
    nlinarith
  calc s * D ≤ s * (4 * β * ((Q.natDegree : ℝ) + 1) * V) := by gcongr
    _ = 4 * β * (Q.natDegree + 1) * (s * V) := by ring

/-! ## Exponential weights -/

theorem gaussPolyFun_sq_mul_exp (Q : ℝ[X]) (β x : ℝ) :
    gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2) = gaussPolyFun Q (β - 1 / 2) x ^ 2 := by
  unfold gaussPolyFun
  rw [mul_pow, mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem setIntegral_tail_gaussPolyFun_sq_mul_exp_le (Q : ℝ[X]) {β L : ℝ} (hβ : 1 / 2 < β)
    (hL : 0 < L) (k : ℕ) :
    ∫ x in {x : ℝ | L ≤ |x|}, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2) ≤
      ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k *
        ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2) := by
  simp_rw [gaussPolyFun_sq_mul_exp]
  exact setIntegral_tail_gaussPolyFun_sq_le Q (by linarith) hL k

theorem integrable_gaussPolyFun_sq_mul_exp (Q : ℝ[X]) {β : ℝ} (hβ : 1 / 2 < β) :
    Integrable (fun x => gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2)) := by
  simp_rw [gaussPolyFun_sq_mul_exp]
  exact integrable_gaussPolyFun_sq Q (by linarith)

/-- **Exponential weight.**  With `r = ((d + k)/((β − ½) L²))^k`,
`(1 − r) ∫ w² e^{x²} ≤ e^{L²} ∫ w²`. -/
theorem integral_gaussPolyFun_sq_mul_exp_le (Q : ℝ[X]) {β L : ℝ} (hβ : 1 / 2 < β) (hL : 0 < L)
    (k : ℕ) :
    (1 - ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k) *
        ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2) ≤
      Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2 := by
  set S := {x : ℝ | L ≤ |x|}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hW := integrable_gaussPolyFun_sq_mul_exp Q hβ
  have hV := integrable_gaussPolyFun_sq Q (by linarith : 0 < β)
  have htail := setIntegral_tail_gaussPolyFun_sq_mul_exp_le Q hβ hL k
  have hsplit := integral_add_compl hS hW
  have hin : ∫ x in Sᶜ, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2) ≤
      ∫ x in Sᶜ, Real.exp (L ^ 2) * gaussPolyFun Q β x ^ 2 := by
    refine setIntegral_mono_on hW.integrableOn (hV.const_mul _).integrableOn hS.compl
      fun x hx => ?_
    have hx' : |x| < L := lt_of_not_ge hx
    have hxL : x ^ 2 ≤ L ^ 2 := by
      have := abs_nonneg x
      nlinarith [sq_abs x]
    have he := Real.exp_le_exp.2 hxL
    have := sq_nonneg (gaussPolyFun Q β x)
    nlinarith
  rw [integral_const_mul] at hin
  have hin2 : ∫ x in Sᶜ, gaussPolyFun Q β x ^ 2 ≤ ∫ x, gaussPolyFun Q β x ^ 2 :=
    setIntegral_le_integral hV (Filter.Eventually.of_forall fun x => by positivity)
  have he := Real.exp_pos (L ^ 2)
  have hin3 := mul_le_mul_of_nonneg_left hin2 he.le
  linarith

/-! ## The strip weight `e^{|x|/2}` -/

theorem one_add_sq_mul_exp_abs_le (x : ℝ) :
    (1 + x ^ 2) * Real.exp |x| ≤ 2 * Real.exp 1 * Real.exp (x ^ 2) := by
  have h1 : 1 + x ^ 2 ≤ 2 * Real.exp |x| := by
    have := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
    nlinarith [abs_nonneg x, sq_abs x]
  have h2 : Real.exp |x| * Real.exp |x| ≤ Real.exp 1 * Real.exp (x ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (|x| - 1), sq_abs x])
  have he := Real.exp_pos |x|
  calc (1 + x ^ 2) * Real.exp |x| ≤ 2 * Real.exp |x| * Real.exp |x| := by gcongr
    _ = 2 * (Real.exp |x| * Real.exp |x|) := by ring
    _ ≤ 2 * (Real.exp 1 * Real.exp (x ^ 2)) := by gcongr
    _ = _ := by ring

theorem abs_mul_exp_half_le (t x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |t| * Real.exp (|x| / 2) ≤
      ε * Real.exp 1 * (t ^ 2 * Real.exp (x ^ 2)) + 1 / (2 * ε) * (1 + x ^ 2)⁻¹ := by
  obtain ⟨c, hc⟩ : ∃ c, c = 1 + x ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨u, hu⟩ : ∃ u, u = |t| * Real.exp (|x| / 2) := ⟨_, rfl⟩
  have hu2 : u ^ 2 = t ^ 2 * Real.exp |x| := by
    rw [hu, mul_pow, sq_abs, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hamgm : u ≤ ε / 2 * (u ^ 2 * c) + 1 / (2 * ε) * c⁻¹ := by
    have key : ε / 2 * (u ^ 2 * c) + 1 / (2 * ε) * c⁻¹ - u = (ε * u * c - 1) ^ 2 / (2 * ε * c) := by
      field_simp
      ring
    have : 0 ≤ (ε * u * c - 1) ^ 2 / (2 * ε * c) := by positivity
    linarith
  have hb : u ^ 2 * c ≤ 2 * Real.exp 1 * (t ^ 2 * Real.exp (x ^ 2)) := by
    rw [hu2, hc]
    have := one_add_sq_mul_exp_abs_le x
    calc t ^ 2 * Real.exp |x| * (1 + x ^ 2) = t ^ 2 * ((1 + x ^ 2) * Real.exp |x|) := by ring
      _ ≤ t ^ 2 * (2 * Real.exp 1 * Real.exp (x ^ 2)) := by gcongr
      _ = _ := by ring
  rw [← hu, ← hc]
  calc u ≤ ε / 2 * (u ^ 2 * c) + 1 / (2 * ε) * c⁻¹ := hamgm
    _ ≤ ε / 2 * (2 * Real.exp 1 * (t ^ 2 * Real.exp (x ^ 2))) + 1 / (2 * ε) * c⁻¹ := by gcongr
    _ = _ := by ring

/-- **Strip weight.**  `(∫_S |f| e^{|x|/2})² ≤ 2eπ ∫_S f² e^{x²}`. -/
theorem sq_setIntegral_abs_mul_exp_half_le {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hS : MeasurableSet S) (hint : IntegrableOn (fun x => f x ^ 2 * Real.exp (x ^ 2)) S) :
    IntegrableOn (fun x => |f x| * Real.exp (|x| / 2)) S ∧
      (∫ x in S, |f x| * Real.exp (|x| / 2)) ^ 2 ≤
        2 * Real.exp 1 * π * ∫ x in S, f x ^ 2 * Real.exp (x ^ 2) := by
  have hdom : ∀ ε : ℝ, IntegrableOn (fun x => ε * Real.exp 1 * (f x ^ 2 * Real.exp (x ^ 2)) +
      1 / (2 * ε) * (1 + x ^ 2)⁻¹) S :=
    fun ε => (hint.const_mul _).add (integrable_inv_one_add_sq.integrableOn.const_mul _)
  have hmeas : AEStronglyMeasurable (fun x => |f x| * Real.exp (|x| / 2)) (volume.restrict S) :=
    ((continuous_abs.comp hf).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
  have hI : IntegrableOn (fun x => |f x| * Real.exp (|x| / 2)) S :=
    (hdom 1).mono' hmeas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact abs_mul_exp_half_le (f x) x one_pos)
  refine ⟨hI, ?_⟩
  obtain ⟨I, hIdef⟩ : ∃ I, I = ∫ x in S, |f x| * Real.exp (|x| / 2) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = ∫ x in S, f x ^ 2 * Real.exp (x ^ 2) := ⟨_, rfl⟩
  rw [← hIdef, ← hWdef]
  have hI0 : 0 ≤ I := hIdef ▸ setIntegral_nonneg hS fun x _ => by positivity
  have hW0 : 0 ≤ W := hWdef ▸ setIntegral_nonneg hS fun x _ => by positivity
  have hπ : ∫ x in S, (1 + x ^ 2)⁻¹ ≤ π := by
    rw [← integral_univ_inv_one_add_sq]
    exact setIntegral_le_integral integrable_inv_one_add_sq
      (Filter.Eventually.of_forall fun x => by positivity)
  have hbound : ∀ ε : ℝ, 0 < ε → I ≤ ε * Real.exp 1 * W + π / (2 * ε) := fun ε hε => by
    rw [hIdef, hWdef]
    calc ∫ x in S, |f x| * Real.exp (|x| / 2)
        ≤ ∫ x in S, (ε * Real.exp 1 * (f x ^ 2 * Real.exp (x ^ 2)) +
            1 / (2 * ε) * (1 + x ^ 2)⁻¹) :=
          setIntegral_mono_on hI (hdom ε) hS fun x _ => abs_mul_exp_half_le (f x) x hε
      _ = ε * Real.exp 1 * (∫ x in S, f x ^ 2 * Real.exp (x ^ 2)) +
            1 / (2 * ε) * (∫ x in S, (1 + x ^ 2)⁻¹) := by
          rw [integral_add (hint.const_mul _) (integrable_inv_one_add_sq.integrableOn.const_mul _),
            integral_const_mul, integral_const_mul]
      _ ≤ ε * Real.exp 1 * (∫ x in S, f x ^ 2 * Real.exp (x ^ 2)) + 1 / (2 * ε) * π := by gcongr
      _ = _ := by ring
  have he := Real.exp_pos 1
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_pow two_ne_zero]
    exact mul_nonneg (by positivity) hW0
  rcases hW0.eq_or_lt with hW | hWpos
  · exfalso
    have h := hbound (π / I) (by positivity)
    have e : π / (2 * (π / I)) = I / 2 := by field_simp
    rw [← hW, e] at h
    linarith
  · have h := hbound (I / (2 * Real.exp 1 * W)) (by positivity)
    have key : I / (2 * Real.exp 1 * W) * Real.exp 1 * W + π / (2 * (I / (2 * Real.exp 1 * W))) =
        I / 2 + π * Real.exp 1 * W / I := by
      field_simp
    rw [key] at h
    have h2 : I / 2 ≤ π * Real.exp 1 * W / I := by linarith
    rw [le_div_iff₀ hpos] at h2
    nlinarith

/-! ## Strip-weighted `L¹` bounds for polynomial–Gaussians -/

/-- **Tail in the strip weight.**  With `r = ((d + k)/((β − ½) L²))^k`,
`(1 − r) (∫_{|x| ≥ L} |w| e^{|x|/2})² ≤ 2eπ r e^{L²} ∫ w²`. -/
theorem sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le (Q : ℝ[X]) {β L : ℝ}
    (hβ : 1 / 2 < β) (hL : 0 < L) (k : ℕ)
    (hr : ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k < 1) :
    IntegrableOn (fun x => |gaussPolyFun Q β x| * Real.exp (|x| / 2)) {x : ℝ | L ≤ |x|} ∧
      (1 - ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k) *
          (∫ x in {x : ℝ | L ≤ |x|}, |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ^ 2 ≤
        2 * Real.exp 1 * π * ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k *
          Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2 := by
  set r := ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2) : ℝ) ^ k with hr_def
  have hS : MeasurableSet {x : ℝ | L ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hW := integrable_gaussPolyFun_sq_mul_exp Q hβ
  obtain ⟨hI, hsq⟩ := sq_setIntegral_abs_mul_exp_half_le (continuous_gaussPolyFun Q β) hS
    hW.integrableOn
  refine ⟨hI, ?_⟩
  have htail := setIntegral_tail_gaussPolyFun_sq_mul_exp_le Q hβ hL k
  have htot := integral_gaussPolyFun_sq_mul_exp_le Q hβ hL k
  rw [← hr_def] at htail htot
  have hr0 : 0 ≤ r := by
    rw [hr_def]
    have : (0 : ℝ) < (β - 1 / 2) * L ^ 2 := by
      have : 0 < β - 1 / 2 := by linarith
      positivity
    positivity
  have h1r : 0 ≤ 1 - r := by linarith
  have hc : (0 : ℝ) ≤ 2 * Real.exp 1 * π := by positivity
  calc (1 - r) * (∫ x in {x : ℝ | L ≤ |x|}, |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ^ 2
      ≤ (1 - r) * (2 * Real.exp 1 * π *
          ∫ x in {x : ℝ | L ≤ |x|}, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq h1r
    _ ≤ (1 - r) * (2 * Real.exp 1 * π * (r * ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2))) := by
        gcongr
    _ = 2 * Real.exp 1 * π * r * ((1 - r) * ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2)) := by
        ring
    _ ≤ 2 * Real.exp 1 * π * r * (Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2) := by
        gcongr
    _ = _ := by ring

/-- **Whole line in the strip weight.**
`(1 − r) (∫ |w| e^{|x|/2})² ≤ 2eπ e^{L²} ∫ w²`. -/
theorem sq_integral_abs_gaussPolyFun_mul_exp_half_le (Q : ℝ[X]) {β L : ℝ}
    (hβ : 1 / 2 < β) (hL : 0 < L) (k : ℕ) :
    Integrable (fun x => |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ∧
      (1 - ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2)) ^ k) *
          (∫ x, |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ^ 2 ≤
        2 * Real.exp 1 * π * Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2 := by
  have hW := integrable_gaussPolyFun_sq_mul_exp Q hβ
  obtain ⟨hI, hsq⟩ := sq_setIntegral_abs_mul_exp_half_le (continuous_gaussPolyFun Q β)
    MeasurableSet.univ hW.integrableOn
  rw [integrableOn_univ] at hI
  rw [setIntegral_univ, setIntegral_univ] at hsq
  refine ⟨hI, ?_⟩
  have htot := integral_gaussPolyFun_sq_mul_exp_le Q hβ hL k
  set r := ((Q.natDegree + k) / ((β - 1 / 2) * L ^ 2) : ℝ) ^ k
  rcases le_or_gt r 1 with h1 | h1
  · calc (1 - r) * (∫ x, |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ^ 2
        ≤ (1 - r) * (2 * Real.exp 1 * π * ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = 2 * Real.exp 1 * π * ((1 - r) * ∫ x, gaussPolyFun Q β x ^ 2 * Real.exp (x ^ 2)) := by
          ring
      _ ≤ 2 * Real.exp 1 * π * (Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2) := by gcongr
      _ = _ := by ring
  · have h0 : (1 - r) * (∫ x, |gaussPolyFun Q β x| * Real.exp (|x| / 2)) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    have : 0 ≤ ∫ x, gaussPolyFun Q β x ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have : 0 ≤ 2 * Real.exp 1 * π * Real.exp (L ^ 2) * ∫ x, gaussPolyFun Q β x ^ 2 := by
      positivity
    linarith

end

end GaloisForLFunctions
