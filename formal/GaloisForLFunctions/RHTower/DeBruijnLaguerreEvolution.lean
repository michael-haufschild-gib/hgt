import GaloisForLFunctions.RHTower.DeBruijnStrictLaguerre

/-!
# Evolution of the first Laguerre expression along the de Bruijn–Newman flow

Write `H_k = ∂_z^k H_t` for the derivatives of the de Bruijn–Newman deformation, and

`L = H_1² − H_0 H_2`,   `L₁ = H_2² − H_1 H_3`

for the first and the next Laguerre expressions.  Every derivative obeys the backward heat equation
`∂_t H_k = −H_{k+2}` (`hasDerivAt_iteratedDeriv_riemannHeat_time`), and a direct computation gives
the evolution law (`hasDerivAt_laguerreExpr_time`)

`∂_t L = −∂_z² L + 2 L₁`,

since `∂_z L = H_1 H_2 − H_0 H_3` and `∂_z² L = H_2² − H_0 H_4`.

At a point where `H_0 ≠ 0`, `L = 0` and `∂_z L = 0`, the next expression vanishes as well
(`laguerreNext_eq_zero_of_touch`): `H_0 L₁ = H_0 H_2² − H_1(H_1 H_2) = H_2 (H_0 H_2 − H_1²) = 0`.
Consequently, at a real point where `x ↦ L(t, x)` has a local minimum with value `0` and `H_t` does
not vanish, `∂_t L = −∂_x² L ≤ 0` (`laguerreExpr_time_deriv_nonpos_of_touch`).  A failure of the
first Laguerre inequality cannot appear, as `t` decreases, at a point where `L` touches zero away
from the zeros of `H_t`; to first order it can only start at a real zero of `H_t`, where
`L = H_1²` vanishes exactly at a double zero.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Derivatives of `H_t` as exponential transforms -/

theorem continuous_heatWeight_mul_pow (t : ℝ) (k : ℕ) :
    Continuous fun x : ℝ => heatWeight t x * (I * x) ^ k := by
  have := continuous_heatWeight t
  fun_prop

theorem integrable_heatWeight_mul_pow {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => ‖heatWeight t x * (I * x) ^ k‖ * Real.exp (c * |x|)) := by
  induction k generalizing c with
  | zero => simpa using integrable_heatWeight ht c
  | succ k ih =>
    have h := integrable_mul_poly (G := fun x : ℝ => heatWeight t x * (I * x) ^ k) ih
      (continuous_heatWeight_mul_pow t k) c
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [pow_succ, mul_assoc]

/-- `∂_z^k H_t = ∫ Φ(x) e^{tx²} (ix)^k e^{izx} dx`. -/
theorem iteratedDeriv_riemannHeat_eq {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    iteratedDeriv k (riemannHeat t) = expTransform (fun x => heatWeight t x * (I * x) ^ k) := by
  induction k with
  | zero => simp [riemannHeat_eq_expTransform]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [(hasDerivAt_expTransform (continuous_heatWeight_mul_pow t k)
      (integrable_heatWeight_mul_pow ht k) z).deriv]
    unfold expTransform
    congr 1
    funext x
    ring

/-- **The heat equation for every derivative.** `∂_t ∫ Φ e^{tx²}(ix)^k e^{izx} dx` is the integral
with the extra factor `x²`. -/
theorem hasDerivAt_expTransform_heatWeight_mul_pow_time {t : ℝ} (ht : 0 < t) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun s => expTransform (fun x => heatWeight s x * (I * x) ^ k) z)
      (expTransform (fun x => ((x ^ 2 : ℝ) : ℂ) * (heatWeight t x * (I * x) ^ k)) z) t := by
  set c := |z.im| with hc
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun x : ℝ => heatWeight s x * (I * x) ^ k * Complex.exp (I * z * x)) volume :=
    fun s => ((continuous_heatWeight_mul_pow s k).mul (by fun_prop)).aestronglyMeasurable
  have hint0 : Integrable
      (fun x : ℝ => heatWeight t x * (I * x) ^ k * Complex.exp (I * z * x)) := by
    refine (integrable_heatWeight_mul_pow ht.le k c).mono' (hmeas t)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul]; gcongr; exact norm_exp_I_mul_le z x
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * (heatWeight t x * (I * x) ^ k) *
        Complex.exp (I * z * x)) volume :=
    (((by fun_prop : Continuous fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))).mul
      (continuous_heatWeight_mul_pow t k) |>.mul (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ s ∈ ball t 1,
      ‖((x ^ 2 : ℝ) : ℂ) * (heatWeight s x * (I * x) ^ k) * Complex.exp (I * z * x)‖ ≤
        ‖heatWeight (t + 2) x * (I * x) ^ k‖ * Real.exp (c * |x|) := by
    refine Eventually.of_forall fun x s hs => ?_
    have hs1 : s ≤ t + 1 := by
      have := mem_ball.mp hs; rw [Real.dist_eq, abs_lt] at this; linarith
    have hw : ∀ r : ℝ, ‖heatWeight r x‖ = riemannKernelReal x * Real.exp (r * x ^ 2) := by
      intro r
      simp only [heatWeight]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
    have hsq : x ^ 2 ≤ Real.exp (x ^ 2) := by linarith [Real.add_one_le_exp (x ^ 2)]
    have hΦ := (riemannKernelReal_pos x).le
    have h1 : x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2)) ≤
        riemannKernelReal x * Real.exp ((t + 2) * x ^ 2) := by
      calc x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2))
          ≤ Real.exp (x ^ 2) * (riemannKernelReal x * Real.exp ((t + 1) * x ^ 2)) :=
            mul_le_mul hsq (by gcongr) (by positivity) (by positivity)
        _ = riemannKernelReal x * Real.exp ((t + 2) * x ^ 2) := by
            rw [show (t + 2) * x ^ 2 = x ^ 2 + (t + 1) * x ^ 2 by ring, Real.exp_add]; ring
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg x), hw, hw]
    calc x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2) * ‖(I * (x : ℂ)) ^ k‖) *
          ‖Complex.exp (I * z * x)‖
        = x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2)) * ‖(I * (x : ℂ)) ^ k‖ *
          ‖Complex.exp (I * z * x)‖ := by ring
      _ ≤ riemannKernelReal x * Real.exp ((t + 2) * x ^ 2) * ‖(I * (x : ℂ)) ^ k‖ *
          Real.exp (c * |x|) := by
          gcongr
          exact norm_exp_I_mul_le z x
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), ∀ s ∈ ball t 1,
      HasDerivAt (fun s => heatWeight s x * (I * x) ^ k * Complex.exp (I * z * x))
        (((x ^ 2 : ℝ) : ℂ) * (heatWeight s x * (I * x) ^ k) * Complex.exp (I * z * x)) s := by
    refine Eventually.of_forall fun x s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => riemannKernelReal x * Real.exp (s * x ^ 2))
        (riemannKernelReal x * (Real.exp (s * x ^ 2) * x ^ 2)) s := by
      have := ((hasDerivAt_id s).mul_const (x ^ 2)).exp.const_mul (riemannKernelReal x)
      simpa using this
    have h2 := (h1.ofReal_comp.mul_const ((I * (x : ℂ)) ^ k)).mul_const
      (Complex.exp (I * z * x))
    simp only [heatWeight]
    refine h2.congr_deriv ?_
    push_cast
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t one_pos)
    (Eventually.of_forall hmeas) hint0 hmeas' hbound
    (integrable_heatWeight_mul_pow (by linarith) k c) hderiv).2

/-- **The backward heat equation for every derivative.** `∂_t ∂_z^k H_t(z) = −∂_z^{k+2} H_t(z)`
for `t > 0`. -/
theorem hasDerivAt_iteratedDeriv_riemannHeat_time {t : ℝ} (ht : 0 < t) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun s => iteratedDeriv k (riemannHeat s) z)
      (-iteratedDeriv (k + 2) (riemannHeat t) z) t := by
  have h := hasDerivAt_expTransform_heatWeight_mul_pow_time ht k z
  have hev : (fun s => iteratedDeriv k (riemannHeat s) z) =ᶠ[𝓝 t]
      fun s => expTransform (fun x => heatWeight s x * (I * x) ^ k) z := by
    filter_upwards [lt_mem_nhds ht] with s hs
    rw [iteratedDeriv_riemannHeat_eq hs.le]
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [iteratedDeriv_riemannHeat_eq ht.le]
  unfold expTransform
  rw [← integral_neg]
  congr 1
  funext x
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Each derivative has the next one as its `z`-derivative. -/
theorem hasDerivAt_iteratedDeriv_riemannHeat {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (z : ℂ) :
    HasDerivAt (iteratedDeriv k (riemannHeat t)) (iteratedDeriv (k + 1) (riemannHeat t) z) z := by
  rw [iteratedDeriv_succ]
  exact (differentiable_iteratedDeriv_riemannHeat ht k z).hasDerivAt

/-- Every derivative of `H_t` is real on the real axis. -/
theorem iteratedDeriv_riemannHeat_ofReal_im {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (x : ℝ) :
    (iteratedDeriv k (riemannHeat t) x).im = 0 := by
  induction k generalizing x with
  | zero => simpa using riemannHeat_ofReal_im ht x
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact im_deriv_eq_zero_of_real (differentiable_iteratedDeriv_riemannHeat ht k) ih x

/-! ## The Laguerre expressions -/

/-- The first Laguerre expression `L = H_1² − H_0 H_2` of `H_t`. -/
def laguerreExpr (t : ℝ) (z : ℂ) : ℂ :=
  iteratedDeriv 1 (riemannHeat t) z ^ 2 - riemannHeat t z * iteratedDeriv 2 (riemannHeat t) z

/-- The next Laguerre expression `L₁ = H_2² − H_1 H_3` of `H_t`. -/
def laguerreNext (t : ℝ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 (riemannHeat t) z ^ 2 -
    iteratedDeriv 1 (riemannHeat t) z * iteratedDeriv 3 (riemannHeat t) z

theorem laguerreExpr_eq (t : ℝ) (z : ℂ) :
    laguerreExpr t z = deriv (riemannHeat t) z ^ 2 -
      riemannHeat t z * deriv (deriv (riemannHeat t)) z := by
  simp [laguerreExpr, iteratedDeriv_succ]

/-- `∂_z L = H_1 H_2 − H_0 H_3`. -/
theorem hasDerivAt_laguerreExpr {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasDerivAt (laguerreExpr t)
      (iteratedDeriv 1 (riemannHeat t) z * iteratedDeriv 2 (riemannHeat t) z -
        riemannHeat t z * iteratedDeriv 3 (riemannHeat t) z) z := by
  have h0 := hasDerivAt_iteratedDeriv_riemannHeat ht 0 z
  have h1 := hasDerivAt_iteratedDeriv_riemannHeat ht 1 z
  have h2 := hasDerivAt_iteratedDeriv_riemannHeat ht 2 z
  simp only [iteratedDeriv_zero, zero_add] at h0
  have h := (h1.pow 2).sub (h0.mul h2)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

theorem deriv_laguerreExpr {t : ℝ} (ht : 0 ≤ t) :
    deriv (laguerreExpr t) = fun z => iteratedDeriv 1 (riemannHeat t) z *
      iteratedDeriv 2 (riemannHeat t) z - riemannHeat t z * iteratedDeriv 3 (riemannHeat t) z := by
  funext z
  exact (hasDerivAt_laguerreExpr ht z).deriv

/-- `∂_z² L = H_2² − H_0 H_4`. -/
theorem hasDerivAt_deriv_laguerreExpr {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasDerivAt (deriv (laguerreExpr t))
      (iteratedDeriv 2 (riemannHeat t) z ^ 2 -
        riemannHeat t z * iteratedDeriv 4 (riemannHeat t) z) z := by
  rw [deriv_laguerreExpr ht]
  have h0 := hasDerivAt_iteratedDeriv_riemannHeat ht 0 z
  have h1 := hasDerivAt_iteratedDeriv_riemannHeat ht 1 z
  have h2 := hasDerivAt_iteratedDeriv_riemannHeat ht 2 z
  have h3 := hasDerivAt_iteratedDeriv_riemannHeat ht 3 z
  simp only [iteratedDeriv_zero, zero_add] at h0
  have h := (h1.mul h2).sub (h0.mul h3)
  refine h.congr_deriv ?_
  ring

/-- **Evolution of the Laguerre expression.** `∂_t L = −∂_z² L + 2 L₁` for `t > 0`. -/
theorem hasDerivAt_laguerreExpr_time {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (fun s => laguerreExpr s z)
      (-deriv (deriv (laguerreExpr t)) z + 2 * laguerreNext t z) t := by
  have h0 := hasDerivAt_iteratedDeriv_riemannHeat_time ht 0 z
  have h1 := hasDerivAt_iteratedDeriv_riemannHeat_time ht 1 z
  have h2 := hasDerivAt_iteratedDeriv_riemannHeat_time ht 2 z
  simp only [iteratedDeriv_zero] at h0
  have h := (h1.pow 2).sub (h0.mul h2)
  rw [(hasDerivAt_deriv_laguerreExpr ht.le z).deriv]
  refine h.congr_deriv ?_
  simp only [laguerreNext, Nat.cast_ofNat]
  ring

/-- **Touching forces the next expression to vanish.** If `H_t(z) ≠ 0`, `L = 0` and `∂_z L = 0`
at `z`, then `L₁ = 0` at `z`. -/
theorem laguerreNext_eq_zero_of_touch {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (h0 : riemannHeat t z ≠ 0)
    (hL : laguerreExpr t z = 0) (hL' : deriv (laguerreExpr t) z = 0) :
    laguerreNext t z = 0 := by
  rw [(hasDerivAt_laguerreExpr ht z).deriv] at hL'
  unfold laguerreExpr at hL
  unfold laguerreNext
  refine mul_left_cancel₀ h0 ?_
  linear_combination (-(iteratedDeriv 2 (riemannHeat t) z)) * hL +
    iteratedDeriv 1 (riemannHeat t) z * hL'

/-- At a touching point the evolution is the backward heat equation: `∂_t L = −∂_z² L`. -/
theorem hasDerivAt_laguerreExpr_time_of_touch {t : ℝ} (ht : 0 < t) {z : ℂ}
    (h0 : riemannHeat t z ≠ 0) (hL : laguerreExpr t z = 0)
    (hL' : deriv (laguerreExpr t) z = 0) :
    HasDerivAt (fun s => laguerreExpr s z) (-deriv (deriv (laguerreExpr t)) z) t := by
  have h := hasDerivAt_laguerreExpr_time ht z
  rwa [laguerreNext_eq_zero_of_touch ht.le h0 hL hL', mul_zero, add_zero] at h

/-! ## The touching law on the real axis -/

/-- A local minimum of a real function has nonnegative second derivative. -/
theorem deriv_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x₀ : ℝ} (hmin : IsLocalMin f x₀)
    (hc : ContinuousAt f x₀) : 0 ≤ deriv (deriv f) x₀ := by
  by_contra hneg'
  have hneg := not_le.mp hneg'
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have hconst : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmin, hmax] with y h1 h2
    exact le_antisymm h2 h1
  have hd : deriv f =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq, deriv_const]
  rw [hd.deriv_eq, deriv_const] at hneg
  exact lt_irrefl _ hneg

theorem laguerreExpr_ofReal_im {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : (laguerreExpr t x).im = 0 := by
  have e : ∀ k : ℕ, iteratedDeriv k (riemannHeat t) x =
      ((iteratedDeriv k (riemannHeat t) x).re : ℂ) := fun k =>
    Complex.ext (by simp) (by simp [iteratedDeriv_riemannHeat_ofReal_im ht k x])
  have e0 : riemannHeat t x = ((riemannHeat t x).re : ℂ) :=
    Complex.ext (by simp) (by simp [riemannHeat_ofReal_im ht x])
  unfold laguerreExpr
  rw [e 1, e 2, e0]
  norm_cast

theorem deriv_laguerreExpr_ofReal_im {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (deriv (laguerreExpr t) x).im = 0 :=
  im_deriv_eq_zero_of_real (fun z => (hasDerivAt_laguerreExpr ht z).differentiableAt)
    (laguerreExpr_ofReal_im ht) x

/-- **The touching law.** Let `t > 0` and let `x₀` be real with `H_t(x₀) ≠ 0`.  If the real
function `x ↦ L(t, x)` has a local minimum at `x₀` with value `0`, then
`∂_t L(t, x₀) = −∂_x² L(t, x₀) ≤ 0`. -/
theorem laguerreExpr_time_deriv_nonpos_of_touch {t : ℝ} (ht : 0 < t) {x₀ : ℝ}
    (h0 : riemannHeat t x₀ ≠ 0) (hmin : IsLocalMin (fun x : ℝ => (laguerreExpr t x).re) x₀)
    (hzero : (laguerreExpr t x₀).re = 0) :
    HasDerivAt (fun s => (laguerreExpr s x₀).re) (-(deriv (deriv (laguerreExpr t)) x₀).re) t ∧
      -(deriv (deriv (laguerreExpr t)) x₀).re ≤ 0 := by
  set ℓ : ℝ → ℝ := fun x => (laguerreExpr t x).re with hℓ
  have hd1 : ∀ x : ℝ, HasDerivAt ℓ (deriv (laguerreExpr t) x).re x := fun x =>
    (hasDerivAt_laguerreExpr ht.le x).differentiableAt.hasDerivAt.real_of_complex
  have hd1' : deriv ℓ = fun x : ℝ => (deriv (laguerreExpr t) x).re := by
    funext x; exact (hd1 x).deriv
  have hdiff2 : Differentiable ℂ (deriv (laguerreExpr t)) := fun z =>
    (hasDerivAt_deriv_laguerreExpr ht.le z).differentiableAt
  have hd2 : deriv (deriv ℓ) x₀ = (deriv (deriv (laguerreExpr t)) x₀).re := by
    rw [hd1']
    exact ((hdiff2 x₀).hasDerivAt.real_of_complex).deriv
  have hcrit : (deriv (laguerreExpr t) x₀).re = 0 := by
    rw [← (hd1 x₀).deriv]; exact hmin.deriv_eq_zero
  have hL : laguerreExpr t x₀ = 0 := Complex.ext hzero (laguerreExpr_ofReal_im ht.le x₀)
  have hL' : deriv (laguerreExpr t) x₀ = 0 :=
    Complex.ext hcrit (deriv_laguerreExpr_ofReal_im ht.le x₀)
  have htime := hasDerivAt_laguerreExpr_time_of_touch ht h0 hL hL'
  have hsecond := deriv_deriv_nonneg_of_isLocalMin hmin (hd1 x₀).continuousAt
  rw [hd2] at hsecond
  refine ⟨?_, by linarith⟩
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t htime
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.neg_re] at h
  exact h

end

end RHTower.DeBruijn
