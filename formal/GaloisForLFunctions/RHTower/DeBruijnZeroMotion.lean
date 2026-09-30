import GaloisForLFunctions.RHTower.DeBruijnHeatEquation

/-!
# How a simple zero of `H_t` moves

**Generic estimate** (`norm_sub_predicted_le`). Let `f(z₀) = 0` with `a = f'(z₀) ≠ 0` in the sense
`‖f(z) − a(z − z₀)‖ ≤ M‖z − z₀‖²`, and let `F = f + h g + E` with `‖g(z) − g(z₀)‖ ≤ L‖z − z₀‖` and
`‖E(z)‖ ≤ K h²`. If `F(z) = 0`, `M‖z − z₀‖ ≤ ‖a‖/4` and `hL ≤ ‖a‖/4`, then `z` is within `O(h)` of
`z₀`, and `‖a‖ ‖z − (z₀ − h g(z₀)/a)‖ ≤ M‖z−z₀‖² + hL‖z−z₀‖ + Kh²`.

**For the flow.** With `f = H_t`, `g = −H_t''` and `E = H_{t+h} − H_t + hH_t''` all three bounds hold
on the unit disc around any point, with constants given by the weighted integrals
`∫ |x|^k Φ(x) e^{tx²} e^{(|Im z₀|+1)|x|} dx`, `k = 2, 3, 4` (`riemannHeat_taylor_bounds`). Hence every
zero of `H_{t+h}` near a simple zero `z₀` of `H_t` satisfies
`Im z ≤ Im z₀ + h Im(H_t''(z₀)/H_t'(z₀)) + C h²` (`im_zero_le_of_simple_zero`): the zero moves with
velocity `H''/H'`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Exponential remainders -/

theorem norm_cexp_sub_one_le (w : ℂ) : ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  refine h.trans ?_
  have := Real.add_one_le_exp (-‖w‖)
  have hmul : Real.exp (-‖w‖) * Real.exp ‖w‖ = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos ‖w‖, norm_nonneg w]

theorem norm_cexp_sub_one_sub_le (w : ℂ) :
    ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, zero_add] at h
  refine (le_of_eq_of_le (by ring_nf) h).trans ?_
  have := Real.add_one_le_exp (-‖w‖)
  have hmul : Real.exp (-‖w‖) * Real.exp ‖w‖ = 1 := by rw [← Real.exp_add]; simp
  have hr := norm_nonneg w
  have h1 : Real.exp ‖w‖ - 1 - ‖w‖ ≤ ‖w‖ * (Real.exp ‖w‖ - 1) := by
    nlinarith [Real.exp_pos ‖w‖]
  have h2 : Real.exp ‖w‖ - 1 ≤ ‖w‖ * Real.exp ‖w‖ := by nlinarith [Real.exp_pos ‖w‖]
  nlinarith

theorem rexp_sub_one_sub_le {r : ℝ} (hr : 0 ≤ r) : Real.exp r - 1 - r ≤ r ^ 2 * Real.exp r := by
  have h := norm_cexp_sub_one_sub_le (r : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
  have e : Complex.exp r - 1 - r = ((Real.exp r - 1 - r : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-! ## The generic zero-motion estimate -/

theorem norm_sub_predicted_le {f g E : ℂ → ℂ} {z₀ a z : ℂ} {M L K h : ℝ} (ha : a ≠ 0)
    (hh : 0 ≤ h)
    (hf : ‖f z - a * (z - z₀)‖ ≤ M * ‖z - z₀‖ ^ 2)
    (hg : ‖g z - g z₀‖ ≤ L * ‖z - z₀‖)
    (hE : ‖E z‖ ≤ K * h ^ 2)
    (hzero : f z + h * g z + E z = 0)
    (hd : M * ‖z - z₀‖ ≤ ‖a‖ / 4) (hhL : h * L ≤ ‖a‖ / 4) :
    ‖z - z₀‖ ≤ 2 * (h * ‖g z₀‖ + K * h ^ 2) / ‖a‖ ∧
      ‖a‖ * ‖z - (z₀ - h * g z₀ / a)‖ ≤ M * ‖z - z₀‖ ^ 2 + h * L * ‖z - z₀‖ + K * h ^ 2 := by
  set d := ‖z - z₀‖ with hdd
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have key : a * (z - z₀) + h * g z₀ =
      -((f z - a * (z - z₀)) + h * (g z - g z₀) + E z) := by
    linear_combination hzero
  have hnorm : ‖a * (z - z₀) + h * g z₀‖ ≤ M * d ^ 2 + h * L * d + K * h ^ 2 := by
    rw [key, norm_neg]
    have t1 := norm_add_le (f z - a * (z - z₀) + (h : ℂ) * (g z - g z₀)) (E z)
    have t2 := norm_add_le (f z - a * (z - z₀)) ((h : ℂ) * (g z - g z₀))
    have t3 : ‖(h : ℂ) * (g z - g z₀)‖ = h * ‖g z - g z₀‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    have := mul_le_mul_of_nonneg_left hg hh
    nlinarith
  have hpred : ‖a‖ * ‖z - (z₀ - h * g z₀ / a)‖ = ‖a * (z - z₀) + h * g z₀‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
    ring
  refine ⟨?_, by rw [hpred]; exact hnorm⟩
  have hlow : ‖a‖ * d - h * ‖g z₀‖ ≤ ‖a * (z - z₀) + h * g z₀‖ := by
    have := norm_sub_norm_le (a * (z - z₀)) (-(h * g z₀))
    rw [sub_neg_eq_add, norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hh] at this
    linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have h1 : M * d ^ 2 ≤ ‖a‖ / 4 * d := by
    have := mul_le_mul_of_nonneg_right hd hd0
    nlinarith
  have h2 : h * L * d ≤ ‖a‖ / 4 * d := mul_le_mul_of_nonneg_right hhL hd0
  rw [le_div_iff₀ hna]
  nlinarith

/-! ## Bounds for the flow -/

theorem integrable_pow_mul_heatWeight {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (c : ℝ) :
    Integrable (fun x => |x| ^ k * ‖heatWeight t x‖ * Real.exp (c * |x|)) := by
  refine ((integrable_heatWeight ht (c + 1)).const_mul (k.factorial : ℝ)).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => |x| ^ k).mul
      ((continuous_heatWeight t).norm) |>.mul (by fun_prop)).aestronglyMeasurable
  · have hk := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hk' : |x| ^ k ≤ k.factorial * Real.exp |x| := by
      rw [div_le_iff₀ hf] at hk; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |x| ^ k * ‖heatWeight t x‖ * Real.exp (c * |x|)
        ≤ (k.factorial * Real.exp |x|) * ‖heatWeight t x‖ * Real.exp (c * |x|) := by gcongr
      _ = k.factorial * (‖heatWeight t x‖ * Real.exp ((c + 1) * |x|)) := by
          rw [show (c + 1) * |x| = |x| + c * |x| by ring, Real.exp_add]; ring

theorem integrable_heat_exp_mul {t : ℝ} (ht : 0 ≤ t) (G : ℝ → ℂ) (hG : Continuous G)
    (hbound : ∀ x, ‖G x‖ ≤ ‖heatWeight t x‖ * (|x| ^ 1 + 1)) (w : ℂ) :
    Integrable (fun x : ℝ => G x * Complex.exp (I * w * x)) := by
  refine ((integrable_pow_mul_heatWeight ht 1 |w.im|).add
    (integrable_heatWeight ht |w.im|)).mono' (hG.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have := norm_exp_I_mul_le w x
  calc ‖G x‖ * ‖Complex.exp (I * w * x)‖
      ≤ ‖heatWeight t x‖ * (|x| ^ 1 + 1) * Real.exp (|w.im| * |x|) := by gcongr; exact hbound x
    _ = _ := by simp only [Pi.add_apply]; ring

/-- **Taylor bound for `H_t`.** -/
theorem norm_riemannHeat_taylor_le {t : ℝ} (ht : 0 ≤ t) {z₀ z : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    ‖riemannHeat t z - riemannHeat t z₀ - deriv (riemannHeat t) z₀ * (z - z₀)‖ ≤
      (∫ x, |x| ^ 2 * ‖heatWeight t x‖ * Real.exp ((|z₀.im| + 1) * |x|)) * ‖z - z₀‖ ^ 2 := by
  set G := heatWeight t
  have hGc := continuous_heatWeight t
  have hself : ∀ x, ‖G x‖ ≤ ‖heatWeight t x‖ * (|x| ^ 1 + 1) := fun x =>
    le_mul_of_one_le_right (norm_nonneg _) (by have := abs_nonneg x; rw [pow_one]; linarith)
  have hA := integrable_heat_exp_mul ht G hGc hself z
  have hB := integrable_heat_exp_mul ht G hGc hself z₀
  have hC := integrable_heat_exp_mul ht (fun x => G x * (I * x)) (hGc.mul (by fun_prop))
    (fun x => by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        pow_one]
      nlinarith [norm_nonneg (G x), abs_nonneg x]) z₀
  rw [deriv_riemannHeat ht]
  simp only [riemannHeat_eq_expTransform, expTransform]
  rw [← integral_mul_const, ← integral_sub hA hB, ← integral_sub ?_ (hC.mul_const _)]
  swap
  · exact hA.sub hB
  refine (norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight ht 2 (|z₀.im| + 1)).mul_const (‖z - z₀‖ ^ 2))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_mul_const _ _))
  set w : ℂ := I * (z - z₀) * x with hw
  have hsplit : G x * Complex.exp (I * z * x) - G x * Complex.exp (I * z₀ * x) -
      G x * (I * x) * Complex.exp (I * z₀ * x) * (z - z₀) =
      G x * Complex.exp (I * z₀ * x) * (Complex.exp w - 1 - w) := by
    have : Complex.exp (I * z * x) = Complex.exp (I * z₀ * x) * Complex.exp w := by
      rw [← Complex.exp_add]; congr 1; rw [hw]; ring
    rw [this]; rw [hw]; ring
  rw [hsplit, norm_mul, norm_mul]
  have hwn : ‖w‖ = ‖z - z₀‖ * |x| := by
    rw [hw, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hwle : ‖w‖ ≤ |x| := by rw [hwn]; nlinarith [abs_nonneg x, norm_nonneg (z - z₀)]
  have h1 := norm_cexp_sub_one_sub_le w
  have h2 := norm_exp_I_mul_le z₀ x
  calc ‖G x‖ * ‖Complex.exp (I * z₀ * x)‖ * ‖Complex.exp w - 1 - w‖
      ≤ ‖G x‖ * Real.exp (|z₀.im| * |x|) * (‖w‖ ^ 2 * Real.exp |x|) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = |x| ^ 2 * ‖G x‖ * Real.exp ((|z₀.im| + 1) * |x|) * ‖z - z₀‖ ^ 2 := by
        rw [hwn, show (|z₀.im| + 1) * |x| = |z₀.im| * |x| + |x| by ring, Real.exp_add]; ring

/-- **Lipschitz bound for `H_t''`.** -/
theorem norm_deriv_deriv_riemannHeat_sub_le {t : ℝ} (ht : 0 ≤ t) {z₀ z : ℂ} (hz : ‖z - z₀‖ ≤ 1) :
    ‖deriv (deriv (riemannHeat t)) z - deriv (deriv (riemannHeat t)) z₀‖ ≤
      (∫ x, |x| ^ 3 * ‖heatWeight t x‖ * Real.exp ((|z₀.im| + 1) * |x|)) * ‖z - z₀‖ := by
  set G := heatWeight t
  have hGc := continuous_heatWeight t
  rw [(hasDerivAt_deriv_riemannHeat ht z).deriv, (hasDerivAt_deriv_riemannHeat ht z₀).deriv]
  have hint : ∀ w : ℂ, Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * w * x)) := by
    intro w
    refine ((integrable_pow_mul_heatWeight ht 2 |w.im|)).mono'
      ((((by fun_prop : Continuous fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))).mul hGc).mul
        (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
      ← sq_abs x]
    gcongr
    exact norm_exp_I_mul_le w x
  simp only [expTransform]
  rw [neg_sub_neg, norm_sub_rev, ← integral_sub (hint z) (hint z₀)]
  refine (norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight ht 3 (|z₀.im| + 1)).mul_const ‖z - z₀‖)
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_mul_const _ _))
  set w : ℂ := I * (z - z₀) * x with hw
  have hsplit : ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z * x) -
      ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z₀ * x) =
      ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z₀ * x) * (Complex.exp w - 1) := by
    have : Complex.exp (I * z * x) = Complex.exp (I * z₀ * x) * Complex.exp w := by
      rw [← Complex.exp_add]; congr 1; rw [hw]; ring
    rw [this]; ring
  rw [hsplit, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg x)]
  have hwn : ‖w‖ = ‖z - z₀‖ * |x| := by
    rw [hw, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hwle : ‖w‖ ≤ |x| := by rw [hwn]; nlinarith [abs_nonneg x, norm_nonneg (z - z₀)]
  have h1 := norm_cexp_sub_one_le w
  have h2 := norm_exp_I_mul_le z₀ x
  calc x ^ 2 * ‖G x‖ * ‖Complex.exp (I * z₀ * x)‖ * ‖Complex.exp w - 1‖
      ≤ x ^ 2 * ‖G x‖ * Real.exp (|z₀.im| * |x|) * (‖w‖ * Real.exp |x|) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = |x| ^ 3 * ‖G x‖ * Real.exp ((|z₀.im| + 1) * |x|) * ‖z - z₀‖ := by
        rw [hwn, show (|z₀.im| + 1) * |x| = |z₀.im| * |x| + |x| by ring, Real.exp_add,
          ← sq_abs x]
        ring

theorem heatWeight_add (t h x : ℝ) :
    heatWeight (t + h) x = heatWeight t x * (Real.exp (h * x ^ 2) : ℂ) := by
  simp only [heatWeight]
  push_cast
  rw [show ((t : ℂ) + h) * (x : ℂ) ^ 2 = (t : ℂ) * (x : ℂ) ^ 2 + (h : ℂ) * (x : ℂ) ^ 2 by ring,
    Complex.exp_add]
  ring

theorem norm_heatWeight_mul_exp (t x : ℝ) :
    ‖heatWeight t x‖ * Real.exp (x ^ 2) = ‖heatWeight (t + 1) x‖ := by
  simp only [heatWeight, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)),
    abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)),
    show (t + 1) * x ^ 2 = t * x ^ 2 + x ^ 2 by ring, Real.exp_add]
  ring

/-- **The time remainder.** `‖H_{t+h}(z) − H_t(z) + h H_t''(z)‖ ≤ K h²` for `0 ≤ h ≤ 1`. -/
theorem norm_riemannHeat_time_remainder_le {t h : ℝ} (ht : 0 ≤ t) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (z : ℂ) :
    ‖riemannHeat (t + h) z - riemannHeat t z + h * deriv (deriv (riemannHeat t)) z‖ ≤
      (∫ x, |x| ^ 4 * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) * h ^ 2 := by
  set G := heatWeight t
  have hGc := continuous_heatWeight t
  rw [(hasDerivAt_deriv_riemannHeat ht z).deriv]
  simp only [riemannHeat_eq_expTransform, expTransform]
  have hself : ∀ s : ℝ, 0 ≤ s → Integrable (fun x : ℝ => heatWeight s x * Complex.exp (I * z * x)) :=
    fun s hs => integrable_heat_exp_mul hs _ (continuous_heatWeight s)
      (fun x => le_mul_of_one_le_right (norm_nonneg _)
        (by have := abs_nonneg x; rw [pow_one]; linarith)) z
  have hsq : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z * x)) := by
    refine ((integrable_pow_mul_heatWeight ht 2 |z.im|)).mono'
      ((((by fun_prop : Continuous fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))).mul hGc).mul
        (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
      ← sq_abs x]
    gcongr
    exact norm_exp_I_mul_le z x
  rw [← integral_mul_const, show ∀ a b c : ℂ, a - b + (h : ℂ) * -c = a - b - c * h by
    intro a b c; ring]
  rw [← integral_sub (hself (t + h) (by linarith)) (hself t ht), ← integral_mul_const,
    ← integral_sub ?_ (hsq.mul_const _)]
  swap
  · exact (hself (t + h) (by linarith)).sub (hself t ht)
  refine norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight (by linarith : (0 : ℝ) ≤ t + 1) 4 |z.im|).mul_const (h ^ 2))
    (Eventually.of_forall fun x => ?_)
  have hsplit : heatWeight (t + h) x * Complex.exp (I * z * x) - G x * Complex.exp (I * z * x) -
      ((x ^ 2 : ℝ) : ℂ) * G x * Complex.exp (I * z * x) * h =
      G x * Complex.exp (I * z * x) *
        ((Real.exp (h * x ^ 2) - 1 - h * x ^ 2 : ℝ) : ℂ) := by
    rw [heatWeight_add]; push_cast; ring
  rw [hsplit, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hr : 0 ≤ h * x ^ 2 := by positivity
  have h1 := rexp_sub_one_sub_le hr
  have h1' : |Real.exp (h * x ^ 2) - 1 - h * x ^ 2| ≤ (h * x ^ 2) ^ 2 * Real.exp (h * x ^ 2) := by
    rw [abs_of_nonneg (by linarith [Real.add_one_le_exp (h * x ^ 2)])]; exact h1
  have h2 := norm_exp_I_mul_le z x
  have h3 : Real.exp (h * x ^ 2) ≤ Real.exp (x ^ 2) := by
    gcongr; nlinarith [sq_nonneg x]
  have hmain := norm_heatWeight_mul_exp t x
  calc ‖G x‖ * ‖Complex.exp (I * z * x)‖ * |Real.exp (h * x ^ 2) - 1 - h * x ^ 2|
      ≤ ‖G x‖ * Real.exp (|z.im| * |x|) * ((h * x ^ 2) ^ 2 * Real.exp (x ^ 2)) := by
        gcongr
        exact h1'.trans (by gcongr)
    _ = |x| ^ 4 * (‖G x‖ * Real.exp (x ^ 2)) * Real.exp (|z.im| * |x|) * h ^ 2 := by
        rw [show |x| ^ 4 = (x ^ 2) ^ 2 by rw [← sq_abs x]; ring]; ring
    _ = |x| ^ 4 * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|) * h ^ 2 := by rw [hmain]

/-- **Zero motion.** Near a simple zero `z₀` of `H_t` (`t > 0`), every zero of `H_{t+h}` satisfies
`Im z ≤ Im z₀ + h Im(H_t''(z₀)/H_t'(z₀)) + C h²` for small `h ≥ 0`. -/
theorem exists_im_zero_le_of_simple_zero {t : ℝ} (ht : 0 < t) {z₀ : ℂ}
    (hz : riemannHeat t z₀ = 0) (hd : deriv (riemannHeat t) z₀ ≠ 0) :
    ∃ r > 0, ∃ h₀ > 0, ∃ C : ℝ, ∀ h ∈ Icc (0 : ℝ) h₀, ∀ z : ℂ, ‖z - z₀‖ ≤ r →
      riemannHeat (t + h) z = 0 →
      z.im ≤ z₀.im + h * (deriv (deriv (riemannHeat t)) z₀ / deriv (riemannHeat t) z₀).im +
        C * h ^ 2 := by
  set a := deriv (riemannHeat t) z₀ with ha_def
  set H'' := deriv (deriv (riemannHeat t)) with hH''
  set c₀ := |z₀.im| + 1 with hc₀
  set M := ∫ x, |x| ^ 2 * ‖heatWeight t x‖ * Real.exp (c₀ * |x|) with hM
  set L := ∫ x, |x| ^ 3 * ‖heatWeight t x‖ * Real.exp (c₀ * |x|) with hL
  set K := ∫ x, |x| ^ 4 * ‖heatWeight (t + 1) x‖ * Real.exp (c₀ * |x|) with hK
  have hM0 : 0 ≤ M := integral_nonneg fun x => by positivity
  have hL0 : 0 ≤ L := integral_nonneg fun x => by positivity
  have hK0 : 0 ≤ K := integral_nonneg fun x => by positivity
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr hd
  set D := 2 * (‖H'' z₀‖ + K) / ‖a‖ with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨min 1 (‖a‖ / (4 * (M + 1))), by positivity, min 1 (‖a‖ / (4 * (L + 1))), by positivity,
    (M * D ^ 2 + L * D + K) / ‖a‖, fun h hh z hzr hzero => ?_⟩
  have hh0 := hh.1
  have hh1 : h ≤ 1 := hh.2.trans (min_le_left _ _)
  have hr1 : ‖z - z₀‖ ≤ 1 := hzr.trans (min_le_left _ _)
  have hzim : |z.im| ≤ c₀ := by
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      have := Complex.abs_im_le_norm (z - z₀); simpa using this
    have := abs_sub_abs_le_abs_sub z.im z₀.im
    rw [hc₀]; linarith
  -- the three hypotheses of the generic estimate
  have hf : ‖riemannHeat t z - a * (z - z₀)‖ ≤ M * ‖z - z₀‖ ^ 2 := by
    have := norm_riemannHeat_taylor_le ht.le (z₀ := z₀) hr1
    rwa [hz, sub_zero] at this
  have hg : ‖(fun w => -H'' w) z - (fun w => -H'' w) z₀‖ ≤ L * ‖z - z₀‖ := by
    simp only
    rw [neg_sub_neg, norm_sub_rev]
    exact norm_deriv_deriv_riemannHeat_sub_le ht.le hr1
  have hE : ‖riemannHeat (t + h) z - riemannHeat t z + h * H'' z‖ ≤ K * h ^ 2 := by
    refine (norm_riemannHeat_time_remainder_le ht.le hh0 hh1 z).trans ?_
    gcongr
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      (integrable_pow_mul_heatWeight (by linarith) 4 c₀) (Eventually.of_forall fun x => ?_)
    simp only
    gcongr
  have hdM : M * ‖z - z₀‖ ≤ ‖a‖ / 4 := by
    have h1 : ‖z - z₀‖ ≤ ‖a‖ / (4 * (M + 1)) := hzr.trans (min_le_right _ _)
    calc M * ‖z - z₀‖ ≤ M * (‖a‖ / (4 * (M + 1))) := by gcongr
      _ ≤ ‖a‖ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hhL : h * L ≤ ‖a‖ / 4 := by
    have h1 : h ≤ ‖a‖ / (4 * (L + 1)) := hh.2.trans (min_le_right _ _)
    calc h * L ≤ ‖a‖ / (4 * (L + 1)) * L := by gcongr
      _ ≤ ‖a‖ / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨hdist, hpred⟩ := norm_sub_predicted_le (f := riemannHeat t) (g := fun w => -H'' w)
    (E := fun w => riemannHeat (t + h) w - riemannHeat t w + h * H'' w) (z₀ := z₀) (a := a)
    (z := z) hd hh0 hf hg hE (by rw [← hzero]; ring) hdM hhL
  rw [norm_neg] at hdist
  -- `‖z − z₀‖ ≤ D h`
  have hdh : ‖z - z₀‖ ≤ D * h := by
    refine hdist.trans ?_
    rw [hD, div_mul_eq_mul_div, div_le_div_iff₀ hna hna]
    have : h ^ 2 ≤ h := by nlinarith
    have key : 2 * (h * ‖H'' z₀‖ + K * h ^ 2) ≤ 2 * (‖H'' z₀‖ + K) * h := by
      nlinarith [mul_le_mul_of_nonneg_left this hK0]
    exact mul_le_mul_of_nonneg_right key hna.le
  have hd0 : 0 ≤ ‖z - z₀‖ := norm_nonneg _
  have hrem : ‖z - (z₀ - h * -H'' z₀ / a)‖ ≤ (M * D ^ 2 + L * D + K) / ‖a‖ * h ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hna, mul_comm]
    refine hpred.trans ?_
    have e1 : M * ‖z - z₀‖ ^ 2 ≤ M * (D * h) ^ 2 := by gcongr
    have e2 : h * L * ‖z - z₀‖ ≤ h * L * (D * h) := by gcongr
    nlinarith
  have him : (z - (z₀ - h * -H'' z₀ / a)).im ≤ ‖z - (z₀ - h * -H'' z₀ / a)‖ :=
    (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have hre : (z - (z₀ - h * -H'' z₀ / a)).im = z.im - z₀.im - h * (H'' z₀ / a).im := by
    rw [show z - (z₀ - (h : ℂ) * -H'' z₀ / a) = z - z₀ - (h : ℂ) * (H'' z₀ / a) by ring,
      Complex.sub_im, Complex.sub_im, Complex.im_ofReal_mul]
  rw [hre] at him
  linarith

end

end RHTower.DeBruijn

