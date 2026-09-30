import GaloisForLFunctions.RHTower.DeBruijnLaguerreLargeHeight

/-!
# The de Bruijn–Newman deformation solves the backward heat equation

For a complex weight `G` with `‖G(x)‖ e^{c|x|}` integrable for every `c`, the transform
`z ↦ ∫ G(x) e^{izx} dx` is differentiable with derivative `∫ G(x)(ix) e^{izx} dx`
(`hasDerivAt_expTransform`, dominated differentiation on unit balls). Applied twice to
`G = Φ(x)e^{tx²}` and once in the heat time,

`∂_t H_t(z) = ∫ x² Φ(x) e^{tx²} e^{izx} dx = −∂_z² H_t(z)`   (`hasDerivAt_riemannHeat_time`).

This is the evolution law behind the motion of the zeros: at a simple zero, `ż = H''/H'`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-- The exponential transform `z ↦ ∫ G(x) e^{izx} dx`. -/
def expTransform (G : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, G x * Complex.exp (I * z * x)

theorem norm_exp_I_mul_le (z : ℂ) (x : ℝ) :
    ‖Complex.exp (I * z * x)‖ ≤ Real.exp (|z.im| * |x|) := by
  rw [Complex.norm_exp]
  gcongr
  have : (I * z * (x : ℂ)).re = -(z.im * x) := by simp [Complex.mul_re]
  rw [this, ← abs_mul]
  exact neg_le_abs _

/-- **Differentiation under the integral.** -/
theorem hasDerivAt_expTransform {G : ℝ → ℂ} (hG : Continuous G)
    (hint : ∀ c : ℝ, Integrable (fun x => ‖G x‖ * Real.exp (c * |x|))) (z₀ : ℂ) :
    HasDerivAt (expTransform G) (expTransform (fun x => G x * (I * x)) z₀) z₀ := by
  set c := |z₀.im| + 1 with hc
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => G x * Complex.exp (I * z * x)) volume :=
    fun z => (hG.mul (by fun_prop)).aestronglyMeasurable
  have hint0 : Integrable (fun x : ℝ => G x * Complex.exp (I * z₀ * x)) := by
    refine (hint |z₀.im|).mono' (hmeas z₀) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    gcongr
    exact norm_exp_I_mul_le z₀ x
  have hmeas' : AEStronglyMeasurable (fun x : ℝ => G x * (I * x) * Complex.exp (I * z₀ * x))
      volume := ((hG.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ z ∈ ball z₀ 1,
      ‖G x * (I * x) * Complex.exp (I * z * x)‖ ≤ ‖G x‖ * Real.exp ((c + 1) * |x|) := by
    refine Eventually.of_forall fun x z hz => ?_
    have hzim : |z.im| ≤ c := by
      have h1 : ‖z - z₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hz
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        have := Complex.abs_im_le_norm (z - z₀); simpa using this
      have h3 := abs_sub_abs_le_abs_sub z.im z₀.im
      rw [hc]; linarith
    have hx : ‖I * (x : ℂ)‖ ≤ Real.exp |x| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith [Real.add_one_le_exp |x|]
    rw [norm_mul, norm_mul]
    calc ‖G x‖ * ‖I * (x : ℂ)‖ * ‖Complex.exp (I * z * x)‖
        ≤ ‖G x‖ * Real.exp |x| * Real.exp (c * |x|) := by
          gcongr
          exact (norm_exp_I_mul_le z x).trans (by gcongr)
      _ = ‖G x‖ * Real.exp ((c + 1) * |x|) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), ∀ z ∈ ball z₀ 1,
      HasDerivAt (fun z => G x * Complex.exp (I * z * x))
        (G x * (I * x) * Complex.exp (I * z * x)) z := by
    refine Eventually.of_forall fun x z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => I * z * x) (I * x) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (x : ℂ)
    have := (h1.cexp).const_mul (G x)
    exact this.congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall hmeas) hint0 hmeas' hbound (hint (c + 1)) hderiv).2

theorem integrable_mul_poly {G : ℝ → ℂ}
    (hint : ∀ c : ℝ, Integrable (fun x => ‖G x‖ * Real.exp (c * |x|))) (hG : Continuous G) (c : ℝ) :
    Integrable (fun x => ‖G x * (I * x)‖ * Real.exp (c * |x|)) := by
  refine (hint (c + 1)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (((hG.mul (by fun_prop)).norm).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖G x‖ * |x| * Real.exp (c * |x|) ≤ ‖G x‖ * Real.exp |x| * Real.exp (c * |x|) := by
          gcongr; linarith [Real.add_one_le_exp |x|]
      _ = ‖G x‖ * Real.exp ((c + 1) * |x|) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The heat weight `Φ(x) e^{tx²}` as a complex function. -/
def heatWeight (t : ℝ) (x : ℝ) : ℂ := ((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ)

theorem continuous_heatWeight (t : ℝ) : Continuous (heatWeight t) := by
  have := continuous_riemannKernelReal
  unfold heatWeight; fun_prop

theorem integrable_heatWeight {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    Integrable (fun x => ‖heatWeight t x‖ * Real.exp (c * |x|)) := by
  refine ((riemannKernel_superExp.mul_exp_sq ht).integrable_mul_exp c).congr
    (Eventually.of_forall fun x => ?_)
  simp only [heatWeight]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]

theorem riemannHeat_eq_expTransform (t : ℝ) : riemannHeat t = expTransform (heatWeight t) := by
  funext z; rfl

/-- The first `z`-derivative of `H_t`. -/
theorem deriv_riemannHeat {t : ℝ} (ht : 0 ≤ t) :
    deriv (riemannHeat t) = expTransform (fun x => heatWeight t x * (I * x)) := by
  funext z
  rw [riemannHeat_eq_expTransform]
  exact (hasDerivAt_expTransform (continuous_heatWeight t) (integrable_heatWeight ht) z).deriv

/-- The second `z`-derivative of `H_t`: `H_t'' = −∫ x² Φ e^{tx²} e^{izx}`. -/
theorem hasDerivAt_deriv_riemannHeat {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasDerivAt (deriv (riemannHeat t))
      (-expTransform (fun x => ((x ^ 2 : ℝ) : ℂ) * heatWeight t x) z) z := by
  rw [deriv_riemannHeat ht]
  have hc : Continuous fun x : ℝ => heatWeight t x * (I * x) := by
    have := continuous_heatWeight t; fun_prop
  have h := hasDerivAt_expTransform (G := fun x : ℝ => heatWeight t x * (I * x)) hc
    (integrable_mul_poly (integrable_heatWeight ht) (continuous_heatWeight t)) z
  refine h.congr_deriv ?_
  unfold expTransform
  rw [← integral_neg]
  congr 1
  funext x
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **The backward heat equation.** `∂_t H_t(z) = −∂_z² H_t(z)` for `t > 0`. -/
theorem hasDerivAt_riemannHeat_time {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (fun s => riemannHeat s z) (-deriv (deriv (riemannHeat t)) z) t := by
  rw [(hasDerivAt_deriv_riemannHeat ht.le z).deriv, neg_neg]
  set c := |z.im| with hc
  have hF : ∀ s : ℝ, riemannHeat s z = ∫ x : ℝ, heatWeight s x * Complex.exp (I * z * x) :=
    fun s => rfl
  simp_rw [hF]
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun x : ℝ => heatWeight s x * Complex.exp (I * z * x)) volume :=
    fun s => ((continuous_heatWeight s).mul (by fun_prop)).aestronglyMeasurable
  have hint0 : Integrable (fun x : ℝ => heatWeight t x * Complex.exp (I * z * x)) := by
    refine (integrable_heatWeight ht.le c).mono' (hmeas t) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]; gcongr; exact norm_exp_I_mul_le z x
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * heatWeight t x * Complex.exp (I * z * x)) volume :=
    (((by fun_prop : Continuous fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))).mul
      (continuous_heatWeight t) |>.mul (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ s ∈ ball t 1,
      ‖((x ^ 2 : ℝ) : ℂ) * heatWeight s x * Complex.exp (I * z * x)‖ ≤
        ‖heatWeight (t + 2) x‖ * Real.exp (c * |x|) := by
    refine Eventually.of_forall fun x s hs => ?_
    have hs1 : s ≤ t + 1 := by
      have := mem_ball.mp hs; rw [Real.dist_eq, abs_lt] at this; linarith
    simp only [heatWeight]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg x), abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)),
      abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
    have hsq : x ^ 2 ≤ Real.exp (x ^ 2) := by linarith [Real.add_one_le_exp (x ^ 2)]
    have hΦ := (riemannKernelReal_pos x).le
    have h1 : x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2)) ≤
        Real.exp (x ^ 2) * (riemannKernelReal x * Real.exp ((t + 1) * x ^ 2)) :=
      mul_le_mul hsq (by gcongr) (by positivity) (by positivity)
    calc x ^ 2 * (riemannKernelReal x * Real.exp (s * x ^ 2)) * ‖Complex.exp (I * z * x)‖
        ≤ Real.exp (x ^ 2) * (riemannKernelReal x * Real.exp ((t + 1) * x ^ 2)) *
            Real.exp (c * |x|) :=
          mul_le_mul h1 (norm_exp_I_mul_le z x) (norm_nonneg _) (by positivity)
      _ = riemannKernelReal x * Real.exp ((t + 2) * x ^ 2) * Real.exp (c * |x|) := by
          rw [show (t + 2) * x ^ 2 = x ^ 2 + (t + 1) * x ^ 2 by ring, Real.exp_add]; ring
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), ∀ s ∈ ball t 1,
      HasDerivAt (fun s => heatWeight s x * Complex.exp (I * z * x))
        (((x ^ 2 : ℝ) : ℂ) * heatWeight s x * Complex.exp (I * z * x)) s := by
    refine Eventually.of_forall fun x s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => riemannKernelReal x * Real.exp (s * x ^ 2))
        (riemannKernelReal x * (Real.exp (s * x ^ 2) * x ^ 2)) s := by
      have := ((hasDerivAt_id s).mul_const (x ^ 2)).exp.const_mul (riemannKernelReal x)
      simpa using this
    have h2 := h1.ofReal_comp.mul_const (Complex.exp (I * z * x))
    simp only [heatWeight]
    refine h2.congr_deriv ?_
    push_cast
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t one_pos)
    (Eventually.of_forall hmeas) hint0 hmeas' hbound
    (integrable_heatWeight (by linarith) c) hderiv).2

end

end RHTower.DeBruijn
