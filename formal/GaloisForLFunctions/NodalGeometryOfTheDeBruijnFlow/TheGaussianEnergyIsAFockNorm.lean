import GaloisForLFunctions.RHTower.DeBruijnHeatEquation
import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage

/-!
# The Gaussian energy of a caloric transform is a Fock norm

Let `g` have super-Gaussian decay and let `u_t(z) = ∫ g(y) e^{ty²} e^{izy} dy` (`caloric`), so that
`∂_t u = −∂_z² u`; `g = Φ` gives `H_t` at every real time. With `G_σ` the normal density of variance
`2σ`, for every complex point `z₀ = x₀ + iy₀`, `t₀ ∈ ℝ` and `σ > 0`,

`∫ ‖u_{t₀+σ}(x + iy₀)‖² G_σ(x − x₀) dx = Σ_n (2σ)^n/n! · ‖∂ⁿu_{t₀}(z₀)‖²`   (`hasSum_fock`).

The left side is a Gaussian energy on a horizontal line at the later time `t₀ + σ`; the right side only
involves the Taylor data of `u_{t₀}` at `z₀`. This is the chaos expansion of the Gaussian variance.

Proof. The left side is `∫∫ φ(y) φ(y') e^{ix₀(y−y')} e^{−σ(y−y')²}` with `φ = g e^{(t₀+σ)y²} e^{−y₀y}`, by
Fubini and the Gaussian transform. Since `σ(y² + y'²) − σ(y − y')² = 2σyy'`, this is
`∫∫ k(y) conj k(y') e^{2σyy'}` with `k = g e^{t₀y²} e^{iz₀y}`, and the exponential series factors termwise.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- Kernels of super-Gaussian decay: `|g(x)| e^{cx²}` is integrable for every real `c`. -/
structure SuperGaussian (g : ℝ → ℝ) : Prop where
  continuous : Continuous g
  integrable_mul_exp : ∀ c : ℝ, Integrable (fun x => |g x| * Real.exp (c * x ^ 2))

/-- The caloric transform `u_t(z) = ∫ g(y) e^{ty²} e^{izy} dy`. -/
def caloric (g : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * y)

namespace SuperGaussian

variable {g : ℝ → ℝ}

/-- Polynomial and exponential factors are absorbed by the Gaussian room. -/
theorem integrable_mul_exp_abs (hg : SuperGaussian g) (t c : ℝ) :
    Integrable (fun y => |g y| * Real.exp (t * y ^ 2) * Real.exp (c * |y|)) := by
  refine ((hg.integrable_mul_exp (t + 1)).mul_const (Real.exp (c ^ 2))).mono'
    ((hg.continuous.abs.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexp : t * y ^ 2 + c * |y| ≤ (t + 1) * y ^ 2 + c ^ 2 := by
    nlinarith only [sq_nonneg (|y| - c), sq_abs y, sq_nonneg c, sq_nonneg (|y| - c / 2)]
  calc |g y| * Real.exp (t * y ^ 2) * Real.exp (c * |y|)
      = |g y| * Real.exp (t * y ^ 2 + c * |y|) := by rw [Real.exp_add]; ring
    _ ≤ |g y| * Real.exp ((t + 1) * y ^ 2 + c ^ 2) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem integrable_mul_pow_exp_abs (hg : SuperGaussian g) (t c : ℝ) (n : ℕ) :
    Integrable (fun y => |g y| * Real.exp (t * y ^ 2) * |y| ^ n * Real.exp (c * |y|)) := by
  refine ((hg.integrable_mul_exp_abs t (c + 1)).const_mul (n.factorial : ℝ)).mono'
    (((hg.continuous.abs.mul (by fun_prop)).mul (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : |y| ^ n ≤ (n.factorial : ℝ) * Real.exp |y| := by
    have h := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) n
    have hf : (0 : ℝ) < n.factorial := by positivity
    rw [div_le_iff₀ hf] at h
    linarith only [h]
  calc |g y| * Real.exp (t * y ^ 2) * |y| ^ n * Real.exp (c * |y|)
      ≤ |g y| * Real.exp (t * y ^ 2) * ((n.factorial : ℝ) * Real.exp |y|) * Real.exp (c * |y|) := by
        gcongr
    _ = _ := by
      rw [show (c + 1) * |y| = c * |y| + |y| by ring, Real.exp_add]; ring

/-- `y g(y)` is again of super-Gaussian decay; its transform reads `∂_z u`. -/
theorem mul_id (hg : SuperGaussian g) : SuperGaussian (fun y => y * g y) := by
  refine ⟨continuous_id.mul hg.continuous, fun c => ?_⟩
  refine (hg.integrable_mul_pow_exp_abs c 0 1).congr (Eventually.of_forall fun y => ?_)
  simp only [abs_mul, zero_mul, Real.exp_zero, mul_one, pow_one]
  ring

end SuperGaussian

/-! ## Derivatives -/

theorem continuous_weight {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    Continuous (fun y : ℝ => ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (hg.mul (by fun_prop))

theorem caloric_eq_expTransform (g : ℝ → ℝ) (t : ℝ) :
    caloric g t = expTransform (fun y : ℝ => ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ)) := rfl

theorem integrable_weight_mul_pow {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) (n : ℕ) (c : ℝ) :
    Integrable (fun y : ℝ =>
      ‖((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * (I * y) ^ n‖ * Real.exp (c * |y|)) := by
  refine (hg.integrable_mul_pow_exp_abs t c n).congr (Eventually.of_forall fun y => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, Real.abs_exp]

/-- `∂ⁿu_t(z) = ∫ g(y) e^{ty²} (iy)ⁿ e^{izy} dy`. -/
theorem iteratedDeriv_caloric {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (caloric g t) =
      expTransform (fun y : ℝ => ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * (I * y) ^ n) := by
  induction n with
  | zero => simp [caloric_eq_expTransform]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hc : Continuous fun y : ℝ => ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * (I * y) ^ n :=
      (continuous_weight hg.continuous t).mul (by fun_prop)
    rw [(hasDerivAt_expTransform hc (integrable_weight_mul_pow hg t n) z).deriv]
    congr 1
    funext y
    ring

theorem differentiable_caloric {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) :
    Differentiable ℂ (caloric g t) := by
  intro z
  have h := hasDerivAt_expTransform (continuous_weight hg.continuous t)
    (fun c => by simpa using integrable_weight_mul_pow hg t 0 c) z
  exact h.differentiableAt

/-- `∂_z u_t = i · u_t[y g]`: the first derivative is the transform of `y g(y)`. -/
theorem deriv_caloric {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) (z : ℂ) :
    deriv (caloric g t) z = I * caloric (fun y => y * g y) t z := by
  have h := congrFun (iteratedDeriv_caloric hg t 1) z
  rw [iteratedDeriv_one] at h
  rw [h, expTransform, caloric, ← integral_const_mul]
  congr 1
  funext y
  push_cast
  ring

/-- The norm of the `n`-th derivative is the norm of the `n`-th moment. -/
theorem norm_iteratedDeriv_caloric {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv n (caloric g t) z‖ =
      ‖∫ y : ℝ, ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * y) * (y : ℂ) ^ n‖ := by
  rw [iteratedDeriv_caloric hg, expTransform]
  have : (fun y : ℝ => ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * (I * y) ^ n * Complex.exp (I * z * y))
      = fun y : ℝ => I ^ n * (((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * y) *
          (y : ℂ) ^ n) := by
    funext y
    rw [mul_pow]
    ring
  rw [this, integral_const_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
