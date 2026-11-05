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
    Real.abs_exp]

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

/-! ## The Gaussian transform on a line -/

/-- `∫ G_σ(x − x₀) e^{ixw} dx = e^{ix₀w − σw²}`. -/
theorem integral_gaussDensity_sub_mul_cexp {σ : ℝ} (hσ : 0 < σ) (x₀ w : ℝ) :
    ∫ x : ℝ, (gaussDensity σ (x - x₀) : ℂ) * Complex.exp (I * x * w) =
      Complex.exp (I * x₀ * w - σ * w ^ 2) := by
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => (gaussDensity σ u : ℂ) * Complex.exp (I * ((u + x₀ : ℝ) : ℂ) * w)) x₀
  simp only [sub_add_cancel] at hshift
  rw [hshift]
  have hmgf := integral_gaussDensity_mul_exp hσ (I * (w : ℂ))
  have hfun : (fun u : ℝ => (gaussDensity σ u : ℂ) * Complex.exp (I * ((u + x₀ : ℝ) : ℂ) * w)) =
      fun u : ℝ => Complex.exp (I * x₀ * w) *
        ((gaussDensity σ u : ℂ) * Complex.exp ((u : ℂ) * (I * (w : ℂ)))) := by
    funext u
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun, integral_const_mul, hmgf, ← Complex.exp_add]
  congr 1
  rw [mul_pow, I_sq]
  ring

theorem integrable_gaussDensity_sub {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    Integrable (fun x : ℝ => gaussDensity σ (x - x₀)) := by
  have h := integrable_gaussDensity_mul_exp hσ 0
  simp only [mul_zero, Complex.exp_zero, mul_one] at h
  have hr : Integrable (fun u : ℝ => gaussDensity σ u) := by
    simpa using h.re
  exact hr.comp_sub_right x₀

theorem continuous_gaussDensity_sub (σ x₀ : ℝ) :
    Continuous (fun x : ℝ => gaussDensity σ (x - x₀)) := by
  unfold gaussDensity
  fun_prop

/-! ## The line energy as a double integral -/

/-- The tilted density of `u_t` on the horizontal line at height `y₀`. -/
private def lineWeight (g : ℝ → ℝ) (t y₀ : ℝ) (y : ℝ) : ℝ :=
  g y * Real.exp (t * y ^ 2) * Real.exp (-y₀ * y)

private theorem caloric_line (g : ℝ → ℝ) (t x y₀ : ℝ) :
    caloric g t ((x : ℂ) + y₀ * I) =
      ∫ y : ℝ, (lineWeight g t y₀ y : ℂ) * Complex.exp (I * x * y) := by
  unfold caloric lineWeight
  congr 1
  funext y
  have he : I * ((x : ℂ) + y₀ * I) * y = ((-y₀ * y : ℝ) : ℂ) + I * x * y := by
    push_cast
    linear_combination ((y₀ : ℂ) * y) * I_sq
  rw [he, Complex.exp_add]
  push_cast
  ring

private theorem continuous_lineWeight {g : ℝ → ℝ} (hg : Continuous g) (t y₀ : ℝ) :
    Continuous (lineWeight g t y₀) := by
  unfold lineWeight
  fun_prop

private theorem integrable_lineWeight {g : ℝ → ℝ} (hg : SuperGaussian g) (t y₀ : ℝ) :
    Integrable (lineWeight g t y₀) := by
  refine (hg.integrable_mul_exp_abs t |y₀|).mono'
    (continuous_lineWeight hg.continuous t y₀).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  unfold lineWeight
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp]
  have : -y₀ * y ≤ |y₀| * |y| := by
    rw [← abs_mul]
    exact (le_abs_self _).trans (by rw [neg_mul, abs_neg])
  gcongr

/-- Fubini: the Gaussian line energy of `∫ φ e^{ixy}` is a double integral. -/
private theorem line_energy_eq_double {φ : ℝ → ℝ} (hc : Continuous φ) (hi : Integrable φ)
    {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    ((∫ x : ℝ, ‖∫ y : ℝ, (φ y : ℂ) * Complex.exp (I * x * y)‖ ^ 2 * gaussDensity σ (x - x₀) : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, (φ p.1 : ℂ) * (φ p.2 : ℂ) *
        Complex.exp (I * x₀ * ((p.1 - p.2 : ℝ) : ℂ) - σ * ((p.1 - p.2 : ℝ) : ℂ) ^ 2) := by
  classical
  set Ψ : ℝ → ℝ × ℝ → ℂ := fun x p => (gaussDensity σ (x - x₀) : ℂ) *
    ((φ p.1 : ℂ) * (φ p.2 : ℂ) * Complex.exp (I * x * ((p.1 - p.2 : ℝ) : ℂ))) with hΨ
  have hnormexp (x w : ℝ) : ‖Complex.exp (I * x * (w : ℂ))‖ = 1 := by
    rw [show I * (x : ℂ) * (w : ℂ) = ((x * w : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- the pointwise square as an integral over pairs
  have hsq (x : ℝ) :
      ((‖∫ y : ℝ, (φ y : ℂ) * Complex.exp (I * x * y)‖ ^ 2 : ℝ) : ℂ) =
        ∫ p : ℝ × ℝ, (φ p.1 : ℂ) * (φ p.2 : ℂ) * Complex.exp (I * x * ((p.1 - p.2 : ℝ) : ℂ)) := by
    set A : ℂ := ∫ y : ℝ, (φ y : ℂ) * Complex.exp (I * x * y) with hA
    have hconj : (starRingEnd ℂ) A = ∫ y : ℝ, (φ y : ℂ) * Complex.exp (-(I * x * y)) := by
      rw [hA, ← integral_conj]
      congr 1
      funext y
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hprod := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun y : ℝ => (φ y : ℂ) * Complex.exp (I * x * y))
      (fun y : ℝ => (φ y : ℂ) * Complex.exp (-(I * x * y)))
    rw [← hconj] at hprod
    have hmul : A * (starRingEnd ℂ) A = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← hmul, ← hprod]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    push_cast
    rw [show (φ p.1 : ℂ) * Complex.exp (I * x * p.1) * ((φ p.2 : ℂ) * Complex.exp (-(I * x * p.2))) =
      (φ p.1 : ℂ) * (φ p.2 : ℂ) * (Complex.exp (I * x * p.1) * Complex.exp (-(I * x * p.2))) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  have hint : Integrable (Function.uncurry Ψ)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have hmaj := ((integrable_gaussDensity_sub hσ x₀).mul_prod
      ((hi.norm.mul_prod hi.norm) : Integrable (fun p : ℝ × ℝ => ‖φ p.1‖ * ‖φ p.2‖)
        ((volume : Measure ℝ).prod volume)))
    refine hmaj.mono' ?_ (Eventually.of_forall fun q => ?_)
    · apply Continuous.aestronglyMeasurable
      refine ((Complex.continuous_ofReal.comp
        ((continuous_gaussDensity_sub σ x₀).comp continuous_fst)).mul
        (((Complex.continuous_ofReal.comp (hc.comp (continuous_fst.comp continuous_snd))).mul
          (Complex.continuous_ofReal.comp (hc.comp (continuous_snd.comp continuous_snd)))).mul ?_))
      fun_prop
    · simp only [Function.uncurry, hΨ, norm_mul, Complex.norm_real, hnormexp, mul_one,
        Real.norm_eq_abs, abs_of_pos (gaussDensity_pos hσ _)]
      exact le_of_eq (by simp)
  have hswap := integral_integral_swap (f := Ψ) hint
  have hleft : ((∫ x : ℝ, ‖∫ y : ℝ, (φ y : ℂ) * Complex.exp (I * x * y)‖ ^ 2 *
      gaussDensity σ (x - x₀) : ℝ) : ℂ) = ∫ x : ℝ, ∫ p : ℝ × ℝ, Ψ x p := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hΨ]
    rw [integral_const_mul, ← hsq x]
    push_cast
    ring
  refine hleft.trans (hswap.trans (integral_congr_ae (Eventually.of_forall fun p => ?_)))
  simp only [hΨ]
  have hfun : (fun x : ℝ => (gaussDensity σ (x - x₀) : ℂ) *
        ((φ p.1 : ℂ) * (φ p.2 : ℂ) * Complex.exp (I * x * ((p.1 - p.2 : ℝ) : ℂ)))) =
      fun x : ℝ => (φ p.1 : ℂ) * (φ p.2 : ℂ) *
        ((gaussDensity σ (x - x₀) : ℂ) * Complex.exp (I * x * ((p.1 - p.2 : ℝ) : ℂ))) := by
    funext x
    ring
  rw [hfun, integral_const_mul, integral_gaussDensity_sub_mul_cexp hσ]

/-! ## The Fock identity -/

/-- The amplitude `k(y) = g(y) e^{ty²} e^{izy}`. -/
private def amp (g : ℝ → ℝ) (t : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  ((g y * Real.exp (t * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z * y)

private theorem norm_amp (g : ℝ → ℝ) (t : ℝ) (z : ℂ) (y : ℝ) :
    ‖amp g t z y‖ = |g y| * Real.exp (t * y ^ 2) * Real.exp (-(z.im * y)) := by
  unfold amp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

private theorem continuous_amp {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) (z : ℂ) :
    Continuous (amp g t z) := by
  unfold amp
  exact (continuous_weight hg t).mul (by fun_prop)

private theorem neg_im_mul_le (z : ℂ) (y : ℝ) : -(z.im * y) ≤ |z.im| * |y| := by
  rw [← abs_mul]
  exact neg_le_abs _

/-- The integrable majorant of the Fock series. -/
private theorem integrable_amp_mul_exp {g : ℝ → ℝ} (hg : SuperGaussian g) (t σ : ℝ) (z : ℂ) :
    Integrable (fun y : ℝ => ‖amp g t z y‖ * Real.exp (σ * y ^ 2)) := by
  refine (hg.integrable_mul_exp_abs (t + σ) |z.im|).mono'
    (((continuous_amp hg.continuous t z).norm.mul (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_amp, add_mul, Real.exp_add]
  have := neg_im_mul_le z y
  calc |g y| * Real.exp (t * y ^ 2) * Real.exp (-(z.im * y)) * Real.exp (σ * y ^ 2)
      ≤ |g y| * Real.exp (t * y ^ 2) * Real.exp (|z.im| * |y|) * Real.exp (σ * y ^ 2) := by gcongr
    _ = _ := by ring

/-- **The Fock identity.** The Gaussian energy of `u_{t₀+σ}` on the horizontal line through `z₀` is the
Fock norm of the Taylor data of `u_{t₀}` at `z₀`. -/
theorem hasSum_fock {g : ℝ → ℝ} (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z₀ : ℂ) :
    HasSum (fun n : ℕ => (2 * σ) ^ n / (n.factorial : ℝ) * ‖iteratedDeriv n (caloric g t₀) z₀‖ ^ 2)
      (∫ x : ℝ, ‖caloric g (t₀ + σ) ((x : ℂ) + z₀.im * I)‖ ^ 2 * gaussDensity σ (x - z₀.re)) := by
  classical
  set k := amp g t₀ z₀ with hk
  set kb : ℝ → ℂ := fun y => (starRingEnd ℂ) (k y) with hkb
  have hkc : Continuous k := continuous_amp hg.continuous t₀ z₀
  have hkbc : Continuous kb := Complex.continuous_conj.comp hkc
  have hnkb (y : ℝ) : ‖kb y‖ = ‖k y‖ := by simp [hkb]
  -- the double integral form
  have hdouble := line_energy_eq_double (continuous_lineWeight hg.continuous (t₀ + σ) z₀.im)
    (integrable_lineWeight hg (t₀ + σ) z₀.im) hσ z₀.re
  simp_rw [← caloric_line g (t₀ + σ)] at hdouble
  have hk1 (y : ℝ) : k y = (g y : ℂ) * Complex.exp ((t₀ : ℂ) * y ^ 2 + I * z₀ * y) := by
    simp only [hk, amp]
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
  have hzc : (starRingEnd ℂ) z₀ = (z₀.re : ℂ) - z₀.im * I :=
    Complex.ext (by simp) (by simp)
  have hk2 (y : ℝ) : kb y = (g y : ℂ) * Complex.exp ((t₀ : ℂ) * y ^ 2 - I * ((z₀.re : ℂ) - z₀.im * I) * y) := by
    simp only [hkb, hk1, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_add, map_pow,
      Complex.conj_I, hzc]
    congr 2
    ring
  have hl (t y : ℝ) : (lineWeight g t z₀.im y : ℂ) =
      (g y : ℂ) * Complex.exp ((t : ℂ) * y ^ 2 - z₀.im * y) := by
    unfold lineWeight
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hpoint (p : ℝ × ℝ) : (lineWeight g (t₀ + σ) z₀.im p.1 : ℂ) *
        (lineWeight g (t₀ + σ) z₀.im p.2 : ℂ) *
        Complex.exp (I * z₀.re * ((p.1 - p.2 : ℝ) : ℂ) - σ * ((p.1 - p.2 : ℝ) : ℂ) ^ 2) =
      k p.1 * kb p.2 * Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ) := by
    rw [hl, hl, hk1, hk2]
    have hz : I * z₀ * (p.1 : ℂ) = I * (z₀.re : ℂ) * p.1 + I ^ 2 * z₀.im * p.1 := by
      conv_lhs => rw [← Complex.re_add_im z₀]
      ring
    rw [show (g p.1 : ℂ) * Complex.exp (((t₀ + σ : ℝ) : ℂ) * (p.1 : ℂ) ^ 2 - z₀.im * p.1) *
          ((g p.2 : ℂ) * Complex.exp (((t₀ + σ : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 - z₀.im * p.2)) *
          Complex.exp (I * z₀.re * ((p.1 - p.2 : ℝ) : ℂ) - σ * ((p.1 - p.2 : ℝ) : ℂ) ^ 2) =
        (g p.1 : ℂ) * (g p.2 : ℂ) * (Complex.exp (((t₀ + σ : ℝ) : ℂ) * (p.1 : ℂ) ^ 2 - z₀.im * p.1) *
          Complex.exp (((t₀ + σ : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 - z₀.im * p.2) *
          Complex.exp (I * z₀.re * ((p.1 - p.2 : ℝ) : ℂ) - σ * ((p.1 - p.2 : ℝ) : ℂ) ^ 2)) by ring,
      show (g p.1 : ℂ) * Complex.exp ((t₀ : ℂ) * (p.1 : ℂ) ^ 2 + I * z₀ * p.1) *
          ((g p.2 : ℂ) * Complex.exp ((t₀ : ℂ) * (p.2 : ℂ) ^ 2 -
            I * ((z₀.re : ℂ) - z₀.im * I) * p.2)) * Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ) =
        (g p.1 : ℂ) * (g p.2 : ℂ) * (Complex.exp ((t₀ : ℂ) * (p.1 : ℂ) ^ 2 + I * z₀ * p.1) *
          Complex.exp ((t₀ : ℂ) * (p.2 : ℂ) ^ 2 - I * ((z₀.re : ℂ) - z₀.im * I) * p.2) *
          Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ)) by ring,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hz]
    congr 2
    push_cast
    linear_combination (-(z₀.im : ℂ) * ((p.1 : ℂ) + p.2)) * I_sq
  simp_rw [hpoint] at hdouble
  -- the exponential series
  set F : ℕ → ℝ × ℝ → ℂ := fun n p =>
    k p.1 * kb p.2 * (((2 * σ * p.1 * p.2 : ℝ) : ℂ) ^ n / (n.factorial : ℂ)) with hF
  set bound : ℕ → ℝ × ℝ → ℝ := fun n p =>
    ‖k p.1‖ * ‖k p.2‖ * ((2 * σ * |p.1| * |p.2|) ^ n / (n.factorial : ℝ)) with hbound
  have hFnorm (n : ℕ) (p : ℝ × ℝ) : ‖F n p‖ = bound n p := by
    simp only [hF, hbound, norm_mul, norm_div, norm_pow, Complex.norm_real, hnkb, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hσ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbsum (p : ℝ × ℝ) : HasSum (fun n => bound n p)
      (‖k p.1‖ * ‖k p.2‖ * Real.exp (2 * σ * |p.1| * |p.2|)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (2 * σ * |p.1| * |p.2| : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h.mul_left _
  have hFsum (p : ℝ × ℝ) : HasSum (fun n => F n p)
      (k p.1 * kb p.2 * Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (((2 * σ * p.1 * p.2 : ℝ) : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at h
    exact h.mul_left _
  have hbint : Integrable (fun p : ℝ × ℝ => ∑' n, bound n p) := by
    have hmaj := (integrable_amp_mul_exp hg t₀ σ z₀).mul_prod (integrable_amp_mul_exp hg t₀ σ z₀)
    refine Integrable.mono' hmaj ?_ (Eventually.of_forall fun p => ?_)
    · simp_rw [fun p => (hbsum p).tsum_eq]
      apply Continuous.aestronglyMeasurable
      have hn : Continuous fun y => ‖k y‖ := hkc.norm
      fun_prop
    · rw [(hbsum p).tsum_eq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hexp : 2 * σ * |p.1| * |p.2| ≤ σ * p.1 ^ 2 + σ * p.2 ^ 2 := by
        have h1 : 2 * (|p.1| * |p.2|) ≤ p.1 ^ 2 + p.2 ^ 2 := by
          nlinarith only [sq_nonneg (|p.1| - |p.2|), sq_abs p.1, sq_abs p.2]
        nlinarith only [mul_le_mul_of_nonneg_left h1 hσ.le]
      calc ‖k p.1‖ * ‖k p.2‖ * Real.exp (2 * σ * |p.1| * |p.2|)
          ≤ ‖k p.1‖ * ‖k p.2‖ * Real.exp (σ * p.1 ^ 2 + σ * p.2 ^ 2) := by gcongr
        _ = _ := by rw [Real.exp_add]; ring
  have hmain := hasSum_integral_of_dominated_convergence (μ := ((volume : Measure ℝ).prod volume)) bound
    (F := F) (f := fun p => k p.1 * kb p.2 * Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ))
    (fun n => Continuous.aestronglyMeasurable (by
      simp only [hF]
      fun_prop))
    (fun n => Eventually.of_forall fun p => (hFnorm n p).le)
    (Eventually.of_forall fun p => (hbsum p).summable)
    hbint
    (Eventually.of_forall hFsum)
  -- each term factors
  have hterm (n : ℕ) : ∫ p, F n p ∂((volume : Measure ℝ).prod volume) =
      (((2 * σ) ^ n / (n.factorial : ℝ) * ‖iteratedDeriv n (caloric g t₀) z₀‖ ^ 2 : ℝ) : ℂ) := by
    set m : ℂ := ∫ y : ℝ, k y * (y : ℂ) ^ n with hm
    have hconj : (starRingEnd ℂ) m = ∫ y : ℝ, kb y * (y : ℂ) ^ n := by
      rw [hm, ← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [hkb]
    have hprod := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun y : ℝ => k y * (y : ℂ) ^ n) (fun y : ℝ => kb y * (y : ℂ) ^ n)
    rw [← hm, ← hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hprod
    have hnorm : ‖iteratedDeriv n (caloric g t₀) z₀‖ = ‖m‖ := norm_iteratedDeriv_caloric hg t₀ n z₀
    have hfun : (fun p : ℝ × ℝ => F n p) = fun p : ℝ × ℝ =>
        ((((2 * σ) ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
          (k p.1 * (p.1 : ℂ) ^ n * (kb p.2 * (p.2 : ℂ) ^ n)) := by
      funext p
      simp only [hF]
      push_cast
      rw [mul_pow, mul_pow, mul_pow]
      ring
    rw [hfun, integral_const_mul, hprod, hnorm]
    push_cast
    ring
  simp_rw [hterm] at hmain
  have hright : (∫ p, k p.1 * kb p.2 * Complex.exp ((2 * σ * p.1 * p.2 : ℝ) : ℂ)
      ∂((volume : Measure ℝ).prod volume)) =
      ((∫ x : ℝ, ‖caloric g (t₀ + σ) ((x : ℂ) + z₀.im * I)‖ ^ 2 *
        gaussDensity σ (x - z₀.re) : ℝ) : ℂ) := hdouble.symm
  rw [hright] at hmain
  exact_mod_cast hmain

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
