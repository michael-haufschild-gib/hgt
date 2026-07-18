import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The Gaussian as a Schwartz function

The Gaussian `x ↦ exp(−πx²)` is smooth and all of its derivatives decay faster than every
polynomial, so it is a Schwartz function.  Mathlib supplies the Gaussian's Fourier transform and
the Schwartz space, but not this object, and it is the only bridge between them: the `L²` Fourier
transform is defined by continuous extension from Schwartz functions, so a pointwise Fourier
identity reaches `L²` only through a Schwartz representative.

The construction is a single induction.  Every iterated derivative of the Gaussian is a
polynomial multiple of it — differentiating `p(x)e^{−πx²}` gives `(p'(x) − 2πx p(x))e^{−πx²}` —
and a polynomial multiple of the Gaussian is bounded after multiplication by any power of `x`,
because `e^{πx²}` dominates every monomial through a single term of its exponential series:
`|x|^{2j} e^{−πx²} ≤ j!/π^j`.

Both the real and the complex-valued Gaussian are produced; the complex one is what the `L²`
model consumes, and its iterated derivatives have the same norms because `ℝ → ℂ` is an isometry.
-/

open scoped Real FourierTransform

noncomputable section

namespace GaloisForLFunctions

/-- The standard self-dual Gaussian. -/
def gaussReal (x : ℝ) : ℝ := Real.exp (-(π * x ^ 2))

theorem gaussReal_pos (x : ℝ) : 0 < gaussReal x := Real.exp_pos _

theorem contDiff_gaussReal {n : WithTop ℕ∞} : ContDiff ℝ n gaussReal := by
  apply ContDiff.exp
  fun_prop

theorem hasDerivAt_gaussReal (x : ℝ) :
    HasDerivAt gaussReal (-(2 * π * x) * gaussReal x) x := by
  have h : HasDerivAt (fun y : ℝ => -(π * y ^ 2)) (-(π * (2 * x))) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul π).neg
  have h2 := h.exp
  unfold gaussReal
  convert h2 using 1
  ring

/-- Differentiating a polynomial multiple of the Gaussian keeps that shape. -/
theorem hasDerivAt_poly_mul_gaussReal (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y => p.eval y * gaussReal y)
      ((p.derivative - Polynomial.C (2 * π) * Polynomial.X * p).eval x * gaussReal x) x := by
  have hp : HasDerivAt (fun y => p.eval y) (p.derivative.eval x) x := p.hasDerivAt x
  have hmul := hp.mul (hasDerivAt_gaussReal x)
  convert hmul using 1
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **Every iterated derivative of the Gaussian is a polynomial multiple of it.** -/
theorem exists_poly_iteratedDeriv_gaussReal (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ, iteratedDeriv n gaussReal x = p.eval x * gaussReal x := by
  induction n with
  | zero =>
    refine ⟨1, fun x => ?_⟩
    simp [iteratedDeriv_zero]
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.derivative - Polynomial.C (2 * π) * Polynomial.X * p, fun x => ?_⟩
    have hfun : iteratedDeriv n gaussReal = fun y => p.eval y * gaussReal y := funext hp
    rw [iteratedDeriv_succ, hfun]
    exact (hasDerivAt_poly_mul_gaussReal p x).deriv

/-- The exponential series dominates a single monomial: `|x|^(2j) e^(−πx²) ≤ j!/π^j`. -/
theorem abs_pow_two_mul_gaussReal_le (j : ℕ) (x : ℝ) :
    |x| ^ (2 * j) * gaussReal x ≤ Nat.factorial j / π ^ j := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx : (0 : ℝ) ≤ π * x ^ 2 := by positivity
  have hkey := Real.pow_div_factorial_le_exp (π * x ^ 2) hx j
  have hexp : (0 : ℝ) < Real.exp (π * x ^ 2) := Real.exp_pos _
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  have habs : |x| ^ (2 * j) = (x ^ 2) ^ j := by
    rw [pow_mul, sq_abs]
  have hg : gaussReal x = (Real.exp (π * x ^ 2))⁻¹ := by
    unfold gaussReal
    rw [← Real.exp_neg]
  rw [habs, hg]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < π ^ j)]
  rw [inv_eq_one_div, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hexp]
  have hstep : (π * x ^ 2) ^ j / (Nat.factorial j : ℝ) ≤ Real.exp (π * x ^ 2) := hkey
  have hexpand : (π * x ^ 2) ^ j = π ^ j * (x ^ 2) ^ j := by rw [mul_pow]
  rw [hexpand] at hstep
  have := (div_le_iff₀ hfac).mp hstep
  nlinarith [this, hfac, hexp.le, pow_nonneg (sq_nonneg x) j]

/-- Any power of `x` times the Gaussian is bounded. -/
theorem exists_bound_abs_pow_mul_gaussReal (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * gaussReal x ≤ C := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k ≤ 2 * j := ⟨k, by omega⟩
  refine ⟨1 + Nat.factorial j / π ^ j, fun x => ?_⟩
  have hb := abs_pow_two_mul_gaussReal_le j x
  have hfacpos : (0 : ℝ) ≤ Nat.factorial j / π ^ j := by positivity
  by_cases hx : |x| ≤ 1
  · have h1 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have h2 : gaussReal x ≤ 1 := by
      unfold gaussReal
      rw [Real.exp_le_one_iff]
      have hnn : (0 : ℝ) ≤ π * x ^ 2 := by positivity
      linarith
    have hprod : |x| ^ k * gaussReal x ≤ 1 * 1 :=
      mul_le_mul h1 h2 (gaussReal_pos x).le zero_le_one
    linarith
  · have hx' : (1 : ℝ) < |x| := not_le.mp hx
    have hmono : |x| ^ k ≤ |x| ^ (2 * j) := pow_le_pow_right₀ hx'.le hj
    have hstep : |x| ^ k * gaussReal x ≤ |x| ^ (2 * j) * gaussReal x :=
      mul_le_mul_of_nonneg_right hmono (gaussReal_pos x).le
    linarith

/-- A polynomial multiple of the Gaussian, times any power of `x`, is bounded. -/
theorem exists_bound_poly_mul_gaussReal (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * (|p.eval x| * gaussReal x) ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C₁, h₁⟩ := hp
    obtain ⟨C₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, fun x => ?_⟩
    have htri : |Polynomial.eval x (p + q)| ≤ |p.eval x| + |q.eval x| := by
      rw [Polynomial.eval_add]
      exact abs_add_le _ _
    have hmul : |x| ^ k * (|Polynomial.eval x (p + q)| * gaussReal x)
        ≤ |x| ^ k * ((|p.eval x| + |q.eval x|) * gaussReal x) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) k)
      exact mul_le_mul_of_nonneg_right htri (gaussReal_pos x).le
    have hsplit : |x| ^ k * ((|p.eval x| + |q.eval x|) * gaussReal x)
        = |x| ^ k * (|p.eval x| * gaussReal x)
          + |x| ^ k * (|q.eval x| * gaussReal x) := by ring
    have := h₁ x
    have := h₂ x
    linarith [hmul, hsplit.le, hsplit.ge, h₁ x, h₂ x]
  | monomial m c =>
    obtain ⟨C, hC⟩ := exists_bound_abs_pow_mul_gaussReal (k + m)
    refine ⟨|c| * C, fun x => ?_⟩
    have heval : |Polynomial.eval x (Polynomial.monomial m c)| = |c| * |x| ^ m := by
      rw [Polynomial.eval_monomial, abs_mul, abs_pow]
    rw [heval]
    have hrw : |x| ^ k * (|c| * |x| ^ m * gaussReal x)
        = |c| * (|x| ^ (k + m) * gaussReal x) := by
      rw [pow_add]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

/-- **The Gaussian as a real-valued Schwartz function.** -/
def gaussianSchwartzReal : SchwartzMap ℝ ℝ where
  toFun := gaussReal
  smooth' := contDiff_gaussReal
  decay' k n := by
    obtain ⟨p, hp⟩ := exists_poly_iteratedDeriv_gaussReal n
    obtain ⟨C, hC⟩ := exists_bound_poly_mul_gaussReal p k
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hp x, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_pos (gaussReal_pos x)]
    exact hC x

@[simp] theorem gaussianSchwartzReal_apply (x : ℝ) : gaussianSchwartzReal x = gaussReal x := rfl

/-- **The Gaussian as a complex-valued Schwartz function**, the form the `L²` model consumes.
The embedding `ℝ → ℂ` is an isometry, so the iterated derivatives have unchanged norms. -/
def gaussianSchwartz : SchwartzMap ℝ ℂ where
  toFun := fun x => (gaussReal x : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp contDiff_gaussReal
  decay' k n := by
    obtain ⟨C, hC⟩ := gaussianSchwartzReal.decay' k n
    refine ⟨C, fun x => ?_⟩
    have hcomp : (fun x : ℝ => (gaussReal x : ℂ)) = Complex.ofRealLI ∘ gaussReal := rfl
    rw [hcomp, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (contDiff_gaussReal (n := (n : WithTop ℕ∞))).contDiffAt le_rfl]
    exact hC x

@[simp] theorem gaussianSchwartz_apply (x : ℝ) :
    gaussianSchwartz x = (gaussReal x : ℂ) := rfl

/-- The Gaussian in the form mathlib's Fourier transform consumes. -/
theorem gaussianSchwartz_eq_cexp (x : ℝ) :
    gaussianSchwartz x = Complex.exp (-(π * (x : ℂ) ^ 2)) := by
  show ((Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) = Complex.exp (-(π * (x : ℂ) ^ 2))
  rw [Complex.ofReal_exp]
  norm_cast



/-! ## The Gaussian is a Fourier eigenfunction, pointwise and in `L²` -/

/-- **The Gaussian is a fixed point of the Fourier transform**, in mathlib's `𝓕`
normalization: the `b = 1` case of the Gaussian Fourier transform. -/
theorem fourierIntegral_gaussianSchwartz :
    𝓕 (fun x : ℝ => Complex.exp (-(π * (x : ℂ) ^ 2)))
      = fun x : ℝ => Complex.exp (-(π * (x : ℂ) ^ 2)) := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have h := fourier_gaussian_pi (b := 1) hb
  simp only [mul_one, div_one, one_div] at h
  rw [show (fun (x : ℝ) => Complex.exp (-(π * (x : ℂ) ^ 2)))
      = fun (x : ℝ) => Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) by
    funext x; ring_nf]
  rw [h]
  funext t
  simp


/-- The Fourier transform of the Gaussian Schwartz function is itself. -/
theorem fourier_gaussianSchwartz : 𝓕 gaussianSchwartz = gaussianSchwartz := by
  apply SchwartzMap.ext
  intro x
  have hfun : (gaussianSchwartz : ℝ → ℂ)
      = fun y : ℝ => Complex.exp (-(π * (y : ℂ) ^ 2)) := by
    funext y
    exact gaussianSchwartz_eq_cexp y
  have hcoe : ((𝓕 gaussianSchwartz : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = 𝓕 (gaussianSchwartz : ℝ → ℂ) := rfl
  rw [hcoe, hfun, fourierIntegral_gaussianSchwartz]

/-- **The Gaussian is a fixed point of the `L²` Fourier transform.**  This is the object the
prolate trial-space argument consumes: a concrete unit-scale function whose `L²` class is
Fourier-invariant, obtained by transporting the pointwise identity through the Schwartz
representative, which is the only route mathlib provides. -/
theorem fourier_gaussianSchwartz_toLp :
    𝓕 (gaussianSchwartz.toLp 2) = gaussianSchwartz.toLp 2 := by
  rw [SchwartzMap.toLp_fourier_eq, fourier_gaussianSchwartz]

end GaloisForLFunctions
