import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics
import GaloisForLFunctions.RHTower.GaussianJetPolynomial

/-!
# The Fourier transform of a polynomial times a Gaussian

Differentiating the Gaussian Fourier integral

`∫ e^{-tx²-iξx} dx = √(π/t) e^{-ξ²/(4t)}`

under the integral sign lowers a factor `-ix`, so the moments

`M_n(ξ) = ∫ x^n e^{-tx²-iξx} dx`

satisfy `M_{n+1} = i ∂_ξ M_n`, and hence are the Gaussian times the jet polynomials:

`M_n(ξ) = i^n √(π/t) q_n(ξ) e^{-ξ²/(4t)}`.

Summing against the coefficients of a polynomial gives the exact factorization of the transform of
`p(x)e^{-tx²}` into the Gaussian times an explicit polynomial in `ξ`.
-/

open MeasureTheory Filter Asymptotics Complex

namespace RHTower

noncomputable section

/-! ## Gaussian majorants -/

theorem integrable_abs_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n * Real.exp (-b * x ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  have hg : Integrable (fun x : ℝ => Real.exp (-(b / 2) * x ^ 2)) := integrable_exp_neg_mul_sq hb2
  have htend := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb2 (n : ℝ)
  have hlt : ∀ᶠ x : ℝ in cocompact ℝ, |x| ^ (n : ℝ) * Real.exp (-(b / 2) * x ^ 2) < 1 :=
    htend.eventually (gt_mem_nhds one_pos)
  have hev : ∀ᶠ x : ℝ in cocompact ℝ,
      ‖|x| ^ n * Real.exp (-b * x ^ 2)‖ ≤ 1 * ‖Real.exp (-(b / 2) * x ^ 2)‖ := by
    filter_upwards [hlt] with x hx
    have hsplit : |x| ^ n * Real.exp (-b * x ^ 2)
        = (|x| ^ (n : ℝ) * Real.exp (-(b / 2) * x ^ 2)) * Real.exp (-(b / 2) * x ^ 2) := by
      rw [Real.rpow_natCast, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hsplit,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (|x| ^ (n : ℝ) * Real.exp (-(b / 2) * x ^ 2))
        * Real.exp (-(b / 2) * x ^ 2)),
      abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hx.le
  have hO : (fun x : ℝ => |x| ^ n * Real.exp (-b * x ^ 2))
      =O[cocompact ℝ] fun x : ℝ => Real.exp (-(b / 2) * x ^ 2) := IsBigO.of_bound 1 hev
  have hloc : LocallyIntegrable (fun x : ℝ => |x| ^ n * Real.exp (-b * x ^ 2)) volume :=
    Continuous.locallyIntegrable (by fun_prop)
  exact hloc.integrable_of_isBigO_cocompact hO (hg.integrableAtFilter _)

/-! ## The Gaussian phase -/

/-- The Gaussian phase `e^{-tx²-iξx}`. -/
def gaussPhase (t ξ x : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 - Complex.I * (ξ : ℂ) * (x : ℂ))

theorem gaussPhase_eq_mul (t ξ x : ℝ) :
    gaussPhase t ξ x
      = Complex.exp (Complex.I * (-(ξ : ℂ)) * (x : ℂ)) * Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) := by
  rw [gaussPhase, ← Complex.exp_add]
  congr 1
  ring

theorem norm_gaussPhase (t ξ x : ℝ) : ‖gaussPhase t ξ x‖ = Real.exp (-t * x ^ 2) := by
  rw [gaussPhase, Complex.norm_exp]
  congr 1
  have h1 : (-(t : ℂ) * (x : ℂ) ^ 2).re = -t * x ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h2 : (Complex.I * (ξ : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.sub_re, h1, h2, sub_zero]

theorem continuous_gaussPhase (t ξ : ℝ) : Continuous fun x : ℝ => gaussPhase t ξ x := by
  unfold gaussPhase
  fun_prop

theorem continuous_gaussMomentIntegrand (t ξ : ℝ) (n : ℕ) :
    Continuous fun x : ℝ => (x : ℂ) ^ n * gaussPhase t ξ x :=
  (Complex.continuous_ofReal.pow n).mul (continuous_gaussPhase t ξ)

theorem continuous_gaussMomentDeriv (t ξ : ℝ) (n : ℕ) :
    Continuous fun x : ℝ => (x : ℂ) ^ n * (-Complex.I * (x : ℂ) * gaussPhase t ξ x) :=
  (Complex.continuous_ofReal.pow n).mul
    ((continuous_const.mul Complex.continuous_ofReal).mul (continuous_gaussPhase t ξ))

/-- The `ξ`-derivative of the Gaussian phase lowers a factor `-ix`. -/
theorem hasDerivAt_gaussPhase (t x ξ : ℝ) :
    HasDerivAt (fun s : ℝ => gaussPhase t s x) (-Complex.I * (x : ℂ) * gaussPhase t ξ x) ξ := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 ξ := by
    simpa using (hasDerivAt_id ξ).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ) * (x : ℂ)) (Complex.I * (x : ℂ)) ξ := by
    simpa using (h1.const_mul Complex.I).mul_const (x : ℂ)
  have h3 : HasDerivAt (fun s : ℝ => -(t : ℂ) * (x : ℂ) ^ 2 - Complex.I * (s : ℂ) * (x : ℂ))
      (-(Complex.I * (x : ℂ))) ξ :=
    HasDerivAt.const_sub (-(t : ℂ) * (x : ℂ) ^ 2) h2
  have h4 := h3.cexp
  refine h4.congr_deriv ?_
  rw [gaussPhase]
  ring

/-! ## Integrability -/

theorem integrable_gaussMomentIntegrand {t : ℝ} (ht : 0 < t) (n : ℕ) (ξ : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * gaussPhase t ξ x) := by
  refine (integrable_abs_pow_mul_exp_neg_mul_sq ht n).mono'
    (continuous_gaussMomentIntegrand t ξ n).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_gaussPhase]

/-! ## The moments -/

/-- The `n`-th Gaussian moment `∫ x^n e^{-tx²-iξx} dx`. -/
def gaussMoment (t : ℝ) (n : ℕ) (ξ : ℝ) : ℂ := ∫ x : ℝ, (x : ℂ) ^ n * gaussPhase t ξ x

/-- Differentiation under the integral sign raises the moment. -/
theorem hasDerivAt_gaussMoment {t : ℝ} (ht : 0 < t) (n : ℕ) (ξ : ℝ) :
    HasDerivAt (fun s : ℝ => gaussMoment t n s) (-Complex.I * gaussMoment t (n + 1) ξ) ξ := by
  set F : ℝ → ℝ → ℂ := fun s x => (x : ℂ) ^ n * gaussPhase t s x with hF
  set F' : ℝ → ℝ → ℂ := fun s x => (x : ℂ) ^ n * (-Complex.I * (x : ℂ) * gaussPhase t s x) with hF'
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (F s) volume := fun s =>
    (continuous_gaussMomentIntegrand t s n).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' ξ) volume :=
    (continuous_gaussMomentDeriv t ξ n).aestronglyMeasurable
  have hbound : Integrable (fun x : ℝ => |x| ^ (n + 1) * Real.exp (-t * x ^ 2)) :=
    integrable_abs_pow_mul_exp_neg_mul_sq ht (n + 1)
  have hle : ∀ᵐ x : ℝ, ∀ s ∈ Set.univ, ‖F' s x‖ ≤ |x| ^ (n + 1) * Real.exp (-t * x ^ 2) := by
    filter_upwards with x s _
    rw [hF']
    simp only
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_neg,
      Complex.norm_I, norm_gaussPhase]
    rw [pow_succ]
    exact le_of_eq (by ring)
  have hdiff : ∀ᵐ x : ℝ, ∀ s ∈ Set.univ, HasDerivAt (fun s : ℝ => F s x) (F' s x) s := by
    filter_upwards with x s _
    rw [hF, hF']
    simp only
    exact (hasDerivAt_gaussPhase t x s).const_mul ((x : ℂ) ^ n)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (x₀ := ξ)
    (bound := fun x => |x| ^ (n + 1) * Real.exp (-t * x ^ 2))
    (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall hmeas)
    (integrable_gaussMomentIntegrand ht n ξ) hmeas' hle hbound hdiff
  have hval : (∫ x : ℝ, F' ξ x) = -Complex.I * gaussMoment t (n + 1) ξ := by
    rw [gaussMoment, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hF']
    simp only
    rw [pow_succ]
    ring
  rw [hval] at hmain
  exact hmain.2

/-- The zeroth moment is the Gaussian Fourier integral. -/
theorem gaussMoment_zero {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    gaussMoment t 0 ξ = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ) := by
  have hb : 0 < ((t : ℂ)).re := by simpa using ht
  have hint : (∫ x : ℝ, Complex.exp (Complex.I * (-(ξ : ℂ)) * (x : ℂ))
        * Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2))
      = ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(-(ξ : ℂ)) ^ 2 / (4 * (t : ℂ))) := fourierIntegral_gaussian hb _
  have hlhs : gaussMoment t 0 ξ
      = ∫ x : ℝ, Complex.exp (Complex.I * (-(ξ : ℂ)) * (x : ℂ))
          * Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) := by
    rw [gaussMoment]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [pow_zero, one_mul, gaussPhase_eq_mul]
  have hcpow : ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) := by
    have hnn : (0 : ℝ) ≤ Real.pi / t := by positivity
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnn]
    norm_num
  have hexp : Complex.exp (-(-(ξ : ℂ)) ^ 2 / (4 * (t : ℂ))) = ((gaussKernel t ξ : ℝ) : ℂ) := by
    rw [gaussKernel, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hlhs, hint, hcpow, hexp]

/-- **The Gaussian moments are the jet polynomials times the Gaussian.** -/
theorem gaussMoment_eq {t : ℝ} (ht : 0 < t) :
    ∀ (n : ℕ) (ξ : ℝ), gaussMoment t n ξ
      = Complex.I ^ n * (Real.sqrt (Real.pi / t) : ℂ)
          * (((gaussJetPoly t n).eval ξ : ℝ) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
  | 0, ξ => by
    rw [gaussMoment_zero ht ξ, gaussJetPoly_zero]
    simp
  | (n + 1), ξ => by
    have hrec := gaussMoment_eq ht n
    have hderiv := hasDerivAt_gaussMoment ht n ξ
    have hreal := hasDerivAt_gaussJet (ne_of_gt ht) n ξ
    have hcplx : HasDerivAt
        (fun y : ℝ => (((gaussJetPoly t n).eval y * Real.exp (-(y ^ 2 / (4 * t))) : ℝ) : ℂ))
        ((((gaussJetPoly t (n + 1)).eval ξ * Real.exp (-(ξ ^ 2 / (4 * t))) : ℝ) : ℂ)) ξ :=
      hreal.ofReal_comp
    have hC := hcplx.const_mul (Complex.I ^ n * (Real.sqrt (Real.pi / t) : ℂ))
    have heq : (fun s : ℝ => gaussMoment t n s)
        = fun s : ℝ => Complex.I ^ n * (Real.sqrt (Real.pi / t) : ℂ)
            * (((gaussJetPoly t n).eval s * Real.exp (-(s ^ 2 / (4 * t))) : ℝ) : ℂ) := by
      funext s
      rw [hrec s, gaussKernel]
      push_cast
      ring
    rw [heq] at hderiv
    have huniq := hderiv.unique hC
    have hI : Complex.I * -Complex.I = 1 := by
      rw [mul_neg, Complex.I_mul_I, neg_neg]
    calc gaussMoment t (n + 1) ξ
        = Complex.I * (-Complex.I * gaussMoment t (n + 1) ξ) := by
          rw [← mul_assoc, hI, one_mul]
      _ = Complex.I * (Complex.I ^ n * (Real.sqrt (Real.pi / t) : ℂ)
            * (((gaussJetPoly t (n + 1)).eval ξ * Real.exp (-(ξ ^ 2 / (4 * t))) : ℝ) : ℂ)) := by
          rw [huniq]
      _ = Complex.I ^ (n + 1) * (Real.sqrt (Real.pi / t) : ℂ)
            * (((gaussJetPoly t (n + 1)).eval ξ : ℝ) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ) := by
          rw [gaussKernel]
          push_cast
          ring

/-! ## The transform of a polynomial times a Gaussian -/

/-- **(24.189) The exact Gaussian Fourier factorization.**  The transform of `p(x)e^{-tx²}` is the
Gaussian `√(π/t)e^{-ξ²/(4t)}` times an explicit polynomial in `ξ` built from the jet
polynomials. -/
theorem gaussPolyFourier {t : ℝ} (ht : 0 < t) (p : Polynomial ℝ) (ξ : ℝ) :
    (∫ x : ℝ, ((p.eval x : ℝ) : ℂ) * gaussPhase t ξ x)
      = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
        * ∑ n ∈ Finset.range (p.natDegree + 1),
            ((p.coeff n : ℝ) : ℂ) * Complex.I ^ n * (((gaussJetPoly t n).eval ξ : ℝ) : ℂ) := by
  have hsplit : ∀ x : ℝ, ((p.eval x : ℝ) : ℂ) * gaussPhase t ξ x
      = ∑ n ∈ Finset.range (p.natDegree + 1),
          ((p.coeff n : ℝ) : ℂ) * ((x : ℂ) ^ n * gaussPhase t ξ x) := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  calc (∫ x : ℝ, ((p.eval x : ℝ) : ℂ) * gaussPhase t ξ x)
      = ∫ x : ℝ, ∑ n ∈ Finset.range (p.natDegree + 1),
          ((p.coeff n : ℝ) : ℂ) * ((x : ℂ) ^ n * gaussPhase t ξ x) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = ∑ n ∈ Finset.range (p.natDegree + 1),
          ∫ x : ℝ, ((p.coeff n : ℝ) : ℂ) * ((x : ℂ) ^ n * gaussPhase t ξ x) :=
        MeasureTheory.integral_finsetSum _
          (fun n _ => (integrable_gaussMomentIntegrand ht n ξ).const_mul _)
    _ = ∑ n ∈ Finset.range (p.natDegree + 1), ((p.coeff n : ℝ) : ℂ) * gaussMoment t n ξ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [gaussMoment, MeasureTheory.integral_const_mul]
    _ = (Real.sqrt (Real.pi / t) : ℂ) * ((gaussKernel t ξ : ℝ) : ℂ)
          * ∑ n ∈ Finset.range (p.natDegree + 1),
              ((p.coeff n : ℝ) : ℂ) * Complex.I ^ n * (((gaussJetPoly t n).eval ξ : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [gaussMoment_eq ht n ξ]
        ring

end

end RHTower
