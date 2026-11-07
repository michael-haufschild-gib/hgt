import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinLawOfTheModularHorizon
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The KMS strip of the horizon

**`¼` is the midpoint of a KMS strip.** In the Mellin variable the functional equation is a KMS condition at inverse temperature `β = 1`: with
`G(z) = F(1 + i z)`, one has `G(z + i) = G(-z)` (`kms_condition`). The strip is `0 ≤ Re s ≤ 1`, and its reflection `z ↦ i - z` is `s ↦ 1 - s`
(`kms_reflection`), with the critical line as fixed line, at the height `β/2` (`kms_midpoint`). A mode of the horizon at `ρ` has the rate
`(1 - Re ρ)/2`, since the modular clock runs at speed `½`. So the partners of the reflection have rates summing to `½`, and `¼ = ½ · β/2` is exactly the
rate of the midpoint (`quarter_iff_midpoint`).

**KMS positivity holds and decides nothing.** The positivity of a KMS correlator at the midpoint is positive-definiteness of `τ ↦ F(½ + iτ)`. For
`ξ` this holds unconditionally: `ξ(½ + iτ)` is the Fourier transform of Riemann's kernel `Φ > 0` (`xi_kms_positive`). So a KMS state on the horizon
exists whether RH holds or not. And it does not force the line: for every `b > 0` the positive even kernel `e^{-x²}(e cosh b + cosh 2x)`
has a transform with the same KMS condition and the same positivity, whose zeros all have `Re s = ½ ± b` (`fake_horizon`). So the geometry of the
strip gives `¼` its meaning, and gives it no force. This is the modular counterpart of the fakes of the graph.
-/

open Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### The strip -/

/-- The correlator in the Mellin variable: `z = τ + i y` is the point `s = 1 + i τ - y` of the strip. -/
def kmsCorrelator (F : ℂ → ℂ) (z : ℂ) : ℂ := F (1 + I * z)

/-- **The functional equation is a KMS condition** at inverse temperature `1`. -/
theorem kms_condition {F : ℂ → ℂ} (hF : ∀ s, F (1 - s) = F s) (z : ℂ) :
    kmsCorrelator F (z + I) = kmsCorrelator F (-z) := by
  unfold kmsCorrelator
  have e1 : 1 + I * (z + I) = 1 - (1 - I * z) := by
    have : I * I = -1 := Complex.I_mul_I
    linear_combination this
  have e2 : 1 + I * -z = 1 - I * z := by ring
  rw [e1, e2, hF]

/-- The reflection of the strip is `s ↦ 1 - s`. -/
theorem kms_reflection {F : ℂ → ℂ} (hF : ∀ s, F (1 - s) = F s) (z : ℂ) :
    kmsCorrelator F (I - z) = kmsCorrelator F z := by
  have h := kms_condition hF (-z)
  rw [neg_neg, show -z + I = I - z by ring] at h
  exact h

/-- **The critical line is the midpoint of the strip.** At height `β/2` the correlator is the function on the line, and the reflection is
`τ ↦ -τ`. -/
theorem kms_midpoint {F : ℂ → ℂ} (hF : ∀ s, F (1 - s) = F s) (τ : ℝ) :
    kmsCorrelator F (τ + I / 2) = F (1 / 2 + I * τ) ∧
      kmsCorrelator F (-τ + I / 2) = kmsCorrelator F (τ + I / 2) := by
  have hI : I * I = -1 := Complex.I_mul_I
  have e : 1 + I * ((τ : ℂ) + I / 2) = 1 / 2 + I * τ := by
    linear_combination (1 / 2 : ℂ) * hI
  refine ⟨by unfold kmsCorrelator; rw [e], ?_⟩
  have h := kms_reflection hF ((τ : ℂ) + I / 2)
  rw [show I - ((τ : ℂ) + I / 2) = -τ + I / 2 by ring] at h
  exact h

/-- **`¼` is the rate of the midpoint.** A mode has rate `(1 - Re ρ)/2`, the reflection sends `r` to `½ - r`, and the fixed rate `¼` is the line. -/
theorem quarter_iff_midpoint (ρ : ℂ) :
    ((1 - ρ.re) / 2 + (1 - (1 - ρ).re) / 2 = 1 / 2) ∧ ((1 - ρ.re) / 2 = 1 / 4 ↔ ρ.re = 1 / 2) := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]
    ring
  · constructor <;> intro h <;> linarith

/-! ### Positivity from a positive kernel -/

/-- **A positive kernel gives KMS positivity.** The Gram matrix of `τ ↦ ∫ e^{iτx} Φ(x) dx` is `∫ Φ |Σ z_j e^{iτ_j x}|²`. -/
theorem kernel_positive {Φ : ℝ → ℝ} (hΦ : ∀ x, 0 ≤ Φ x)
    (hint : ∀ τ : ℝ, Integrable fun x : ℝ => Complex.exp (I * τ * x) * (Φ x : ℂ)) {n : ℕ}
    (τ : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, z j * conj (z k) * ∫ x : ℝ, Complex.exp (I * ((τ j - τ k : ℝ) : ℂ) * x) * (Φ x : ℂ) := by
  set S : ℝ → ℂ := fun x => ∑ j, z j * Complex.exp (I * τ j * x) with hS
  have hpoint (x : ℝ) : ∑ j, ∑ k, z j * conj (z k) *
      (Complex.exp (I * ((τ j - τ k : ℝ) : ℂ) * x) * (Φ x : ℂ)) =
      ((Φ x * Complex.normSq (S x) : ℝ) : ℂ) := by
    have hconj : conj (S x) = ∑ k, conj (z k) * Complex.exp (-(I * τ k * x)) := by
      simp only [hS, map_sum, map_mul, ← Complex.exp_conj]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      simp
    have hsq : ((Complex.normSq (S x) : ℝ) : ℂ) = S x * conj (S x) := (Complex.mul_conj _).symm
    push_cast
    rw [hsq, hconj]
    simp only [hS]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have he : Complex.exp (I * ((τ j : ℂ) - τ k) * x) =
        Complex.exp (I * τ j * x) * Complex.exp (-(I * τ k * x)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hrow (j k : Fin n) : Integrable fun x : ℝ => z j * conj (z k) *
      (Complex.exp (I * ((τ j - τ k : ℝ) : ℂ) * x) * (Φ x : ℂ)) :=
    (hint (τ j - τ k)).const_mul _
  have hswap : ∑ j, ∑ k, z j * conj (z k) *
      ∫ x : ℝ, Complex.exp (I * ((τ j - τ k : ℝ) : ℂ) * x) * (Φ x : ℂ) =
      ∫ x : ℝ, ((Φ x * Complex.normSq (S x) : ℝ) : ℂ) := by
    simp only [← hpoint]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hrow j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hrow j k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
  rw [hswap, integral_complex_ofReal]
  exact Complex.zero_le_real.mpr
    (integral_nonneg fun x => mul_nonneg (hΦ x) (Complex.normSq_nonneg _))

/-! ### The KMS state of `ξ` -/

open _root_.RHTower in
/-- **The horizon has a KMS state, whether RH holds or not.** The correlator `τ ↦ ξ(½ + iτ)` is positive definite, since Riemann's kernel is
positive. -/
theorem xi_kms_positive {n : ℕ} (τ : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, z j * conj (z k) * xi (1 / 2 + I * ((τ j - τ k : ℝ) : ℂ)) := by
  have hint (t : ℝ) : Integrable fun x : ℝ =>
      Complex.exp (I * t * x) * ((riemannKernelReal x : ℝ) : ℂ) := by
    have h := integrable_riemannPhiKernel_mul_exp (t : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show riemannPhiKernel x * _ = _
    rw [riemannPhiKernel_eq_ofReal]
    ring
  have h := kernel_positive (fun x => (riemannKernelReal_pos x).le) hint τ z
  convert h using 4 with j _ k _
  rw [← riemannPhiTransform_eq_xi]
  unfold riemannPhiTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ * riemannPhiKernel x = _
  rw [riemannPhiKernel_eq_ofReal]
  congr 2
  ring

open _root_.RHTower in
/-- `ξ` has the KMS condition. -/
theorem xi_kms_condition (z : ℂ) : kmsCorrelator xi (z + I) = kmsCorrelator xi (-z) :=
  kms_condition xi_one_sub z

/-! ### A fake horizon -/

/-- A positive even kernel. -/
def fakeKernel (b x : ℝ) : ℝ := Real.exp (-x ^ 2) * (Real.exp 1 * Real.cosh b + Real.cosh (2 * x))

/-- Its transform, in closed form. -/
def fakeXi (b : ℝ) (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp ((s - 1 / 2) ^ 2 / 4) * Complex.exp 1 *
    (Complex.cosh b + Complex.cosh (s - 1 / 2))

theorem fakeKernel_pos (b x : ℝ) : 0 < fakeKernel b x := by
  unfold fakeKernel
  have := Real.cosh_pos b
  have h2 := Real.cosh_pos (2 * x)
  have h3 := Real.exp_pos 1
  positivity

theorem fakeKernel_neg (b x : ℝ) : fakeKernel b (-x) = fakeKernel b x := by
  unfold fakeKernel
  rw [show 2 * -x = -(2 * x) by ring, Real.cosh_neg]
  ring_nf

theorem fakeXi_one_sub (b : ℝ) (s : ℂ) : fakeXi b (1 - s) = fakeXi b s := by
  unfold fakeXi
  rw [show 1 - s - 1 / 2 = -(s - 1 / 2) by ring, Complex.cosh_neg]
  ring_nf

/-- The kernel as a sum of three Gaussians. -/
theorem fakeKernel_expand (b x : ℝ) (w : ℂ) :
    Complex.exp (w * x) * (fakeKernel b x : ℂ) =
      (Real.exp 1 * Real.cosh b : ℝ) * Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0) +
        (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w + 2) * x + 0) +
        (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w - 2) * x + 0) := by
  unfold fakeKernel
  push_cast
  have hc : Complex.cosh (2 * (x : ℂ)) = (Complex.exp (2 * x) + Complex.exp (-(2 * x))) / 2 := rfl
  rw [hc, show (w + 2) * (x : ℂ) = w * x + 2 * x by ring,
    show (w - 2) * (x : ℂ) = w * x + -(2 * x) by ring]
  have e1 : Complex.exp (-1 * (x : ℂ) ^ 2 + (w * x + 2 * x) + 0) =
      Complex.exp (w * x) * Complex.exp (-(x : ℂ) ^ 2) * Complex.exp (2 * x) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp (-1 * (x : ℂ) ^ 2 + (w * x + -(2 * x)) + 0) =
      Complex.exp (w * x) * Complex.exp (-(x : ℂ) ^ 2) * Complex.exp (-(2 * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e3 : Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0) =
      Complex.exp (w * x) * Complex.exp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [e1, e2, e3]
  ring

theorem integrable_gauss (c : ℂ) :
    Integrable fun x : ℝ => Complex.exp (-1 * (x : ℂ) ^ 2 + c * x + 0) :=
  integrable_cexp_quadratic (b := 1) (by simp) c 0

/-- `∫ e^{c x} e^{-x²} dx = √π e^{c²/4}`. -/
theorem integral_gauss (c : ℂ) :
    ∫ x : ℝ, Complex.exp (-1 * (x : ℂ) ^ 2 + c * x + 0) =
      (Real.sqrt Real.pi : ℂ) * Complex.exp (c ^ 2 / 4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) c 0
  rw [h]
  have e : (0 : ℂ) - c ^ 2 / (4 * -1) = c ^ 2 / 4 := by ring
  rw [e]
  congr 1
  rw [show ((Real.pi : ℂ) / -(-1 : ℂ)) = (Real.pi : ℂ) by simp, Real.sqrt_eq_rpow,
    Complex.ofReal_cpow Real.pi_pos.le]
  norm_num

/-- The transform of the fake kernel is `fakeXi`. -/
theorem fakeXi_eq_integral (b : ℝ) (s : ℂ) :
    ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) * (fakeKernel b x : ℂ) = fakeXi b s := by
  set w := s - 1 / 2 with hw
  simp only [fakeKernel_expand]
  set A : ℂ := ((Real.exp 1 * Real.cosh b : ℝ) : ℂ) with hA
  have i1 := (integrable_gauss w).const_mul A
  have i2 := (integrable_gauss (w + 2)).const_mul (1 / 2 : ℂ)
  have i3 := (integrable_gauss (w - 2)).const_mul (1 / 2 : ℂ)
  have a1 : ∫ x : ℝ, (A * Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0) +
      (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w + 2) * x + 0)) +
      (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w - 2) * x + 0) =
      (∫ x : ℝ, (A * Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0) +
        (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w + 2) * x + 0))) +
      ∫ x : ℝ, (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w - 2) * x + 0) :=
    integral_add (i1.add i2) i3
  have a2 : ∫ x : ℝ, (A * Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0) +
      (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w + 2) * x + 0)) =
      (∫ x : ℝ, A * Complex.exp (-1 * (x : ℂ) ^ 2 + w * x + 0)) +
      ∫ x : ℝ, (1 / 2 : ℂ) * Complex.exp (-1 * (x : ℂ) ^ 2 + (w + 2) * x + 0) :=
    integral_add i1 i2
  rw [a1, a2, integral_const_mul, integral_const_mul, integral_const_mul, integral_gauss,
    integral_gauss, integral_gauss, hA]
  unfold fakeXi
  rw [← hw]
  have e1 : Complex.exp ((w + 2) ^ 2 / 4) = Complex.exp (w ^ 2 / 4) * Complex.exp 1 * Complex.exp w := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp ((w - 2) ^ 2 / 4) = Complex.exp (w ^ 2 / 4) * Complex.exp 1 * Complex.exp (-w) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hcw : Complex.cosh w = (Complex.exp w + Complex.exp (-w)) / 2 := rfl
  rw [e1, e2, hcw]
  push_cast
  ring

/-- The transform of the fake kernel on the line is integrable against every exponential. -/
theorem integrable_fakeKernel (b t : ℝ) :
    Integrable fun x : ℝ => Complex.exp (I * t * x) * (fakeKernel b x : ℂ) := by
  simp only [fakeKernel_expand]
  exact (((integrable_gauss _).const_mul _).add ((integrable_gauss _).const_mul _)).add
    ((integrable_gauss _).const_mul _)

/-- `cosh (u + i v) = cosh u cos v + i sinh u sin v`. -/
theorem cosh_re_im (u v : ℝ) :
    Complex.cosh ((u : ℂ) + (v : ℂ) * I) =
      ((Real.cosh u * Real.cos v : ℝ) : ℂ) + ((Real.sinh u * Real.sin v : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  ring

/-- **All zeros of the fake lie at distance `b` from the line.** -/
theorem fakeXi_zero_off_line {b : ℝ} (hb : 0 < b) {s : ℂ} (h : fakeXi b s = 0) :
    |(s - 1 / 2).re| = b := by
  unfold fakeXi at h
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h0 : Complex.cosh b + Complex.cosh (s - 1 / 2) = 0 := by
    simpa [hpi, Complex.exp_ne_zero] using h
  set w := s - 1 / 2 with hw
  have hdec : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  rw [hdec, cosh_re_im, ← Complex.ofReal_cosh] at h0
  have hre : Real.cosh b + Real.cosh w.re * Real.cos w.im = 0 := by
    have := congrArg Complex.re h0
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul, sub_zero, add_zero] using this
  have him : Real.sinh w.re * Real.sin w.im = 0 := by
    have := congrArg Complex.im h0
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.zero_im, mul_zero, zero_mul, zero_add, add_zero, mul_one] using this
  have hcb : 1 < Real.cosh b := Real.one_lt_cosh.mpr hb.ne'
  rcases mul_eq_zero.mp him with hs | hs
  · -- `w.re = 0` is impossible
    have hu : w.re = 0 := Real.sinh_eq_zero.mp hs
    rw [hu, Real.cosh_zero, one_mul] at hre
    linarith [Real.neg_one_le_cos w.im]
  · have hc : Real.cos w.im ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq w.im
      rw [hs] at this
      linarith
    have hcu := Real.cosh_pos w.re
    have hcos : Real.cos w.im = -1 := by
      have hf : (Real.cos w.im - 1) * (Real.cos w.im + 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp hf with h1 | h1
      · have h2 : Real.cos w.im = 1 := by linarith
        rw [h2] at hre
        linarith
      · linarith
    rw [hcos] at hre
    have heq : Real.cosh w.re = Real.cosh b := by linarith
    have h1 := Real.cosh_le_cosh.mp heq.le
    have h2 := Real.cosh_le_cosh.mp heq.ge
    rw [abs_of_pos hb] at h1 h2
    linarith

/-- **A fake modular horizon.** For every `b > 0` there is a positive even kernel, decaying like a Gaussian, whose transform has the KMS condition and KMS
positivity, has no zero on the line, and has a zero at distance `b` from it, all its zeros being at that distance. So KMS, reflection symmetry and positivity of
the kernel do not place the zeros. -/
theorem fake_horizon {b : ℝ} (hb : 0 < b) :
    (∀ x, 0 < fakeKernel b x) ∧ (∀ x, fakeKernel b (-x) = fakeKernel b x) ∧
      (∀ z, kmsCorrelator (fakeXi b) (z + I) = kmsCorrelator (fakeXi b) (-z)) ∧
      (∀ {n : ℕ} (τ : Fin n → ℝ) (z : Fin n → ℂ),
        0 ≤ ∑ j, ∑ k, z j * conj (z k) * fakeXi b (1 / 2 + I * ((τ j - τ k : ℝ) : ℂ))) ∧
      (∀ τ : ℝ, fakeXi b (1 / 2 + I * τ) ≠ 0) ∧
      fakeXi b (1 / 2 + b + Real.pi * I) = 0 ∧
      (∀ s, fakeXi b s = 0 → |(s - 1 / 2).re| = b) := by
  refine ⟨fakeKernel_pos b, fakeKernel_neg b, kms_condition (fakeXi_one_sub b), ?_, ?_, ?_,
    fun s hs => fakeXi_zero_off_line hb hs⟩
  · intro n τ z
    have h := kernel_positive (fun x => (fakeKernel_pos b x).le) (integrable_fakeKernel b) τ z
    convert h using 4 with j _ k _
    rw [← fakeXi_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Complex.exp _ * _ = Complex.exp _ * _
    congr 2
    ring
  · intro τ h0
    have h := fakeXi_zero_off_line hb h0
    simp at h
    linarith [hb]
  · unfold fakeXi
    have e : 1 / 2 + (b : ℂ) + Real.pi * I - 1 / 2 = (b : ℂ) + (Real.pi : ℝ) * I := by
      ring
    rw [e, cosh_re_im, ← Complex.ofReal_cosh]
    simp

end GaloisForLFunctions.ArithmeticScatteringHolography

end
