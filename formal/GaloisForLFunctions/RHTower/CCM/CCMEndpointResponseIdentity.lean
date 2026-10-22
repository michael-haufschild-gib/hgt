import GaloisForLFunctions.RHTower.SlepianKernelFourier
import GaloisForLFunctions.HTGeometry.HellmannFeynman

/-!
# The endpoint-response identity of the constrained CCM layer

The exact endpoint response `d/dc log nu_m(c) = 2 |psi(1)|²/c` of a simple prolate branch rests on three
steps.  The first is the Hellmann–Feynman derivative of the sinc kernel, whose `c`-derivative is the *smooth*
kernel `cos(c(x-y))/pi` — no removable singularity is involved.  The second is the factorisation

```text
int int psi(x) psi(y) cos(c(x-y)) dx dy = |int psi(x) exp(i c x) dx|²,
```

which is the content of the card's `(7)`: the double integral of the cosine kernel against a real function is
the squared modulus of its finite Fourier transform.  The third is the finite-Fourier eigenrelation, which
converts that squared modulus into `|mu|² |psi(1)|²`, and the operator identity
`Q_c = (c/2 pi) F_c^* F_c`, which gives `|mu|² = 2 pi nu/c`.

This file proves the second and third steps unconditionally, and assembles the identity from the first one
taken as a hypothesis on the branch (the derivative of an eigenvalue branch is exactly what a Hellmann–Feynman
statement provides).
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.RHTower

/-! ## The finite Fourier transform of a real function on the band -/

/-- The finite Fourier transform at frequency `c`, on the band `[-1, 1]`. -/
def bandFourier (c : ℝ) (ψ : ℝ → ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))

theorem intervalIntegrable_bandFourier_integrand (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    IntervalIntegrable (fun x : ℝ => (ψ x : ℂ) * Complex.exp (Complex.I * (c * x)))
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- The conjugate of the band transform is the transform at the opposite frequency. -/
theorem conj_bandFourier (c : ℝ) {ψ : ℝ → ℝ} (_hψ : Continuous ψ) :
    (starRingEnd ℂ) (bandFourier c ψ)
      = ∫ y in (-1 : ℝ)..1, (ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))) := by
  rw [bandFourier, ← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr ?_
  intro y _
  show (starRingEnd ℂ) ((ψ y : ℂ) * Complex.exp (Complex.I * ((c : ℂ) * (y : ℂ))))
      = (ψ y : ℂ) * Complex.exp (-(Complex.I * ((c : ℂ) * (y : ℂ))))
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_I]

/-- **The cosine factorisation, equation `(7)`.**  The double integral of the cosine kernel against a real
continuous function is the squared modulus of its finite Fourier transform.  No Fubini theorem is needed: the
product of the two single integrals is the double integral because each factor is constant for the other
variable. -/
theorem double_integral_cos_eq_norm_sq (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = ‖bandFourier c ψ‖ ^ (2 : ℕ) := by
  -- the product of the two transforms is the double integral of the complex kernel
  have hprod : bandFourier c ψ * (starRingEnd ℂ) (bandFourier c ψ)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))) := by
    rw [conj_bandFourier c hψ, bandFourier, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr ?_
    intro x _
    show (ψ x : ℂ) * Complex.exp (Complex.I * ((c : ℂ) * (x : ℂ)))
        * (∫ y in (-1 : ℝ)..1, (ψ y : ℂ) * Complex.exp (-(Complex.I * ((c : ℂ) * (y : ℂ)))))
      = ∫ y in (-1 : ℝ)..1, ((ψ x * ψ y : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ))))
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro y _
    show (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
        * ((ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))))
      = ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))
    rw [show Complex.I * (c * ((x : ℂ) - y)) = Complex.I * (c * x) + -(Complex.I * (c * y)) by
      ring, Complex.exp_add]
    push_cast
    ring
  -- the real part of the double integral is the double integral of the cosine kernel
  have hinner : ∀ x : ℝ, (∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = (∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))).re := by
    intro x
    have hint : IntervalIntegrable (fun y : ℝ =>
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) volume (-1) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.intervalIntegral_re (f := fun y : ℝ =>
      ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
      (a := -1) (b := 1) (μ := volume) hint
    have hcongr : (∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
        = ∫ y in (-1 : ℝ)..1, RCLike.re
          (((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) := by
      refine intervalIntegral.integral_congr ?_
      intro y _
      show ψ x * ψ y * Real.cos (c * (x - y))
        = RCLike.re (((ψ x * ψ y : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ)))))
      have hcast : Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ)))
          = ((c * (x - y) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hre : RCLike.re (((ψ x * ψ y : ℝ) : ℂ)
            * Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I))
          = (((ψ x * ψ y : ℝ) : ℂ)
            * Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I)).re := rfl
      rw [hcast, hre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    rw [hcongr, h]
    rfl
  have houter : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))).re := by
    have hint : IntervalIntegrable (fun x : ℝ => ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) volume (-1) 1 := by
      have hcongr : (fun x : ℝ => ∫ y in (-1 : ℝ)..1,
          ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
          = fun x : ℝ => (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
            * ((starRingEnd ℂ) (bandFourier c ψ)) := by
        funext x
        rw [conj_bandFourier c hψ, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr ?_
        intro y _
        show ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))
          = (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
            * ((ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))))
        rw [show Complex.I * (c * ((x : ℂ) - y)) = Complex.I * (c * x) + -(Complex.I * (c * y)) by
          ring, Complex.exp_add]
        push_cast
        ring
      rw [hcongr]
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.intervalIntegral_re (f := fun x : ℝ => ∫ y in (-1 : ℝ)..1,
      ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
      (a := -1) (b := 1) (μ := volume) hint
    have hcongr2 : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
        = ∫ x in (-1 : ℝ)..1, RCLike.re (∫ y in (-1 : ℝ)..1,
          ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact hinner x
    rw [hcongr2, h]
    rfl
  rw [houter, ← hprod, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]


/-! ## The endpoint-response identity

Given the two branch inputs — the Hellmann–Feynman derivative and the finite-Fourier eigenrelation — the
identity `(4)` is arithmetic.  The cosine factorisation turns the derivative into `|mu|² |psi(1)|²/pi`, and the
operator identity `(6)` turns `|mu|²` into `2 pi nu/c`. -/

/-- **The exact endpoint response, equation `(4)`.**  If

* `nup = (1/pi) int int psi(x) psi(y) cos(c(x-y))` — the Hellmann–Feynman derivative of the band operator,
  whose kernel derivative is the smooth kernel `cos(c(x-y))/pi`;
* `bandFourier c psi = mu * psi 1` — the finite-Fourier eigenrelation evaluated at the band edge;
* `nu = (c/(2 pi)) ‖mu‖²` — the operator identity `Q_c = (c/2 pi) F_c^* F_c` on a normalized eigenfunction;

then

```text
nup = 2 nu |psi 1|² / c.
```

Every step is an identity; no estimate and no asymptotics enter. -/
theorem endpointResponse_eq {c nup nu : ℝ} {μ : ℂ} {ψ : ℝ → ℝ} (hc : c ≠ 0)
    (hψ : Continuous ψ)
    (hHF : nup = (1 / Real.pi)
      * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
    (hFF : bandFourier c ψ = μ * (ψ 1 : ℂ))
    (hnu : nu = c / (2 * Real.pi) * ‖μ‖ ^ (2 : ℕ)) :
    nup = 2 * nu * ψ 1 ^ (2 : ℕ) / c := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfact := double_integral_cos_eq_norm_sq c hψ
  have hnorm : ‖bandFourier c ψ‖ ^ (2 : ℕ) = ‖μ‖ ^ (2 : ℕ) * ψ 1 ^ (2 : ℕ) := by
    rw [hFF, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hHF, hfact, hnorm, hnu]
  field_simp

/-- The gap `d(λ) = 1 - nu(2 pi λ²)` in the CCM normalisation, differentiated. -/
theorem hasDerivAt_ccmGap {ν : ℝ → ℝ} {νp lam : ℝ}
    (hν : HasDerivAt ν νp (2 * Real.pi * lam ^ (2 : ℕ))) :
    HasDerivAt (fun t : ℝ => 1 - ν (2 * Real.pi * t ^ (2 : ℕ)))
      (-(νp * (4 * Real.pi * lam))) lam := by
  have hinner : HasDerivAt (fun t : ℝ => 2 * Real.pi * t ^ (2 : ℕ)) (4 * Real.pi * lam) lam := by
    have h := (hasDerivAt_pow 2 lam).const_mul (2 * Real.pi)
    have hval : 2 * Real.pi * ((2 : ℕ) * lam ^ (2 - 1 : ℕ)) = 4 * Real.pi * lam := by
      norm_num
      ring
    rw [hval] at h
    exact h
  have h := (hν.comp lam hinner).const_sub 1
  exact h

/-- **The scaled endpoint response, equation `(5)`.**  In the CCM variable `c = 2 pi λ²`, with
`|e_(m,λ)(λ)|² = |psi(1)|²/λ` and `d = 1 - nu`, the identity `(4)` becomes

```text
|e_(m,λ)(λ)|² = -d'(λ) / (4 (1 - d(λ))).
```

The right-hand side is written out with `d'(λ) = -nup · 4 pi λ` from the chain rule and `1 - d = nu`. -/
theorem endpointResponse_scaled {nu nup p lam : ℝ} (hlam : 0 < lam) (hnu : 0 < nu)
    (h4 : nup = 2 * nu * p / (2 * Real.pi * lam ^ (2 : ℕ))) :
    p / lam = nup * (4 * Real.pi * lam) / (4 * nu) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [h4]
  field_simp



/-! ## The identity from the Hellmann–Feynman package

Composing the abstract Hellmann–Feynman lemma with the factorisation makes the chain of `(4)` explicit: the
only inputs left are the identification of the expectation `⟪psi, w⟫` with the double integral of the kernel
derivative, the finite-Fourier eigenrelation, and the operator identity `(6)`. -/

/-- **Equation `(4)` from the Hellmann–Feynman package.**  The eigenvalue derivative of a normalized
differentiable branch of the band operator equals `2 nu |psi(1)|²/c`, given

* the Hellmann–Feynman data for the family (`hnorm`, `hsa`, the two derivatives, the eigenrelation);
* `hexp`: the expectation of the family's derivative is the double integral of the cosine kernel, which is
  what the `c`-derivative of the sinc kernel `sin(c(x-y))/(pi(x-y))` is;
* `hFF`: the finite-Fourier eigenrelation at the band edge;
* `hnu`: the operator identity `Q_c = (c/2 pi) F_c^* F_c` on a normalized eigenfunction.
-/
theorem endpointResponse_of_hellmannFeynman {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {Ψ : ℝ → E} {Ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ} {w : E} {c : ℝ}
    {μ : ℂ} {ψ : ℝ → ℝ} (hc : c ≠ 0) (hψ : Continuous ψ)
    (hnorm : (inner ℝ (Ψ c) (Ψ c) : ℝ) = 1)
    (hsa : (inner ℝ (Ψ c) (A c Ψ') : ℝ) = (inner ℝ (A c (Ψ c)) Ψ' : ℝ))
    (hν : HasDerivAt ν νp c)
    (hΨ : HasDerivAt Ψ Ψ' c)
    (hAΨ : HasDerivAt (fun t => A t (Ψ t)) (w + A c Ψ') c)
    (hrel : ∀ t, A t (Ψ t) = ν t • Ψ t)
    (hexp : (inner ℝ (Ψ c) w : ℝ) = (1 / Real.pi)
      * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
    (hFF : bandFourier c ψ = μ * (ψ 1 : ℂ))
    (hnuval : ν c = c / (2 * Real.pi) * ‖μ‖ ^ (2 : ℕ)) :
    νp = 2 * ν c * ψ 1 ^ (2 : ℕ) / c := by
  have hHF := GaloisForLFunctions.HTGeometry.hellmann_feynman hnorm hsa hν hΨ hAΨ hrel
  have hderiv : νp = (1 / Real.pi)
      * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)) := by
    rw [hHF, hexp]
  exact endpointResponse_eq hc hψ hderiv hFF hnuval



/-! ## The expectation of the kernel derivative

The `c`-derivative of the sinc kernel is `cos(c(x-y))/pi`, and the expectation of an integral operator in the
integral realisation of the inner product is the iterated integral of its kernel.  So the `hexp` input of the
composition above is an identity for the concrete operator: no Fubini theorem is needed, because the iterated
order is kept and only the outer factor is pulled inside. -/

/-- The expectation of the cosine-kernel operator is the double integral of `(7)`. -/
theorem expectation_cosKernel_eq (c : ℝ) (ψ : ℝ → ℝ) :
    (∫ x in (-1 : ℝ)..1, ψ x
        * ∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y)) / Real.pi * ψ y)
      = (1 / Real.pi)
        * ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro x _
  show ψ x * ∫ y in (-1 : ℝ)..1, Real.cos (c * (x - y)) / Real.pi * ψ y
    = (1 / Real.pi) * ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y))
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro y _
  show ψ x * (Real.cos (c * (x - y)) / Real.pi * ψ y)
    = (1 / Real.pi) * (ψ x * ψ y * Real.cos (c * (x - y)))
  ring



/-! ## Differentiability of the sinc family in the aperture

The Hellmann–Feynman input needs the family's own derivative.  At kernel level that derivative is uniform:
the sinc kernel is *entire* in `c` and its second `c`-derivative is bounded by `|u|/pi` on the band, so the
first-order Taylor error is `O(h²)` *uniformly in the kernel variables*.  Since the band is compact, that is
exactly what makes the operator family differentiable in the Hilbert–Schmidt norm, with derivative the
cosine-kernel operator. -/

/-- The second-order Taylor bound for the sine: `|sin(a+b) - sin a - b cos a| <= b²`.  The mean value
inequality applied to `t ↦ sin(a+t) - sin a - t cos a`, whose derivative `cos(a+t) - cos a` is bounded by
`|t|`. -/
theorem abs_sin_add_sub_taylor_le (a b : ℝ) :
    |Real.sin (a + b) - Real.sin a - b * Real.cos a| ≤ b ^ (2 : ℕ) := by
  set g : ℝ → ℝ := fun t => Real.sin (a + t) - Real.sin a - t * Real.cos a with hg
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) b,
      HasDerivWithinAt g (Real.cos (a + t) - Real.cos a) (Set.uIcc (0 : ℝ) b) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => Real.sin (a + u)) (Real.cos (a + t)) t := by
      have hf : HasDerivAt (fun u : ℝ => a + u) 1 t := by
        simpa using (hasDerivAt_id t).const_add a
      simpa using hf.sin
    have h2 : HasDerivAt (fun u : ℝ => u * Real.cos a) (Real.cos a) t := by
      simpa using (hasDerivAt_id t).mul_const (Real.cos a)
    have h := (h1.sub_const (Real.sin a)).sub h2
    exact h.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) b, ‖Real.cos (a + t) - Real.cos a‖ ≤ |b| := by
    intro t ht
    have h1 : |Real.cos (a + t) - Real.cos a| ≤ |a + t - a| := Real.abs_cos_sub_cos_le _ _
    have h2 : |a + t - a| = |t| := by
      congr 1
      ring
    have h3 : |t| ≤ |b| := by
      rcases le_or_gt 0 b with hb | hb
      · rw [Set.uIcc_of_le hb] at ht
        rw [abs_of_nonneg hb, abs_of_nonneg ht.1]
        exact ht.2
      · rw [Set.uIcc_of_ge hb.le] at ht
        rw [abs_of_neg hb, abs_of_nonpos ht.2]
        linarith [ht.1]
    rw [Real.norm_eq_abs]
    linarith [h1, h2.le, h2.ge, h3]
  have h := (convex_uIcc (0 : ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hg0 : g 0 = 0 := by
    rw [hg]
    simp
  rw [hg0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
  calc |Real.sin (a + b) - Real.sin a - b * Real.cos a| = |g b| := by rw [hg]
    _ ≤ |b| * |b| := h
    _ = b ^ (2 : ℕ) := by
        rw [← abs_mul, ← sq, abs_sq]

/-- **The sinc kernel is differentiable in the aperture, uniformly.**  The first-order Taylor error of
`c ↦ sincSmooth c u` is at most `h² |u|/pi`, for every kernel variable `u`; the derivative is
`cos(c u)/pi`, which is the kernel whose expectation `(7)` computes. -/
theorem abs_sincSmooth_taylor_le (c h u : ℝ) :
    |_root_.RHTower.sincSmooth (c + h) u - _root_.RHTower.sincSmooth c u
        - h * (Real.cos (c * u) / Real.pi)|
      ≤ h ^ (2 : ℕ) * |u| / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    have hzero : (c + h) / Real.pi - c / Real.pi - h * (Real.cos (c * 0) / Real.pi) = 0 := by
      rw [mul_zero, Real.cos_zero]
      field_simp
      ring
    rw [_root_.RHTower.sincSmooth_zero, _root_.RHTower.sincSmooth_zero, hzero]
    simp
  · rw [_root_.RHTower.sincSmooth_eq_off hu, _root_.RHTower.sincSmooth_eq_off hu,
      _root_.RHTower.sincScalar, _root_.RHTower.sincScalar]
    have hune : |u| ≠ 0 := abs_ne_zero.mpr hu
    have hupos : 0 < |u| := abs_pos.mpr hu
    have hsin := abs_sin_add_sub_taylor_le (c * u) (h * u)
    have hval : Real.sin ((c + h) * u) / (Real.pi * u) - Real.sin (c * u) / (Real.pi * u)
        - h * (Real.cos (c * u) / Real.pi)
        = (Real.sin (c * u + h * u) - Real.sin (c * u) - h * u * Real.cos (c * u))
          / (Real.pi * u) := by
      rw [show (c + h) * u = c * u + h * u from by ring]
      field_simp
    rw [hval, abs_div, abs_mul, abs_of_pos hpi]
    rw [div_le_div_iff₀ (by positivity) hpi]
    have hstep : |Real.sin (c * u + h * u) - Real.sin (c * u) - h * u * Real.cos (c * u)|
        ≤ (h * u) ^ (2 : ℕ) := hsin
    have hexp : (h * u) ^ (2 : ℕ) = h ^ (2 : ℕ) * |u| * |u| := by
      rw [mul_pow, mul_assoc, abs_mul_abs_self, ← sq]
    nlinarith [hstep, hexp, hupos, hpi]


end GaloisForLFunctions.RHTower

end
