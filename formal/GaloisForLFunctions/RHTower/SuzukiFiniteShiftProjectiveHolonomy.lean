import GaloisForLFunctions.RHTower.SuzukiFiniteShiftNonClock

/-!
# Suzuki's flat finite-shift projective holonomy

For a fixed Suzuki aperture, write `F_r` for the Fourier transform of the shifted resolvent
source `(A + r)⁻¹ eˣ`.  The second resolvent identity gives an exact finite update

`F_s = F_r + (r - s) J_{s,r}`.

This module extracts its dependency-closed projective content.  The reflected cross ratio

`H(F₁,F₀;z) = F₁(z)F₀(-z) / (F₁(-z)F₀(z))`

transports the complete Fourier--Livšic carrier from `F₀` to `F₁`.  It is a flat cocycle: every
intermediate source cancels exactly.  Substituting the finite resolvent update gives a branch-free
nonlinear response in terms of the reflected two-resolvent determinant already used for Suzuki's
free-boundary tangent.

On paper this says that finite shift integration and prime-activation ordering disappear after
projectivization.  The remaining RH problem is cofinal control of one endpoint transport, not
summation of perturbative remainders.  No RH assumption and no numerical computation occur here.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Endpoint projective transport -/

/-- Reflected cross-ratio transport from source transform `F₀` to source transform `F₁`. -/
def suzukiProjectiveSourceTransport (F₁ F₀ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F₁ z * F₀ (-z)) / (F₁ (-z) * F₀ z)

/-- The transport from a nonvanishing source value to itself is the identity. -/
@[simp] theorem suzukiProjectiveSourceTransport_self
    {F : ℂ → ℂ} {z : ℂ} (hFz : F z ≠ 0) (hFneg : F (-z) ≠ 0) :
    suzukiProjectiveSourceTransport F F z = 1 := by
  rw [suzukiProjectiveSourceTransport]
  field_simp [hFz, hFneg]

/-- **Flat cocycle law.** Every intermediate source cancels from projective transport. -/
theorem suzukiProjectiveSourceTransport_comp
    {F₂ F₁ F₀ : ℂ → ℂ} {z : ℂ}
    (hF₂z : F₂ z ≠ 0) (hF₂neg : F₂ (-z) ≠ 0)
    (hF₁z : F₁ z ≠ 0) (hF₁neg : F₁ (-z) ≠ 0)
    (hF₀z : F₀ z ≠ 0) (hF₀neg : F₀ (-z) ≠ 0) :
    suzukiProjectiveSourceTransport F₂ F₀ z =
      suzukiProjectiveSourceTransport F₂ F₁ z *
        suzukiProjectiveSourceTransport F₁ F₀ z := by
  rw [suzukiProjectiveSourceTransport, suzukiProjectiveSourceTransport,
    suzukiProjectiveSourceTransport]
  field_simp [hF₂z, hF₂neg, hF₁z, hF₁neg, hF₀z, hF₀neg]

/-- Two different finite paths with the same endpoints have the same projective holonomy. -/
theorem suzukiProjectiveSourceTransport_path_independent
    {F₂ F₁ G₁ F₀ : ℂ → ℂ} {z : ℂ}
    (hF₂z : F₂ z ≠ 0) (hF₂neg : F₂ (-z) ≠ 0)
    (hF₁z : F₁ z ≠ 0) (hF₁neg : F₁ (-z) ≠ 0)
    (hG₁z : G₁ z ≠ 0) (hG₁neg : G₁ (-z) ≠ 0)
    (hF₀z : F₀ z ≠ 0) (hF₀neg : F₀ (-z) ≠ 0) :
    suzukiProjectiveSourceTransport F₂ F₁ z *
        suzukiProjectiveSourceTransport F₁ F₀ z =
      suzukiProjectiveSourceTransport F₂ G₁ z *
        suzukiProjectiveSourceTransport G₁ F₀ z := by
  rw [← suzukiProjectiveSourceTransport_comp hF₂z hF₂neg hF₁z hF₁neg hF₀z hF₀neg,
    ← suzukiProjectiveSourceTransport_comp hF₂z hF₂neg hG₁z hG₁neg hF₀z hF₀neg]

/-! ## Exact finite resolvent update -/

/-- Abstract transform form of the second-resolvent update `F_s = F_r + δ J_{s,r}`. -/
def suzukiFiniteShiftSource (F J : ℂ → ℂ) (δ : ℂ) (z : ℂ) : ℂ :=
  F z + δ * J z

/-- The cross determinant of a finite update is exactly the shift times the reflected tangent
numerator.  There is no higher-order remainder. -/
theorem suzukiFiniteShiftSource_cross
    (F J : ℂ → ℂ) (δ z : ℂ) :
    suzukiFiniteShiftSource F J δ z * F (-z) -
        suzukiFiniteShiftSource F J δ (-z) * F z =
      δ * suzukiReflectionTangentNumerator F J z := by
  simp only [suzukiFiniteShiftSource, suzukiReflectionTangentNumerator]
  ring

/-- Exact finite-shift response of the endpoint cross-ratio transport. -/
theorem suzukiProjectiveSourceTransport_finiteShift_sub_one
    {F J : ℂ → ℂ} {δ z : ℂ}
    (hnewNeg : suzukiFiniteShiftSource F J δ (-z) ≠ 0)
    (hFz : F z ≠ 0) :
    suzukiProjectiveSourceTransport (suzukiFiniteShiftSource F J δ) F z - 1 =
      δ * suzukiReflectionTangentNumerator F J z /
        (suzukiFiniteShiftSource F J δ (-z) * F z) := by
  rw [suzukiProjectiveSourceTransport]
  field_simp [hnewNeg, hFz]
  simp only [suzukiFiniteShiftSource, suzukiReflectionTangentNumerator]
  ring

/-! ## Exact transport of Suzuki's Fourier--Livšic carrier -/

/-- The endpoint cross ratio transports the whole Fourier--Livšic carrier; its universal Cayley
factor cancels. -/
theorem suzukiFourierLivsic_eq_transport_mul
    {F₁ F₀ : ℂ → ℂ} {z : ℂ}
    (hz : z + I ≠ 0)
    (hF₁neg : F₁ (-z) ≠ 0)
    (hF₀z : F₀ z ≠ 0) (hF₀neg : F₀ (-z) ≠ 0) :
    suzukiLivsicQuotient (suzukiFourierNumerator F₁)
        (suzukiFourierDenominator F₁) z =
      suzukiProjectiveSourceTransport F₁ F₀ z *
        suzukiLivsicQuotient (suzukiFourierNumerator F₀)
          (suzukiFourierDenominator F₀) z := by
  rw [suzukiLivsicQuotient, suzukiLivsicQuotient, suzukiFourierNumerator,
    suzukiFourierNumerator, suzukiFourierDenominator, suzukiFourierDenominator,
    suzukiProjectiveSourceTransport]
  field_simp [hz, hF₁neg, hF₀z, hF₀neg]

/-- **Branch-free finite-shift carrier law.**  The exact carrier difference is the reflected
two-resolvent determinant divided only by endpoint source values. -/
theorem suzukiFourierLivsic_finiteShift_sub
    {F J : ℂ → ℂ} {δ z : ℂ}
    (hz : z + I ≠ 0)
    (hnewNeg : suzukiFiniteShiftSource F J δ (-z) ≠ 0)
    (hFneg : F (-z) ≠ 0) :
    suzukiLivsicQuotient
          (suzukiFourierNumerator (suzukiFiniteShiftSource F J δ))
          (suzukiFourierDenominator (suzukiFiniteShiftSource F J δ)) z -
        suzukiLivsicQuotient (suzukiFourierNumerator F)
          (suzukiFourierDenominator F) z =
      GaloisForLFunctions.HTGeometry.lineCayley z *
        (δ * suzukiReflectionTangentNumerator F J z /
          (suzukiFiniteShiftSource F J δ (-z) * F (-z))) := by
  rw [suzukiLivsicQuotient, suzukiLivsicQuotient, suzukiFourierNumerator,
    suzukiFourierNumerator, suzukiFourierDenominator, suzukiFourierDenominator,
    GaloisForLFunctions.HTGeometry.lineCayley]
  field_simp [hz, hnewNeg, hFneg]
  simp only [suzukiFiniteShiftSource, suzukiReflectionTangentNumerator]
  ring

/-- Exact divided difference: the finite response has the same reflected numerator as the
boundary tangent, dressed only by the new endpoint denominator. -/
theorem suzukiFourierLivsic_finiteShift_dividedDifference
    {F J : ℂ → ℂ} {δ z : ℂ}
    (hδ : δ ≠ 0) (hz : z + I ≠ 0)
    (hnewNeg : suzukiFiniteShiftSource F J δ (-z) ≠ 0)
    (hFneg : F (-z) ≠ 0) :
    (suzukiLivsicQuotient
          (suzukiFourierNumerator (suzukiFiniteShiftSource F J δ))
          (suzukiFourierDenominator (suzukiFiniteShiftSource F J δ)) z -
        suzukiLivsicQuotient (suzukiFourierNumerator F)
          (suzukiFourierDenominator F) z) / δ =
      GaloisForLFunctions.HTGeometry.lineCayley z *
        (suzukiReflectionTangentNumerator F J z /
          (suzukiFiniteShiftSource F J δ (-z) * F (-z))) := by
  rw [suzukiFourierLivsic_finiteShift_sub hz hnewNeg hFneg]
  field_simp [hδ]

/-! ## Infinitesimal generator and Donoghue-pole velocity -/

/-- Logarithmic source generator obtained from the derivative `∂ᵣ F_r = -G_r`. -/
def suzukiLogarithmicSourceGenerator (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  G (-z) / F (-z) - G z / F z

/-- The logarithmic generator is the normalized reflected tangent determinant. -/
theorem suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent
    {F G : ℂ → ℂ} {z : ℂ} (hFz : F z ≠ 0) (hFneg : F (-z) ≠ 0) :
    suzukiLogarithmicSourceGenerator F G z =
      -suzukiReflectionTangentNumerator F G z / (F z * F (-z)) := by
  rw [suzukiLogarithmicSourceGenerator, suzukiReflectionTangentNumerator]
  field_simp [hFz, hFneg]
  ring

/-- Real Fourier sources make the logarithmic generator anti-real on the real spectral line. -/
theorem conj_suzukiLogarithmicSourceGenerator_eq_neg
    {F G : ℂ → ℂ} {x : ℂ}
    (hF : F (-x) = conj (F x)) (hG : G (-x) = conj (G x)) :
    conj (suzukiLogarithmicSourceGenerator F G x) =
      -suzukiLogarithmicSourceGenerator F G x := by
  rw [suzukiLogarithmicSourceGenerator, hF, hG]
  rw [map_sub, map_div₀, map_div₀, Complex.conj_conj, Complex.conj_conj]
  ring

/-- Consequently the logarithmic generator has zero real part. -/
theorem suzukiLogarithmicSourceGenerator_re_eq_zero
    {F G : ℂ → ℂ} {x : ℂ}
    (hF : F (-x) = conj (F x)) (hG : G (-x) = conj (G x)) :
    (suzukiLogarithmicSourceGenerator F G x).re = 0 := by
  have hanti := conj_suzukiLogarithmicSourceGenerator_eq_neg hF hG
  have hre := congrArg Complex.re hanti
  simp only [conj_re, neg_re] at hre
  linarith

/-- The implicit simple-pole velocity and the Clark-atom transport formula are identical. -/
theorem suzukiImplicitPoleVelocity_eq_clarkTransport
    {Ξ : ℂ} {phaseSpeed atomMass : ℝ}
    (hspeed : phaseSpeed ≠ 0) (hmass : atomMass = 2 / phaseSpeed) :
    -Ξ / (I * (phaseSpeed : ℂ)) =
      I * (atomMass : ℂ) * Ξ / 2 := by
  rw [hmass]
  push_cast
  field_simp [hspeed]
  rw [Complex.I_sq]
  ring

/-- The Clark-atom velocity is real when the source generator is anti-real. -/
theorem suzukiClarkTransport_im_eq_zero
    {Ξ : ℂ} {atomMass : ℝ} (hΞ : conj Ξ = -Ξ) :
    (I * (atomMass : ℂ) * Ξ / 2).im = 0 := by
  have hre := congrArg Complex.re hΞ
  simp only [conj_re, neg_re] at hre
  calc
    (I * (atomMass : ℂ) * Ξ / 2).im = atomMass * Ξ.re / 2 := by
      simp [mul_im, mul_re]
    _ = 0 := by rw [show Ξ.re = 0 by linarith]; ring

end GaloisForLFunctions.RHTower
