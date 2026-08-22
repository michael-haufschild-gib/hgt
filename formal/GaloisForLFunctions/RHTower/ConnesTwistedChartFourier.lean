import GaloisForLFunctions.RHTower.ConnesBesovSupInequality

/-!
# The twisted chart and the error term of §VII Theorem 4

§VII (26), (35)-(37) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

In the proof of Theorem 4 the symbol attached to a lattice element `q` is the *twisted chart*

  `g_q(u) = f(q (u+1)^{-1}) |u+1|^{-1}`,                                     (26)

and Connes' Lemma 2 rewrites the error term

  `δ_q(Λ) = ∫ ĝ_q(u) ε_Λ(u) du`                                             (35)

as the inverse Fourier transform of `ε_Λ · ξ̂` evaluated at `q^{-1}`, where

  `ξ(x) = f(x^{-1}) |x^{-1}|`   so that   `g_q(x) = ξ(q^{-1}(1+x))`.        (37)

The two computational steps - `ĝ_q(u) = |q| α(-u) ξ̂(q u)` and the substitution `y = q u` - are
proved here at the archimedean place, for an arbitrary (not necessarily integrable) `ξ`, since
mathlib's dilation and translation laws for the Lebesgue integral hold unconditionally.
-/

open MeasureTheory Real Set
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§VII (26).**  Connes' twisted chart `g_q(u) = f(q(u+1)^{-1})|u+1|^{-1}`. -/
def connesTwistedChart (f : ℝ → ℂ) (q u : ℝ) : ℂ := f (q * (u + 1)⁻¹) * ((|u + 1| : ℝ) : ℂ)⁻¹

/-- Connes' `ξ(x) = f(x^{-1})|x^{-1}|`, the function whose translates-and-dilates are the twisted
charts. -/
def connesInverseWeight (f : ℝ → ℂ) (x : ℝ) : ℂ := f x⁻¹ * ((|x⁻¹| : ℝ) : ℂ)

/-- The value of the twisted chart at the origin is `f(q)`; this is the step
`∫ ĝ_q(u) du = g_q(0) = f(q)` of (31). -/
theorem connesTwistedChart_zero (f : ℝ → ℂ) (q : ℝ) : connesTwistedChart f q 0 = f q := by
  simp [connesTwistedChart]

/-- **§VII, Lemma 2.**  The twisted chart is a translate-and-dilate of `ξ`, up to the module of
`q`: `ξ(q^{-1}(1+u)) = |q| g_q(u)`. -/
theorem connes_inverseWeight_twistedChart (f : ℝ → ℂ) (q u : ℝ) :
    connesInverseWeight f (q⁻¹ * (1 + u)) = ((|q| : ℝ) : ℂ) * connesTwistedChart f q u := by
  have hinv : (q⁻¹ * (1 + u))⁻¹ = q * (1 + u)⁻¹ := by
    rw [mul_inv, inv_inv]
  rw [connesInverseWeight, connesTwistedChart, hinv, add_comm u 1]
  have habs : |q * (1 + u)⁻¹| = |q| * |(1 + u)|⁻¹ := by
    rw [abs_mul, abs_inv]
  rw [habs]
  push_cast
  ring

/-- The character identity behind the dilation step: shifting the argument by `-1` and rescaling by
`q` turns the frequency `u` into `q u` and produces the phase `α(-u)`. -/
theorem connes_fourierChar_dilate_shift (q u z : ℝ) :
    connesFourierChar u (q * z - 1)
      = Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) * connesFourierChar (q * u) z := by
  simp only [connesFourierChar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **§VII, Lemma 2, the transform of the twisted chart.**  `ĝ_q(u) = |q| α(-u) ξ̂(q u)`.
No integrability hypothesis is needed: mathlib's dilation and translation laws for the Lebesgue
integral are unconditional. -/
theorem connes_twisted_fourier (ξ : ℝ → ℂ) {q : ℝ} (hq : q ≠ 0) (u : ℝ) :
    𝓕 (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u
      = ((|q| : ℝ) : ℂ) * Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) * 𝓕 ξ (q * u) := by
  have hq0 : |q| ≠ 0 := abs_ne_zero.mpr hq
  set Φ : ℝ → ℂ := fun y : ℝ => connesFourierChar u y * ξ (q⁻¹ * (1 + y)) with hΦ
  set Ψ : ℝ → ℂ := fun y : ℝ => connesFourierChar u (y - 1) * ξ (q⁻¹ * y) with hΨ
  have hshift : (∫ y : ℝ, Φ y) = ∫ y : ℝ, Ψ y := by
    have h := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ)) Φ 1
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΦ, hΨ]
    congr 2
    ring
  have hdil : (∫ z : ℝ, Ψ (q * z)) = |q⁻¹| • ∫ y : ℝ, Ψ y :=
    MeasureTheory.Measure.integral_comp_mul_left Ψ q
  have hval : ∀ z : ℝ, Ψ (q * z)
      = Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) *
        (connesFourierChar (q * u) z * ξ z) := by
    intro z
    simp only [hΨ]
    rw [inv_mul_cancel_left₀ hq, connes_fourierChar_dilate_shift q u z]
    ring
  have hrewrite : (∫ z : ℝ, Ψ (q * z))
      = Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) * 𝓕 ξ (q * u) := by
    rw [connes_fourier_eq_integral ξ (q * u), ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hval)
  have hfinal : (∫ y : ℝ, Ψ y)
      = ((|q| : ℝ) : ℂ) * (Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) * 𝓕 ξ (q * u)) := by
    rw [← hrewrite, hdil, Complex.real_smul, abs_inv]
    rw [← mul_assoc]
    have hcan : ((|q| : ℝ) : ℂ) * ((|q|⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hq0, Complex.ofReal_one]
    rw [hcan, one_mul]
  rw [connes_fourier_eq_integral (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u]
  rw [show (∫ y : ℝ, connesFourierChar u y * ξ (q⁻¹ * (1 + y))) = ∫ y : ℝ, Φ y from rfl]
  rw [hshift, hfinal, ← mul_assoc]

/-- **§VII (35)-(37), the substitution `y = q u`.**  For an arbitrary weight `w` the error integral
is an inverse-Fourier integral of `ξ̂ · w(q^{-1} ·)` at `q^{-1}`.  Hypothesis-free. -/
theorem connes_errorTerm_substitution (ξ : ℝ → ℂ) {q : ℝ} (hq : q ≠ 0) (w : ℝ → ℂ) :
    (∫ u : ℝ, 𝓕 (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u * w u)
      = ∫ y : ℝ, Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I) * 𝓕 ξ y
          * w (q⁻¹ * y) := by
  have hq0 : |q| ≠ 0 := abs_ne_zero.mpr hq
  set Φ : ℝ → ℂ := fun u : ℝ =>
    ((|q| : ℝ) : ℂ) * Complex.exp (((2 * π * u : ℝ) : ℂ) * Complex.I) * 𝓕 ξ (q * u) * w u with hΦ
  have hlhs : (∫ u : ℝ, 𝓕 (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u * w u) = ∫ u : ℝ, Φ u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show 𝓕 (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u * w u = Φ u
    rw [connes_twisted_fourier ξ hq u]
  have hdil : (∫ y : ℝ, Φ (q⁻¹ * y)) = |(q⁻¹)⁻¹| • ∫ u : ℝ, Φ u :=
    MeasureTheory.Measure.integral_comp_mul_left Φ q⁻¹
  have hval : ∀ y : ℝ, Φ (q⁻¹ * y)
      = ((|q| : ℝ) : ℂ) * (Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I) * 𝓕 ξ y
          * w (q⁻¹ * y)) := by
    intro y
    simp only [hΦ]
    rw [mul_inv_cancel_left₀ hq]
    ring
  have hsplit : (∫ y : ℝ, Φ (q⁻¹ * y))
      = ((|q| : ℝ) : ℂ) * ∫ y : ℝ, Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I)
          * 𝓕 ξ y * w (q⁻¹ * y) := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hval)
  rw [hlhs]
  have hq' : |(q⁻¹)⁻¹| = |q| := by rw [inv_inv]
  rw [hq', Complex.real_smul, hsplit] at hdil
  have hne : ((|q| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0
  exact (mul_left_cancel₀ hne hdil).symm

/-- **§VII (37).**  For a weight invariant under the module-one scaling `y ↦ q^{-1} y` - which is
what `ε_Λ(u) = (log|u| − 2 log' Λ)^+` is, since `|q| = 1` for a lattice unit - the error term is
the inverse Fourier transform of `ε_Λ · ξ̂` at `q^{-1}`. -/
theorem connes_errorTerm_fourierInv (ξ : ℝ → ℂ) {q : ℝ} (hq : q ≠ 0) (w : ℝ → ℂ)
    (hw : ∀ y : ℝ, w (q⁻¹ * y) = w y) :
    (∫ u : ℝ, 𝓕 (fun x : ℝ => ξ (q⁻¹ * (1 + x))) u * w u)
      = ∫ y : ℝ, Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I) * (𝓕 ξ y * w y) := by
  rw [connes_errorTerm_substitution ξ hq w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I) * 𝓕 ξ y * w (q⁻¹ * y)
    = Complex.exp (((2 * π * (q⁻¹ * y) : ℝ) : ℂ) * Complex.I) * (𝓕 ξ y * w y)
  rw [hw y, mul_assoc]

end

end GaloisForLFunctions.RHTower
