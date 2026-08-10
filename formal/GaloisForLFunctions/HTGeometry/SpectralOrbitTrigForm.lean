import GaloisForLFunctions.HTGeometry.OrbitExceptionalTimes
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A spectral orbit is a trigonometric orbit

The coordinates of `e^{-itH}Ω` in any basis are `∑ⱼ wⱼ e^{-i t Eⱼ}` with real `Eⱼ`.  Taking real
parts turns each into a finite trigonometric sum, so the exceptional-time finiteness of
`OrbitExceptionalTimes` applies verbatim.

Imaginary parts need no separate treatment: `Im z = Re (-i z)`, so an imaginary coordinate is again
of the form `Re (∑ⱼ wⱼ' e^{-i t Eⱼ})` with `wⱼ' = -i wⱼ`.  One statement therefore covers all `2D`
real coordinates of a `D`-dimensional complex state.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The real part of a phase times a constant is a trigonometric combination. -/
theorem re_mul_exp_neg_mul_I (w : ℂ) (θ : ℝ) :
    (w * Complex.exp (-((θ : ℂ)) * Complex.I)).re
      = w.re * Real.cos θ + w.im * Real.sin θ := by
  have hexp : Complex.exp (-((θ : ℂ)) * Complex.I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The imaginary part is the real part of the rotated constant. -/
theorem im_eq_re_neg_I_mul (z : ℂ) : z.im = (-Complex.I * z).re := by
  simp [Complex.mul_re]

/-- **A spectral sum has trigonometric real part.** -/
theorem re_sum_exp {n : ℕ} (w : Fin n → ℂ) (E : Fin n → ℝ) (t : ℝ) :
    (∑ j, w j * Complex.exp (-((E j * t : ℝ) : ℂ) * Complex.I)).re
      = ∑ j, ((w j).re * Real.cos (E j * t) + (w j).im * Real.sin (E j * t)) := by
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => re_mul_exp_neg_mul_I (w j) (E j * t)

/-- **Exceptional times of a spectral orbit are finite.**  Each real coordinate of the orbit is the
real part of a spectral sum; on any compact time set the orbit lands in the union of finitely many
polynomial images with fewer parameters than the number of algebraically independent coordinates
only finitely often. -/
theorem finite_exceptional_times_of_spectralOrbit {ι : Type*} {r k n : ℕ}
    (Ps : Finset ι) (m : ι → ℕ) (hm : ∀ p ∈ Ps, m p < k) (σ : Fin k → Fin r)
    (Φ : ∀ p : ι, Fin r → MvPolynomial (Fin (m p)) ℚ)
    (w : Fin r → Fin n → ℂ) (E : Fin n → ℝ) {t₀ : ℝ}
    (hP : AlgebraicIndependent ℚ (fun i : Fin k =>
      (∑ j, w (σ i) j * Complex.exp (-((E j * t₀ : ℝ) : ℂ) * Complex.I)).re))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ p ∈ Ps, ∃ u : Fin (m p) → ℝ, ∀ i : Fin r,
      (∑ j, w i j * Complex.exp (-((E j * t : ℝ) : ℂ) * Complex.I)).re
        = MvPolynomial.aeval u (Φ p i)}.Finite := by
  have hform : ∀ (i : Fin r) (t : ℝ),
      (∑ j, w i j * Complex.exp (-((E j * t : ℝ) : ℂ) * Complex.I)).re
        = ∑ j, ((w i j).re * Real.cos (E j * t) + (w i j).im * Real.sin (E j * t)) :=
    fun i t => re_sum_exp (w i) E t
  have hmain := finite_exceptional_times_subfamily Ps m hm σ Φ
    (fun i j => (w i j).re) (fun i j => (w i j).im) E (t₀ := t₀)
    (by simpa only [hform] using hP) hS
  simpa only [hform] using hmain

end GaloisForLFunctions.HTGeometry
