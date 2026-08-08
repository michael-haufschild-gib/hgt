/-
The divisor-indexed form of the spectral criterion for the Riemann hypothesis.

`riemannHypothesis_of_xiSpectralPoint_real` is stated on the multiplicity-copy carrier
`XiZeroCopy`.  Purity arguments on middle cohomology produce eigenvalues indexed by the divisor
itself, in the centered form `1/2 + i·μ_ρ`, and each of them re-derives the passage from that shape
to the critical line by hand: open `rh_iff_xi_ne_zero_right`, build the divisor point, compute the
real part.

That passage is one lemma and uses no operator.  This file states it in the three shapes the
purity arguments actually produce: reality of the divisor-indexed spectral points, vanishing of
their imaginary parts, and the centered eigenvalue having real part one half.
-/
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

namespace RHTower

noncomputable section

/-- **Reality of the divisor-indexed spectral points forces RH.**  The multiplicity-copy criterion
`riemannHypothesis_of_xiSpectralPoint_real`, read on the divisor itself: a copy sits over each
divisor point and the two spectral points agree. -/
theorem riemannHypothesis_of_xiSpectralPointSupport_real
    (hreal : ∀ ρ : XiDivisorSupport, ∃ t : ℝ, xiSpectralPointSupport ρ = (t : ℂ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiSpectralPoint_real fun q => by
    rw [xiSpectralPoint_eq_support]
    exact hreal q.1

/-- The imaginary part of the divisor-indexed spectral point is the distance of the divisor point
from the critical line. -/
theorem xiSpectralPointSupport_im (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).im = 1 / 2 - (ρ : ℂ).re := by
  rw [xiSpectralPointSupport]
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- **The two vocabularies agree.**  A divisor-indexed spectral point is real exactly when its
divisor point lies on the critical line, so a criterion stated in either vocabulary feeds the
other. -/
theorem xiSpectralPointSupport_im_eq_zero_iff (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).im = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [xiSpectralPointSupport_im]
  constructor <;> intro h <;> linarith

/-- **Vanishing of the divisor-indexed spectral imaginary parts forces RH.** -/
theorem riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
    (him : ∀ ρ : XiDivisorSupport, (xiSpectralPointSupport ρ).im = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiSpectralPointSupport_real fun ρ =>
    ⟨(xiSpectralPointSupport ρ).re, Complex.ext (by simp) (by simp [him ρ])⟩

/-- The real part of a centered value. -/
theorem re_half_add_I_mul (μ : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * μ).re = 1 / 2 - μ.im := by
  have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- **The centered spectral criterion.**  Every purity argument on a Deninger-style middle flow
produces eigenvalues in the centered form `1/2 + i·μ_ρ` and concludes by showing their real part is
one half; that last step is this lemma, and it needs no operator at all. -/
theorem riemannHypothesis_of_centeredEigenvalue_re_eq_half
    (h : ∀ ρ : XiDivisorSupport,
      ((1 / 2 : ℂ) + Complex.I * xiSpectralPointSupport ρ).re = 1 / 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero fun ρ => ?_
  have hρ := h ρ
  rw [re_half_add_I_mul] at hρ
  linarith

end

end RHTower
