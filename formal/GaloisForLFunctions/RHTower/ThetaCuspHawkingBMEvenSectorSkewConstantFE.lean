import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewConstantTilt
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewPlateauOdd

/-!
# Functional-equation invariance of the constant-mode kernel is the critical line

Reflecting the zero `ρ ↦ 1 − conj ρ` sends the rate `s = ρ − 2` to `−3 − conj s`. By the rate-swap
oddness and the real coefficients of the plateau kernel, `K(−3 − conj s) = −conj K(s)`, so the kernel
takes the same value at a zero and at its reflection exactly when its real part vanishes; with the
certified tilt detection this happens exactly on the critical line for `t ≥ 92`
(`skewConstantKernel_fe_invariant_iff`). This is the explicit, elementary form at the fundamental of
the corpus's abstract statement that source–functional-equation clock covariance is equivalent to
criticality: a receiver, stated on the certified dominant kernel.
-/

set_option autoImplicit false

namespace RHTower.D4BMScalarStream

/-- The kernel at the reflected zero is minus the conjugate of the kernel at the zero. -/
theorem skewConstantKernel_reflected_zero (s : ℂ) :
    skewPlateauMu (-3 - starRingEnd ℂ s) 0 = -starRingEnd ℂ (skewPlateauMu s 0) := by
  rw [skewPlateauMu_reflect]
  have h : skewPlateauMu (starRingEnd ℂ s) 0 = starRingEnd ℂ (skewPlateauMu s 0) := by
    have := skewPlateauMu_conj s 0
    simpa using this
  rw [h]

/-- The kernel is invariant under the reflection of the zero exactly when its real part vanishes. -/
theorem skewConstantKernel_fe_invariant_iff_re (s : ℂ) :
    skewPlateauMu s 0 = skewPlateauMu (-3 - starRingEnd ℂ s) 0 ↔ (skewPlateauMu s 0).re = 0 := by
  rw [skewConstantKernel_reflected_zero]
  constructor
  · intro h
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, Complex.conj_re] at h'
    linarith
  · intro h
    apply Complex.ext
    · rw [Complex.neg_re, Complex.conj_re, h]; ring
    · rw [Complex.neg_im, Complex.conj_im]; ring

/-- Above height `92` the constant-mode kernel is functional-equation invariant exactly on the line. -/
theorem skewConstantKernel_fe_invariant_iff (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (92 : ℝ) ≤ t) :
    skewPlateauMu ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) 0 =
        skewPlateauMu (-3 - starRingEnd ℂ ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)) 0 ↔ σ = 1 / 2 := by
  rw [skewConstantKernel_fe_invariant_iff_re]
  exact skewConstantKernel_re_eq_zero_iff σ t h0 h1 ht

end RHTower.D4BMScalarStream
