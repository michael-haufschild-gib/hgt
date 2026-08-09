import GaloisForLFunctions.HTGeometry.NevNumeratorFactor
import GaloisForLFunctions.HTGeometry.NevTruncConvergent
import GaloisForLFunctions.HTGeometry.NevanlinnaRealMatrix

/-!
# The truncated Nevanlinna Möbius image is the quadrature Cauchy transform

At a complex point the two closed forms of the truncated entries combine into

`A(z)·τ − C(z) = (h₀/hₙ)·(α·R_{n+1}(z) + β·Rₙ(z))`,
`B(z)·τ − D(z) = (h₀/hₙ)·(α·Q_{n+1}(z) + β·Qₙ(z))`,

with the same pair `α, β`.  Whenever `α ≠ 0` the ratio is the quasi-orthogonal ratio at the
parameter `β/α`, which the divided-difference identity identifies with the Cauchy transform of the
quadrature measure of that level.  This is the finite stage of the Weyl-disc description, at every
complex point off the nodes.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem ofReal_nevAlpha (s : ℕ → ℝ) (n : ℕ) (tau : ℝ) :
    ((nevAlpha s n tau : ℝ) : ℂ) = (tau : ℂ) * secondKindC s n 0 - monicOrthoC s n 0 := by
  rw [nevAlpha, secondKindC_at_zero, monicOrthoC_at_zero]
  push_cast
  ring

theorem ofReal_nevBeta (s : ℕ → ℝ) (n : ℕ) (tau : ℝ) :
    ((nevBeta s n tau : ℝ) : ℂ)
      = monicOrthoC s (n + 1) 0 - (tau : ℂ) * secondKindC s (n + 1) 0 := by
  rw [nevBeta, secondKindC_at_zero, monicOrthoC_at_zero]
  push_cast
  ring

/-- **The truncated numerator in the quasi-orthogonal basis, at a complex point.** -/
theorem nevTruncNumeratorC_closed (h : PositiveMomentForm s) (n : ℕ) (tau : ℝ) (z : ℂ) :
    nevAtruncC s n z * (tau : ℂ) - nevCtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        (((nevAlpha s n tau : ℝ) : ℂ) * secondKindC s (n + 1) z
          + ((nevBeta s n tau : ℝ) : ℂ) * secondKindC s n z) := by
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    simpa using h.self_ne_zero (monicOrtho_ne_zero s n)
  rw [nevAtruncC_eq h n z, nevCtruncC_eq h n z, ofReal_nevAlpha, ofReal_nevBeta]
  field_simp
  ring

/-- **The truncated denominator in the quasi-orthogonal basis, at a complex point.** -/
theorem nevTruncDenominatorC_closed (h : PositiveMomentForm s) (n : ℕ) (tau : ℝ) (z : ℂ) :
    nevBtruncC s n z * (tau : ℂ) - nevDtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        (((nevAlpha s n tau : ℝ) : ℂ) * monicOrthoC s (n + 1) z
          + ((nevBeta s n tau : ℝ) : ℂ) * monicOrthoC s n z) := by
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    simpa using h.self_ne_zero (monicOrtho_ne_zero s n)
  rw [nevBtruncC_eq h n z, nevDtruncC_eq h n z, ofReal_nevAlpha, ofReal_nevBeta]
  field_simp
  ring

theorem aeval_quasiSecondKind (s : ℕ → ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    Polynomial.aeval z (quasiSecondKind s n t)
      = secondKindC s (n + 1) z + (t : ℂ) * secondKindC s n z := by
  rw [quasiSecondKind, map_add, map_mul, secondKindC, secondKindC]
  simp

/-- The truncated numerator is the leading coefficient times the quasi-orthogonal combination of
the second kind. -/
theorem nevTruncNumeratorC_eq_quasi (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (z : ℂ) :
    nevAtruncC s n z * (tau : ℂ) - nevCtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((nevAlpha s n tau : ℝ) : ℂ) *
        Polynomial.aeval z (quasiSecondKind s n (nevBeta s n tau / nevAlpha s n tau)) := by
  have hαC : ((nevAlpha s n tau : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [nevTruncNumeratorC_closed h n tau z, aeval_quasiSecondKind]
  push_cast
  field_simp

/-- The truncated denominator is the same multiple of the quasi-orthogonal polynomial. -/
theorem nevTruncDenominatorC_eq_quasi (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (z : ℂ) :
    nevBtruncC s n z * (tau : ℂ) - nevDtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((nevAlpha s n tau : ℝ) : ℂ) *
        Polynomial.aeval z (quasiOrtho s n (nevBeta s n tau / nevAlpha s n tau)) := by
  have hαC : ((nevAlpha s n tau : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [nevTruncDenominatorC_closed h n tau z, aeval_quasiOrtho]
  push_cast
  field_simp

/-- **The finite stage of the Weyl-disc description.**  The Cauchy transform of the level-`n`
quadrature measure is the truncated Nevanlinna Möbius image of the parameter. -/
theorem quasiSum_cauchy_eq_nevTruncC (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) {z : ℂ}
    (hz : ∀ y ∈ quasiNodes s n (nevBeta s n tau / nevAlpha s n tau), z - ((y : ℝ) : ℂ) ≠ 0) :
    ∑ x ∈ quasiNodes s n (nevBeta s n tau / nevAlpha s n tau),
        ((quasiWeight s n (nevBeta s n tau / nevAlpha s n tau) x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - z)
      = -((s 0 : ℂ) * (nevAtruncC s n z * (tau : ℂ) - nevCtruncC s n z)) /
          (nevBtruncC s n z * (tau : ℂ) - nevDtruncC s n z) := by
  have hc : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
      ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
      ((nevAlpha s n tau : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero (div_ne_zero ?_ ?_) (by exact_mod_cast hα)
    · simpa using h.self_ne_zero (monicOrtho_ne_zero s 0)
    · simpa using h.self_ne_zero (monicOrtho_ne_zero s n)
  have key : ∀ K X Y : ℂ, K ≠ 0 →
      -((s 0 : ℂ) * X) / Y = -((s 0 : ℂ) * (K * X)) / (K * Y) := by
    intro K X Y hK
    rw [show -((s 0 : ℂ) * (K * X)) = K * -((s 0 : ℂ) * X) by ring, mul_div_mul_left _ _ hK]
  rw [quasiSum_cauchy_complex h n (nevBeta s n tau / nevAlpha s n tau) hz,
    nevTruncNumeratorC_eq_quasi h n hα z, nevTruncDenominatorC_eq_quasi h n hα z]
  exact key _ _ _ hc

end HTGeometry
