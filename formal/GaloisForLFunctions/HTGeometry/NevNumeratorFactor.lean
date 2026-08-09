import GaloisForLFunctions.HTGeometry.NevDenominatorFactor
import GaloisForLFunctions.HTGeometry.QuasiCauchyTransform

/-!
# The truncated Nevanlinna numerator in the quasi-orthogonal basis

The two Christoffel--Darboux identities of the second kind put the truncated `A` and `C` entries in
closed form, and the same two coefficients `α`, `β` that expand the denominator
`B·τ − D` in `Q_{n+1}, Qₙ` expand the numerator `A·τ − C` in `R_{n+1}, Rₙ`:

`A(x)·τ − C(x) = (h₀/hₙ)·(α·R_{n+1}(x) + β·Rₙ(x))`,
`B(x)·τ − D(x) = (h₀/hₙ)·(α·Q_{n+1}(x) + β·Qₙ(x))`.

Hence the truncated Möbius image of a real parameter is the ratio of the two quasi-orthogonal
combinations, which is exactly the Cauchy transform of the quadrature measure of that level.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Closed form for the truncated `A` entry.** -/
theorem nevAreal_closed (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    nevAreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((secondKind s (n + 1)).eval x * (secondKind s n).eval 0
          - (secondKind s n).eval x * (secondKind s (n + 1)).eval 0) := by
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have hcd := secondKindChristoffelDarboux h n x 0
  rw [eq_div_iff hn] at hcd
  have hsum : ∑ k ∈ Finset.range (n + 1), (secondKind s k).eval 0 * (secondKind s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)
      = ∑ k ∈ Finset.range (n + 1), (secondKind s k).eval x * (secondKind s k).eval 0 /
      momentInner s (monicOrtho s k) (monicOrtho s k) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [nevAreal, hsum, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination (momentInner s (monicOrtho s 0) (monicOrtho s 0)) * hcd

/-- **Closed form for the truncated `C` entry.** -/
theorem nevCreal_closed (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    nevCreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((monicOrtho s n).eval 0 * (secondKind s (n + 1)).eval x
          - (monicOrtho s (n + 1)).eval 0 * (secondKind s n).eval x) := by
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    (monicOrtho_inner_self_pos h 0).ne'
  have hmix := mixedChristoffelDarboux h n 0 x
  rw [div_add_div _ _ hn h0, eq_div_iff (mul_ne_zero hn h0)] at hmix
  rw [nevCreal, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination -hmix

/-- **The numerator is the same two-term combination, of the second kind.** -/
theorem nevNumerator_closed (h : PositiveMomentForm s) (n : ℕ) (tau x : ℝ) :
    nevAreal s n x * tau - nevCreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        (nevAlpha s n tau * (secondKind s (n + 1)).eval x
          + nevBeta s n tau * (secondKind s n).eval x) := by
  rw [nevAreal_closed h n x, nevCreal_closed h n x, nevAlpha, nevBeta]
  ring

/-- When the leading coefficient survives, the numerator is the matching nonzero multiple of the
quasi-orthogonal combination of the second kind. -/
theorem nevNumerator_eq_quasiSecondKind (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (x : ℝ) :
    nevAreal s n x * tau - nevCreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlpha s n tau *
        (quasiSecondKind s n (nevBeta s n tau / nevAlpha s n tau)).eval x := by
  rw [nevNumerator_closed h n tau x, quasiSecondKind_eval]
  field_simp

/-- **The truncated Möbius image of a real parameter is the quasi-orthogonal ratio.** -/
theorem nevTruncRatio_eq_quasiRatio (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (x : ℝ) :
    (nevAreal s n x * tau - nevCreal s n x) / (nevBreal s n x * tau - nevDreal s n x)
      = (quasiSecondKind s n (nevBeta s n tau / nevAlpha s n tau)).eval x /
          (quasiOrtho s n (nevBeta s n tau / nevAlpha s n tau)).eval x := by
  have hc : momentInner s (monicOrtho s 0) (monicOrtho s 0) /
      momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlpha s n tau ≠ 0 :=
    mul_ne_zero (div_ne_zero (monicOrtho_inner_self_pos h 0).ne'
      (monicOrtho_inner_self_pos h n).ne') hα
  rw [nevNumerator_eq_quasiSecondKind h n hα x, nevDenominator_eq_quasiOrtho h n hα x]
  rw [mul_comm _ ((quasiSecondKind s n (nevBeta s n tau / nevAlpha s n tau)).eval x),
    mul_comm _ ((quasiOrtho s n (nevBeta s n tau / nevAlpha s n tau)).eval x)]
  rw [mul_div_mul_right _ _ hc]

end HTGeometry
