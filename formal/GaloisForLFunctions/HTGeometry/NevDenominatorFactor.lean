import GaloisForLFunctions.HTGeometry.QuasiOrthogonal
import GaloisForLFunctions.HTGeometry.NevanlinnaPluecker

/-!
# The truncated Nevanlinna denominator is a quasi-orthogonal polynomial

Christoffel--Darboux at `(0, x)` collapses each truncated entry to a two-term combination of
`Q_{n+1}` and `Qₙ`:

`Bₙ(x) = (h₀/hₙ)·(Rₙ(0)·Q_{n+1}(x) − R_{n+1}(0)·Qₙ(x))`,
`Dₙ(x) = (h₀/hₙ)·(Qₙ(0)·Q_{n+1}(x) − Q_{n+1}(0)·Qₙ(x))`.

So the denominator `Bₙ(x)·τ − Dₙ(x)` is `(h₀/hₙ)·(α·Q_{n+1}(x) + β·Qₙ(x))` with constants `α, β`
depending only on `τ` and `n`.  The Wronskian at `0` is the nonzero constant `−hₙ/h₀`, so `α` and `β`
never vanish together: the denominator is never the zero polynomial.

This is an identity, not a limit theorem — the level-`n` denominator *is* a quasi-orthogonal
polynomial, so `QuasiOrthogonal` applies to it directly.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The Wronskian evaluated at the origin. -/
theorem wronskian_eval_zero (h : PositiveMomentForm s) (n : ℕ) :
    (monicOrtho s (n + 1)).eval 0 * (secondKind s n).eval 0
        - (monicOrtho s n).eval 0 * (secondKind s (n + 1)).eval 0
      = -(momentInner s (monicOrtho s n) (monicOrtho s n) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
  have hev := congrArg (Polynomial.eval (0:ℝ)) (momentWronskian_eq h n)
  simpa [momentWronskian] using hev

/-- **Closed form for the truncated `D` entry.** -/
theorem nevDreal_closed (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    nevDreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((monicOrtho s n).eval 0 * (monicOrtho s (n + 1)).eval x
          - (monicOrtho s (n + 1)).eval 0 * (monicOrtho s n).eval x) := by
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have hcd := christoffelDarboux h n 0 x
  rw [eq_div_iff hn] at hcd
  rw [nevDreal, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination (-(momentInner s (monicOrtho s 0) (monicOrtho s 0))) * hcd

/-- **Closed form for the truncated `B` entry.** -/
theorem nevBreal_closed (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    nevBreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((secondKind s n).eval 0 * (monicOrtho s (n + 1)).eval x
          - (secondKind s (n + 1)).eval 0 * (monicOrtho s n).eval x) := by
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    (monicOrtho_inner_self_pos h n).ne'
  have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    (monicOrtho_inner_self_pos h 0).ne'
  have hmix := mixedChristoffelDarboux h n x 0
  rw [div_add_div _ _ hn h0, eq_div_iff (mul_ne_zero hn h0)] at hmix
  rw [nevBreal, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination hmix

/-- The leading coefficient of the denominator in the quasi-orthogonal basis. -/
noncomputable def nevAlpha (s : ℕ → ℝ) (n : ℕ) (tau : ℝ) : ℝ :=
  tau * (secondKind s n).eval 0 - (monicOrtho s n).eval 0

/-- The trailing coefficient of the denominator in the quasi-orthogonal basis. -/
noncomputable def nevBeta (s : ℕ → ℝ) (n : ℕ) (tau : ℝ) : ℝ :=
  (monicOrtho s (n + 1)).eval 0 - tau * (secondKind s (n + 1)).eval 0

/-- **The denominator is a two-term combination of `Q_{n+1}` and `Qₙ`.** -/
theorem nevDenominator_closed (h : PositiveMomentForm s) (n : ℕ) (tau x : ℝ) :
    nevBreal s n x * tau - nevDreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) *
        (nevAlpha s n tau * (monicOrtho s (n + 1)).eval x
          + nevBeta s n tau * (monicOrtho s n).eval x) := by
  rw [nevBreal_closed h n x, nevDreal_closed h n x, nevAlpha, nevBeta]
  ring

/-- **The denominator never degenerates.**  Both coefficients vanishing would make the Wronskian at
the origin zero, but it is the nonzero constant `−hₙ/h₀`. -/
theorem nevAlpha_beta_ne_zero (h : PositiveMomentForm s) (n : ℕ) (tau : ℝ) :
    ¬ (nevAlpha s n tau = 0 ∧ nevBeta s n tau = 0) := by
  rintro ⟨ha, hb⟩
  rw [nevAlpha] at ha
  rw [nevBeta] at hb
  have hQn : (monicOrtho s n).eval 0 = tau * (secondKind s n).eval 0 := by linarith
  have hQn1 : (monicOrtho s (n + 1)).eval 0 = tau * (secondKind s (n + 1)).eval 0 := by linarith
  have hw := wronskian_eval_zero h n
  rw [hQn, hQn1] at hw
  have hzero : (0 : ℝ) = -(momentInner s (monicOrtho s n) (monicOrtho s n) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    rw [← hw]
    ring
  have hpos : 0 < momentInner s (monicOrtho s n) (monicOrtho s n) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    div_pos (monicOrtho_inner_self_pos h n) (monicOrtho_inner_self_pos h 0)
  linarith

/-- When the leading coefficient survives, the denominator is a nonzero multiple of a
quasi-orthogonal polynomial, so it has exactly `n+1` simple real zeros. -/
theorem nevDenominator_eq_quasiOrtho (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (x : ℝ) :
    nevBreal s n x * tau - nevDreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlpha s n tau *
        (quasiOrtho s n (nevBeta s n tau / nevAlpha s n tau)).eval x := by
  rw [nevDenominator_closed h n tau x, quasiOrtho_eval]
  field_simp

/-- **The zeros of the level-`n` denominator are exactly the quasi-orthogonal nodes.** -/
theorem nevDenominator_zero_iff (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) (x : ℝ) :
    nevBreal s n x * tau - nevDreal s n x = 0
      ↔ x ∈ quasiNodes s n (nevBeta s n tau / nevAlpha s n tau) := by
  have hc : momentInner s (monicOrtho s 0) (monicOrtho s 0) /
      momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlpha s n tau ≠ 0 :=
    mul_ne_zero (div_ne_zero (monicOrtho_inner_self_pos h 0).ne'
      (monicOrtho_inner_self_pos h n).ne') hα
  rw [nevDenominator_eq_quasiOrtho h n hα x, mem_quasiNodes_iff, mul_eq_zero]
  constructor
  · rintro (hcz | hz)
    · exact absurd hcz hc
    · exact hz
  · exact Or.inr

/-- **The zero set of the level-`n` denominator is a quasi-orthogonal node set**, hence has exactly
`n+1` elements by `quasiNodes_card`. -/
theorem nevDenominator_zeroSet (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) :
    {x : ℝ | nevBreal s n x * tau - nevDreal s n x = 0}
      = (quasiNodes s n (nevBeta s n tau / nevAlpha s n tau) : Set ℝ) := by
  ext x
  simpa using nevDenominator_zero_iff h n hα x

end HTGeometry
