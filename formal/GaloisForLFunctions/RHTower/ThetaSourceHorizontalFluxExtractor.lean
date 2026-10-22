import GaloisForLFunctions.RHTower.ThetaTiltFluxCarrier
import GaloisForLFunctions.HTGeometry.HorizontalModulusDerivative

/-!
# Horizontal flux extraction for theta-source Laplace transforms

Let `F(w) = ∫ k(x) e^(w x) dx` be the bilateral Laplace transform of a theta source `k` (even,
positive, continuous, faster than exponential decay), and let
`B(w, v) = (F'(w) conj F(v) + F(w) conj F'(v)) / (w + conj v)` be its source Bezoutian. On the
horizontal line `Im w = b`, the diagonal `B(w, w)` equals `(d/da |F(a + ib)|^2) / (2a)`. By the mean
value theorem, if `F` vanishes at `A + ib` with `A > 0` but not at `ib`, then `|F|^2` must decrease
somewhere on the segment, so the diagonal Bezoutian has negative real part at some `a + ib` with
`0 < a < A`.

## Main results

- `exists_sourceBezoutian_diagonal_neg_of_horizontal_zero`: a zero of `F` at `A + ib` (`A > 0`)
  with `F(ib) ≠ 0` forces `Re B(a + ib, a + ib) < 0` for some `a ∈ (0, A)`.

## Hypotheses

The theorem is an implication: it assumes `A > 0`, a zero `F(A + ib) = 0`, and the nonvanishing
`F(ib) ≠ 0`. No further analytic input is used; the theta-source axioms are part of the data.
-/

open Complex Set
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Assuming `A > 0`, `F(A + ib) = 0` and `F(ib) ≠ 0` for the bilateral Laplace transform `F` of a
theta source, the diagonal source Bezoutian has negative real part at some `a + ib` with
`0 < a < A`. -/
theorem exists_sourceBezoutian_diagonal_neg_of_horizontal_zero
    (S : ThetaSource) {A b : ℝ} (hA : 0 < A)
    (hzero : bilateralLaplace S ((A : ℂ) + (b : ℂ) * I) = 0)
    (hbase : bilateralLaplace S ((b : ℂ) * I) ≠ 0) :
    ∃ a : ℝ, a ∈ Ioo 0 A ∧
      (sourceBezoutian S ((a : ℂ) + (b : ℂ) * I)
        ((a : ℂ) + (b : ℂ) * I)).re < 0 := by
  let f : ℂ → ℂ := bilateralLaplace S
  let g : ℝ → ℝ := fun a => normSq (f ((a : ℂ) + (b : ℂ) * I))
  let g' : ℝ → ℝ := fun a =>
    2 * (deriv f ((a : ℂ) + (b : ℂ) * I) *
      conj (f ((a : ℂ) + (b : ℂ) * I))).re
  have hdiff (a : ℝ) : HasDerivAt g (g' a) a := by
    exact HTGeometry.hasDerivAt_normSq_horizontal_general f b a
      (differentiable_bilateralLaplace S ((a : ℂ) + (b : ℂ) * I))
  have hcont : ContinuousOn g (Icc 0 A) := fun a _ => (hdiff a).continuousAt.continuousWithinAt
  obtain ⟨a, ha, hslope⟩ := exists_hasDerivAt_eq_slope g g' hA hcont
    (fun x _ => hdiff x)
  have hgA : g A = 0 := by simp [g, f, hzero]
  have hg0 : 0 < g 0 := by
    dsimp [g, f]
    simp only [zero_add]
    exact normSq_pos.mpr hbase
  have hg' : g' a < 0 := by
    rw [hslope, hgA]
    apply div_neg_of_neg_of_pos
    · linarith
    · linarith
  refine ⟨a, ha, ?_⟩
  let w : ℂ := (a : ℂ) + (b : ℂ) * I
  have ha0 : 0 < a := ha.1
  have hden : w + conj w = (2 * a : ℝ) := by
    apply Complex.ext <;> simp [w]
    ring
  have hderiv : deriv f w = bilateralLaplaceDeriv S w := by
    exact deriv_bilateralLaplace S w
  have hnum :
      (bilateralLaplaceDeriv S w * conj (bilateralLaplace S w) +
        bilateralLaplace S w * conj (bilateralLaplaceDeriv S w)).re = g' a := by
    dsimp [g', f, w]
    rw [hderiv]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [sourceBezoutian, hden, Complex.div_ofReal_re, hnum]
  exact div_neg_of_neg_of_pos hg' (mul_pos (by norm_num) ha0)

end

end RHTower
