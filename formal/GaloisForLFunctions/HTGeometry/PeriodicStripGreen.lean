import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Periodic strip Green formula

A finite-height strip with matching horizontal flux at its two periodic sides
has no side contribution in the planar divergence theorem.  This is the exact
Stokes step used to move the finite-deck Maass Laplacian from the source onto a
cuspidal test vector before the cusp cutoff is removed.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- On a finite strip, a continuously differentiable divergence with equal left
and right flux has only its top and bottom boundary currents. -/
theorem periodic_strip_divergence
    {a b c d : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ × ℝ → E) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E)
    (hcf : ContinuousOn f (uIcc a b ×ˢ uIcc c d))
    (hcg : ContinuousOn g (uIcc a b ×ˢ uIcc c d))
    (hdf : ∀ p ∈ Ioo (min a b) (max a b) ×ˢ Ioo (min c d) (max c d),
      HasFDerivAt f (f' p) p)
    (hdg : ∀ p ∈ Ioo (min a b) (max a b) ×ˢ Ioo (min c d) (max c d),
      HasFDerivAt g (g' p) p)
    (hint : IntegrableOn (fun p => f' p (1, 0) + g' p (0, 1))
      (uIcc a b ×ˢ uIcc c d))
    (hperiodic : ∀ y ∈ uIcc c d, f (b, y) = f (a, y)) :
    (∫ x in a..b, ∫ y in c..d, f' (x, y) (1, 0) + g' (x, y) (0, 1)) =
      (∫ x in a..b, g (x, d)) - ∫ x in a..b, g (x, c) := by
  have hstokes := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    f g f' g' a c b d hcf hcg hdf hdg hint
  have hside : (∫ y in c..d, f (b, y)) = ∫ y in c..d, f (a, y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hperiodic y hy
  rw [hstokes, hside]
  abel

/-- Real-coordinate directional derivative of a complex strip field. -/
def stripDeriv (e : ℝ × ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ F p e

/-- A `C²` strip field has `C¹` directional derivatives. -/
theorem contDiff_stripDeriv (e : ℝ × ℝ) (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (stripDeriv e F) := by
  unfold stripDeriv
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem fderiv_star_apply (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 1 F)
    (p e : ℝ × ℝ) :
    fderiv ℝ (fun q => star (F q)) p e = star (fderiv ℝ F p e) := by
  have h := ((hF.contDiffAt (x := p)).differentiableAt (by norm_num)).hasFDerivAt.star
  have he := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℂ => L e) h.fderiv
  simpa using he

private theorem fderiv_stripDeriv_mul_star_apply (e : ℝ × ℝ) (U V : ℝ × ℝ → ℂ)
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 1 V)
    (p d : ℝ × ℝ) :
    fderiv ℝ (fun q => stripDeriv e U q * star (V q)) p d =
      stripDeriv d (stripDeriv e U) p * star (V p) +
        stripDeriv e U p * star (stripDeriv d V p) := by
  change fderiv ℝ (stripDeriv e U * fun q => star (V q)) p d = _
  have hderiv := ((contDiff_stripDeriv e U hU).contDiffAt (x := p)).differentiableAt
    (by norm_num) |>.hasFDerivAt
  have hstar := ((hV.contDiffAt (x := p)).differentiableAt (by norm_num)).hasFDerivAt.star
  have h := hderiv.mul hstar
  have he := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℂ => L d) h.fderiv
  have he' :
      fderiv ℝ (stripDeriv e U * fun q => star (V q)) p d =
        stripDeriv e U p * star (stripDeriv d V p) +
          star (V p) * stripDeriv d (stripDeriv e U) p := by
    simpa [stripDeriv, fderiv_star_apply V hV p d] using he
  rw [he']
  ring

/-- Mixed Green identity on a finite periodic strip.  It moves both real second
derivatives from a `C²` source `U` onto a `C¹` test `V`, retaining the exact
top-minus-bottom vertical flux. -/
theorem complex_periodic_strip_green
    {a b c d : ℝ} (U V : ℝ × ℝ → ℂ)
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 1 V)
    (hperiodic : ∀ y ∈ uIcc c d,
      stripDeriv (1, 0) U (b, y) * star (V (b, y)) =
        stripDeriv (1, 0) U (a, y) * star (V (a, y))) :
    (∫ x in a..b, ∫ y in c..d,
      (stripDeriv (1, 0) (stripDeriv (1, 0) U) (x, y) * star (V (x, y)) +
        stripDeriv (1, 0) U (x, y) * star (stripDeriv (1, 0) V (x, y))) +
      (stripDeriv (0, 1) (stripDeriv (0, 1) U) (x, y) * star (V (x, y)) +
        stripDeriv (0, 1) U (x, y) * star (stripDeriv (0, 1) V (x, y)))) =
      (∫ x in a..b, stripDeriv (0, 1) U (x, d) * star (V (x, d))) -
        ∫ x in a..b, stripDeriv (0, 1) U (x, c) * star (V (x, c)) := by
  let fx : ℝ × ℝ → ℂ := fun p => stripDeriv (1, 0) U p * star (V p)
  let fy : ℝ × ℝ → ℂ := fun p => stripDeriv (0, 1) U p * star (V p)
  have hfx : ContDiff ℝ 1 fx :=
    (contDiff_stripDeriv (1, 0) U hU).mul (Complex.conjCLE.contDiff.comp hV)
  have hfy : ContDiff ℝ 1 fy :=
    (contDiff_stripDeriv (0, 1) U hU).mul (Complex.conjCLE.contDiff.comp hV)
  have hdiv := periodic_strip_divergence (a := a) (b := b) (c := c) (d := d)
    fx fy (fderiv ℝ fx) (fderiv ℝ fy)
    hfx.continuous.continuousOn hfy.continuous.continuousOn
    (fun p _ => (hfx.contDiffAt (x := p)).differentiableAt (by norm_num) |>.hasFDerivAt)
    (fun p _ => (hfy.contDiffAt (x := p)).differentiableAt (by norm_num) |>.hasFDerivAt)
    (by
      exact (((hfx.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const)).add
        ((hfy.continuous_fderiv_apply one_ne_zero).comp
          (continuous_id.prodMk continuous_const))).continuousOn.integrableOn_compact
          (isCompact_uIcc.prod isCompact_uIcc))
    (by
      intro y hy
      exact hperiodic y hy)
  calc
    (∫ x in a..b, ∫ y in c..d,
        (stripDeriv (1, 0) (stripDeriv (1, 0) U) (x, y) * star (V (x, y)) +
          stripDeriv (1, 0) U (x, y) * star (stripDeriv (1, 0) V (x, y))) +
        (stripDeriv (0, 1) (stripDeriv (0, 1) U) (x, y) * star (V (x, y)) +
          stripDeriv (0, 1) U (x, y) * star (stripDeriv (0, 1) V (x, y)))) =
        ∫ x in a..b, ∫ y in c..d,
          fderiv ℝ fx (x, y) (1, 0) + fderiv ℝ fy (x, y) (0, 1) := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply intervalIntegral.integral_congr
          intro y hy
          dsimp only [fx, fy]
          rw [fderiv_stripDeriv_mul_star_apply (1, 0) U V hU hV (x, y) (1, 0),
            fderiv_stripDeriv_mul_star_apply (0, 1) U V hU hV (x, y) (0, 1)]
    _ = (∫ x in a..b, fy (x, d)) - ∫ x in a..b, fy (x, c) := hdiv
    _ = (∫ x in a..b, stripDeriv (0, 1) U (x, d) * star (V (x, d))) -
        ∫ x in a..b, stripDeriv (0, 1) U (x, c) * star (V (x, c)) := by
          rfl

end

end GaloisForLFunctions.HTGeometry
