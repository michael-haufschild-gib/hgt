import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion

/-!
# Exact unconditional Gaussian smooth AFE

The infinite contour identity is normalized by `2π` and its right edge is
identified with the absolutely convergent smoothed Dirichlet series.  The left
edge remains an exact reflected Mellin integral; subsequent modules may expand
it termwise and approximate its shifted Gamma ratio.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- Normalized reflected (left-edge) Mellin integral. -/
def smoothAFEZetaDualMellinAt (τ x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaMellinIntegrand (linePt τ) x
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

/-- Exact Gaussian smooth approximate functional equation before expanding the
reflected edge into its dual Dirichlet series. -/
theorem riemannZeta_line_eq_smoothAFEZetaMellin_sub_dual_sub_residue
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    riemannZeta (linePt τ) =
      smoothAFEZetaMellinAt 1 (linePt τ) x -
        smoothAFEZetaDualMellinAt τ x -
        smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  let R : ℂ := ∫ v : ℝ,
    smoothAFEZetaMellinIntegrand (linePt τ) x
      (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    smoothAFEZetaMellinIntegrand (linePt τ) x
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)
  let z : ℂ := riemannZeta (linePt τ)
  let ρ : ℂ := smoothAFEZetaShiftedPoleResidue (linePt τ) x
  have hcontour := smoothAFEZetaMellin_infinite_contour_shift_line hx τ
  have hcancel : R - L = (2 * Real.pi : ℂ) * (z + ρ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, z, ρ, smul_eq_mul, mul_sub, mul_assoc,
      mul_left_comm, mul_comm] using hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  unfold smoothAFEZetaMellinAt smoothAFEZetaDualMellinAt
  rw [Complex.real_smul, Complex.real_smul]
  change z = ((1 / (2 * Real.pi) : ℝ) : ℂ) * R -
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * L - ρ
  have hscale :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
        ((2 * Real.pi : ℂ) : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscale]
  symm
  calc
    (2 * Real.pi : ℂ)⁻¹ * R - (2 * Real.pi : ℂ)⁻¹ * L - ρ =
        (2 * Real.pi : ℂ)⁻¹ * (R - L) - ρ := by ring
    _ = (2 * Real.pi : ℂ)⁻¹ *
          ((2 * Real.pi : ℂ) * (z + ρ)) - ρ := by rw [hcancel]
    _ = z := by
      rw [inv_mul_cancel_left₀ hpi]
      ring

/-- Direct-plus-reflected exact smooth AFE with the right edge written as a
canonical Gaussian-cutoff Dirichlet series. -/
theorem riemannZeta_line_eq_tsum_smoothAFECutoff_sub_dual_sub_residue
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    riemannZeta (linePt τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) -
      smoothAFEZetaDualMellinAt τ x -
      smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  rw [← smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff
    (s := linePt τ) (x := x) (c := 1)
    hx (by norm_num) (by rw [linePt_re]; norm_num)]
  exact riemannZeta_line_eq_smoothAFEZetaMellin_sub_dual_sub_residue hx τ

end RHTower
