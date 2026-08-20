import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralVertical
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralHorizontal
import GaloisForLFunctions.RHTower.SmoothAFEZetaContour
import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion

/-!
# The Gaussian smooth approximate functional equation at a general point

The corpus proves the exact smooth AFE only on the critical line.  Every ingredient is in fact
general: the two-pole rectangle identity already takes an arbitrary base point, the vertical edges
are integrable off the pole abscissa, and the horizontal Gaussian edges vanish at any fixed `s`.

Assembling them gives the exact identity at every `s` in the open strip `0 < Re s < 2`, which is
what a Levinson-type argument at the abscissa `σ₀ = ½ − R/log T` consumes.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- Normalized reflected (left-edge) Mellin integral at a general base point. -/
def smoothAFEZetaDualMellinGeneral (s : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaMellinIntegrand s x (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

/-- **The finite two-pole rectangle identity at a general base point.** -/
theorem smoothAFEZetaMellin_finite_contour_shift_general
    {x T : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hre0 : 0 < s.re) (hre2 : s.re < 2)
    (hT : |s.im| < T) :
    ((∫ u : ℝ in (-1)..1, smoothAFEZetaMellinIntegrand s x ((u : ℂ) - (T : ℂ) * I)) -
        (∫ u : ℝ in (-1)..1, smoothAFEZetaMellinIntegrand s x ((u : ℂ) + (T : ℂ) * I)) +
      I • (∫ v : ℝ in (-T)..T, smoothAFEZetaMellinIntegrand s x ((1 : ℂ) + (v : ℂ) * I))) -
      I • (∫ v : ℝ in (-T)..T, smoothAFEZetaMellinIntegrand s x ((-1 : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg _) hT
  have hρre : (1 - s).re = 1 - s.re := by simp
  have hρim : (1 - s).im = -s.im := by simp
  have habs := abs_lt.mp hT
  have hbox := rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box
    (s := s) (x := x) (a := -1) (b := 1) (T := T)
    hx hs (by norm_num) (by norm_num) hTpos
    (by rw [hρre]; linarith) (by rw [hρre]; linarith)
    (by rw [hρim]; linarith) (by rw [hρim]; linarith)
  simpa [rectIntegral] using! hbox

theorem tendsto_smoothAFEZetaMellinIntegrand_vertical_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} {c : ℝ} (hc : c ≠ 0) (hsc : s.re + c ≠ 1) :
    Tendsto
      (fun T : ℝ => ∫ v : ℝ in (-T)..T,
        smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (v : ℂ) * I))
      atTop
      (𝓝 (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x ((c : ℂ) + (v : ℂ) * I))) :=
  intervalIntegral_tendsto_integral
    (smoothAFEZetaMellinIntegrand_verticalIntegrable_general hx hc hsc)
    tendsto_neg_atTop_atBot tendsto_id

/-- **The infinite vertical-line contour identity at a general base point.** -/
theorem smoothAFEZetaMellin_infinite_contour_shift_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hre0 : 0 < s.re) (hre2 : s.re < 2) :
    I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  set F : ℂ → ℂ := smoothAFEZetaMellinIntegrand s x with hF
  have hre1 : s.re + (1 : ℝ) ≠ 1 := by intro h; linarith
  have hrem1 : s.re + (-1 : ℝ) ≠ 1 := by intro h; linarith
  have hright := tendsto_smoothAFEZetaMellinIntegrand_vertical_general (x := x) hx
    (c := (1 : ℝ)) (by norm_num) hre1
  have hleft := tendsto_smoothAFEZetaMellinIntegrand_vertical_general (x := x) hx
    (c := (-1 : ℝ)) (by norm_num) hrem1
  have htop0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_general hx s
    (ε := (1 : ℝ)) (by norm_num)
  have hbot0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_general hx s
    (ε := (-1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine htop0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine hbot0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [hF] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
    filter_upwards [eventually_gt_atTop |s.im|] with T hT
    simpa [hF] using smoothAFEZetaMellin_finite_contour_shift_general hx hs hre0 hre2 hT
  exact tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds

/-- **The exact Gaussian smooth AFE at a general base point.** -/
theorem riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hre0 : 0 < s.re) (hre2 : s.re < 2) :
    riemannZeta s =
      smoothAFEZetaMellinAt 1 s x - smoothAFEZetaDualMellinGeneral s x -
        smoothAFEZetaShiftedPoleResidue s x := by
  set R : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hR
  set L : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((-1 : ℝ) : ℂ) + (v : ℂ) * I) with hL
  set z : ℂ := riemannZeta s with hz
  set ρ : ℂ := smoothAFEZetaShiftedPoleResidue s x with hρ
  have hcontour := smoothAFEZetaMellin_infinite_contour_shift_general hx hs hre0 hre2
  have hcancel : R - L = (2 * Real.pi : ℂ) * (z + ρ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, z, ρ, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  unfold smoothAFEZetaMellinAt smoothAFEZetaDualMellinGeneral
  rw [Complex.real_smul, Complex.real_smul]
  change z = ((1 / (2 * Real.pi) : ℝ) : ℂ) * R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * L - ρ
  have hscale : (((1 / (2 * Real.pi) : ℝ) : ℂ)) = ((2 * Real.pi : ℂ) : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscale]
  symm
  calc
    (2 * Real.pi : ℂ)⁻¹ * R - (2 * Real.pi : ℂ)⁻¹ * L - ρ
        = (2 * Real.pi : ℂ)⁻¹ * (R - L) - ρ := by ring
    _ = (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) * (z + ρ)) - ρ := by rw [hcancel]
    _ = z := by
        rw [inv_mul_cancel_left₀ hpi]
        ring

/-- **The smooth AFE at a general base point, with the direct edge as a Dirichlet series.** -/
theorem riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1) (hre0 : 0 < s.re) (hre2 : s.re < 2) :
    riemannZeta s =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-s) * smoothAFECutoff ((n + 1 : ℝ) / x)) -
        smoothAFEZetaDualMellinGeneral s x -
        smoothAFEZetaShiftedPoleResidue s x := by
  rw [← smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff (s := s) (x := x) (c := 1)
    hx (by norm_num) (by linarith)]
  exact riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx hs hre0 hre2

end RHTower

end
