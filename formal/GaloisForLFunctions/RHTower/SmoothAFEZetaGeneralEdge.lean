import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneral

/-!
# The smooth AFE with a movable left edge

The reflected edge of the Gaussian smooth AFE is taken at `Re w = -1` in the corpus.  For the
expansion of that edge into a dual Dirichlet series one needs `Re(1-s-w) > 1`, i.e. the edge
abscissa to exceed `Re s`, *and* one needs `Re(s+w)` to stay inside the strip on which the
functional-equation factor `χ` is controlled.  Both are arranged by moving the edge to `Re w = -c`
with `Re s < c ≤ Re s + 1/2`.

Only the contour abscissa changes; the horizontal decay, the vertical integrability and the
two-pole rectangle identity are already available at a general base point.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- Normalized reflected Mellin integral on the edge `Re w = -c`. -/
def smoothAFEZetaDualMellinEdge (s : ℂ) (x c : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaMellinIntegrand s x (((-c : ℝ) : ℂ) + (v : ℂ) * I)

theorem tendsto_smoothAFEZetaMellinIntegrand_horizontal_edge
    {x c : ℝ} (hx : 0 < x) (hc0 : 0 < c) (hc1 : c ≤ 1) (s : ℂ) {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-c)..1,
        smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|s.re| + 1)
  set K : ℝ := C * max x x⁻¹ * Real.exp 1 with hK
  have hK0 : (0 : ℝ) ≤ K := by
    have hmax : (0 : ℝ) ≤ max x x⁻¹ := le_trans hx.le (le_max_left _ _)
    have := Real.exp_pos (1 : ℝ)
    positivity
  have hlim : Tendsto (fun T : ℝ => 2 * (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2)))))
      atTop (𝓝 0) := by
    have h := (tendsto_shifted_pow_mul_exp_neg_sq |s.im| N).const_mul K
    simpa using h.const_mul (2 : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (|s.im| + 1)] with T hT
  have hsim0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hT0 : (0 : ℝ) < T := by linarith
  have habsv : |ε * T| = T := by
    rw [abs_mul, hε, one_mul, abs_of_pos hT0]
  have hpoint : ∀ u ∈ Set.uIoc (-c : ℝ) 1,
      ‖smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : (-c : ℝ) ≤ 1)] at hu
    have hulow : (-1 : ℝ) ≤ u := by
      have := hu.1
      linarith
    have hbound := norm_smoothAFEZetaMellinIntegrand_general_le hx s hC0 hC
      (u := u) (v := ε * T) hulow hu.2 (by rw [habsv]; linarith)
    rw [habsv] at hbound
    have hsq : (ε * T) ^ 2 = T ^ 2 := by
      have h1 : (ε * T) ^ 2 = ε ^ 2 * T ^ 2 := by ring
      rw [h1, show ε ^ 2 = |ε| ^ 2 by rw [sq_abs], hε]
      ring
    rw [hsq] at hbound
    exact hbound
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |(1 : ℝ) - (-c)| = 1 + c := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < (1 : ℝ) - (-c))]
    ring
  rw [habs] at h
  have hlen : (1 : ℝ) + c ≤ 2 := by linarith
  have hnn : (0 : ℝ) ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by
    have : (0 : ℝ) ≤ (|s.im| + T) ^ N := by positivity
    positivity
  calc ‖∫ u : ℝ in (-c : ℝ)..1,
        smoothAFEZetaMellinIntegrand s x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) * (1 + c) := h
    _ ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) * 2 :=
        mul_le_mul_of_nonneg_left hlen hnn
    _ = 2 * (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2)))) := by ring

/-- **The finite two-pole rectangle identity with the left edge at `-c`.** -/
theorem smoothAFEZetaMellin_finite_contour_shift_edge
    {x T c : ℝ} (hx : 0 < x) (hc0 : 0 < c) {s : ℂ} (hs : s ≠ 1)
    (hleft : -c < (1 - s).re) (hright : (1 - s).re < 1) (hT : |s.im| < T) :
    ((∫ u : ℝ in (-c)..1, smoothAFEZetaMellinIntegrand s x ((u : ℂ) - (T : ℂ) * I)) -
        (∫ u : ℝ in (-c)..1, smoothAFEZetaMellinIntegrand s x ((u : ℂ) + (T : ℂ) * I)) +
      I • (∫ v : ℝ in (-T)..T, smoothAFEZetaMellinIntegrand s x ((1 : ℂ) + (v : ℂ) * I))) -
      I • (∫ v : ℝ in (-T)..T, smoothAFEZetaMellinIntegrand s x (((-c : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg _) hT
  have hρim : (1 - s).im = -s.im := by simp
  have habs := abs_lt.mp hT
  have hbox := rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box
    (s := s) (x := x) (a := -c) (b := 1) (T := T)
    hx hs (by linarith) (by norm_num) hTpos hleft hright
    (by rw [hρim]; linarith) (by rw [hρim]; linarith)
  simpa [rectIntegral] using! hbox

/-- **The infinite contour identity with the left edge at `-c`.** -/
theorem smoothAFEZetaMellin_infinite_contour_shift_edge
    {x c : ℝ} (hx : 0 < x) (hc0 : 0 < c) (hc1 : c ≤ 1) {s : ℂ} (hs : s ≠ 1)
    (hre0 : 0 < s.re) (hrec : s.re < 1 + c) :
    I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((-c : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  set F : ℂ → ℂ := smoothAFEZetaMellinIntegrand s x with hF
  have hleft' : -c < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hright' : (1 - s).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hre1 : s.re + (1 : ℝ) ≠ 1 := by intro h; linarith
  have hrem1 : s.re + (-c : ℝ) ≠ 1 := by intro h; linarith
  have hright := tendsto_smoothAFEZetaMellinIntegrand_vertical_general (x := x) hx
    (c := (1 : ℝ)) (by norm_num) hre1
  have hleftv := tendsto_smoothAFEZetaMellinIntegrand_vertical_general (x := x) hx
    (c := (-c : ℝ)) (by linarith) hrem1
  have htop0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_edge hx hc0 hc1 s
    (ε := (1 : ℝ)) (by norm_num)
  have hbot0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_edge hx hc0 hc1 s
    (ε := (-1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-c)..1, F ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine htop0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (-c)..1, F ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine hbot0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleftv.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (-c)..1, F ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (-c)..1, F ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, F (((-c : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, F (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, F (((-c : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [hF] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-c)..1, F ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-c)..1, F ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, F (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, F (((-c : ℝ) : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
    filter_upwards [eventually_gt_atTop |s.im|] with T hT
    simpa [hF] using smoothAFEZetaMellin_finite_contour_shift_edge hx hc0 hs hleft' hright' hT
  exact tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds

/-- **The exact smooth AFE with the reflected edge taken at `-c`.** -/
theorem riemannZeta_eq_smoothAFEZetaMellin_sub_dualEdge_sub_residue
    {x c : ℝ} (hx : 0 < x) (hc0 : 0 < c) (hc1 : c ≤ 1) {s : ℂ} (hs : s ≠ 1)
    (hre0 : 0 < s.re) (hrec : s.re < 1 + c) :
    riemannZeta s =
      smoothAFEZetaMellinAt 1 s x - smoothAFEZetaDualMellinEdge s x c -
        smoothAFEZetaShiftedPoleResidue s x := by
  set R : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hR
  set L : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x (((-c : ℝ) : ℂ) + (v : ℂ) * I) with hL
  set z : ℂ := riemannZeta s with hz
  set ρ : ℂ := smoothAFEZetaShiftedPoleResidue s x with hρ
  have hcontour := smoothAFEZetaMellin_infinite_contour_shift_edge hx hc0 hc1 hs hre0 hrec
  have hcancel : R - L = (2 * Real.pi : ℂ) * (z + ρ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, z, ρ, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  unfold smoothAFEZetaMellinAt smoothAFEZetaDualMellinEdge
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

end RHTower

end
