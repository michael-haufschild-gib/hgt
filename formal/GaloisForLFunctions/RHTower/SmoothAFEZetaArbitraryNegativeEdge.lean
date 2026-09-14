import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralEdge
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralVertical
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound

/-!
# Smooth AFE on an arbitrary negative edge

The existing movable-edge theorem restricted the depth to `c ≤ 1` only
because its horizontal Gaussian estimate was stated on `-1 ≤ Re w ≤ 1`.
The Gaussian argument works on every fixed rectangle.  This module removes
that artificial restriction and identifies every admissible negative edge
with the original edge `Re w = -1`.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- Gaussian-kernel bound on the arbitrary rectangle `-c ≤ Re w ≤ 1`. -/
theorem norm_smoothAFEGaussianKernel_horizontal_arbitrary_le
    {c u v : ℝ} (_hc : 0 < c) (huLow : -c ≤ u) (huHigh : u ≤ 1)
    (hv : 1 ≤ |v|) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp ((max c 1) ^ 2) * Real.exp (-(v ^ 2)) := by
  let B : ℝ := max c 1
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hcB : c ≤ B := le_max_left _ _
  have huAbs : |u| ≤ B := by
    rw [abs_le]
    constructor
    · linarith
    · exact huHigh.trans hB1
  have huSq : u ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - u), sq_nonneg (B + u)]
  let w : ℂ := (u : ℂ) + (v : ℂ) * I
  have hre : (w ^ 2).re = u ^ 2 - v ^ 2 := by
    dsimp only [w]
    rw [pow_two]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hwim : w.im = v := by simp [w]
  have hwnorm : (1 : ℝ) ≤ ‖w‖ := by
    calc
      (1 : ℝ) ≤ |v| := hv
      _ = |w.im| := by rw [hwim]
      _ ≤ ‖w‖ := Complex.abs_im_le_norm _
  have hnum : ‖Complex.exp (w ^ 2)‖ ≤
      Real.exp (B ^ 2) * Real.exp (-(v ^ 2)) := by
    rw [Complex.norm_exp, hre, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold smoothAFEGaussianKernel
  rw [norm_div]
  calc
    ‖Complex.exp (w ^ 2)‖ / ‖w‖
        ≤ (Real.exp (B ^ 2) * Real.exp (-(v ^ 2))) / ‖w‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ Real.exp (B ^ 2) * Real.exp (-(v ^ 2)) := by
      rw [div_le_iff₀ (zero_lt_one.trans_le hwnorm)]
      exact le_mul_of_one_le_right (by positivity) hwnorm
    _ = Real.exp ((max c 1) ^ 2) * Real.exp (-(v ^ 2)) := by rfl

/-- A positive Mellin power is uniformly bounded on `-c ≤ Re w ≤ 1`. -/
theorem norm_cpow_horizontal_arbitrary_le
    {x c u v : ℝ} (hx : 0 < x) (_hc : 0 < c)
    (huLow : -c ≤ u) (huHigh : u ≤ 1) :
    ‖(x : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp (max c 1 * |Real.log x|) := by
  let B : ℝ := max c 1
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hcB : c ≤ B := le_max_left _ _
  have huAbs : |u| ≤ B := by
    rw [abs_le]
    constructor
    · linarith
    · exact huHigh.trans hB1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    Real.log x * u ≤ |Real.log x * u| := le_abs_self _
    _ = |Real.log x| * |u| := abs_mul _ _
    _ ≤ |Real.log x| * B :=
      mul_le_mul_of_nonneg_left huAbs (abs_nonneg _)
    _ = max c 1 * |Real.log x| := by rw [mul_comm]

/-- Horizontal pointwise majorant on an arbitrary fixed negative rectangle. -/
theorem norm_smoothAFEZetaMellinIntegrand_arbitrary_edge_le
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (s : ℂ)
    {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ}
    (hC : ∀ σ t : ℝ, |σ| ≤ |s.re| + max c 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u v : ℝ} (huLow : -c ≤ u) (huHigh : u ≤ 1)
    (hv : |s.im| + 1 ≤ |v|) :
    ‖smoothAFEZetaMellinIntegrand s x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.exp (max c 1 * |Real.log x|) *
          Real.exp ((max c 1) ^ 2)) *
        ((|s.im| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
  let w : ℂ := (u : ℂ) + (v : ℂ) * I
  have hwre : w.re = u := by simp [w]
  have hwim : w.im = v := by simp [w]
  have hsre : (s + w).re = s.re + u := by rw [Complex.add_re, hwre]
  have hsim : (s + w).im = s.im + v := by rw [Complex.add_im, hwim]
  have hB1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have hcB : c ≤ max c 1 := le_max_left _ _
  have huAbs : |u| ≤ max c 1 := by
    rw [abs_le]
    constructor
    · linarith
    · exact huHigh.trans hB1
  have hzeta : ‖riemannZeta (s + w)‖ ≤ C * (|s.im| + |v|) ^ N := by
    have hrec : (((s + w).re : ℝ) : ℂ) + (((s + w).im : ℝ) : ℂ) * I = s + w :=
      Complex.re_add_im _
    have hreabs : |(s + w).re| ≤ |s.re| + max c 1 := by
      rw [hsre]
      linarith [abs_add_le s.re u]
    have himabs : |(s + w).im| ≤ |s.im| + |v| := by
      rw [hsim]
      exact abs_add_le _ _
    have himge : (1 : ℝ) ≤ |(s + w).im| := by
      rw [hsim]
      have hrev : |v| - |s.im| ≤ |s.im + v| := by
        have h := abs_sub_abs_le_abs_sub v (-s.im)
        simp only [abs_neg, sub_neg_eq_add] at h
        rw [add_comm v s.im] at h
        linarith
      linarith
    have hbase := hC (s + w).re (s + w).im hreabs himge
    rw [hrec] at hbase
    exact hbase.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) himabs N) hC0)
  have hpow := norm_cpow_horizontal_arbitrary_le hx hc huLow huHigh (v := v)
  have hv1 : (1 : ℝ) ≤ |v| := by linarith [abs_nonneg s.im]
  have hker := norm_smoothAFEGaussianKernel_horizontal_arbitrary_le hc huLow huHigh
    hv1
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  have hpow0 : (0 : ℝ) ≤ Real.exp (max c 1 * |Real.log x|) := (Real.exp_pos _).le
  have hz0 : (0 : ℝ) ≤ C * (|s.im| + |v|) ^ N := by positivity
  calc
    ‖riemannZeta (s + w)‖ *
          ‖(x : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
      ≤ (C * (|s.im| + |v|) ^ N) *
          Real.exp (max c 1 * |Real.log x|) *
            (Real.exp ((max c 1) ^ 2) * Real.exp (-(v ^ 2))) := by
        exact mul_le_mul
          (mul_le_mul hzeta (by simpa only [w] using hpow)
            (norm_nonneg _) hz0)
          (by simpa only [w] using hker) (norm_nonneg _)
          (mul_nonneg hz0 hpow0)
    _ = (C * Real.exp (max c 1 * |Real.log x|) *
          Real.exp ((max c 1) ^ 2)) *
        ((|s.im| + |v|) ^ N * Real.exp (-(v ^ 2))) := by ring

/-- Both horizontal sides vanish for every fixed negative depth `c > 0`. -/
theorem tendsto_smoothAFEZetaMellinIntegrand_horizontal_arbitrary_edge
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (s : ℂ)
    {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-c)..1,
        smoothAFEZetaMellinIntegrand s x
          ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC0, hC⟩ :=
    exists_bound_norm_riemannZeta_strip (|s.re| + max c 1)
  let K : ℝ := C * Real.exp (max c 1 * |Real.log x|) *
    Real.exp ((max c 1) ^ 2)
  have hK0 : (0 : ℝ) ≤ K := by dsimp only [K]; positivity
  have hlen0 : (0 : ℝ) ≤ 1 + c := by linarith
  have hlim : Tendsto
      (fun T : ℝ => (1 + c) *
        (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))))) atTop (𝓝 0) := by
    have h := (tendsto_shifted_pow_mul_exp_neg_sq |s.im| N).const_mul K
    simpa using h.const_mul (1 + c)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (|s.im| + 1)] with T hT
  have hT0 : (0 : ℝ) < T := by linarith [abs_nonneg s.im]
  have habsv : |ε * T| = T := by
    rw [abs_mul, hε, one_mul, abs_of_pos hT0]
  have hpoint : ∀ u ∈ Set.uIoc (-c : ℝ) 1,
      ‖smoothAFEZetaMellinIntegrand s x
        ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤
        K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : (-c : ℝ) ≤ 1)] at hu
    have hb := norm_smoothAFEZetaMellinIntegrand_arbitrary_edge_le
      hx hc s hC0 hC (le_of_lt hu.1) hu.2 (by rw [habsv]; exact hT)
    rw [habsv] at hb
    have hsq : (ε * T) ^ 2 = T ^ 2 := by
      have h1 : (ε * T) ^ 2 = ε ^ 2 * T ^ 2 := by ring
      rw [h1, show ε ^ 2 = |ε| ^ 2 by rw [sq_abs], hε]
      ring
    rw [hsq] at hb
    exact hb
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |(1 : ℝ) - (-c)| = 1 + c := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < (1 : ℝ) - (-c))]
    ring
  rw [habs] at hint
  calc
    ‖∫ u : ℝ in (-c : ℝ)..1,
        smoothAFEZetaMellinIntegrand s x
          ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2))) * (1 + c) := hint
    _ = (1 + c) *
        (K * ((|s.im| + T) ^ N * Real.exp (-(T ^ 2)))) := by ring

/-- Infinite smooth-AFE contour identity at every negative depth `c > 0`. -/
theorem smoothAFEZetaMellin_infinite_contour_shift_arbitrary_edge
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {s : ℂ} (hs : s ≠ 1)
    (hre0 : 0 < s.re) (hrec : s.re < 1 + c) :
    I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
          (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        I • (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
          (((-c : ℝ) : ℂ) + (v : ℂ) * I)) =
      2 * Real.pi * I *
        (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
  set F : ℂ → ℂ := smoothAFEZetaMellinIntegrand s x with hF
  have hleft' : -c < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hright' : (1 - s).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hre1 : s.re + (1 : ℝ) ≠ 1 := by intro h; linarith
  have hremc : s.re + (-c : ℝ) ≠ 1 := by intro h; linarith
  have hright := tendsto_smoothAFEZetaMellinIntegrand_vertical_general
    (x := x) hx (c := (1 : ℝ)) (by norm_num) hre1
  have hleftv := tendsto_smoothAFEZetaMellinIntegrand_vertical_general
    (x := x) hx (c := (-c : ℝ)) (by linarith) hremc
  have htop0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_arbitrary_edge
    hx hc s (ε := (1 : ℝ)) (by norm_num)
  have hbot0 := tendsto_smoothAFEZetaMellinIntegrand_horizontal_arbitrary_edge
    hx hc s (ε := (-1 : ℝ)) (by norm_num)
  have htop : Tendsto
      (fun T : ℝ => ∫ u : ℝ in (-c)..1, F ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine htop0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hbottom : Tendsto
      (fun T : ℝ => ∫ u : ℝ in (-c)..1, F ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine hbot0.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    push_cast
    ring
  have hlimit :=
    ((hbottom.sub htop).add (hright.const_smul I)).sub (hleftv.const_smul I)
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
        2 * Real.pi * I *
          (riemannZeta s + smoothAFEZetaShiftedPoleResidue s x) := by
    filter_upwards [eventually_gt_atTop |s.im|] with T hT
    simpa [hF] using
      smoothAFEZetaMellin_finite_contour_shift_edge hx hc hs hleft' hright' hT
  exact tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds

/-- Exact smooth AFE with no artificial upper bound on the negative-edge depth. -/
theorem riemannZeta_eq_smoothAFEZetaMellin_sub_arbitrary_dualEdge_sub_residue
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {s : ℂ} (hs : s ≠ 1)
    (hre0 : 0 < s.re) (hrec : s.re < 1 + c) :
    riemannZeta s =
      smoothAFEZetaMellinAt 1 s x - smoothAFEZetaDualMellinEdge s x c -
        smoothAFEZetaShiftedPoleResidue s x := by
  let R : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
    (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
    (((-c : ℝ) : ℂ) + (v : ℂ) * I)
  let z : ℂ := riemannZeta s
  let rho : ℂ := smoothAFEZetaShiftedPoleResidue s x
  have hcontour := smoothAFEZetaMellin_infinite_contour_shift_arbitrary_edge
    hx hc hs hre0 hrec
  have hcancel : R - L = (2 * Real.pi : ℂ) * (z + rho) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [R, L, z, rho, smul_eq_mul, mul_sub, mul_assoc, mul_left_comm,
      mul_comm] using hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  unfold smoothAFEZetaMellinAt smoothAFEZetaDualMellinEdge
  rw [Complex.real_smul, Complex.real_smul]
  change z = ((1 / (2 * Real.pi) : ℝ) : ℂ) * R -
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * L - rho
  have hscale : (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
      ((2 * Real.pi : ℂ) : ℂ)⁻¹ := by
    push_cast
    rw [one_div]
  rw [hscale]
  symm
  calc
    (2 * Real.pi : ℂ)⁻¹ * R - (2 * Real.pi : ℂ)⁻¹ * L - rho
        = (2 * Real.pi : ℂ)⁻¹ * (R - L) - rho := by ring
    _ = (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) * (z + rho)) - rho := by
      rw [hcancel]
    _ = z := by
      rw [inv_mul_cancel_left₀ hpi]
      ring

/-- Every admissible negative edge gives the same normalized dual integral as `Re w = -1`. -/
theorem smoothAFEZetaDualMellinEdge_eq_left_one
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {s : ℂ} (hs : s ≠ 1)
    (hre0 : 0 < s.re) (hreTwo : s.re < 2) (hrec : s.re < 1 + c) :
    smoothAFEZetaDualMellinEdge s x c = smoothAFEZetaDualMellinEdge s x 1 := by
  have hcEdge :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_arbitrary_dualEdge_sub_residue
      hx hc hs hre0 hrec
  have hOne := riemannZeta_eq_smoothAFEZetaMellin_sub_dualEdge_sub_residue
    hx (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
      hs hre0 (by linarith)
  exact sub_right_inj.mp (sub_left_inj.mp (hcEdge.symm.trans hOne))

/-- On the displaced Levinson line, depth `4-d` fixes `Re(s+w)=-7/2` while
leaving the exact dual integral unchanged. -/
theorem smoothAFEZetaDualMellinEdge_displaced_deep_eq_left_one
    {x d tau : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    smoothAFEZetaDualMellinEdge (displacedLinePt d tau) x (4 - d) =
      smoothAFEZetaDualMellinEdge (displacedLinePt d tau) x 1 := by
  apply smoothAFEZetaDualMellinEdge_eq_left_one hx (by linarith)
  · intro h
    have hre := congrArg Complex.re h
    rw [displacedLinePt_re] at hre
    norm_num at hre
    linarith
  · rw [displacedLinePt_re]
    linarith
  · rw [displacedLinePt_re]
    linarith
  · rw [displacedLinePt_re]
    linarith

end RHTower
