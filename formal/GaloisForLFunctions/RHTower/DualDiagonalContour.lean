import GaloisForLFunctions.RHTower.DualDiagonalMellin
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound

/-!
# The smoothed dual diagonal: contour shift and asymptotic

The dual diagonal integrand `F̃(w) = χ(s₁−w)χ(s₂−w)(cx)^{-w}e^{w²}/w · ζ(1+2d+2w)` is moved from
`Re w = 1` to `Re w = −1/4`, crossing the kernel pole (residue `χ(s₁)χ(s₂)ζ(1+2d)`) and the zeta
pole at `−d` (residue `−(cx)^d e^{d²}/(2d)`).  On the left line both `χ` arguments sit on the
abscissa `¾ − d ∈ [½, ¾]`, where `‖χ(σ+it)‖ ≤ C(1+|t|)^{-(σ−½)}`; transferring that decay from the
heights `τ ∓ v` to `τ` and integrating the Gaussian gives the remainder

`‖(1/2π)∫_{Re w = −¼} F̃‖ ≤ K (cx)^{1/4} (1+|τ|)^{-(½−2d)}`,

with `K` independent of `d ∈ (0, ⅛]`, `c`, `x`, `τ`.  Hence

`Σ_j (j+1)^{-(1+2d)} χ(s₁)χ(s₂)W((j+1)²cx) = χ(s₁)χ(s₂)ζ(1+2d) − (cx)^d e^{d²}/(2d) + O((cx)^{1/4}τ^{2d−½})`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-! ## Decay of `χ` on the right strip `½ ≤ σ ≤ ¾`, at every height -/

theorem exists_norm_zetaChi_le_rightStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  -- the compact part
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (1 / 2 : ℝ) (3 / 4) ×ˢ Set.Icc (-256 : ℝ) 256)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn zetaChi K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hG : Gammaℝ (1 - ((p.1 : ℂ) + (p.2 : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp
      linarith [hp.1.2]
    exact (zetaChi_analyticAt hG).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  set A : ℝ := Real.exp ((1 / 4) * (Real.log Real.pi + Real.log 2 + 2)) with hAdef
  refine ⟨max C₀ 0 * 257 + 2 * A, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have ha0 : 0 ≤ σ - 1 / 2 := by linarith
  have ha1 : σ - 1 / 2 ≤ 1 / 4 := by linarith
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  rcases le_or_gt 256 |t| with ht | ht
  · -- large height: the corpus decay along the right lines
    have hσ' : σ < 1 := by linarith
    have h := norm_zetaChi_le_right_line_rpow hσ1 hσ' ht
    rw [norm_zetaChi_real_add_im_eq_abs]
    refine h.trans ?_
    have hlog : 0 ≤ Real.log Real.pi + Real.log 2 + 2 := by
      have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hexp : Real.exp ((σ - 1 / 2) * (Real.log Real.pi + Real.log 2 + 2)) ≤ A := by
      rw [hAdef]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right ha1 hlog
    -- `|t|^{-a} ≤ 2 (1+|t|)^{-a}` since `1 + |t| ≤ 2|t|`
    have hrpow : |t| ^ (-(σ - 1 / 2)) ≤ 2 * (1 + |t|) ^ (-(σ - 1 / 2)) := by
      have h2 : 1 + |t| ≤ 2 * |t| := by linarith
      have h3 : (2 * |t|) ^ (-(σ - 1 / 2)) ≤ (1 + |t|) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos h2 (by linarith)
      rw [Real.mul_rpow (by norm_num) (abs_nonneg t)] at h3
      have h4 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(σ - 1 / 2)) := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : -(1 / 4 : ℝ) ≤ -(σ - 1 / 2))
        have h5 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
          rw [Real.rpow_neg (by norm_num), one_div]
          refine inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) ?_
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        linarith
      have h6 : 0 ≤ |t| ^ (-(σ - 1 / 2)) := by positivity
      nlinarith
    calc Real.exp ((σ - 1 / 2) * (Real.log Real.pi + Real.log 2 + 2)) * |t| ^ (-(σ - 1 / 2))
        ≤ A * |t| ^ (-(σ - 1 / 2)) := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ A * (2 * (1 + |t|) ^ (-(σ - 1 / 2))) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ (max C₀ 0 * 257 + 2 * A) * (1 + |t|) ^ (-(σ - 1 / 2)) := by
          have : 0 ≤ max C₀ 0 * 257 := by positivity
          nlinarith [(by positivity : (0 : ℝ) ≤ (1 + |t|) ^ (-(σ - 1 / 2)))]
  · -- small height: the compact bound, transferred through `(1+|t|)^{-a} ≥ 257^{-1/4}`
    have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ1, hσ2⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩, rfl⟩
    have h := hC₀ _ hmem
    have hlow : (1 : ℝ) / 257 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by
      have h1 : (1 + |t|) ^ (-(σ - 1 / 2)) ≥ (257 : ℝ) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
      have h2 : (257 : ℝ) ^ (-(σ - 1 / 2)) ≥ (257 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith [show (257 : ℝ)⁻¹ = 1 / 257 by norm_num]
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ max C₀ 0 := le_max_left _ _
      _ = (max C₀ 0 * 257) * (1 / 257) := by ring
      _ ≤ (max C₀ 0 * 257) * (1 + |t|) ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (max C₀ 0 * 257 + 2 * A) * (1 + |t|) ^ (-(σ - 1 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [(by positivity : (0 : ℝ) ≤ A)]


/-! ## Pointwise bounds on the dual integrand -/

theorem norm_cpow_ofReal_neg_le {b : ℝ} (hb : 0 < b) {u : ℝ} (hu1 : -(1 / 4) ≤ u) (hu2 : u ≤ 1)
    (t : ℝ) :
    ‖((b : ℝ) : ℂ) ^ (-((u : ℂ) + (t : ℂ) * I))‖ ≤ max (b ^ (1 / 4 : ℝ)) (b ^ (-(1 : ℝ))) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  rcases le_or_gt 1 b with hb1 | hb1
  · calc b ^ (-u) ≤ b ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      _ ≤ max (b ^ (1 / 4 : ℝ)) (b ^ (-(1 : ℝ))) := le_max_left _ _
  · calc b ^ (-u) ≤ b ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hb hb1.le (by linarith)
      _ ≤ max (b ^ (1 / 4 : ℝ)) (b ^ (-(1 : ℝ))) := le_max_right _ _

/-- The dual integrand on a horizontal edge `u ± iT`, `−1/4 ≤ u ≤ 1`, `T ≥ T₀ + |τ| + 1`. -/
theorem norm_dualDiagonalIntegrand_horizontal_le {d c x τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} {Nχ Nζ : ℕ} {T₀ : ℝ} (hCχ : 0 ≤ Cχ)
    (hCζ : 0 ≤ Cζ)
    (hχ : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 1 → T₀ ≤ |s.im| → ‖zetaChi s‖ ≤ Cχ * (1 + |s.im|) ^ Nχ)
    (hζ : ∀ σ t : ℝ, |σ| ≤ 4 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * |t| ^ Nζ)
    {u T : ℝ} (hu1 : -(1 / 4) ≤ u) (hu2 : u ≤ 1) (hT : max T₀ 0 + |τ| + 1 ≤ T) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (-(1 : ℝ))) * Real.exp 1)
          * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hT1 : 1 ≤ T := by linarith [abs_nonneg τ, le_max_right T₀ 0]
  have hT0' : 0 ≤ T := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  -- the two chi factors: heights `τ − εT`, `−τ − εT`, both at least `T − |τ| ≥ T₀`
  have hheight : ∀ σ : ℝ, |σ| ≤ |τ| → T₀ ≤ |σ - ε * T| ∧ |σ - ε * T| ≤ |τ| + T := by
    intro σ hσ
    have h1 : |σ - ε * T| ≤ |σ| + |ε * T| := abs_sub _ _
    have h2 : |ε * T| = T := by rw [abs_mul, hεabs, one_mul, abs_of_nonneg hT0']
    have h3 : |ε * T| - |σ| ≤ |σ - ε * T| := by
      have := abs_sub_abs_le_abs_sub (ε * T) σ
      rw [abs_sub_comm] at this
      linarith
    constructor
    · rw [h2] at h3; linarith [le_max_left T₀ 0]
    · rw [h2] at h1; linarith
  have hχbound : ∀ σ : ℝ, |σ| ≤ |τ| →
      ‖zetaChi (displacedLinePt d σ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        ≤ Cχ * (1 + |τ| + T) ^ Nχ := by
    intro σ hσ
    obtain ⟨hlow, hup⟩ := hheight σ hσ
    have harg : displacedLinePt d σ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
        = ((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I)
      (by simp; linarith) (by simp; linarith) (by simp; exact hlow)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ hCχ
    apply pow_le_pow_left₀ (by positivity) _ Nχ
    linarith
  have h1 := hχbound τ le_rfl
  have h2 := hχbound (-τ) (by rw [abs_neg])
  -- the power factor
  have hp := norm_cpow_ofReal_neg_le (mul_pos hc hx) hu1 hu2 (ε * T)
  -- the kernel
  have hk : ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
    rw [norm_smoothAFEGaussianKernel_eq_contour]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    have hnorm : T ≤ ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
      rw [abs_mul, hεabs, one_mul, abs_of_nonneg hT0'] at this
      exact this
    have hu2' : u ^ 2 ≤ 1 := by nlinarith
    have hsq : (ε * T) ^ 2 = T ^ 2 := by rw [mul_pow, hεsq, one_mul]
    rw [hsq]
    calc Real.exp (u ^ 2 - T ^ 2) / ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖
        ≤ Real.exp (u ^ 2 - T ^ 2) / 1 := by
          apply div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos
          linarith
      _ = Real.exp (u ^ 2) * Real.exp (-(T ^ 2)) := by rw [div_one, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu2') (Real.exp_pos _).le
  -- the zeta factor
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ Cζ * 2 ^ Nζ * (1 + |τ| + T) ^ Nζ := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        = ((1 + 2 * d + 2 * u : ℝ) : ℂ) + ((2 * (ε * T) : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    have h := hζ (1 + 2 * d + 2 * u) (2 * (ε * T)) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_nonneg hT0']; linarith)
    rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hT0',
      one_mul] at h
    refine h.trans ?_
    rw [mul_pow, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCζ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ hT0' _ Nζ
    linarith [abs_nonneg τ]
  have hpow : (1 + |τ| + T) ^ Nχ * (1 + |τ| + T) ^ Nχ * (1 + |τ| + T) ^ Nζ
      = (1 + |τ| + T) ^ (2 * Nχ + Nζ) := by
    rw [← pow_add, ← pow_add, two_mul]
  calc ‖zetaChi (displacedLinePt d τ - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ (Cχ * (1 + |τ| + T) ^ Nχ) * (Cχ * (1 + |τ| + T) ^ Nχ)
          * (max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (-(1 : ℝ)))
            * (Real.exp 1 * Real.exp (-(T ^ 2))))
          * (Cζ * 2 ^ Nζ * (1 + |τ| + T) ^ Nζ) := by
        gcongr
    _ = (Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (-(1 : ℝ))) * Real.exp 1)
          * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
        rw [← hpow]; ring

/-- Transfer of decay from height `τ − v` to height `τ`. -/
theorem one_add_abs_sub_rpow_neg_le {a : ℝ} (ha : 0 ≤ a) (τ v : ℝ) :
    (1 + |τ - v|) ^ (-a) ≤ (1 + |v|) ^ a * (1 + |τ|) ^ (-a) := by
  have h : 1 + |τ| ≤ (1 + |τ - v|) * (1 + |v|) := by
    have h2 : |τ| ≤ |τ - v| + |v| := by
      have := abs_add_le (τ - v) v
      rw [sub_add_cancel] at this
      exact this
    nlinarith [abs_nonneg τ, abs_nonneg v, abs_nonneg (τ - v)]
  have h1 : ((1 + |τ - v|) * (1 + |v|)) ^ (-a) ≤ (1 + |τ|) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |v|)]
    at h1
  have hv : 0 < (1 + |v|) ^ a := by positivity
  calc (1 + |τ - v|) ^ (-a) = ((1 + |τ - v|) ^ (-a) * ((1 + |v|) ^ a)⁻¹) * (1 + |v|) ^ a := by
        field_simp
    _ ≤ (1 + |τ|) ^ (-a) * (1 + |v|) ^ a := mul_le_mul_of_nonneg_right h1 hv.le
    _ = (1 + |v|) ^ a * (1 + |τ|) ^ (-a) := by ring

/-- The dual integrand on the left line `Re w = −1/4`. -/
theorem norm_dualDiagonalIntegrand_left_le {d c x τ : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2)
    (v : ℝ) :
    ‖dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
  have ha0 : (0 : ℝ) ≤ 1 / 4 - d := by linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  -- chi factors with decay
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        ≤ Cχ * ((1 + |v|) ^ (1 / 4 - d) * (1 + |τ|) ^ (-(1 / 4 - d))) := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)
        = ((3 / 4 - d : ℝ) : ℂ) + ((σ - v : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (3 / 4 - d) (σ - v) (by linarith) (by linarith)
    rw [show (3 / 4 - d - 1 / 2 : ℝ) = 1 / 4 - d by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCχ)
    -- `(1+|σ−v|)^{-a} ≤ (1+|v|)^a (1+|σ|)^{-a} ≤ (1+|v|)^a (1+|τ|)^{-a}` needs `|σ| = |τ|`:
    -- both uses have `|σ| = |τ|` (σ = ±τ), so transfer through `|σ|` and compare.
    have htr := one_add_abs_sub_rpow_neg_le ha0 σ v
    refine htr.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  -- power
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖ = (c * x) ^ (1 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp
  -- kernel
  have hk : ‖smoothAFEGaussianKernel ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ 4 * Real.exp (1 / 16) * Real.exp (-(v ^ 2)) := by
    rw [norm_smoothAFEGaussianKernel_eq_contour]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    have hnorm : (1 / 4 : ℝ) ≤ ‖(((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)
      rw [show ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I).re = -(1 / 4) by simp, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at this
      exact this
    calc Real.exp ((-(1 / 4)) ^ 2 - v ^ 2) / ‖(((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I‖
        ≤ Real.exp ((-(1 / 4)) ^ 2 - v ^ 2) / (1 / 4) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
      _ = 4 * Real.exp (1 / 16) * Real.exp (-(v ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add,
            show ((-(1 / 4) : ℝ)) ^ 2 - v ^ 2 = 1 / 16 + -(v ^ 2) by ring]
          field_simp
  -- zeta
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ Cζ * (1 + |2 * v|) ^ 2 := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))
        = ((1 / 2 + 2 * d : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    exact hζ (1 / 2 + 2 * d) (2 * v) (by linarith) (by linarith)
  -- combine the frequency powers: `(1+|v|)^{2a} (1+|2v|)^(2 : ℕ) ≤ 4 (1+|v|)^(3 : ℕ)`
  have hva : (1 + |v|) ^ (1 / 4 - d) * (1 + |v|) ^ (1 / 4 - d) ≤ 1 + |v| := by
    rw [← Real.rpow_add (by positivity)]
    calc (1 + |v|) ^ (1 / 4 - d + (1 / 4 - d)) ≤ (1 + |v|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by linarith)
      _ = 1 + |v| := Real.rpow_one _
  have h2v : (1 + |2 * v|) ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by
    have : 1 + |2 * v| ≤ 2 * (1 + |v|) := by rw [abs_mul, abs_two]; linarith
    calc (1 + |2 * v|) ^ 2 ≤ (2 * (1 + |v|)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 4 * (1 + |v|) ^ 2 := by ring
  have hτa : (1 + |τ|) ^ (-(1 / 4 - d)) * (1 + |τ|) ^ (-(1 / 4 - d)) = (1 + |τ|) ^ (-(1 / 2 - 2 * d)) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖zetaChi (displacedLinePt d τ - ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ (Cχ * ((1 + |v|) ^ (1 / 4 - d) * (1 + |τ|) ^ (-(1 / 4 - d))))
          * (Cχ * ((1 + |v|) ^ (1 / 4 - d) * (1 + |τ|) ^ (-(1 / 4 - d))))
          * ((c * x) ^ (1 / 4 : ℝ) * (4 * Real.exp (1 / 16) * Real.exp (-(v ^ 2))))
          * (Cζ * (1 + |2 * v|) ^ 2) := by
        rw [hp]
        gcongr
    _ = (Cχ * Cχ * Cζ * (4 * Real.exp (1 / 16))) * (c * x) ^ (1 / 4 : ℝ)
          * ((1 + |τ|) ^ (-(1 / 4 - d)) * (1 + |τ|) ^ (-(1 / 4 - d)))
          * (((1 + |v|) ^ (1 / 4 - d) * (1 + |v|) ^ (1 / 4 - d)) * (1 + |2 * v|) ^ 2
              * Real.exp (-(v ^ 2))) := by ring
    _ ≤ (Cχ * Cχ * Cζ * (4 * Real.exp (1 / 16))) * (c * x) ^ (1 / 4 : ℝ)
          * ((1 + |τ|) ^ (-(1 / 4 - d)) * (1 + |τ|) ^ (-(1 / 4 - d)))
          * ((1 + |v|) * (4 * (1 + |v|) ^ 2) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hva h2v (by positivity) (by positivity)
    _ = (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
        rw [hτa]; ring

/-! ## Continuity and integrability on vertical lines -/

theorem continuous_dualDiagonalIntegrand_line {d c x τ : ℝ} (hc : 0 < c) (hx : 0 < x) {u : ℝ}
    (hu0 : u ≠ 0) (hu : -(1 / 2) - d < u) (hpole : 1 + 2 * d + 2 * u ≠ 1) :
    Continuous (fun v : ℝ => dualDiagonalIntegrand d c x τ ((u : ℂ) + (v : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hline : ContinuousAt (fun v : ℝ => (u : ℂ) + (v : ℂ) * I) v := by fun_prop
  have hw0 : (u : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hu0 this
  have hw : -(1 / 2) - d < ((u : ℂ) + (v : ℂ) * I).re := by simp; linarith
  have hcar : AnalyticAt ℂ (carrierIntegrand d τ (c * x)) ((u : ℂ) + (v : ℂ) * I) :=
    ((analyticAt_zetaChi_displaced_sub d τ hw).mul (analyticAt_zetaChi_displaced_sub d (-τ) hw)).mul
      (analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hw0)
  have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + (v : ℂ) * I)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hpole (by linarith)
  have hz : ContinuousAt (fun v : ℝ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + (v : ℂ) * I))) v :=
    ContinuousAt.comp (g := riemannZeta)
      (f := fun v : ℝ => (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + (v : ℂ) * I)))
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  exact (ContinuousAt.comp (f := fun v : ℝ => (u : ℂ) + (v : ℂ) * I) hcar.continuousAt hline).mul hz

theorem integrable_dualDiagonalIntegrand_right {d c x τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ => dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have hcar := integrable_carrierIntegrand_one_line hd hd4 (mul_pos hc hx) τ
  have hcont := continuous_dualDiagonalIntegrand_line (d := d) (τ := τ) hc hx (u := 1) one_ne_zero
    (by linarith) (by linarith)
  refine Integrable.mono' (hcar.norm.const_mul (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  unfold dualDiagonalIntegrand
  rw [norm_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply norm_riemannZeta_le_of_two_le_re_tsum
  simp
  linarith

theorem integrable_one_add_abs_cube_mul_exp_neg_sq :
    Integrable (fun v : ℝ => (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
  GaloisForLFunctions.HTGeometry.integrable_one_add_abs_pow_mul_exp_neg_sq 3

theorem integrable_dualDiagonalIntegrand_left {d c x τ : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ => dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hcont := continuous_dualDiagonalIntegrand_line (d := d) (τ := τ) hc hx (u := -(1 / 4))
    (by norm_num) (by linarith) (by linarith)
  refine Integrable.mono' (integrable_one_add_abs_cube_mul_exp_neg_sq.const_mul
    ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d))))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  exact norm_dualDiagonalIntegrand_left_le hd hd8 hc hx hCχ hCζ hχ hζ v

/-! ## The rectangle and its horizontal edges -/

theorem rectIntegral_dualDiagonalIntegrand_eq {d c x τ T : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) (hT : 0 < T) :
    rectIntegral (dualDiagonalIntegrand d c x τ) (((-(1 / 4) : ℝ) : ℂ) - (T : ℂ) * I)
        (((1 : ℝ) : ℂ) + (T : ℂ) * I)
      = 2 * Real.pi * I * ((zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
          * riemannZeta ((1 + 2 * d : ℝ) : ℂ)) + dualDiagonalShiftedResidue d c x) := by
  apply rectIntegral_eq_two_pole_residues_of_analyticOnNhd (U := dualDiagonalRegion d)
    (p := 0) (q := -(d : ℂ)) (R := dualDiagonalRemainder d c x τ)
  · intro w hw
    have hre := (Complex.mem_reProdIm.mp hw).1
    have h1 : ((((-(1 / 4) : ℝ) : ℂ)) - (T : ℂ) * I).re = -(1 / 4) := by simp
    have h2 : (((1 : ℝ) : ℂ) + (T : ℂ) * I).re = 1 := by simp
    rw [h1, h2, Set.uIcc_of_le (by norm_num)] at hre
    show -(1 / 2) - d < w.re
    linarith [hre.1]
  · simp
  · simp
  · simpa using hT
  · simpa using hT
  · simp; linarith
  · simp; linarith
  · simpa using hT
  · simpa using hT
  · exact analyticOnNhd_dualDiagonalRemainder hc hx hd τ
  · intro z hz0 hzd
    simpa only [sub_zero, add_assoc] using
      dualDiagonalIntegrand_eq_two_poles_add_remainder hd c x τ hz0 hzd

/-- Both horizontal edges vanish as `T → ∞`. -/
theorem tendsto_dualDiagonalIntegrand_horizontal {d c x τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hc : 0 < c) (hx : 0 < x) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨T₀, Nχ, Cχ, hCχ, hχ⟩ := hasStripPolyGrowthOffReal_zetaChi (-1) 1
  obtain ⟨Cζ, Nζ, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 4
  set B : ℝ := Cχ * Cχ * Cζ * 2 ^ Nζ * max ((c * x) ^ (1 / 4 : ℝ)) ((c * x) ^ (-(1 : ℝ))) * Real.exp 1
    with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ => ((5 / 4) * B) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ)
      * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) (2 * Nχ + Nζ)).const_mul ((5 / 4) * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max T₀ 0 + |τ| + 1)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-(1 / 4) : ℝ) (1 : ℝ),
      ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    exact norm_dualDiagonalIntegrand_horizontal_le hd hd4 hc hx hCχ hCζ hχ hζ hu.1.le hu.2 hT hε
  calc ‖∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
        dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-(1 / 4))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((5 / 4) * B) * ((1 + |τ| + T) ^ (2 * Nχ + Nζ) * Real.exp (-(T ^ 2))) := by
        rw [show |(1 : ℝ) - (-(1 / 4))| = 5 / 4 by norm_num]
        ring

/-! ## The contour shift and the asymptotic -/

/-- **The dual diagonal is the two residues plus the left-line integral.** -/
theorem dualDiagonal_eq_residues_add_left {d c x τ : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) :
    dualDiagonal d c x τ
      = zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
          * riemannZeta ((1 + 2 * d : ℝ) : ℂ)
        + dualDiagonalShiftedResidue d c x
        + (1 / (2 * Real.pi)) • ∫ v : ℝ,
            dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have hbottom' := tendsto_dualDiagonalIntegrand_horizontal (τ := τ) hd hd4 hc hx (ε := -1) (Or.inr rfl)
  have htop' := tendsto_dualDiagonalIntegrand_horizontal (τ := τ) hd hd4 hc hx (ε := 1) (Or.inl rfl)
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    refine hbottom'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      dualDiagonalIntegrand d c x τ ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine htop'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have hright : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_dualDiagonalIntegrand_right hd hd4 hc hx)
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_dualDiagonalIntegrand_left hd hd8 hc hx)
      tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  set R : ℂ := zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
    * riemannZeta ((1 + 2 * d : ℝ) : ℂ) + dualDiagonalShiftedResidue d c x with hRdef
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
          dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          (∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
            dualDiagonalIntegrand d c x τ ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
        = 2 * Real.pi * I * R := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hrect := rectIntegral_dualDiagonalIntegrand_eq (d := d) (c := c) (x := x) (τ := τ) (T := T)
      hd hd8 hc hx hT
    rw [hRdef, ← hrect]
    simp only [RHTower.rectIntegral, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
      add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_sub, zero_add]
  have h := tendsto_nhds_unique (hlimit.congr' hevent) (tendsto_const_nhds (x := 2 * Real.pi * I * R))
  have h' : I • ((∫ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      ∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
      = 2 * Real.pi * I * R := by
    rw [smul_sub]
    simpa [sub_eq_add_neg] using h
  have hI : (∫ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      = 2 * Real.pi * R + ∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) := by
    have hI2 : I * ((∫ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        ∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
        = I * (2 * Real.pi * R) := by
      rw [← smul_eq_mul, h']
      ring
    have := mul_left_cancel₀ I_ne_zero hI2
    linear_combination this
  rw [dualDiagonal_eq_integral hc hx hd hd4 τ, hI, smul_add, hRdef]
  congr 1
  rw [Complex.real_smul]
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast
  field_simp

/-- **The dual left-line remainder is `O((cx)^{1/4}(1+|τ|)^{2d−½})`**, uniformly in
`d ∈ (0, ⅛]`, `c`, `x`, `τ`. -/
theorem exists_norm_dualDiagonal_left_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 8 → 0 < c → 0 < x →
      ‖(1 / (2 * Real.pi)) • ∫ v : ℝ,
          dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ K * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hG0 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)
    * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))), by positivity,
    fun d c x τ hd hd8 hc hx => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun v : ℝ =>
    norm_dualDiagonalIntegrand_left_le (τ := τ) hd hd8 hc hx hCχ hCζ hχ hζ v
  set A : ℝ := (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
    * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hnorm : ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by
    calc ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v : ℝ, ‖dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, A * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
            (integrable_one_add_abs_cube_mul_exp_neg_sq.const_mul A)
            (Filter.Eventually.of_forall fun v => hbound v)
      _ = A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ, dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (A * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 / (2 * Real.pi)) * (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)
          * ∫ v : ℝ, (1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) * (c * x) ^ (1 / 4 : ℝ)
          * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) := by
        rw [hAdef]; ring

end RHTower

end
