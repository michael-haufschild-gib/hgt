import GaloisForLFunctions.RHTower.GaussianPrimeBudgetOneSidedLaw

/-!
# The exponent law of the Gaussian prime gap

For real `σ > 0` let `P_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²}` and `C_σ(y) = ∫₁^∞ u^{-σ} e^{-yu²} du`.

* **Germs of zeros to the right** (`norm_zeroGerm_le_of_re_le`).  For a zero with `Re ρ ≤ θ` and
  `σ ≤ θ`, two steps of the incomplete-Gamma recursion `E(y,a) = −e^{-y}/a + (2y/a)E(y,a+2)` give
  `|e^{-y}/(ρ−½) + E(y, ρ−σ)| ≤ (c + c' y^{-(θ−σ)/2}) |ρ−½|^{-2}`; the last remainder `E(y, a+4)`
  is bounded by the complete Gamma integral.
* **Upper bound** (`exists_abs_gaussianWeightedGap_le_rpow`).  By the exact zero-field law the gap
  `P_σ − C_σ` is the archimedean Mellin–Barnes transform (bounded on `(0, 1]`) minus the germ field,
  so `|P_σ − C_σ|(y) = O(y^{-(θ−σ)/2})` whenever all zeros satisfy `Re ρ ≤ θ`.
* **Exponent law** (`xi_zero_re_le_iff_gaussianWeightedGap_le_rpow`).  For `0 < σ ≤ θ ≤ σ + 2`,
  all zeros satisfy `Re ρ ≤ θ` iff `P_σ − C_σ ≤ K y^{-(θ−σ)/2}` on `(0, 1]`; the converse is the
  growth form of the one-sided Landau law.
* **RH at one point** (`riemannHypothesis_iff_gaussianWeightedGap_le_rpow`).  For any fixed
  `σ ∈ (0, ½]`, RH holds iff `P_σ(y) − C_σ(y) ≤ K y^{-(½−σ)/2}` on `(0, 1]`.  At the centre
  (`riemannHypothesis_iff_gaussianCentralPrimeBudget`): RH iff `P_{1/2} ≤ C_{1/2} + K` on `(0, 1]`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- **Germ of a zero right of `σ`.**  For a zero with `Re ρ ≤ θ`, `σ ≤ θ`, `0 < y ≤ 1`, two steps of
the incomplete-Gamma recursion give
`‖e^{-y}/(ρ−½) + E(y, ρ−σ)‖ ≤ (|½−σ|C₁ + (2y + 2Γ((θ−σ+4)/2) y^{-(θ−σ)/2}) C₁C₂) |ρ−½|^{-2}`
with `C₁ = max 2 (2|σ−½|)`, `C₂ = max 2 (2|σ−5/2|)`. -/
theorem norm_zeroGerm_le_of_re_le {θ σ y : ℝ} (hy : 0 < y) (hσθ : σ ≤ θ) (q : XiZeroCopy)
    (hq : (xiZero q).re ≤ θ) :
    ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - σ)‖ ≤
      (|1 / 2 - σ| * max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) +
        (2 * y + 2 * Real.Gamma ((θ - σ + 4) / 2) * y ^ (-(θ - σ) / 2)) *
          (max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) * max 2 (2 * ‖(σ : ℂ) - 5 / 2‖))) *
        ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set ρ : ℂ := xiZero q with hρ
  set a : ℂ := ρ - σ with ha
  set C1 : ℝ := max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) with hC1
  set C2 : ℝ := max 2 (2 * ‖(σ : ℂ) - 5 / 2‖) with hC2
  set G : ℝ := Real.Gamma ((θ - σ + 4) / 2) with hG
  have hC1pos : 0 ≤ C1 := le_trans (by norm_num) (le_max_left _ _)
  have hC2pos : 0 ≤ C2 := le_trans (by norm_num) (le_max_left _ _)
  have hG0 : 0 ≤ G := (Real.Gamma_pos_of_pos (by linarith)).le
  -- the height of the zero
  have him : 1 < |ρ.im| := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_abs_im_le_one h (xi_xiZero q)
  have hκ : 0 < ‖ρ - 1 / 2‖ := lt_trans one_pos (one_lt_norm_xiZero_sub_half q)
  have hm1 : (1 : ℝ) ≤ ‖(ρ - 1 / 2) - ((σ : ℂ) - 1 / 2)‖ := by
    have h := Complex.abs_im_le_norm ((ρ - 1 / 2) - ((σ : ℂ) - 1 / 2))
    have hre : ((ρ - 1 / 2) - ((σ : ℂ) - 1 / 2)).im = ρ.im := by simp
    rw [hre] at h; linarith
  have hm2 : (1 : ℝ) ≤ ‖(ρ - 1 / 2) - ((σ : ℂ) - 5 / 2)‖ := by
    have h := Complex.abs_im_le_norm ((ρ - 1 / 2) - ((σ : ℂ) - 5 / 2))
    have hre : ((ρ - 1 / 2) - ((σ : ℂ) - 5 / 2)).im = ρ.im := by simp
    rw [hre] at h; linarith
  have hinv1 : ‖a‖⁻¹ ≤ C1 * ‖ρ - 1 / 2‖⁻¹ := by
    have h := inv_norm_sub_le_of_ge one_pos hκ hm1
    rwa [div_one, show (ρ - 1 / 2) - ((σ : ℂ) - 1 / 2) = a by rw [ha]; ring] at h
  have hinv2 : ‖a + 2‖⁻¹ ≤ C2 * ‖ρ - 1 / 2‖⁻¹ := by
    have h := inv_norm_sub_le_of_ge one_pos hκ hm2
    rwa [div_one, show (ρ - 1 / 2) - ((σ : ℂ) - 5 / 2) = a + 2 by rw [ha]; ring] at h
  have ha0 : a ≠ 0 := by
    intro h; have := hm1
    rw [show (ρ - 1 / 2) - ((σ : ℂ) - 1 / 2) = a by rw [ha]; ring, h, norm_zero] at this
    linarith
  have ha2 : a + 2 ≠ 0 := by
    intro h; have := hm2
    rw [show (ρ - 1 / 2) - ((σ : ℂ) - 5 / 2) = a + 2 by rw [ha]; ring, h, norm_zero] at this
    linarith
  have hκ0 : ρ - 1 / 2 ≠ 0 := by intro h; rw [h, norm_zero] at hκ; linarith
  -- the expansion
  have hexp : (Real.exp (-y) : ℂ) / (ρ - 1 / 2) + gaussianIncompleteMellin y a =
      (Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((ρ - 1 / 2) * a)) -
        2 * y * (Real.exp (-y) : ℂ) / (a * (a + 2)) +
        4 * (y : ℂ) ^ 2 * gaussianIncompleteMellin y (a + 2 + 2) / (a * (a + 2)) := by
    rw [gaussianIncompleteMellin_recursion hy ha0, gaussianIncompleteMellin_recursion hy ha2]
    generalize gaussianIncompleteMellin y (a + 2 + 2) = E4'
    generalize (Real.exp (-y) : ℂ) = e'
    have h1 : (1 / 2 - (σ : ℂ)) = a - (ρ - 1 / 2) := by rw [ha]; ring
    rw [h1]
    generalize ρ - 1 / 2 = κ at hκ0 ⊢
    field_simp
    ring
  rw [hexp]
  set E4 : ℂ := gaussianIncompleteMellin y (a + 2 + 2) with hE4
  set e : ℂ := (Real.exp (-y) : ℂ) with he
  have he1 : ‖e‖ ≤ 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hE4b : ‖E4‖ ≤ y ^ (-((θ - σ + 3) + 1) / 2) * (1 / 2) * Real.Gamma (((θ - σ + 3) + 1) / 2) :=
    norm_gaussianIncompleteMellin_le hy (by linarith) (by rw [ha]; simp; linarith)
  have hpow : (y : ℝ) ^ 2 * y ^ (-((θ - σ + 3) + 1) / 2) = y ^ (-(θ - σ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; push_cast; ring
  have hGeq : Real.Gamma (((θ - σ + 3) + 1) / 2) = G := by rw [hG]; congr 1; ring
  have hk1 : ‖(1 / 2 - (σ : ℂ))‖ = |1 / 2 - σ| := by
    rw [show (1 / 2 - (σ : ℂ)) = ((1 / 2 - σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  have hinvs : ‖ρ - 1 / 2‖⁻¹ ^ 2 = ‖(ρ - 1 / 2)⁻¹‖ ^ 2 := by rw [norm_inv]
  have hpart1 : ‖e * ((1 / 2 - σ) / ((ρ - 1 / 2) * a))‖ ≤
      |1 / 2 - σ| * C1 * ‖(ρ - 1 / 2)⁻¹‖ ^ 2 := by
    rw [norm_mul, norm_div, norm_mul, hk1, ← hinvs]
    have h1 : ‖e‖ * (|1 / 2 - σ| / (‖ρ - 1 / 2‖ * ‖a‖)) ≤ |1 / 2 - σ| / (‖ρ - 1 / 2‖ * ‖a‖) := by
      have h0 : 0 ≤ |1 / 2 - σ| / (‖ρ - 1 / 2‖ * ‖a‖) := by positivity
      nlinarith
    refine h1.trans ?_
    rw [div_eq_mul_inv, mul_inv]
    calc |1 / 2 - σ| * (‖ρ - 1 / 2‖⁻¹ * ‖a‖⁻¹) ≤ |1 / 2 - σ| * (‖ρ - 1 / 2‖⁻¹ *
          (C1 * ‖ρ - 1 / 2‖⁻¹)) := by gcongr
      _ = _ := by ring
  have hpart2 : ‖2 * (y : ℂ) * e / (a * (a + 2))‖ ≤ 2 * y * (C1 * C2) * ‖(ρ - 1 / 2)⁻¹‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, Complex.norm_two, ← hinvs, div_eq_mul_inv, mul_inv]
    have h1 : 2 * y * ‖e‖ ≤ 2 * y := by nlinarith
    calc 2 * y * ‖e‖ * (‖a‖⁻¹ * ‖a + 2‖⁻¹) ≤ 2 * y * ((C1 * ‖ρ - 1 / 2‖⁻¹) *
          (C2 * ‖ρ - 1 / 2‖⁻¹)) := by gcongr
      _ = _ := by ring
  have hpart3 : ‖4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2))‖ ≤
      2 * G * y ^ (-(θ - σ) / 2) * (C1 * C2) * ‖(ρ - 1 / 2)⁻¹‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, ← hinvs, div_eq_mul_inv, mul_inv]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    have hE : 4 * y ^ 2 * ‖E4‖ ≤ 2 * G * y ^ (-(θ - σ) / 2) := by
      calc 4 * y ^ 2 * ‖E4‖ ≤ 4 * y ^ 2 *
            (y ^ (-((θ - σ + 3) + 1) / 2) * (1 / 2) * Real.Gamma (((θ - σ + 3) + 1) / 2)) := by
            gcongr
        _ = 2 * G * y ^ (-(θ - σ) / 2) := by rw [hGeq, ← hpow]; ring
    calc 4 * y ^ 2 * ‖E4‖ * (‖a‖⁻¹ * ‖a + 2‖⁻¹) ≤ (2 * G * y ^ (-(θ - σ) / 2)) *
          ((C1 * ‖ρ - 1 / 2‖⁻¹) * (C2 * ‖ρ - 1 / 2‖⁻¹)) := by
          gcongr
      _ = _ := by ring
  calc ‖e * ((1 / 2 - σ) / ((ρ - 1 / 2) * a)) - 2 * y * e / (a * (a + 2)) +
        4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2))‖
      ≤ ‖e * ((1 / 2 - σ) / ((ρ - 1 / 2) * a))‖ + ‖2 * (y : ℂ) * e / (a * (a + 2))‖ +
          ‖4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
        have := add_le_add (add_le_add hpart1 hpart2) hpart3
        linarith

/-- On `0 < y ≤ 1` the archimedean Mellin–Barnes transform at `σ > 0` is uniformly bounded. -/
theorem norm_gaussianArchimedeanMB_le {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖gaussianArchimedeanMB y 2 (σ : ℂ)‖ ≤ ‖gaussianArchimedeanCurrent (σ : ℂ)‖ +
      (‖gaussianArchimedeanConstant‖ + ‖(σ : ℂ) - 2‖ +
        (2 + 2 * Real.Gamma ((4 - 1) / 2)) / (min (σ : ℂ).re 1 / 2)) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  set G₁ : ℝ := Real.Gamma ((4 - 1) / 2) with hG₁
  have hG₁0 : 0 ≤ G₁ := (Real.Gamma_pos_of_pos (by norm_num)).le
  set S₀ : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun m => by positivity
  set μ : ℝ := min (σ : ℂ).re 1 / 2 with hμ
  have hμ0 : 0 < μ := by rw [hμ]; exact half_pos (lt_min hs one_pos)
  have hp12 : y ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
  have hA := norm_gaussianArchimedeanCurrent_sub_MB_le two_pos hy hs
  rw [← hG₁, ← hS₀, ← hμ] at hA
  have hnum : (2 * y + 2 * G₁ * y ^ ((1 : ℝ) / 2)) ≤ 2 + 2 * G₁ := by
    have := mul_le_mul_of_nonneg_left hp12 hG₁0
    linarith
  have h3 : (2 * y + 2 * G₁ * y ^ ((1 : ℝ) / 2)) / μ ≤ (2 + 2 * G₁) / μ :=
    div_le_div_of_nonneg_right hnum hμ0.le
  have h1 : y * ‖gaussianArchimedeanConstant‖ ≤ ‖gaussianArchimedeanConstant‖ := by
    have := norm_nonneg gaussianArchimedeanConstant; nlinarith
  have h2 : y * ‖(σ : ℂ) - 2‖ ≤ ‖(σ : ℂ) - 2‖ := by
    have := norm_nonneg ((σ : ℂ) - 2); nlinarith
  have hAle : ‖gaussianArchimedeanCurrent (σ : ℂ) - gaussianArchimedeanMB y 2 (σ : ℂ)‖ ≤
      (‖gaussianArchimedeanConstant‖ + ‖(σ : ℂ) - 2‖ + (2 + 2 * G₁) / μ) * S₀ :=
    hA.trans (mul_le_mul_of_nonneg_right (by linarith) hS₀0)
  have := norm_sub_le (gaussianArchimedeanCurrent (σ : ℂ))
    (gaussianArchimedeanCurrent (σ : ℂ) - gaussianArchimedeanMB y 2 (σ : ℂ))
  rw [sub_sub_cancel] at this
  linarith

/-- The germ field of zeros with `Re ρ ≤ θ`, at `σ ≤ θ`, is `O(y^{-(θ−σ)/2})` on `(0, 1]`. -/
theorem norm_tsum_zeroGerm_le_rpow {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {σ : ℝ}
    (hσθ : σ ≤ θ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin y (xiZero q - σ))‖ ≤
      ((|1 / 2 - σ| * max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) + (2 + 2 * Real.Gamma ((θ - σ + 4) / 2)) *
        (max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) * max 2 (2 * ‖(σ : ℂ) - 5 / 2‖))) *
        ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) * y ^ (-(θ - σ) / 2) := by
  set C1 : ℝ := max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) with hC1
  set C2 : ℝ := max 2 (2 * ‖(σ : ℂ) - 5 / 2‖) with hC2
  set G : ℝ := Real.Gamma ((θ - σ + 4) / 2) with hG
  have hC1pos : 0 ≤ C1 := le_trans (by norm_num) (le_max_left _ _)
  have hC2pos : 0 ≤ C2 := le_trans (by norm_num) (le_max_left _ _)
  have hG0 : 0 ≤ G := (Real.Gamma_pos_of_pos (by linarith)).le
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun q => by positivity
  set Y : ℝ := y ^ (-(θ - σ) / 2) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  set W : ℝ := |1 / 2 - σ| * C1 + (2 * y + 2 * G * Y) * (C1 * C2) with hW
  have hgerm : ∀ q : XiZeroCopy, ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - σ)‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    fun q => norm_zeroGerm_le_of_re_le hy hσθ q (hθ _ (xi_xiZero q))
  have hw := summable_norm_inv_xiZero_sub_half_sq
  have hsn : Summable fun q : XiZeroCopy => ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - σ)‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hgerm (hw.mul_left W)
  have hZle : ‖∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - σ))‖ ≤ W * S := by
    calc _ ≤ ∑' q, ‖(Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin y (xiZero q - σ)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' q, W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := hsn.tsum_le_tsum hgerm (hw.mul_left W)
      _ = W * S := tsum_mul_left
  have hC12 : 0 ≤ C1 * C2 := mul_nonneg hC1pos hC2pos
  have hk : 0 ≤ |1 / 2 - σ| * C1 := mul_nonneg (abs_nonneg _) hC1pos
  have hWle : W ≤ (|1 / 2 - σ| * C1 + (2 + 2 * G) * (C1 * C2)) * Y := by
    have e1 : |1 / 2 - σ| * C1 ≤ |1 / 2 - σ| * C1 * Y := le_mul_of_one_le_right hk hY1
    have e2 : 2 * y + 2 * G * Y ≤ (2 + 2 * G) * Y := by nlinarith
    have e3 := mul_le_mul_of_nonneg_right e2 hC12
    rw [hW]
    calc |1 / 2 - σ| * C1 + (2 * y + 2 * G * Y) * (C1 * C2)
        ≤ |1 / 2 - σ| * C1 * Y + (2 + 2 * G) * Y * (C1 * C2) := add_le_add e1 e3
      _ = _ := by ring
  calc _ ≤ W * S := hZle
    _ ≤ ((|1 / 2 - σ| * C1 + (2 + 2 * G) * (C1 * C2)) * Y) * S :=
        mul_le_mul_of_nonneg_right hWle hS0
    _ = _ := by ring

/-- **Upper exponent bound.**  If every zero of `ξ` has `Re ρ ≤ θ` and `0 < σ ≤ θ`, then
`|P_σ − C_σ|(y) ≤ K y^{-(θ−σ)/2}` on `(0, 1]`: the gap is the archimedean transform minus the germ
field, and each germ is `O(y^{-(θ−σ)/2} |ρ−½|^{-2})`. -/
theorem exists_abs_gaussianWeightedGap_le_rpow {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ)
    {σ : ℝ} (hσ : 0 < σ) (hσθ : σ ≤ θ) :
    ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      |gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y| ≤
        K * y ^ (-(θ - σ) / 2) := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  set CA : ℝ := ‖gaussianArchimedeanCurrent (σ : ℂ)‖ +
      (‖gaussianArchimedeanConstant‖ + ‖(σ : ℂ) - 2‖ +
        (2 + 2 * Real.Gamma ((4 - 1) / 2)) / (min (σ : ℂ).re 1 / 2)) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 with hCA
  set CZ : ℝ := (|1 / 2 - σ| * max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) +
      (2 + 2 * Real.Gamma ((θ - σ + 4) / 2)) *
        (max 2 (2 * ‖(σ : ℂ) - 1 / 2‖) * max 2 (2 * ‖(σ : ℂ) - 5 / 2‖))) *
        ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hCZ
  refine ⟨CA + CZ, fun y hy hy1 => ?_⟩
  have hY1 : 1 ≤ y ^ (-(θ - σ) / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by linarith)
  have hx : 0 < y / Real.pi := div_pos hy Real.pi_pos
  have hpy : Real.pi * (y / Real.pi) = y := mul_div_cancel₀ _ Real.pi_ne_zero
  have hid := (logDeriv_gaussianFormation_eq_sub_gap hx hs).symm.trans
    (logDeriv_gaussianFormation_eq_zeroField hx hs)
  rw [hpy] at hid
  have hgap : gaussianPrimeContinuumGap (σ : ℂ) y = gaussianArchimedeanMB y 2 (σ : ℂ) -
      ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin y (xiZero q - σ)) := by
    linear_combination -hid
  have habs : |gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y| =
      ‖gaussianPrimeContinuumGap (σ : ℂ) y‖ := by
    rw [gaussianPrimeContinuumGap_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hgap]
  have hMB := norm_gaussianArchimedeanMB_le hσ hy hy1
  rw [← hCA] at hMB
  have hZ := norm_tsum_zeroGerm_le_rpow hθ hσθ hy hy1
  rw [← hCZ] at hZ
  have hCA0 : 0 ≤ CA := le_trans (norm_nonneg _) hMB
  have := mul_le_mul_of_nonneg_left hY1 hCA0
  calc _ ≤ ‖gaussianArchimedeanMB y 2 (σ : ℂ)‖ + ‖∑' q : XiZeroCopy,
        ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - σ))‖ :=
        norm_sub_le _ _
    _ ≤ CA * y ^ (-(θ - σ) / 2) + CZ * y ^ (-(θ - σ) / 2) := by linarith
    _ = _ := by ring

/-- **Exponent law.**  For `0 < σ ≤ θ ≤ σ + 2`, every zero of `ξ` has `Re ρ ≤ θ` iff
`P_σ(y) − C_σ(y) ≤ K y^{-(θ−σ)/2}` on `(0, 1]` for some `K`; one side of the bound suffices. -/
theorem xi_zero_re_le_iff_gaussianWeightedGap_le_rpow {θ σ : ℝ} (hσ : 0 < σ) (hσθ : σ ≤ θ)
    (hθσ : θ ≤ σ + 2) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) ↔ ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y ≤
        K * y ^ (-(θ - σ) / 2) := by
  constructor
  · intro hθ
    obtain ⟨K, hK⟩ := exists_abs_gaussianWeightedGap_le_rpow hθ hσ hσθ
    exact ⟨K, fun y hy hy1 => (le_abs_self _).trans (hK y hy hy1)⟩
  · rintro ⟨K, hK⟩ ρ hρ
    by_contra hlt
    push Not at hlt
    refine xi_ne_zero_of_gaussianPrimeGrowthBudget hσ (Or.inl rfl) (a := (θ - σ) / 2)
      (by linarith) (by linarith) (B := K) (fun y hy hy1 => ?_) (by linarith) hρ
    rw [one_mul, show -((θ - σ) / 2) = -(θ - σ) / 2 by ring]
    exact hK y hy hy1

/-- **RH as a single-point exponent law.**  For any `0 < σ ≤ ½`, RH holds iff
`Σ Λ(n) n^{-σ} e^{-yn²} − ∫₁^∞ u^{-σ} e^{-yu²} du ≤ K y^{-(½−σ)/2}` on `(0, 1]` for some `K`. -/
theorem riemannHypothesis_iff_gaussianWeightedGap_le_rpow {σ : ℝ} (hσ : 0 < σ)
    (hσ2 : σ ≤ 1 / 2) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y ≤
        K * y ^ (-(1 / 2 - σ) / 2) := by
  rw [← xi_zero_re_le_iff_gaussianWeightedGap_le_rpow hσ hσ2 (by linarith), rh_iff_xi_ne_zero_right]
  constructor
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    exact h ρ (mem_rightHalf.mpr hlt) hρ
  · intro h s hs hzero
    have := h s hzero
    rw [mem_rightHalf] at hs
    linarith

/-- **RH as the central Gaussian prime budget.**  RH holds iff the central Gaussian prime mass
`Σ Λ(n) n^{-1/2} e^{-yn²}` never exceeds its continuum `∫₁^∞ u^{-1/2} e^{-yu²} du` by more than a
constant on `(0, 1]`. -/
theorem riemannHypothesis_iff_gaussianCentralPrimeBudget :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass (1 / 2) y ≤ gaussianWeightedContinuumMass (1 / 2) y + K := by
  rw [riemannHypothesis_iff_gaussianWeightedGap_le_rpow (σ := 1 / 2) (by norm_num) le_rfl]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun y hy hy1 => ?_⟩
    have := hK y hy hy1
    rw [sub_self, neg_zero, zero_div, Real.rpow_zero, mul_one] at this
    linarith
  · rintro ⟨K, hK⟩
    refine ⟨K, fun y hy hy1 => ?_⟩
    rw [sub_self, neg_zero, zero_div, Real.rpow_zero, mul_one]
    linarith [hK y hy hy1]

end

end RHTower
