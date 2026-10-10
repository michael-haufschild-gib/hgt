import GaloisForLFunctions.RHTower.GaussianCentralGapExtremalSignChanges

/-!
# The sign phase transition of the Gaussian prime gaps

For `0 < σ < 1` let `G_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²} − ∫₁^∞ u^{-σ} e^{-yu²} du` and
`Θ = sup Re ρ`.

* **σ-germs** (`norm_sigmaZeroGerm_sub_le`).  For every zero, with `a = ρ − σ`,
  `e^{-y}/(ρ−½) + E(y, a) = e^{-y}(½−σ)/((ρ−½)a) + ½ Γ(a/2) y^{-a/2} + O(y|ρ−½|^{-2})`.
* **Extremal decomposition below the abscissa** (`tendsto_sigmaWeightedGap_add_extremalSeries`).
  If every zero has `Re ρ ≤ θ` and `σ < θ`, then
  `e^{-(θ−σ)u/2} G_σ(e^{-u}) + Σ_{Re ρ = θ} ½ Γ((ρ−σ)/2) e^{i(Im ρ/2)u} → 0`.
* **Dense sign changes below an attained abscissa**
  (`exists_dense_sign_changes_sigmaGap_of_extremal_zero`).  If a zero lies on `Re ρ = Θ` and
  `0 < σ < Θ`, then `G_σ(e^{-u})` exceeds `ε e^{(Θ−σ)u/2}` and falls below `−ε e^{(Θ−σ)u/2}` in
  every late window of a fixed length.
* **Phase transition under RH** (`riemannHypothesis_sign_phase_transition`).  Under RH, `G_σ` has
  relatively dense sign changes for every `0 < σ < ½` and is eventually negative for every
  `½ ≤ σ < 2`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- `|ρ − s| ≥ |Im ρ| ≥ |ρ − ½| / (3/2)` for every zero and real `s`. -/
theorem norm_inv_xiZero_sub_ofReal_le (q : XiZeroCopy) (s : ℝ) :
    ‖(xiZero q - s)⁻¹‖ ≤ 3 / 2 * ‖(xiZero q - 1 / 2)⁻¹‖ := by
  have him : 1 < |(xiZero q).im| := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_abs_im_le_one h (xi_xiZero q)
  have hb := re_xiZero_sub_half_bounds q
  have h1 : |(xiZero q).im| ≤ ‖xiZero q - s‖ := by
    have := Complex.abs_im_le_norm (xiZero q - s); simpa using this
  have h2 : ‖xiZero q - 1 / 2‖ ≤ 3 / 2 * |(xiZero q).im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := abs_le.2 ⟨hb.1.le, hb.2.le⟩
    have : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
    rw [this]
    linarith
  have hpos1 : 0 < ‖xiZero q - s‖ := by linarith
  have hpos2 : 0 < ‖xiZero q - 1 / 2‖ := norm_pos_iff.2 (xiZero_sub_half_ne_zero q)
  rw [norm_inv, norm_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hpos1 hpos2]
  nlinarith

/-- The σ-germ of a zero copy. -/
def sigmaZeroGerm (σ y : ℝ) (q : XiZeroCopy) : ℂ :=
  (Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - σ)

/-- The σ-amplitude `½ Γ((ρ−σ)/2)` of a zero copy. -/
def sigmaZeroAmplitude (σ : ℝ) (q : XiZeroCopy) : ℂ :=
  (1 / 2 : ℂ) * Complex.Gamma ((xiZero q - σ) / 2)

/-- **σ-germ expansion.**  For `σ < 2` and `y > 0`, the σ-germ is
`e^{-y}(½−σ)/((ρ−½)(ρ−σ)) + ½ Γ((ρ−σ)/2) y^{-(ρ−σ)/2}` up to `(9/2)(2y+2y²)|ρ−½|^{-2}`. -/
theorem norm_sigmaZeroGerm_sub_le {σ : ℝ} (hσ : σ < 3 / 2) {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖sigmaZeroGerm σ y q - (Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ))) -
        sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2))‖ ≤
      9 / 4 * (2 * y + 2 * y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set a : ℂ := xiZero q - σ with ha
  have hb := re_xiZero_sub_half_bounds q
  have hare : -2 < a.re := by
    rw [ha]; simp only [Complex.sub_re, Complex.ofReal_re]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    linarith [hb.1]
  have ha0 : a ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [ha] at him
    exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)
  have hκ0 : xiZero q - 1 / 2 ≠ 0 := xiZero_sub_half_ne_zero q
  have h := norm_zeroGerm_sub_gamma_le hy hare ha0
  have hid : sigmaZeroGerm σ y q - (Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * a)) -
      sigmaZeroAmplitude σ q * (y : ℂ) ^ (-(a / 2)) =
      (Real.exp (-y) : ℂ) / a + gaussianIncompleteMellin y a -
        (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2)) := by
    rw [sigmaZeroGerm, sigmaZeroAmplitude, ← ha]
    have h1 : (1 / 2 - (σ : ℂ)) = a - (xiZero q - 1 / 2) := by rw [ha]; ring
    rw [h1]
    generalize (Real.exp (-y) : ℂ) = e
    generalize gaussianIncompleteMellin y a = E
    generalize xiZero q - 1 / 2 = κ at hκ0 ⊢
    field_simp
    ring
  rw [hid]
  refine h.trans ?_
  -- `‖a‖ ‖a+2‖ ≥ ‖ρ−½‖²/(9/4)`
  have h1 := norm_inv_xiZero_sub_ofReal_le q σ
  have h2 := norm_inv_xiZero_sub_ofReal_le q (σ - 2)
  have ha2 : a + 2 = xiZero q - ((σ - 2 : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  rw [← ha] at h1
  rw [← ha2] at h2
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hna2 : a + 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hnb : 0 < ‖a + 2‖ := norm_pos_iff.2 hna2
  rw [div_eq_mul_inv, mul_inv]
  have hk := norm_nonneg (xiZero q - 1 / 2)⁻¹
  rw [norm_inv] at h1 h2
  calc (2 * y + 2 * y ^ 2) * (‖a‖⁻¹ * ‖a + 2‖⁻¹)
      ≤ (2 * y + 2 * y ^ 2) * ((3 / 2 * ‖(xiZero q - 1 / 2)⁻¹‖) * (3 / 2 * ‖(xiZero q - 1 / 2)⁻¹‖)) := by
        gcongr
    _ = 9 / 4 * (2 * y + 2 * y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by ring

/-- The σ-remainder: σ-germ minus its Bohr term. -/
def sigmaZeroRemainder (σ y : ℝ) (q : XiZeroCopy) : ℂ :=
  sigmaZeroGerm σ y q - sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2))

/-- The σ-remainder is `O(|ρ−½|^{-2})` uniformly on `(0, 1]`. -/
theorem norm_sigmaZeroRemainder_le {σ : ℝ} (hσ : σ < 3 / 2) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (q : XiZeroCopy) :
    ‖sigmaZeroRemainder σ y q‖ ≤ (3 / 2 * |1 / 2 - σ| + 9) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  have h := norm_sigmaZeroGerm_sub_le hσ hy q
  have hc : ‖(Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ)))‖ ≤
      3 / 2 * |1 / 2 - σ| * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_div,
      norm_mul]
    have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hσn : ‖(1 / 2 - (σ : ℂ))‖ = |1 / 2 - σ| := by
      rw [show (1 / 2 - (σ : ℂ)) = ((1 / 2 - σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hσn]
    have h1 := norm_inv_xiZero_sub_ofReal_le q σ
    have hk0 : 0 < ‖xiZero q - 1 / 2‖ := norm_pos_iff.2 (xiZero_sub_half_ne_zero q)
    have hs0 : 0 < ‖xiZero q - σ‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have him := congrArg Complex.im h0
      simp at him
      exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)
    simp only [norm_inv] at h1
    rw [norm_inv, div_eq_mul_inv, mul_inv]
    have hσ0 := abs_nonneg (1 / 2 - σ)
    calc Real.exp (-y) * (|1 / 2 - σ| * (‖xiZero q - 1 / 2‖⁻¹ * ‖xiZero q - σ‖⁻¹))
        ≤ 1 * (|1 / 2 - σ| * (‖xiZero q - 1 / 2‖⁻¹ * (3 / 2 * ‖xiZero q - 1 / 2‖⁻¹))) := by
          gcongr
      _ = 3 / 2 * |1 / 2 - σ| * ‖xiZero q - 1 / 2‖⁻¹ ^ 2 := by ring
  have hy2 : 9 / 4 * (2 * y + 2 * y ^ 2) ≤ 9 := by nlinarith
  have hk := sq_nonneg ‖(xiZero q - 1 / 2)⁻¹‖
  have := norm_sub_le
    (sigmaZeroGerm σ y q - (Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ))) -
      sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)))
    (-((Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ)))))
  rw [sigmaZeroRemainder]
  rw [norm_neg] at this
  have heq : sigmaZeroGerm σ y q - sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)) =
      sigmaZeroGerm σ y q - (Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ))) -
        sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)) -
        -((Real.exp (-y) : ℂ) * ((1 / 2 - σ) / ((xiZero q - 1 / 2) * (xiZero q - σ)))) := by ring
  rw [heq]
  nlinarith

theorem summable_sigmaZeroGerm {σ : ℝ} (hσ1 : σ ≤ 1) {y : ℝ} (hy : 0 < y) :
    Summable fun q : XiZeroCopy => sigmaZeroGerm σ y q := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, ∀ q : XiZeroCopy,
      ‖sigmaZeroGerm σ y q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    ⟨_, fun q => norm_zeroGerm_le_of_re_le (θ := 1) (σ := σ) hy hσ1 q (xiZero_re_le_one q)⟩
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hW
    (summable_norm_inv_xiZero_sub_half_sq.mul_left W))

/-- The σ-amplitudes are absolutely summable. -/
theorem summable_norm_sigmaZeroAmplitude {σ : ℝ} (hσ1 : σ ≤ 1) :
    Summable fun q : XiZeroCopy => ‖sigmaZeroAmplitude σ q‖ := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, ∀ q : XiZeroCopy,
      ‖sigmaZeroGerm σ 1 q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    ⟨_, fun q => norm_zeroGerm_le_of_re_le (θ := 1) (σ := σ) one_pos hσ1 q (xiZero_re_le_one q)⟩
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_norm_inv_xiZero_sub_half_sq.mul_left (W + (3 / 2 * |1 / 2 - σ| + 9)))
  have h1 := norm_sigmaZeroRemainder_le (σ := σ) (by linarith) one_pos le_rfl q
  rw [sigmaZeroRemainder, Complex.ofReal_one, Complex.one_cpow, mul_one] at h1
  have h3 : ‖sigmaZeroAmplitude σ q‖ ≤ ‖sigmaZeroGerm σ 1 q‖ +
      ‖sigmaZeroGerm σ 1 q - sigmaZeroAmplitude σ q‖ := by
    have := norm_sub_le (sigmaZeroGerm σ 1 q) (sigmaZeroGerm σ 1 q - sigmaZeroAmplitude σ q)
    rwa [sub_sub_cancel] at this
  have h2 := hW q
  nlinarith

/-- **σ-expansion.**  `G_σ(y) = A_y(σ) − Σ_ρ ½ Γ((ρ−σ)/2) y^{-(ρ−σ)/2} − Σ_ρ R_ρ(y)`. -/
theorem sigmaGap_eq_archimedean_sub_zeroSeries {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {y : ℝ}
    (hy : 0 < y) :
    ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) =
      gaussianArchimedeanMB y 2 (σ : ℂ) -
        (∑' q : XiZeroCopy, sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2))) -
        ∑' q : XiZeroCopy, sigmaZeroRemainder σ y q := by
  have hgap := gaussianWeightedGap_eq_MB_sub_germField hσ0 hy
  have hS : Summable fun q : XiZeroCopy =>
      sigmaZeroAmplitude σ q * (y : ℂ) ^ (-((xiZero q - σ) / 2)) := by
    refine Summable.of_norm ((summable_norm_sigmaZeroAmplitude hσ1).mul_right
      (y ^ (-(1 / 2 : ℝ)) + y ^ (1 / 2 : ℝ)) |>.of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := re_xiZero_sub_half_bounds q
    have hre : (-((xiZero q - σ) / 2)).re = -(((xiZero q).re - σ) / 2) := by simp
    rw [hre]
    have h0 : 0 < (xiZero q).re := xiZeroCopy_re_pos q
    have h1 := xiZero_re_le_one q
    rcases le_total y 1 with hy1 | hy1
    · have : y ^ (-(((xiZero q).re - σ) / 2)) ≤ y ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
      linarith [Real.rpow_nonneg hy.le (1 / 2 : ℝ)]
    · have : y ^ (-(((xiZero q).re - σ) / 2)) ≤ y ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      linarith [Real.rpow_nonneg hy.le (-(1 / 2 : ℝ))]
  have hR : Summable fun q : XiZeroCopy => sigmaZeroRemainder σ y q :=
    ((summable_sigmaZeroGerm hσ1 hy).sub hS).congr fun q => by rw [sigmaZeroRemainder]
  rw [hgap, sub_sub, ← hS.tsum_add hR]
  congr 1
  refine tsum_congr fun q => ?_
  rw [sigmaZeroRemainder, add_sub_cancel]
  rfl

/-! ## Below the abscissa -/

/-- The weighted σ-term `½ Γ((ρ−σ)/2) e^{(ρ−θ)u/2}`. -/
def sigmaWeightedTerm (σ θ u : ℝ) (q : XiZeroCopy) : ℂ :=
  sigmaZeroAmplitude σ q * Complex.exp ((xiZero q - θ) * (u : ℂ) / 2)

theorem norm_sigmaWeightedTerm (σ θ u : ℝ) (q : XiZeroCopy) :
    ‖sigmaWeightedTerm σ θ u q‖ =
      ‖sigmaZeroAmplitude σ q‖ * Real.exp (((xiZero q).re - θ) * u / 2) := by
  rw [sigmaWeightedTerm, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_im]

theorem sigmaWeightedTerm_of_re_eq (σ : ℝ) {θ : ℝ} (u : ℝ) {q : XiZeroCopy}
    (hq : (xiZero q).re = θ) :
    sigmaWeightedTerm σ θ u q =
      sigmaZeroAmplitude σ q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := by
  rw [sigmaWeightedTerm, xiZeroHalfOrdinate]
  congr 2
  have hz : xiZero q - θ = (((xiZero q).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hq]
  rw [hz]
  push_cast
  ring

/-- **Extremal decomposition below the abscissa.**  If every zero has `Re ρ ≤ θ` and
`0 < σ < θ`, `σ ≤ 1`, then
`e^{-(θ−σ)u/2} G_σ(e^{-u}) + Σ_{Re ρ = θ} ½ Γ((ρ−σ)/2) e^{i(Im ρ/2)u} → 0`. -/
theorem tendsto_sigmaWeightedGap_add_extremalSeries {θ σ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hσθ : σ < θ) :
    Tendsto (fun u : ℝ =>
        ((Real.exp (-((θ - σ) * u / 2)) * (gaussianWeightedPrimeMass σ (Real.exp (-u)) -
          gaussianWeightedContinuumMass σ (Real.exp (-u))) : ℝ) : ℂ) +
        ∑' q : XiZeroCopy, (if (xiZero q).re = θ then sigmaZeroAmplitude σ q else 0) *
          Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) atTop (𝓝 0) := by
  set w : ℝ → ℝ := fun u => Real.exp (-((θ - σ) * u / 2)) with hw
  set c : XiZeroCopy → ℂ := fun q => if (xiZero q).re = θ then sigmaZeroAmplitude σ q else 0
    with hc
  have hamp := summable_norm_sigmaZeroAmplitude hσ1
  have hcnorm : ∀ q, ‖c q‖ ≤ ‖sigmaZeroAmplitude σ q‖ := fun q => by
    simp only [hc]; split_ifs <;> simp
  have hcsum : Summable fun q => ‖c q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcnorm hamp
  have hcexp : ∀ u : ℝ, Summable fun q : XiZeroCopy =>
      c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := fun u =>
    Summable.of_norm (hcsum.congr fun q => by rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one])
  have hterm_sum : ∀ u : ℝ, Summable fun q : XiZeroCopy => sigmaWeightedTerm σ θ u q := by
    intro u
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      (hamp.mul_right (Real.exp ((1 + |θ|) * |u| / 2))))
    rw [norm_sigmaWeightedTerm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h0 : 0 < (xiZero q).re := xiZeroCopy_re_pos q
    have h1 := xiZero_re_le_one q
    have hβ : |(xiZero q).re - θ| ≤ 1 + |θ| := by
      rw [abs_le]; constructor <;> cases abs_cases θ <;> linarith
    have h2 : ((xiZero q).re - θ) * u ≤ (1 + |θ|) * |u| := by
      calc ((xiZero q).re - θ) * u ≤ |((xiZero q).re - θ) * u| := le_abs_self _
        _ = |(xiZero q).re - θ| * |u| := abs_mul _ _
        _ ≤ (1 + |θ|) * |u| := by gcongr
    linarith
  -- the weight tends to zero
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have hpos : 0 < (θ - σ) / 2 := by linarith
    have h1 : Tendsto (fun u : ℝ => -((θ - σ) * u / 2)) atTop atBot := by
      have := (tendsto_id (α := ℝ)).const_mul_atTop hpos
      refine tendsto_neg_atTop_atBot.comp (this.congr fun u => ?_)
      simp only [id]; ring
    exact Real.tendsto_exp_atBot.comp h1
  have hwC : Tendsto (fun u => ((w u : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hw0
    rw [Complex.ofReal_zero] at this
    exact this
  -- the expansion
  have hterm : ∀ u : ℝ, ∀ q : XiZeroCopy, ((w u : ℝ) : ℂ) *
      (sigmaZeroAmplitude σ q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - σ) / 2))) =
      sigmaWeightedTerm σ θ u q := by
    intro u q
    rw [exp_neg_cpow_eq_cexp_mul, sigmaWeightedTerm, hw]
    simp only
    rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  set D : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, (sigmaWeightedTerm σ θ u q -
    c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) with hDdef
  set Rs : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, sigmaZeroRemainder σ (Real.exp (-u)) q with hRs
  have hexpand : ∀ u : ℝ,
      ((w u * (gaussianWeightedPrimeMass σ (Real.exp (-u)) -
        gaussianWeightedContinuumMass σ (Real.exp (-u))) : ℝ) : ℂ) +
      ∑' q : XiZeroCopy, c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) =
      ((w u : ℝ) : ℂ) * gaussianArchimedeanMB (Real.exp (-u)) 2 (σ : ℂ) - D u -
        ((w u : ℝ) : ℂ) * Rs u := by
    intro u
    have he := sigmaGap_eq_archimedean_sub_zeroSeries hσ0 hσ1 (Real.exp_pos (-u))
    have hmul : ((w u : ℝ) : ℂ) * ∑' q : XiZeroCopy, sigmaZeroAmplitude σ q *
        ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZero q - σ) / 2)) =
        ∑' q : XiZeroCopy, sigmaWeightedTerm σ θ u q := by
      rw [← tsum_mul_left]
      exact tsum_congr fun q => hterm u q
    have hD : D u = (∑' q : XiZeroCopy, sigmaWeightedTerm σ θ u q) -
        ∑' q : XiZeroCopy, c q * Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) := by
      rw [hDdef]
      exact (hterm_sum u).tsum_sub (hcexp u)
    rw [Complex.ofReal_mul, he, hD, ← hmul]
    ring
  -- the pieces vanish
  have hexp0 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ Real.tendsto_exp_neg_atTop_nhds_zero
      (Eventually.of_forall fun u => Real.exp_pos _)
  have hMB : Tendsto (fun u : ℝ => gaussianArchimedeanMB (Real.exp (-u)) 2 (σ : ℂ)) atTop
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ))) := by
    have h1 := (tendsto_gaussianArchimedeanCurrent_sub_MB two_pos (s := (σ : ℂ))
      (by simpa using hσ0)).comp hexp0
    have h2 := (tendsto_const_nhds (x := gaussianArchimedeanCurrent (σ : ℂ))).sub h1
    rw [sub_zero] at h2
    exact h2.congr fun u => by simp only [Function.comp]; ring
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hlim : (0 : ℂ) = ∑' q : XiZeroCopy, (0 : ℂ) := tsum_zero.symm
    rw [hlim]
    refine tendsto_tsum_of_dominated_convergence (hamp.mul_left 2) (fun q => ?_) ?_
    · by_cases hq : (xiZero q).re = θ
      · refine tendsto_const_nhds.congr fun u => ?_
        rw [sigmaWeightedTerm_of_re_eq σ u hq]
        simp [hc, hq]
      · have hlt : (xiZero q).re < θ := lt_of_le_of_ne (hθ _ (xi_xiZero q)) hq
        have hc0 : c q = 0 := by simp [hc, hq]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hdecay : Tendsto (fun u : ℝ => ‖sigmaZeroAmplitude σ q‖ *
            Real.exp (((xiZero q).re - θ) * u / 2)) atTop (𝓝 0) := by
          have hneg : ((xiZero q).re - θ) / 2 < 0 := by linarith
          have h1 : Tendsto (fun u : ℝ => ((xiZero q).re - θ) * u / 2) atTop atBot := by
            have := (tendsto_id (α := ℝ)).const_mul_atTop_of_neg hneg
            exact this.congr fun u => by simp only [id]; ring
          simpa using (Real.tendsto_exp_atBot.comp h1).const_mul ‖sigmaZeroAmplitude σ q‖
        refine hdecay.congr fun u => ?_
        rw [hc0, zero_mul, sub_zero, norm_sigmaWeightedTerm]
    · filter_upwards [eventually_ge_atTop 0] with u hu q
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one, norm_sigmaWeightedTerm]
      have h1 : Real.exp (((xiZero q).re - θ) * u / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hθ _ (xi_xiZero q)
        nlinarith
      have h2 := hcnorm q
      have h3 := norm_nonneg (sigmaZeroAmplitude σ q)
      nlinarith
  have hRs : Tendsto (fun u => ((w u : ℝ) : ℂ) * Rs u) atTop (𝓝 0) := by
    set K : ℝ := (3 / 2 * |1 / 2 - σ| + 9) * ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hK
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun u : ℝ => w u * K) atTop (𝓝 0) := by
      simpa using hw0.mul_const K
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with u hu
    have hy := Real.exp_pos (-u)
    have hy1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hb := fun q => norm_sigmaZeroRemainder_le (σ := σ) (by linarith) hy hy1 q
    have hsn : Summable fun q : XiZeroCopy => ‖sigmaZeroRemainder σ (Real.exp (-u)) q‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
        (summable_norm_inv_xiZero_sub_half_sq.mul_left _)
    have hRle : ‖Rs u‖ ≤ K := by
      rw [hRs, hK, ← tsum_mul_left]
      exact (norm_tsum_le_tsum_norm hsn).trans
        (hsn.tsum_le_tsum hb (summable_norm_inv_xiZero_sub_half_sq.mul_left _))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hRle (Real.exp_pos _).le
  have htot := ((hwC.mul hMB).sub hD0).sub hRs
  rw [zero_mul, sub_zero, sub_zero] at htot
  refine htot.congr fun u => ?_
  rw [hexpand u]

/-! ## Visibility and dense sign changes below an attained abscissa -/

theorem tsum_sigmaExtremalCoefficient_eq (σ : ℝ) {ρ₀ : ℂ} {θ : ℝ} (hre : ρ₀.re = θ) :
    (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = ρ₀.im / 2 then
        (if (xiZero q).re = θ then sigmaZeroAmplitude σ q else 0) else 0) =
      (1 / 2 : ℂ) * Complex.Gamma ((ρ₀ - σ) / 2) *
        ((∑' q : XiZeroCopy, if xiZero q = ρ₀ then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  by_cases h : xiZero q = ρ₀
  · have h1 : xiZeroHalfOrdinate q = ρ₀.im / 2 := by rw [xiZeroHalfOrdinate, h]
    have h2 : (xiZero q).re = θ := by rw [h, hre]
    rw [if_pos h1, if_pos h2, if_pos h, sigmaZeroAmplitude, h]; push_cast; ring
  · have h1 : ¬ (xiZeroHalfOrdinate q = ρ₀.im / 2 ∧ (xiZero q).re = θ) := by
      rintro ⟨h1, h2⟩
      apply h
      rw [xiZeroHalfOrdinate] at h1
      apply Complex.ext
      · rw [h2, hre]
      · linarith
    by_cases h1' : xiZeroHalfOrdinate q = ρ₀.im / 2
    · rw [if_pos h1', if_neg (fun h2 => h1 ⟨h1', h2⟩), if_neg h]; simp
    · rw [if_neg h1', if_neg h]; simp

/-- **Dense sign changes of `G_σ` below an attained abscissa.**  If `ξ` has a zero on `Re ρ = Θ`
and `0 < σ < Θ`, there are `L, ε > 0` and `U₀` such that every window `[u₀, u₀ + L]`, `u₀ ≥ U₀`,
contains points with `G_σ(e^{-u}) > ε e^{(Θ−σ)u/2}` and points with `G_σ(e^{-u}) < −ε e^{(Θ−σ)u/2}`. -/
theorem exists_dense_sign_changes_sigmaGap_of_extremal_zero {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0)
    (hre : ρ₀.re = xiZeroAbscissa) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < xiZeroAbscissa) :
    ∃ L ε U₀ : ℝ, 0 < L ∧ 0 < ε ∧ ∀ u₀ : ℝ, U₀ ≤ u₀ →
      (∃ u ∈ Icc u₀ (u₀ + L), ε * Real.exp ((xiZeroAbscissa - σ) * u / 2) <
        gaussianWeightedPrimeMass σ (Real.exp (-u)) - gaussianWeightedContinuumMass σ (Real.exp (-u))) ∧
      (∃ u ∈ Icc u₀ (u₀ + L), gaussianWeightedPrimeMass σ (Real.exp (-u)) -
          gaussianWeightedContinuumMass σ (Real.exp (-u)) <
        -(ε * Real.exp ((xiZeroAbscissa - σ) * u / 2))) := by
  set Θ : ℝ := xiZeroAbscissa with hΘdef
  have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ Θ := fun _ hρ => re_le_xiZeroAbscissa hρ
  have hσ1 : σ ≤ 1 := (hσ.trans_le xiZeroAbscissa_le_one).le
  set G : ℝ → ℝ := fun u => gaussianWeightedPrimeMass σ (Real.exp (-u)) -
    gaussianWeightedContinuumMass σ (Real.exp (-u)) with hGdef
  have hGcont : Continuous G := by
    have h := continuous_gaussianBudgetProfile hσ0 (-1) 0 0
    have heq : G = gaussianBudgetProfile (-1) σ 0 0 := by
      funext u; simp [hGdef, gaussianBudgetProfile]
    rw [heq]; exact h
  set g : ℝ → ℝ := fun u => Real.exp (-((Θ - σ) * u / 2)) * G u with hgdef
  have hgcont : Continuous g := (by fun_prop : Continuous fun u : ℝ =>
    Real.exp (-((Θ - σ) * u / 2))).mul hGcont
  set c : XiZeroCopy → ℂ := fun q => if (xiZero q).re = Θ then sigmaZeroAmplitude σ q else 0
    with hc
  have hcsum : Summable fun q => ‖c q‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by simp only [hc]; split_ifs <;> simp) (summable_norm_sigmaZeroAmplitude hσ1)
  have hlim : Tendsto (fun u : ℝ => (g u : ℂ) + ∑' q, c q *
      Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) atTop (𝓝 0) :=
    tendsto_sigmaWeightedGap_add_extremalSeries hθ hσ0 hσ1 hσ
  have h0 : (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = 0 then c q else 0) = 0 := by
    have hall : ∀ q : XiZeroCopy, ¬ xiZeroHalfOrdinate q = 0 := by
      intro q hq
      rw [xiZeroHalfOrdinate] at hq
      have him : (xiZero q).im = 0 := by linarith
      exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)
    simp [hall]
  have hτ₀ : (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = ρ₀.im / 2 then c q else 0) ≠ 0 := by
    simp only [hc]
    rw [tsum_sigmaExtremalCoefficient_eq σ hre]
    have hΓ : Complex.Gamma ((ρ₀ - σ) / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun m hm => ?_
      have him := congrArg Complex.im hm
      simp at him
      exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) hρ₀
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_eq_of_xi_eq_zero hρ₀
    have hle : (1 : ℝ) ≤ ∑' q : XiZeroCopy, if xiZero q = ρ₀ then (1 : ℝ) else 0 := by
      have := (summable_indicator_xiZero_eq ρ₀).le_tsum q₀ (fun j _ => by split_ifs <;> norm_num)
      rwa [if_pos hq₀] at this
    refine mul_ne_zero (mul_ne_zero (by norm_num) hΓ) ?_
    exact_mod_cast (show (∑' q : XiZeroCopy, if xiZero q = ρ₀ then (1 : ℝ) else 0) ≠ 0 by linarith)
  obtain ⟨L, ε, U₀, hL, hε, hwin⟩ :=
    exists_dense_sign_changes_of_tendsto_add_tsum hgcont c hcsum xiZeroHalfOrdinate hlim h0 hτ₀
  have hGg : ∀ u, G u = Real.exp ((Θ - σ) * u / 2) * g u := by
    intro u
    simp only [hgdef]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  refine ⟨L, ε, U₀, hL, hε, fun u₀ hu₀ => ?_⟩
  obtain ⟨⟨u, hu, hgu⟩, ⟨u', hu', hgu'⟩⟩ := hwin u₀ hu₀
  refine ⟨⟨u, hu, ?_⟩, ⟨u', hu', ?_⟩⟩
  · have hpos := Real.exp_pos ((Θ - σ) * u / 2)
    show ε * Real.exp ((Θ - σ) * u / 2) < G u
    rw [hGg u]; nlinarith
  · have hpos := Real.exp_pos ((Θ - σ) * u' / 2)
    show G u' < -(ε * Real.exp ((Θ - σ) * u' / 2))
    rw [hGg u']; nlinarith

/-- **Sign phase transition under RH.**  Under RH the Gaussian gap `G_σ` has relatively dense sign
changes (with amplitude `ε e^{(½−σ)u/2}`) for every `0 < σ < ½`, and is eventually negative for
every `½ ≤ σ < 2`. -/
theorem riemannHypothesis_sign_phase_transition (hRH : RiemannHypothesis) :
    (∀ σ : ℝ, 0 < σ → σ < 1 / 2 → ∃ L ε U₀ : ℝ, 0 < L ∧ 0 < ε ∧ ∀ u₀ : ℝ, U₀ ≤ u₀ →
      (∃ u ∈ Icc u₀ (u₀ + L), ε * Real.exp ((1 / 2 - σ) * u / 2) <
        gaussianWeightedPrimeMass σ (Real.exp (-u)) - gaussianWeightedContinuumMass σ (Real.exp (-u))) ∧
      (∃ u ∈ Icc u₀ (u₀ + L), gaussianWeightedPrimeMass σ (Real.exp (-u)) -
          gaussianWeightedContinuumMass σ (Real.exp (-u)) <
        -(ε * Real.exp ((1 / 2 - σ) * u / 2)))) ∧
    (∀ σ : ℝ, 1 / 2 ≤ σ → σ < 2 → ∀ᶠ y in 𝓝[>] 0,
      gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y) := by
  have hΘ : xiZeroAbscissa = 1 / 2 := riemannHypothesis_iff_xiZeroAbscissa_eq_half.1 hRH
  obtain ⟨ρ₀, hρ₀, hre⟩ := exists_xi_zero_re_eq_half
  refine ⟨fun σ hσ0 hσ => ?_, fun σ hσ hσ2 => ?_⟩
  · have h := exists_dense_sign_changes_sigmaGap_of_extremal_zero hρ₀ (hre.trans hΘ.symm) hσ0
      (by rw [hΘ]; exact hσ)
    rw [hΘ] at h
    exact h
  · rcases eq_or_lt_of_le hσ with h | h
    · rw [← h]
      exact riemannHypothesis_iff_eventually_gaussianCentralGap_neg.1 hRH
    · have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := fun ρ hρ => by
        have := re_le_xiZeroAbscissa hρ; rwa [hΘ] at this
      have hneg := log_add_two_div_two_pi_neg (σ := σ) (by linarith) hσ2
      filter_upwards [eventually_gaussianWeightedGap_lt_of_zero_bound hθ h hσ2] with y hy
      linarith

end

end RHTower
