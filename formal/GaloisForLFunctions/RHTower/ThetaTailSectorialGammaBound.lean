import GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity
import GaloisForLFunctions.HTGeometry.GaussianPairControlQuotient
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# The sectorial Gamma bound and the Xi disc count

Along the rays `z_R = R(sin δ - i cos δ)`, the exact Gauss-product exponent for
`Γ(σ/2)/|Γ(s/2)|` equals `|s| D(φ) + ½ log(1 + t²/σ²)` with `φ = arctan(t/σ)` and
`D(δ) = ½[cos δ log(cos δ) + δ sin δ]`, which is even, nondecreasing on `[0, π/2)` and
`δ²/4 + O(δ⁴)`. Hence `|F(i Im z_R)| ≤ (3/cos δ) e^{(R+1/2) D(δ)} |F(z_R)|` and the relative-source
quotient obeys `|Q(z_R)| ≤ (3C/cos δ) e^{(R+1/2) D(δ)}`: `limsup R⁻¹ log|Q(z_R)| ≤ D(δ)`. A linear
angular cusp such as the Gaussian control's `e^{-ω²/4} cosh(ωz/2)` violates this bound.

The complete Xi divisor fills discs exactly at the Riemann–von Mangoldt rate:
`n_F(c, R) = [1/π + o(1)] R log R` for every centre `c`.
-/

open MeasureTheory Set Filter Topology Complex Metric

namespace RHTower

noncomputable section

/-! ## The sectorial exponent `D(δ)` -/

/-- `D(δ) = ½[cos δ log(cos δ) + δ sin δ]`. -/
def sectorialExponent (δ : ℝ) : ℝ := (Real.cos δ * Real.log (Real.cos δ) + δ * Real.sin δ) / 2

theorem sectorialExponent_neg (δ : ℝ) : sectorialExponent (-δ) = sectorialExponent δ := by
  simp [sectorialExponent, Real.cos_neg, Real.sin_neg]

theorem hasDerivAt_sectorialExponent {δ : ℝ} (hc : Real.cos δ ≠ 0) :
    HasDerivAt sectorialExponent
      ((δ * Real.cos δ - Real.sin δ * Real.log (Real.cos δ)) / 2) δ := by
  have h1 := (Real.hasDerivAt_cos δ).mul ((Real.hasDerivAt_cos δ).log hc)
  have h2 := (hasDerivAt_id δ).mul (Real.hasDerivAt_sin δ)
  refine ((h1.add h2).div_const 2).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `D` is nondecreasing on `[0, π/2)`. -/
theorem monotoneOn_sectorialExponent : MonotoneOn sectorialExponent (Ico 0 (Real.pi / 2)) := by
  have hcos : ∀ δ ∈ Ico 0 (Real.pi / 2), 0 < Real.cos δ := fun δ hδ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hδ.1, Real.pi_pos], hδ.2⟩
  refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) ?_ ?_ ?_
  · intro δ hδ
    exact (hasDerivAt_sectorialExponent (hcos δ hδ).ne').continuousAt.continuousWithinAt
  · intro δ hδ
    rw [interior_Ico] at hδ
    exact (hasDerivAt_sectorialExponent (hcos δ (Ioo_subset_Ico_self hδ)).ne').differentiableAt.differentiableWithinAt
  · intro δ hδ
    rw [interior_Ico] at hδ
    have hc := hcos δ (Ioo_subset_Ico_self hδ)
    rw [(hasDerivAt_sectorialExponent hc.ne').deriv]
    have hs : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ.1.le
      (by linarith [hδ.2, Real.pi_pos])
    have hl : Real.log (Real.cos δ) ≤ 0 := Real.log_nonpos hc.le (Real.cos_le_one δ)
    have : 0 ≤ δ * Real.cos δ := mul_nonneg hδ.1.le hc.le
    nlinarith [mul_nonneg hs (neg_nonneg.mpr hl)]

theorem sectorialExponent_zero : sectorialExponent 0 = 0 := by simp [sectorialExponent]

theorem sectorialExponent_nonneg {δ : ℝ} (hδ : |δ| < Real.pi / 2) : 0 ≤ sectorialExponent δ := by
  have h := monotoneOn_sectorialExponent (show (0 : ℝ) ∈ Ico 0 (Real.pi / 2) from
    ⟨le_rfl, Real.pi_div_two_pos⟩) (show |δ| ∈ Ico 0 (Real.pi / 2) from ⟨abs_nonneg δ, hδ⟩)
    (abs_nonneg δ)
  rw [sectorialExponent_zero] at h
  rcases le_or_gt 0 δ with h0 | h0
  · rwa [abs_of_nonneg h0] at h
  · rwa [abs_of_neg h0, sectorialExponent_neg] at h

/-- **`D(δ) = δ²/4 + O(δ⁴)`:** `|D(δ) - δ²/4| ≤ δ⁴` for `|δ| ≤ 1`. -/
theorem abs_sectorialExponent_sub_le {δ : ℝ} (hδ : |δ| ≤ 1) :
    |sectorialExponent δ - δ ^ 2 / 4| ≤ δ ^ 4 := by
  wlog h0 : 0 ≤ δ generalizing δ
  · have := this (δ := -δ) (by rwa [abs_neg]) (by linarith)
    rwa [sectorialExponent_neg, neg_sq, show (-δ) ^ 4 = δ ^ 4 by ring] at this
  have hδ1 : δ ≤ 1 := by rwa [abs_of_nonneg h0] at hδ
  set c := Real.cos δ with hcdef
  have hc1 : 1 - δ ^ 2 / 2 ≤ c := Real.one_sub_sq_div_two_le_cos
  have hcb := Real.cos_bound hδ
  rw [abs_of_nonneg h0] at hcb
  have hcup : c - 1 ≤ -(δ ^ 2 / 2) + δ ^ 4 * (5 / 96) := by
    have := (abs_le.mp hcb).2; linarith
  have hc0 : 0 < c := by nlinarith
  have hcle1 : c ≤ 1 := Real.cos_le_one δ
  have hlogup : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  have hloglow : 1 - c⁻¹ ≤ Real.log c := Real.one_sub_inv_le_log_of_pos hc0
  have hsup : Real.sin δ ≤ δ := Real.sin_le h0
  have hslow : δ - δ ^ 3 / 6 ≤ Real.sin δ := by
    rcases h0.lt_or_eq with h | h
    · exact (Real.sin_gt_sub_cube h).le
    · rw [← h]; simp
  have hup1 : c * Real.log c ≤ c * (c - 1) := mul_le_mul_of_nonneg_left hlogup hc0.le
  have hup2 : c * (c - 1) ≤ (1 - δ ^ 2 / 2) * (c - 1) :=
    mul_le_mul_of_nonpos_right hc1 (by linarith)
  have hup3 : (1 - δ ^ 2 / 2) * (c - 1) ≤ (1 - δ ^ 2 / 2) * (-(δ ^ 2 / 2) + δ ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_left hcup (by nlinarith)
  have hlow1 : c * (1 - c⁻¹) ≤ c * Real.log c := mul_le_mul_of_nonneg_left hloglow hc0.le
  have hlow2 : c * (1 - c⁻¹) = c - 1 := by field_simp
  have hδs1 : δ * Real.sin δ ≤ δ * δ := mul_le_mul_of_nonneg_left hsup h0
  have hδs2 : δ * (δ - δ ^ 3 / 6) ≤ δ * Real.sin δ := mul_le_mul_of_nonneg_left hslow h0
  have hδ4 : δ ^ 6 ≤ δ ^ 4 := pow_le_pow_of_le_one h0 hδ1 (by norm_num)
  rw [sectorialExponent, abs_le]
  constructor <;> nlinarith [pow_nonneg h0 4, pow_nonneg h0 6]

/-! ## The exact Gamma horizontal exponent in polar form -/

/-- `B(σ/2, t/2) = √(σ² + t²) · D(arctan(t/σ)) + ½ log(1 + t²/σ²)` for `σ > 0`, `t ≥ 0`. -/
theorem gammaRatioBound_eq_polar {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    HTGeometry.gammaRatioBound (σ / 2) (t / 2) =
      Real.sqrt (σ ^ 2 + t ^ 2) * sectorialExponent (Real.arctan (t / σ)) +
        Real.log (1 + t ^ 2 / σ ^ 2) / 2 := by
  set x := t / σ with hx
  have hx0 : 0 ≤ x := div_nonneg ht hσ.le
  have hq : 0 < 1 + x ^ 2 := by positivity
  have hsq : Real.sqrt (σ ^ 2 + t ^ 2) = σ * Real.sqrt (1 + x ^ 2) := by
    rw [show σ ^ 2 + t ^ 2 = σ ^ 2 * (1 + x ^ 2) by rw [hx]; field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hσ.le]
  have hsqrt0 : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hq
  have hlogc : Real.log (1 / Real.sqrt (1 + x ^ 2)) = -(Real.log (1 + x ^ 2) / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hq.le]
  have htx : t = σ * x := by rw [hx]; field_simp
  rw [HTGeometry.gammaRatioBound, sectorialExponent, Real.cos_arctan, Real.sin_arctan, hsq, hlogc,
    abs_of_nonneg (by positivity : 0 ≤ t / 2), show t / 2 / (σ / 2) = x by rw [hx]; field_simp,
    show (t / 2) ^ 2 / (σ / 2) ^ 2 = x ^ 2 by rw [hx]; field_simp, show t ^ 2 / σ ^ 2 = x ^ 2 by
      rw [hx]; field_simp, htx]
  field_simp
  ring

/-! ## The sectorial Gamma bound (3) -/

/-- The ray point `z_R = R(sin δ - i cos δ)`. -/
def sectorialRay (δ R : ℝ) : ℂ := ((R * Real.sin δ : ℝ) : ℂ) - ((R * Real.cos δ : ℝ) : ℂ) * I

theorem sectorialRay_re (δ R : ℝ) : (sectorialRay δ R).re = R * Real.sin δ := by
  simp only [sectorialRay, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]; ring

theorem sectorialRay_im (δ R : ℝ) : (sectorialRay δ R).im = -(R * Real.cos δ) := by
  simp only [sectorialRay, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re]; ring

/-- **The completed-gamma comparison on rays (3).** For `|δ| < π/2` and `R cos δ ≥ 5/2`,
`|F(i Im z_R)| ≤ (3/cos δ) e^{(R + 1/2) D(δ)} |F(z_R)|`, so
`R⁻¹ log(|F(i Im z_R)|/|F(z_R)|) ≤ D(δ) + O(1/R)`. -/
theorem thetaSourceLaplace_le_sectorialRay {δ R : ℝ} (hδ : |δ| < Real.pi / 2)
    (hR : 5 / 2 ≤ R * Real.cos δ) :
    thetaSourceLaplace (sectorialRay δ R).im ≤
      3 * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ * ‖XiC (sectorialRay δ R)‖ := by
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hδ).1],
    (abs_lt.mp hδ).2⟩
  have hR0 : 0 < R := by
    by_contra h; push Not at h
    have : R * Real.cos δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hcos.le
    linarith
  have him : |(sectorialRay δ R).im| = R * Real.cos δ := by
    rw [sectorialRay_im, abs_neg, abs_of_pos (mul_pos hR0 hcos)]
  have hre : |(sectorialRay δ R).re| = R * |Real.sin δ| := by
    rw [sectorialRay_re, abs_mul, abs_of_pos hR0]
  have hmain := thetaSourceLaplace_le_mul_norm_XiC (z := sectorialRay δ R) (by rw [him]; exact hR)
  rw [him, hre] at hmain
  set σ := 1 / 2 + R * Real.cos δ with hσ
  set t := R * |Real.sin δ| with ht
  have hσ0 : 0 < σ := by positivity
  have ht0 : 0 ≤ t := by positivity
  rw [show (1 / 2 + R * Real.cos δ) / 2 = σ / 2 from rfl, show R * |Real.sin δ| / 2 = t / 2 from rfl,
    gammaRatioBound_eq_polar hσ0 ht0] at hmain
  -- the angle and the modulus
  have htan : t / σ ≤ Real.tan |δ| := by
    rw [Real.tan_eq_sin_div_cos, Real.cos_abs, div_le_div_iff₀ hσ0 hcos]
    have hsa : Real.sin |δ| = |Real.sin δ| := by
      rcases le_or_gt 0 δ with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by
          linarith [(abs_lt.mp hδ).2, Real.pi_pos]))]
      · rw [abs_of_neg h, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h (by
          linarith [(abs_lt.mp hδ).1, Real.pi_pos]))]
    rw [hsa, ht, hσ]
    nlinarith [abs_nonneg (Real.sin δ), mul_nonneg hR0.le (abs_nonneg (Real.sin δ))]
  have hφ0 : 0 ≤ Real.arctan (t / σ) := Real.arctan_nonneg.mpr (div_nonneg ht0 hσ0.le)
  have hφ : Real.arctan (t / σ) ≤ |δ| := by
    calc Real.arctan (t / σ) ≤ Real.arctan (Real.tan |δ|) := Real.arctan_strictMono.monotone htan
      _ = |δ| := Real.arctan_tan (by linarith [abs_nonneg δ, Real.pi_pos]) hδ
  have hDφ : sectorialExponent (Real.arctan (t / σ)) ≤ sectorialExponent δ := by
    have := monotoneOn_sectorialExponent ⟨hφ0, hφ.trans_lt hδ⟩ ⟨abs_nonneg δ, hδ⟩ hφ
    rcases le_or_gt 0 δ with h | h
    · rwa [abs_of_nonneg h] at this
    · rwa [abs_of_neg h, sectorialExponent_neg] at this
  have hD0 : 0 ≤ sectorialExponent (Real.arctan (t / σ)) :=
    sectorialExponent_nonneg (by rw [abs_of_nonneg hφ0]; linarith)
  have hmod : Real.sqrt (σ ^ 2 + t ^ 2) ≤ R + 1 / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    have h1 : t ^ 2 = R ^ 2 * Real.sin δ ^ 2 := by rw [ht, mul_pow, sq_abs]
    have h2 := Real.sin_sq_add_cos_sq δ
    have h3 : R * Real.cos δ ≤ R := mul_le_of_le_one_right hR0.le (Real.cos_le_one δ)
    rw [hσ, h1]; nlinarith
  have hlog : Real.log (1 + t ^ 2 / σ ^ 2) / 2 ≤ -Real.log (Real.cos δ) := by
    have hq : 1 + t ^ 2 / σ ^ 2 ≤ 1 / Real.cos δ ^ 2 := by
      have h1 : t / σ ≤ |Real.sin δ| / Real.cos δ := by
        rw [div_le_div_iff₀ hσ0 hcos, ht, hσ]
        nlinarith [abs_nonneg (Real.sin δ), mul_nonneg hR0.le (abs_nonneg (Real.sin δ))]
      have h2 : (t / σ) ^ 2 ≤ (|Real.sin δ| / Real.cos δ) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ht0 hσ0.le) h1 2
      rw [div_pow, div_pow, sq_abs] at h2
      have h3 := Real.sin_sq_add_cos_sq δ
      rw [show 1 / Real.cos δ ^ 2 = 1 + Real.sin δ ^ 2 / Real.cos δ ^ 2 by field_simp; linarith]
      linarith
    have := Real.log_le_log (by positivity) hq
    rw [one_div, Real.log_inv, Real.log_pow] at this
    push_cast at this
    linarith
  have hB : Real.sqrt (σ ^ 2 + t ^ 2) * sectorialExponent (Real.arctan (t / σ)) +
      Real.log (1 + t ^ 2 / σ ^ 2) / 2 ≤ (R + 1 / 2) * sectorialExponent δ - Real.log (Real.cos δ) := by
    have := mul_le_mul hmod hDφ hD0 (by linarith)
    linarith
  calc thetaSourceLaplace (sectorialRay δ R).im ≤ 3 * Real.exp (Real.sqrt (σ ^ 2 + t ^ 2) *
        sectorialExponent (Real.arctan (t / σ)) + Real.log (1 + t ^ 2 / σ ^ 2) / 2) *
        ‖XiC (sectorialRay δ R)‖ := hmain
    _ ≤ 3 * Real.exp ((R + 1 / 2) * sectorialExponent δ - Real.log (Real.cos δ)) *
        ‖XiC (sectorialRay δ R)‖ := by gcongr
    _ = _ := by rw [Real.exp_sub, Real.exp_log hcos]; ring

/-- **(3) for the quotient.** Under the relative-source hypotheses,
`|Q(z_R)| ≤ (3C/cos δ) e^{(R + 1/2) D(δ)}` for `R cos δ ≥ 5/2`. -/
theorem norm_quotient_le_sectorialRay {u : ℝ → ℂ} {C : ℝ} {q : ℂ → ℂ}
    (hC : ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) (hq : ∀ z, sourceTransform u z = q z * XiC z)
    {δ R : ℝ} (hδ : |δ| < Real.pi / 2) (hR : 5 / 2 ≤ R * Real.cos δ) :
    ‖q (sectorialRay δ R)‖ ≤ 3 * C * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (thetaCuspFullSource_pos 0)
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hδ).1],
    (abs_lt.mp hδ).2⟩
  have h1 := norm_sourceTransform_le hC (sectorialRay δ R)
  have h2 := thetaSourceLaplace_le_sectorialRay hδ hR
  have hF : 0 < ‖XiC (sectorialRay δ R)‖ := by
    by_contra hF; push Not at hF
    have := thetaSourceLaplace_pos (sectorialRay δ R).im
    have h3 : 3 * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ *
        ‖XiC (sectorialRay δ R)‖ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hF
    linarith
  rw [hq, norm_mul] at h1
  have h3 : ‖q (sectorialRay δ R)‖ * ‖XiC (sectorialRay δ R)‖ ≤
      3 * C * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ * ‖XiC (sectorialRay δ R)‖ := by
    calc ‖q (sectorialRay δ R)‖ * ‖XiC (sectorialRay δ R)‖ ≤
          C * thetaSourceLaplace (sectorialRay δ R).im := h1
      _ ≤ C * (3 * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ *
          ‖XiC (sectorialRay δ R)‖) := mul_le_mul_of_nonneg_left h2 hC0
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hF

/-- **The linear cusp is excluded.** For every `κ > 0`, `D(δ) < κ sin δ` for all small `δ > 0`;
so a quotient growing like `e^{κ R sin δ}` along the rays (the Gaussian control, `κ = |ω|/2`)
violates (3). -/
theorem exists_sectorialExponent_lt_linear {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → sectorialExponent δ < κ * Real.sin δ := by
  refine ⟨min 1 (2 / 3 * κ), lt_min one_pos (by linarith), fun δ hδ0 hδ => ?_⟩
  have hδ1 : δ ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  have hδκ : δ < 2 / 3 * κ := hδ.trans_le (min_le_right _ _)
  have hD := abs_sectorialExponent_sub_le (by rw [abs_of_pos hδ0]; exact hδ1)
  have hDup : sectorialExponent δ ≤ δ ^ 2 / 4 + δ ^ 4 := by linarith [(abs_le.mp hD).2]
  have hs : δ - δ ^ 3 / 6 < Real.sin δ := Real.sin_gt_sub_cube hδ0
  have h4 : δ ^ 4 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num)
  have h3 : δ ^ 3 ≤ δ := by nlinarith [pow_le_pow_of_le_one hδ0.le hδ1 (show 1 ≤ 3 by norm_num)]
  nlinarith

/-! ## The disc count of the complete Xi divisor (2) -/

/-- **Upper disc count.** The zeros of `F = XiC` in `closedBall c R` lie in the symmetric
rectangle of height `R + |c|`. -/
theorem finsum_divisor_XiC_le_xiSymmetricMass (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ᶠ z, MeromorphicOn.divisor XiC (closedBall c R) z ≤ xiSymmetricMass (R + ‖c‖) := by
  set T := R + ‖c‖
  set rect := Rectangle (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I)
  have hT : 0 ≤ T := by positivity
  let e : ℂ ≃ ℂ :=
    { toFun := fun z => 1 / 2 + z * I
      invFun := fun s => (s - 1 / 2) * (-I)
      left_inv := fun z => by
        simp only
        rw [show (1 / 2 + z * I - 1 / 2) * -I = z * (-(I * I)) by ring, I_mul_I]; ring
      right_inv := fun s => by
        simp only
        rw [mul_assoc, show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]; ring }
  have hxiA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
  have hXA : AnalyticOnNhd ℂ XiC univ := fun z _ => XiC_differentiable.analyticAt z
  have hfinX : (MeromorphicOn.divisor XiC (closedBall c R)).support.Finite :=
    (MeromorphicOn.divisor XiC (closedBall c R)).finiteSupport (isCompact_closedBall c R)
  have hfinx : (MeromorphicOn.divisor xi rect).support.Finite :=
    (MeromorphicOn.divisor xi rect).finiteSupport (isCompact_uIcc.reProdIm isCompact_uIcc)
  rw [xiSymmetricMass, xiRegionOrderSum]
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_le_finsum' hfinX (hfinx.preimage (e.injective.injOn)) fun z => ?_
  have hes : e z = 1 / 2 + z * I := rfl
  by_cases hz : z ∈ closedBall c R
  · by_cases hzero : XiC z = 0
    · have hxi : xi (e z) = 0 := hzero
      have hre0 := xi_zero_re_pos hxi
      have hre1 := xi_zero_re_lt_one hxi
      have hmem : e z ∈ rect := by
        show e z ∈ Set.uIcc (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ((2 : ℂ) + (T : ℂ) * I).re ×ℂ
          Set.uIcc (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ((2 : ℂ) + (T : ℂ) * I).im
        rw [Complex.mem_reProdIm]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, Complex.re_ofNat,
          Complex.add_im, Complex.mul_im, zero_add, Complex.im_ofNat, add_zero]
        rw [uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]
        have him : (e z).im = z.re := by rw [hes]; simp
        have hzre : |z.re| ≤ T := by
          have h1 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
            calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
              _ ≤ _ := norm_add_le _ _
          have h2 : ‖z - c‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
          exact (Complex.abs_re_le_norm z).trans (by linarith)
        rw [him] at *
        refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith [(abs_le.mp hzre).1], (abs_le.mp hzre).2⟩⟩
      rw [MeromorphicOn.divisor_apply (hXA.mono (subset_univ _)).meromorphicOn hz,
        MeromorphicOn.divisor_apply (hxiA.mono (subset_univ _)).meromorphicOn hmem,
        (hXA z (mem_univ z)).meromorphicOrderAt_eq, (hxiA _ (mem_univ _)).meromorphicOrderAt_eq]
      have hc : z = (e z - 1 / 2) * -I := (e.left_inv z).symm
      conv_lhs => rw [hc]
      rw [analyticOrderAt_XiC_centeredCoordinate]
    · rw [MeromorphicOn.divisor_apply (hXA.mono (subset_univ _)).meromorphicOn hz,
        (hXA z (mem_univ z)).meromorphicOrderAt_eq,
        (hXA z (mem_univ z)).analyticOrderAt_eq_zero.mpr hzero]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hxiA.mono (subset_univ _)) _
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hxiA.mono (subset_univ _)) _

/-- **The Riemann–von Mangoldt disc count (2).** For every centre `c`,
`n_F(c, R) = [1/π + o(1)] R log R`. -/
theorem eventually_abs_finsum_divisor_XiC_sub_le (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R in atTop, |((∑ᶠ z, MeromorphicOn.divisor XiC (closedBall c R) z : ℤ) : ℝ) -
      1 / Real.pi * (R * Real.log R)| ≤ ε * (R * Real.log R) := by
  have hπ := Real.pi_pos
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min ε (1 / Real.pi) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := hε' ▸ lt_min hε (by positivity)
  have hε'1 : ε' ≤ 1 / Real.pi := hε' ▸ min_le_right _ _
  have hε'ε : ε' ≤ ε := hε' ▸ min_le_left _ _
  obtain ⟨T₀, hT₀4, hmass⟩ := exists_xiSymmetricMass_close (ε' / 2) (by positivity)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 / 2 + ‖c‖ := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖c‖ := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ norm_nonneg c
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = 2 / ε' * (1 / Real.pi) * (Real.log 2 + K) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + 2 / (Real.pi * ε') := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  have hML : 0 ≤ 4 * M * L := by positivity
  filter_upwards [eventually_ge_atTop (T₀ + 2 * K + 2), eventually_ge_atTop (Real.exp A₁),
    eventually_ge_atTop (4 * M * L + 3)] with R hR1 hR2 hR3
  have hR0 : 0 < R := by linarith
  have hR3' : 3 ≤ R := by linarith
  have hRlog1 : 1 ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le hR0]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)).trans hR3'
  have hRL : L ≤ R := by nlinarith
  set N := ((∑ᶠ z, MeromorphicOn.divisor XiC (closedBall c R) z : ℤ) : ℝ) with hN
  have hRlog : 0 ≤ R * Real.log R := by positivity
  -- lower bound
  have hlow : (1 / Real.pi - ε') * (R * Real.log R) ≤ N := by
    obtain ⟨T, hTdef⟩ : ∃ T, T = R - K := ⟨_, rfl⟩
    have hT : T₀ ≤ T := by rw [hTdef]; linarith
    have hTpos : 0 < T := by rw [hTdef]; linarith
    have hdisc := xiSymmetricMass_le_finsum_divisor_XiC c (r := R) (T := T) hTpos.le
      (le_of_eq (by rw [hTdef, hK]; ring))
    have hmT := (abs_le.mp (hmass T hT)).1
    have hlogT : Real.log R - Real.log 2 ≤ Real.log T := by
      rw [← Real.log_div hR0.ne' two_ne_zero]
      exact Real.log_le_log (by positivity) (by rw [hTdef]; linarith)
    have hlogr : Real.log R ≤ R := (Real.log_le_sub_one_of_pos hR0).trans (by linarith)
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hTT : R * Real.log R - (Real.log 2 + K) * R ≤ T * Real.log T := by
      have h1 : T * (Real.log R - Real.log 2) ≤ T * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT hTpos.le
      have h2 : T * (Real.log R - Real.log 2) = R * Real.log R - R * Real.log 2 - K * Real.log R +
          K * Real.log 2 := by rw [hTdef]; ring
      have h3 := mul_le_mul_of_nonneg_left hlogr hK0.le
      have h4 : 0 ≤ K * Real.log 2 := mul_nonneg hK0.le hlog2
      linarith
    have hA : A₁ ≤ Real.log R := by
      rw [Real.le_log_iff_exp_le hR0]; exact hR2
    have hkey : (1 / Real.pi - ε' / 2) * (Real.log 2 + K) * R ≤ ε' / 2 * (R * Real.log R) := by
      have h1 : (1 / Real.pi - ε' / 2) * (Real.log 2 + K) ≤ ε' / 2 * A₁ := by
        have hsub : 1 / Real.pi - ε' / 2 ≤ 1 / Real.pi := by linarith
        have hpos : 0 ≤ Real.log 2 + K := by linarith
        have hA1 : ε' / 2 * A₁ = 1 / Real.pi * (Real.log 2 + K) := by rw [hA₁]; field_simp
        rw [hA1]; exact mul_le_mul_of_nonneg_right hsub hpos
      have h2 : ε' / 2 * A₁ ≤ ε' / 2 * Real.log R := mul_le_mul_of_nonneg_left hA (by positivity)
      have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) hR0.le
      linarith
    have hc0 : 0 ≤ 1 / Real.pi - ε' / 2 := by linarith
    have h3 : (1 / Real.pi - ε' / 2) * (R * Real.log R - (Real.log 2 + K) * R) ≤
        (1 / Real.pi - ε' / 2) * (T * Real.log T) := mul_le_mul_of_nonneg_left hTT hc0
    have h4 : (1 / Real.pi - ε' / 2) * (T * Real.log T) ≤ (xiSymmetricMass T : ℝ) := by linarith
    have h5 : (xiSymmetricMass T : ℝ) ≤ N := by rw [hN]; exact_mod_cast hdisc
    have h6 : (1 / Real.pi - ε') * (R * Real.log R) = (1 / Real.pi - ε' / 2) * (R * Real.log R) -
        ε' / 2 * (R * Real.log R) := by ring
    have h7 : (1 / Real.pi - ε' / 2) * (R * Real.log R - (Real.log 2 + K) * R) =
        (1 / Real.pi - ε' / 2) * (R * Real.log R) - (1 / Real.pi - ε' / 2) * (Real.log 2 + K) * R := by
      ring
    linarith
  -- upper bound
  have hup : N ≤ (1 / Real.pi + ε') * (R * Real.log R) := by
    have hTu : T₀ ≤ R + L := by linarith
    have hdisc := finsum_divisor_XiC_le_xiSymmetricMass c hR0.le
    rw [← hL] at hdisc
    have hmT := (abs_le.mp (hmass (R + L) hTu)).2
    have hlogRL : Real.log (R + L) ≤ Real.log R + L / R := by
      rw [show R + L = R * (1 + L / R) by field_simp, Real.log_mul hR0.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + L / R by positivity)
      linarith
    have hRLlog : (R + L) * Real.log (R + L) ≤ R * Real.log R + L * Real.log R + 2 * L := by
      have h1 : (R + L) * Real.log (R + L) ≤ (R + L) * (Real.log R + L / R) :=
        mul_le_mul_of_nonneg_left hlogRL (by linarith)
      have h2 : (R + L) * (Real.log R + L / R) = R * Real.log R + L * Real.log R + L + L * (L / R) := by
        field_simp; ring
      have h3 : L * (L / R) ≤ L := by
        rw [mul_div_assoc']; exact div_le_of_le_mul₀ hR0.le hL0 (mul_le_mul_of_nonneg_left hRL hL0)
      linarith
    have hsmall : (1 / Real.pi + ε' / 2) * (L * Real.log R + 2 * L) ≤ ε' / 2 * (R * Real.log R) := by
      have hMe : (1 / Real.pi + ε' / 2) = ε' / 2 * M := by rw [hM]; field_simp; ring
      rw [hMe, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hMLR : M * L ≤ R / 4 := by nlinarith
      have h1 : M * (L * Real.log R) ≤ R / 4 * Real.log R := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hMLR (by linarith)
      have h2 : M * (2 * L) ≤ R / 2 * Real.log R := by
        have : M * (2 * L) ≤ R / 2 := by nlinarith
        exact this.trans (le_mul_of_one_le_right (by positivity) hRlog1)
      have h3 : R / 4 * Real.log R + R / 2 * Real.log R ≤ R * Real.log R := by nlinarith
      nlinarith
    have hmass' : (xiSymmetricMass (R + L) : ℝ) ≤
        (1 / Real.pi + ε' / 2) * ((R + L) * Real.log (R + L)) := by linarith
    have h5 : N ≤ (xiSymmetricMass (R + L) : ℝ) := by rw [hN]; exact_mod_cast hdisc
    have hc0 : 0 ≤ 1 / Real.pi + ε' / 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_left hRLlog hc0
    have h7 : (1 / Real.pi + ε' / 2) * (R * Real.log R + L * Real.log R + 2 * L) =
        (1 / Real.pi + ε' / 2) * (R * Real.log R) + (1 / Real.pi + ε' / 2) * (L * Real.log R + 2 * L) := by
      ring
    have h8 : (1 / Real.pi + ε') * (R * Real.log R) =
        (1 / Real.pi + ε' / 2) * (R * Real.log R) + ε' / 2 * (R * Real.log R) := by ring
    linarith
  have hεR := mul_le_mul_of_nonneg_right hε'ε hRlog
  rw [abs_le]
  constructor
  · have : (1 / Real.pi - ε') * (R * Real.log R) = 1 / Real.pi * (R * Real.log R) - ε' * (R * Real.log R) := by
      ring
    linarith
  · have : (1 / Real.pi + ε') * (R * Real.log R) = 1 / Real.pi * (R * Real.log R) + ε' * (R * Real.log R) := by
      ring
    linarith

/-! ## The Gaussian control violates (3) -/

theorem sectorialRay_eq (δ R : ℝ) :
    sectorialRay δ R = (R : ℂ) * ((Real.sin δ : ℂ) - (Real.cos δ : ℂ) * I) := by
  rw [sectorialRay]; push_cast; ring

/-- **The control quotient is not sectorially bounded.** For `ω ≠ 0` there is a ray angle
`δ ∈ (0, π/2)` along which `e^{-ω²/4} cosh(ωz/2)` exceeds every bound
`C e^{(R+1/2) D(δ)}/cos δ` at arbitrarily large `R`: the linear angular cusp of the Gaussian control
is exactly what (3) forbids for the theta source. -/
theorem gaussPairQuotient_not_sectorially_bounded {ω : ℝ} (hω : ω ≠ 0) :
    ∃ δ, 0 < δ ∧ δ < Real.pi / 2 ∧ ∀ C R₁ : ℝ, ∃ R, R₁ ≤ R ∧
      C * Real.exp ((R + 1 / 2) * sectorialExponent δ) / Real.cos δ <
        ‖HTGeometry.gaussPairQuotient ω (sectorialRay δ R)‖ := by
  have hκ : 0 < |ω| / 2 := by positivity
  obtain ⟨δ₀, hδ₀, hlin⟩ := exists_sectorialExponent_lt_linear hκ
  set δ := min (δ₀ / 2) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδπ : δ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hδδ₀ : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hgap := hlin δ hδ0 hδδ₀
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)
  have hcos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hδπ⟩
  refine ⟨δ, hδ0, hδπ, fun C R₁ => ?_⟩
  set g := |ω| / 2 * Real.sin δ - sectorialExponent δ with hg
  have hg0 : 0 < g := by linarith
  set D := sectorialExponent δ
  set A := Real.log (4 * (|C| + 1) * Real.exp (ω ^ 2 / 4) / Real.cos δ) + |D| + Real.log 2 + 1
  set R := max (max R₁ 1) (A / g)
  have hR1 : R₁ ≤ R := le_max_of_le_left (le_max_left _ _)
  have hRone : 1 ≤ R := le_max_of_le_left (le_max_right _ _)
  have hRA : A / g ≤ R := le_max_right _ _
  refine ⟨R, hR1, ?_⟩
  have hlow := HTGeometry.sinh_le_norm_gaussPairQuotient_ray ω R δ
  rw [← sectorialRay_eq] at hlow
  set x := |ω * R * Real.sin δ| / 2 with hx
  have hxval : x = |ω| / 2 * Real.sin δ * R := by
    rw [hx, abs_mul, abs_mul, abs_of_pos hsin, abs_of_pos (by linarith : (0 : ℝ) < R)]; ring
  have hgR : A ≤ g * R := by rw [div_le_iff₀ hg0] at hRA; linarith
  -- `sinh x ≥ e^x/4` once `x ≥ log 2`
  have hxlog2 : Real.log 2 ≤ x := by
    have hDR : D * R ≤ |D| * R := mul_le_mul_of_nonneg_right (le_abs_self D) (by linarith)
    have hAx : Real.log 2 ≤ A := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * (|C| + 1) * Real.exp (ω ^ 2 / 4) / Real.cos δ by
        rw [le_div_iff₀ hcos]
        have := Real.one_le_exp (show 0 ≤ ω ^ 2 / 4 by positivity)
        nlinarith [Real.cos_le_one δ, abs_nonneg C])
      simp only [A]; linarith [abs_nonneg D]
    rw [hxval]
    have hDpos : 0 ≤ D * R := mul_nonneg (sectorialExponent_nonneg (by rw [abs_of_pos hδ0]; exact hδπ)) (by linarith)
    nlinarith
  have hsinh : Real.exp x / 4 ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    have h2 : Real.exp (-x) ≤ Real.exp x / 2 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have := Real.exp_le_exp.mpr hxlog2
      rw [Real.exp_log (by norm_num)] at this
      nlinarith [Real.exp_pos x]
    linarith
  -- the comparison of exponents
  have hbig : Real.log (4 * (|C| + 1) * Real.exp (ω ^ 2 / 4) / Real.cos δ) + (R + 1 / 2) * D < x := by
    rw [hxval]
    have : (R + 1 / 2) * D ≤ R * D + |D| := by nlinarith [le_abs_self D, abs_nonneg D]
    have hgRD : g * R = |ω| / 2 * Real.sin δ * R - D * R := by simp only [hg, D]; ring
    have hl2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    simp only [A] at hgR
    linarith
  have hpos : 0 < 4 * (|C| + 1) * Real.exp (ω ^ 2 / 4) / Real.cos δ := by positivity
  have hexp := Real.exp_lt_exp.mpr hbig
  rw [Real.exp_add, Real.exp_log hpos] at hexp
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * Real.exp ((R + 1 / 2) * D) / Real.cos δ ≤ (|C| + 1) * Real.exp ((R + 1 / 2) * D) / Real.cos δ := by
        gcongr
    _ = Real.exp (-ω ^ 2 / 4) * (4 * (|C| + 1) * Real.exp (ω ^ 2 / 4) / Real.cos δ *
          Real.exp ((R + 1 / 2) * D)) / 4 := by
        rw [show Real.exp (-ω ^ 2 / 4) = (Real.exp (ω ^ 2 / 4))⁻¹ by rw [← Real.exp_neg]; ring_nf]
        field_simp
    _ < Real.exp (-ω ^ 2 / 4) * Real.exp x / 4 := by gcongr
    _ ≤ Real.exp (-ω ^ 2 / 4) * Real.sinh x := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hsinh (Real.exp_pos _).le
    _ ≤ _ := hlow

end

end RHTower
