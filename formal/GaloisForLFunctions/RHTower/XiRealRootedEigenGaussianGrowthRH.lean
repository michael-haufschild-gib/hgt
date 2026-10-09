import GaloisForLFunctions.RHTower.XiRealRootedApproxEigenLimitRH

/-!
# Real-rooted eigenvector transforms of Gaussian growth force RH

Let `G_j` be holomorphic on the strip `|Im z| < 1/2 + η`, with only real zeros there and
`G_j(0) = 1`. Suppose that on the strip

* `‖G_j(z)‖ ≤ M e^{A (Re z)²}` (uniform Gaussian growth), and
* `‖G_j(z)‖ ≤ M e^{K a_j}` (Paley–Wiener growth at aperture `a_j`),

and that each `G_j` satisfies the zero-side eigen-equation against every smooth test supported in
`[-R, R]`, `R < a_j`, with `a_j → ∞`. Then the Riemann hypothesis holds.

Uniform boundedness on the strip is not needed. The weights `G_j(z) e^{-σz²}`, `σ = A + 1`, are
uniformly bounded, and they satisfy the eigen-equation asymptotically. The Gaussian
`e^{-σz²} e^{-izu}` is the transform of a Gaussian in the shift variable. Smearing the exact
eigen-equation on translated bumps over shifts in `[-R, R]`, `R = a_j - 2`, reproduces it up to the
Gaussian tail beyond `R`. Against the Paley–Wiener growth `e^{K a_j}` that tail tends to zero.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The Gaussian weight in the shift variable -/

/-- The normalizing constant `(4πσ)^{1/2}` of the Gaussian Fourier pair. -/
def gaussShiftConst (σ : ℝ) : ℂ := ((Real.pi : ℂ) / -(-(1 / (4 * (σ : ℂ))))) ^ (1 / 2 : ℂ)

theorem gaussShiftConst_ne_zero {σ : ℝ} (hσ : 0 < σ) : gaussShiftConst σ ≠ 0 := by
  rw [gaussShiftConst, Ne, Complex.cpow_eq_zero_iff]
  rintro ⟨h, -⟩
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [neg_neg, div_eq_zero_iff] at h
  rcases h with h | h
  · exact hpi h
  · exact (one_div_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hσ')) h

/-- The Gaussian weight `v ↦ (4πσ)^{-1/2} e^{-(v-u)²/(4σ)}`, whose transform is
`e^{-σz²} e^{-izu}`. -/
def gaussShiftWeight (σ u : ℝ) (v : ℝ) : ℂ :=
  (gaussShiftConst σ)⁻¹ * cexp (-(((v : ℂ) - u) ^ 2) / (4 * σ))

theorem integral_gaussShiftWeight_mul (σ u : ℝ) (hσ : 0 < σ) (z : ℂ) :
    ∫ v : ℝ, gaussShiftWeight σ u v * cexp (-(I * z) * v) =
      cexp (-(σ : ℂ) * z ^ 2) * cexp (-(I * z) * u) := by
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  set b : ℂ := -(1 / (4 * (σ : ℂ))) with hb
  have hbre : b.re < 0 := by
    have : (1 / (4 * (σ : ℂ))) = ((1 / (4 * σ) : ℝ) : ℂ) := by push_cast; ring
    rw [hb, this, neg_re, ofReal_re]
    have : 0 < 1 / (4 * σ) := by positivity
    linarith
  set c : ℂ := (u : ℂ) / (2 * σ) - I * z with hc
  set d : ℂ := -((u : ℂ) ^ 2) / (4 * σ) with hd
  have key := integral_cexp_quadratic hbre c d
  have hpt : ∀ v : ℝ, gaussShiftWeight σ u v * cexp (-(I * z) * v) =
      (gaussShiftConst σ)⁻¹ * cexp (b * (v : ℂ) ^ 2 + c * v + d) := by
    intro v
    rw [gaussShiftWeight, mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hb, hc, hd]
    field_simp
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul, key]
  have hP : gaussShiftConst σ ≠ 0 := gaussShiftConst_ne_zero hσ
  have hPeq : ((Real.pi : ℂ) / -b) ^ (1 / 2 : ℂ) = gaussShiftConst σ := by
    rw [gaussShiftConst, hb]
  rw [hPeq, ← mul_assoc, inv_mul_cancel₀ hP, one_mul, ← Complex.exp_add]
  congr 1
  rw [hb, hc, hd]
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem norm_gaussShiftWeight (σ u v : ℝ) :
    ‖gaussShiftWeight σ u v‖ = ‖gaussShiftConst σ‖⁻¹ * Real.exp (-((v - u) ^ 2) / (4 * σ)) := by
  rw [gaussShiftWeight, norm_mul, norm_inv, Complex.norm_exp]
  congr 2
  have : -(((v : ℂ) - u) ^ 2) / (4 * σ) = ((-((v - u) ^ 2) / (4 * σ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]

theorem continuous_gaussShiftWeight (σ u : ℝ) : Continuous (gaussShiftWeight σ u) := by
  unfold gaussShiftWeight
  fun_prop

/-- Completing the square: `-(v-u)²/(4σ) + c|v| ≤ -v²/(8σ) + 2σ(|u|/(2σ) + |c|)²`. -/
theorem neg_sq_div_add_mul_abs_le {σ : ℝ} (hσ : 0 < σ) (u c v : ℝ) :
    -((v - u) ^ 2) / (4 * σ) + c * |v| ≤
      -(1 / (8 * σ)) * v ^ 2 + 2 * σ * (|u| / (2 * σ) + |c|) ^ 2 := by
  have h8 : 0 < 8 * σ := by positivity
  have h1 : -((v - u) ^ 2) / (4 * σ) + c * |v| = (-2 * (v - u) ^ 2 + 8 * σ * (c * |v|)) / (8 * σ) := by
    field_simp; ring
  have h2 : -(1 / (8 * σ)) * v ^ 2 + 2 * σ * (|u| / (2 * σ) + |c|) ^ 2 =
      (-v ^ 2 + 4 * (|u| + 2 * σ * |c|) ^ 2) / (8 * σ) := by
    field_simp; ring
  rw [h1, h2]
  apply div_le_div_of_nonneg_right _ h8.le
  have hcv : 8 * σ * (c * |v|) ≤ 8 * σ * (|c| * |v|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg v)) h8.le
  have huv : u * v ≤ |u| * |v| := by rw [← abs_mul]; exact le_abs_self _
  have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  nlinarith [sq_nonneg (|v| - 2 * (|u| + 2 * σ * |c|)), sq_nonneg u, abs_nonneg v]

/-- The Gaussian weight against any exponential `e^{c|v|}` is integrable. -/
theorem integrable_norm_gaussShiftWeight_mul_exp {σ : ℝ} (hσ : 0 < σ) (u c : ℝ) :
    Integrable fun v : ℝ => ‖gaussShiftWeight σ u v‖ * Real.exp (c * |v|) := by
  set K : ℝ := 2 * σ * (|u| / (2 * σ) + |c|) ^ 2 with hK
  have hdom : Integrable fun v : ℝ =>
      ‖gaussShiftConst σ‖⁻¹ * Real.exp K * Real.exp (-(1 / (8 * σ)) * v ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hdom.mono' (((continuous_gaussShiftWeight σ u).norm.mul
    (by fun_prop : Continuous fun v : ℝ => Real.exp (c * |v|))).aestronglyMeasurable)
    (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_gaussShiftWeight]
  calc ‖gaussShiftConst σ‖⁻¹ * Real.exp (-((v - u) ^ 2) / (4 * σ)) * Real.exp (c * |v|)
      = ‖gaussShiftConst σ‖⁻¹ * Real.exp (-((v - u) ^ 2) / (4 * σ) + c * |v|) := by
        rw [Real.exp_add]; ring
    _ ≤ ‖gaussShiftConst σ‖⁻¹ * Real.exp (-(1 / (8 * σ)) * v ^ 2 + K) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have := neg_sq_div_add_mul_abs_le hσ u c v
        linarith
    _ = ‖gaussShiftConst σ‖⁻¹ * Real.exp K * Real.exp (-(1 / (8 * σ)) * v ^ 2) := by
        rw [Real.exp_add]; ring

/-! ## Smearing over shifts -/

/-- Smearing a sum of exponentials over shifts in `[-R, R]`: the sum and the shift integral
commute. -/
theorem tsum_mul_setIntegral_Icc_eq {ι : Type*} [Countable ι] {A : ι → ℂ} {w : ι → ℂ} {Y : ℝ}
    (hA : Summable fun q => ‖A q‖) (hw : ∀ q, |(w q).im| ≤ Y) {ϕ : ℝ → ℂ} (hϕ : Continuous ϕ)
    (R : ℝ) :
    ∑' q, A q * ∫ v in Icc (-R) R, ϕ v * cexp (-(I * w q) * v) =
      ∫ v in Icc (-R) R, ϕ v * ∑' q, A q * cexp (-(I * w q) * v) := by
  set Cϕ : ℝ := ∫ v in Icc (-R) R, ‖ϕ v‖ * Real.exp (Y * |v|) with hCϕ
  have hint : ∀ q, IntegrableOn (fun v : ℝ => A q * (ϕ v * cexp (-(I * w q) * v)))
      (Icc (-R) R) := fun q => (by fun_prop : Continuous fun v : ℝ =>
        A q * (ϕ v * cexp (-(I * w q) * v))).integrableOn_Icc
  have hbd : ∀ q, ∫ v in Icc (-R) R, ‖A q * (ϕ v * cexp (-(I * w q) * v))‖ ≤ ‖A q‖ * Cϕ := by
    intro q
    rw [hCϕ, ← integral_const_mul]
    refine setIntegral_mono_on (hint q).norm ?_ measurableSet_Icc (fun v _ => ?_)
    · exact ((by fun_prop : Continuous fun v : ℝ =>
        ‖ϕ v‖ * Real.exp (Y * |v|)).integrableOn_Icc).const_mul _
    · rw [norm_mul, norm_mul, norm_cexp_neg_I_mul_ofReal]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (norm_nonneg _)) (norm_nonneg _)
      calc v * (w q).im ≤ |v * (w q).im| := le_abs_self _
        _ = |v| * |(w q).im| := abs_mul _ _
        _ ≤ |v| * Y := by gcongr; exact hw q
        _ = Y * |v| := mul_comm _ _
  have hsum : Summable fun q => ∫ v in Icc (-R) R, ‖A q * (ϕ v * cexp (-(I * w q) * v))‖ :=
    (hA.mul_right Cϕ).of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hbd
  have h1 : ∀ q, A q * ∫ v in Icc (-R) R, ϕ v * cexp (-(I * w q) * v) =
      ∫ v in Icc (-R) R, A q * (ϕ v * cexp (-(I * w q) * v)) :=
    fun q => (integral_const_mul _ _).symm
  simp_rw [h1]
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  funext v
  rw [← tsum_mul_left]
  congr 1
  funext q
  ring

/-- Smearing a line integral of exponentials over shifts in `[-R, R]`: the two integrals
commute. -/
theorem integral_mul_setIntegral_Icc_swap {H : ℝ → ℂ} (hH : Continuous H) (hHi : Integrable H)
    {ϕ : ℝ → ℂ} (hϕ : Continuous ϕ) (R : ℝ) :
    ∫ s : ℝ, H s * ∫ v in Icc (-R) R, ϕ v * cexp (-(I * (s : ℂ)) * v) =
      ∫ v in Icc (-R) R, ϕ v * ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * v) := by
  have h1 : ∀ s : ℝ, H s * ∫ v in Icc (-R) R, ϕ v * cexp (-(I * (s : ℂ)) * v) =
      ∫ v in Icc (-R) R, H s * (ϕ v * cexp (-(I * (s : ℂ)) * v)) :=
    fun s => (integral_const_mul _ _).symm
  have h2 : ∀ v : ℝ, ϕ v * ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * v) =
      ∫ s : ℝ, H s * (ϕ v * cexp (-(I * (s : ℂ)) * v)) := by
    intro v
    rw [← integral_const_mul]
    congr 1
    funext s
    ring
  simp_rw [h1, h2]
  refine integral_integral_swap ?_
  have hϕi : Integrable ϕ (volume.restrict (Icc (-R) R)) := hϕ.integrableOn_Icc
  refine (hHi.norm.mul_prod hϕi.norm).mono' ?_ (ae_of_all _ fun p => ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      H p.1 * (ϕ p.2 * cexp (-(I * (p.1 : ℂ)) * p.2))).aestronglyMeasurable
  · show ‖H p.1 * (ϕ p.2 * cexp (-(I * (p.1 : ℂ)) * p.2))‖ ≤ ‖H p.1‖ * ‖ϕ p.2‖
    rw [norm_mul, norm_mul, norm_cexp_neg_I_mul_ofReal]
    simp

/-! ## The defect of the eigen-equation -/

/-- The defect of the zero-side eigen-equation on the test transform `z ↦ b̂(c - z) Ψ(z)`. -/
def eigenDefect (G : ℂ → ℂ) (κ : ℂ) (b : SuzukiSmoothCompactTest 1) (c : ℝ) (Ψ : ℂ → ℂ) : ℂ :=
  (∑' q : XiZeroCopy, G (xiSpectralPoint q) *
      (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) * Ψ (xiSpectralPoint q))) -
    κ * ∫ s : ℝ, G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * Ψ (s : ℂ))

/-- The constant in the defect bound. -/
def eigenDefectConst (b : SuzukiSmoothCompactTest 1) (η c : ℝ) : ℝ :=
  2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η) *
    ((∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) + ∫ s : ℝ, (1 + s ^ 2)⁻¹)

private theorem abs_im_xiSpectralPoint_le (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  have := xiSpectralPoint_im_mem_openHalf q
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem mem_xiOneSidedStrip_xiSpectralPoint {η : ℝ} (hη : 0 < η) (q : XiZeroCopy) :
    xiSpectralPoint q ∈ xiOneSidedStrip η := by
  show |(xiSpectralPoint q).im| < 1 / 2 + η
  linarith [abs_im_xiSpectralPoint_le q]

theorem ofReal_mem_xiOneSidedStrip {η : ℝ} (hη : 0 < η) (s : ℝ) :
    (s : ℂ) ∈ xiOneSidedStrip η := by
  show |((s : ℂ)).im| < 1 / 2 + η
  simp; linarith

theorem norm_eigenDefect_term_le {η B ε : ℝ} (hη : 0 < η) {G : ℂ → ℂ}
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c : ℝ)
    {Ψ : ℂ → ℂ} {z : ℂ} (hz : z ∈ xiOneSidedStrip η) (hΨ : ‖Ψ z‖ ≤ ε) :
    ‖G z * (suzukiSmoothFourier b ((c : ℂ) - z) * Ψ z)‖ ≤
      B * ε * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)) / (1 + ‖z‖ ^ 2) := by
  have hY : (0 : ℝ) ≤ 1 / 2 + η := by linarith
  have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := z) (le_of_lt hz)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB z hz)
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  rw [norm_mul, norm_mul]
  calc ‖G z‖ * (‖suzukiSmoothFourier b ((c : ℂ) - z)‖ * ‖Ψ z‖)
      ≤ B * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η) / (1 + ‖z‖ ^ 2) * ε) := by
        have hK := suzukiTestDecayConst_nonneg b (1 / 2 + η)
        exact mul_le_mul (hB z hz) (mul_le_mul hb hΨ (norm_nonneg _) (by positivity))
          (by positivity) hB0
    _ = B * ε * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)) / (1 + ‖z‖ ^ 2) := by
        ring

theorem norm_eigenDefect_le {η B ε : ℝ} (hη : 0 < η) {G : ℂ → ℂ} {κ : ℂ}
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c : ℝ)
    {Ψ : ℂ → ℂ} (hΨq : ∀ q : XiZeroCopy, ‖Ψ (xiSpectralPoint q)‖ ≤ ε)
    (hΨs : ∀ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ ε) :
    ‖eigenDefect G κ b c Ψ‖ ≤ (1 + ‖κ‖) * (B * ε * eigenDefectConst b η c) := by
  set P : ℝ := B * ε * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)) with hP
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (ofReal_mem_xiOneSidedStrip hη 0))
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hΨs 0)
  have hK : 0 ≤ suzukiTestDecayConst b (1 / 2 + η) := suzukiTestDecayConst_nonneg b _
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set Sq : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hSq
  set I1 : ℝ := ∫ s : ℝ, (1 + s ^ 2)⁻¹ with hI1
  have hSq0 : 0 ≤ Sq := tsum_nonneg fun q => by positivity
  have hI10 : 0 ≤ I1 := integral_nonneg fun s => by positivity
  have hsum : ‖∑' q : XiZeroCopy, G (xiSpectralPoint q) *
      (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) * Ψ (xiSpectralPoint q))‖ ≤ P * Sq := by
    refine tsum_of_norm_bounded (xiSpectralPoint_inv_sq_summable.hasSum.mul_left P) fun q => ?_
    have h := norm_eigenDefect_term_le hη hB b c (mem_xiOneSidedStrip_xiSpectralPoint hη q)
      (hΨq q)
    rw [← hP] at h
    refine h.trans ?_
    have hq0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
    rw [div_eq_mul_one_div]
    gcongr
    linarith
  have hint : ‖∫ s : ℝ, G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * Ψ (s : ℂ))‖ ≤
      P * I1 := by
    rw [hI1, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul P)
      (ae_of_all _ fun s => ?_)
    have h := norm_eigenDefect_term_le hη hB b c (ofReal_mem_xiOneSidedStrip hη s) (hΨs s)
    rw [← hP] at h
    have hs2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by simp [sq_abs]
    rw [hs2] at h
    simpa [div_eq_mul_inv] using h
  have hconst : B * ε * eigenDefectConst b η c = P * (Sq + I1) := by
    rw [eigenDefectConst, hP, hSq, hI1]; ring
  rw [hconst, eigenDefect]
  calc ‖(∑' q : XiZeroCopy, G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) * Ψ (xiSpectralPoint q))) -
        κ * ∫ s : ℝ, G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * Ψ (s : ℂ))‖
      ≤ P * Sq + ‖κ‖ * (P * I1) := by
        refine (norm_sub_le _ _).trans (add_le_add hsum ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ (1 + ‖κ‖) * (P * (Sq + I1)) := by
        have hk : 0 ≤ ‖κ‖ := norm_nonneg _
        nlinarith [mul_nonneg hP0 hSq0, mul_nonneg hP0 hI10, mul_nonneg hk (mul_nonneg hP0 hSq0)]

theorem norm_eigenDefect_term_q_le {η B ε : ℝ} (hη : 0 < η) {G : ℂ → ℂ}
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c : ℝ)
    {Ψ : ℂ → ℂ} (q : XiZeroCopy) (hΨ : ‖Ψ (xiSpectralPoint q)‖ ≤ ε) :
    ‖G (xiSpectralPoint q) * (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
        Ψ (xiSpectralPoint q))‖ ≤
      B * ε * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have h := norm_eigenDefect_term_le hη hB b c (mem_xiOneSidedStrip_xiSpectralPoint hη q) hΨ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (ofReal_mem_xiOneSidedStrip hη 0))
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) hΨ
  have hK := suzukiTestDecayConst_nonneg b (1 / 2 + η)
  refine h.trans ?_
  have hq0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
  rw [div_eq_mul_one_div]
  gcongr
  linarith

theorem norm_eigenDefect_term_s_le {η B ε : ℝ} (hη : 0 < η) {G : ℂ → ℂ}
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c : ℝ)
    {Ψ : ℂ → ℂ} (s : ℝ) (hΨ : ‖Ψ (s : ℂ)‖ ≤ ε) :
    ‖G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * Ψ (s : ℂ))‖ ≤
      B * ε * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)) * (1 + s ^ 2)⁻¹ := by
  have h := norm_eigenDefect_term_le hη hB b c (ofReal_mem_xiOneSidedStrip hη s) hΨ
  have hs2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by simp [sq_abs]
  rw [hs2] at h
  simpa [div_eq_mul_inv] using h

theorem continuous_ofReal_of_differentiableOn_strip {η : ℝ} (hη : 0 < η) {G : ℂ → ℂ}
    (hGdiff : DifferentiableOn ℂ G (xiOneSidedStrip η)) : Continuous fun s : ℝ => G (s : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hc : ContinuousAt G (s : ℂ) := (hGdiff.differentiableAt ((isOpen_xiOneSidedStrip η).mem_nhds
    (ofReal_mem_xiOneSidedStrip hη s))).continuousAt
  exact ContinuousAt.comp (g := G) hc Complex.continuous_ofReal.continuousAt

theorem eigenDefect_sub {η B ε₁ ε₂ : ℝ} (hη : 0 < η) {G : ℂ → ℂ} {κ : ℂ}
    (hGdiff : DifferentiableOn ℂ G (xiOneSidedStrip η))
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c : ℝ)
    {Ψ₁ Ψ₂ : ℂ → ℂ}
    (h1q : ∀ q : XiZeroCopy, ‖Ψ₁ (xiSpectralPoint q)‖ ≤ ε₁) (h1s : ∀ s : ℝ, ‖Ψ₁ (s : ℂ)‖ ≤ ε₁)
    (h1c : Continuous fun s : ℝ => Ψ₁ (s : ℂ))
    (h2q : ∀ q : XiZeroCopy, ‖Ψ₂ (xiSpectralPoint q)‖ ≤ ε₂) (h2s : ∀ s : ℝ, ‖Ψ₂ (s : ℂ)‖ ≤ ε₂)
    (h2c : Continuous fun s : ℝ => Ψ₂ (s : ℂ)) :
    eigenDefect G κ b c Ψ₁ - eigenDefect G κ b c Ψ₂ =
      eigenDefect G κ b c (fun z => Ψ₁ z - Ψ₂ z) := by
  have hsum : ∀ {Ψ : ℂ → ℂ} {ε : ℝ}, (∀ q : XiZeroCopy, ‖Ψ (xiSpectralPoint q)‖ ≤ ε) →
      Summable fun q : XiZeroCopy => G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) * Ψ (xiSpectralPoint q)) :=
    fun hq => Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left _)
      fun q => norm_eigenDefect_term_q_le hη hB b c q (hq q)
  have hGc := continuous_ofReal_of_differentiableOn_strip hη hGdiff
  have hbc : Continuous fun s : ℝ => suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) :=
    (differentiable_suzukiSmoothFourier zero_le_one b).continuous.comp (by fun_prop)
  have hint : ∀ {Ψ : ℂ → ℂ} {ε : ℝ}, (∀ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ ε) →
      (Continuous fun s : ℝ => Ψ (s : ℂ)) →
      Integrable fun s : ℝ => G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * Ψ (s : ℂ)) :=
    fun hs hc => (integrable_inv_one_add_sq.const_mul _).mono'
      (hGc.mul (hbc.mul hc)).aestronglyMeasurable
      (ae_of_all _ fun s => norm_eigenDefect_term_s_le hη hB b c s (hs s))
  unfold eigenDefect
  rw [sub_sub_sub_comm, ← (hsum h1q).tsum_sub (hsum h2q), ← mul_sub,
    ← integral_sub (hint h1s h1c) (hint h2s h2c)]
  congr 1
  · exact tsum_congr fun q => by ring
  · congr 1
    exact integral_congr_ae (ae_of_all _ fun s => by ring)

/-! ## The smeared eigen-equation is exact -/

/-- The shift-smeared transform `Ψ_R(z) = ∫_{-R}^{R} ϕ(v) e^{-izv} dv`. -/
def shiftSmear (ϕ : ℝ → ℂ) (R : ℝ) (z : ℂ) : ℂ := ∫ v in Icc (-R) R, ϕ v * cexp (-(I * z) * v)

/-- Smearing the exact eigen-equations on shifts `|v| ≤ R` against any continuous weight gives the
exact eigen-equation on the smeared transform. -/
theorem eigenDefect_shiftSmear_eq_zero {η B : ℝ} (hη : 0 < η) {G : ℂ → ℂ} {κ : ℂ}
    (hGdiff : DifferentiableOn ℂ G (xiOneSidedStrip η))
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c R : ℝ)
    {ϕ : ℝ → ℂ} (hϕ : Continuous ϕ)
    (hid : ∀ v : ℝ, |v| ≤ R → ∑' q : XiZeroCopy, G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * v)) =
      κ * ∫ s : ℝ, G (s : ℂ) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * v))) :
    eigenDefect G κ b c (shiftSmear ϕ R) = 0 := by
  set A : XiZeroCopy → ℂ := fun q =>
    G (xiSpectralPoint q) * suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) with hAdef
  have hA : Summable fun q => ‖A q‖ := by
    refine (xiSpectralPoint_inv_sq_summable.mul_left
      (B * 1 * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)))).of_nonneg_of_le
        (fun q => norm_nonneg _) (fun q => ?_)
    have := norm_eigenDefect_term_q_le hη hB b c (Ψ := fun _ => 1) (ε := 1) q (by simp)
    simpa [hAdef] using this
  have hbc : Continuous fun s : ℝ => suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) :=
    (differentiable_suzukiSmoothFourier zero_le_one b).continuous.comp (by fun_prop)
  set H : ℝ → ℂ := fun s => G (s : ℂ) * suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) with hHdef
  have hHc : Continuous H := (continuous_ofReal_of_differentiableOn_strip hη hGdiff).mul hbc
  have hHi : Integrable H := by
    refine (integrable_inv_one_add_sq.const_mul
      (B * 1 * (2 * (1 + c ^ 2) * suzukiTestDecayConst b (1 / 2 + η)))).mono'
        hHc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    have := norm_eigenDefect_term_s_le hη hB b c (Ψ := fun _ => 1) (ε := 1) s (by simp)
    simpa [hHdef] using this
  have hL : ∑' q : XiZeroCopy, G (xiSpectralPoint q) *
      (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) * shiftSmear ϕ R (xiSpectralPoint q)) =
      ∫ v in Icc (-R) R, ϕ v * ∑' q, A q * cexp (-(I * xiSpectralPoint q) * v) := by
    rw [← tsum_mul_setIntegral_Icc_eq hA (fun q => abs_im_xiSpectralPoint_le q) hϕ R]
    exact tsum_congr fun q => by simp only [shiftSmear, hAdef]; ring
  have hR : ∫ s : ℝ, G (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) *
      shiftSmear ϕ R (s : ℂ)) =
      ∫ v in Icc (-R) R, ϕ v * ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * v) := by
    rw [← integral_mul_setIntegral_Icc_swap hHc hHi hϕ R]
    exact integral_congr_ae (ae_of_all _ fun s => by simp only [shiftSmear, hHdef]; ring)
  unfold eigenDefect
  rw [hL, hR, sub_eq_zero, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun v hv => ?_)
  have hv' : |v| ≤ R := abs_le.mpr hv
  have h' : ∑' q, A q * cexp (-(I * xiSpectralPoint q) * v) =
      κ * ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * v) := by
    have := hid v hv'
    simpa [hAdef, hHdef, mul_assoc] using this
  show ϕ v * ∑' q, A q * cexp (-(I * xiSpectralPoint q) * v) =
    κ * (ϕ v * ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * v))
  rw [h']
  ring

/-! ## The Gaussian tail -/

/-- The Gaussian tail beyond `[-R, R]`, weighted by `e^{|v|/2}`. -/
def gaussShiftTail (σ u R : ℝ) : ℝ :=
  ∫ v in (Icc (-R) R)ᶜ, ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|)

theorem norm_gaussShiftWeight_mul_cexp_le (σ u v : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖gaussShiftWeight σ u v * cexp (-(I * z) * v)‖ ≤
      ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|) := by
  rw [norm_mul, norm_cexp_neg_I_mul_ofReal]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  calc v * z.im ≤ |v * z.im| := le_abs_self _
    _ = |v| * |z.im| := abs_mul _ _
    _ ≤ |v| * (1 / 2) := by gcongr
    _ = 1 / 2 * |v| := mul_comm _ _

theorem norm_gauss_sub_shiftSmear_le {σ : ℝ} (hσ : 0 < σ) (u R : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖cexp (-(σ : ℂ) * z ^ 2) * cexp (-(I * z) * u) - shiftSmear (gaussShiftWeight σ u) R z‖ ≤
      gaussShiftTail σ u R := by
  have hint : Integrable fun v : ℝ => gaussShiftWeight σ u v * cexp (-(I * z) * v) :=
    (integrable_norm_gaussShiftWeight_mul_exp hσ u (1 / 2)).mono'
      ((continuous_gaussShiftWeight σ u).mul (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun v => norm_gaussShiftWeight_mul_cexp_le σ u v hz)
  rw [← integral_gaussShiftWeight_mul σ u hσ z, shiftSmear,
    ← integral_add_compl measurableSet_Icc hint, add_sub_cancel_left]
  exact norm_integral_le_of_norm_le
    (integrable_norm_gaussShiftWeight_mul_exp hσ u (1 / 2)).integrableOn
    (ae_of_all _ fun v => norm_gaussShiftWeight_mul_cexp_le σ u v hz)

theorem tendsto_exp_mul_gaussShiftTail {σ K : ℝ} (hσ : 0 < σ) (hK : 0 ≤ K) (u : ℝ) :
    Tendsto (fun R => Real.exp (K * R) * gaussShiftTail σ u R) atTop (𝓝 0) := by
  set f : ℝ → ℝ := fun v => ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|) with hf
  have hfc : Continuous f := (continuous_gaussShiftWeight σ u).norm.mul (by fun_prop)
  have hrw : ∀ R, Real.exp (K * R) * gaussShiftTail σ u R =
      ∫ v, (Icc (-R) R)ᶜ.indicator (fun v => Real.exp (K * R) * f v) v := by
    intro R
    rw [integral_indicator measurableSet_Icc.compl, gaussShiftTail, integral_const_mul]
  simp_rw [hrw]
  have h0 : (0 : ℝ) = ∫ _v : ℝ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => ‖gaussShiftWeight σ u v‖ * Real.exp ((K + 1 / 2) * |v|)) ?_ ?_
    (integrable_norm_gaussShiftWeight_mul_exp hσ u (K + 1 / 2)) ?_
  · exact Eventually.of_forall fun R =>
      ((continuous_const.mul hfc).aestronglyMeasurable).indicator measurableSet_Icc.compl
  · refine Eventually.of_forall fun R => ae_of_all _ fun v => ?_
    by_cases hv : v ∈ (Icc (-R) R)ᶜ
    · rw [indicator_of_mem hv, Real.norm_eq_abs, abs_of_nonneg (by positivity), hf]
      have hRv : R ≤ |v| := by
        by_contra hlt
        push Not at hlt
        exact hv (abs_le.mp hlt.le)
      calc Real.exp (K * R) * (‖gaussShiftWeight σ u v‖ * Real.exp (1 / 2 * |v|))
          ≤ Real.exp (K * |v|) * (‖gaussShiftWeight σ u v‖ * Real.exp (1 / 2 * |v|)) := by
            gcongr
        _ = ‖gaussShiftWeight σ u v‖ * Real.exp ((K + 1 / 2) * |v|) := by
            rw [mul_left_comm, ← Real.exp_add]; ring_nf
    · rw [indicator_of_notMem hv, norm_zero]
      positivity
  · refine ae_of_all _ fun v => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |v|] with R hR
    rw [indicator_of_notMem (by simpa using abs_le.mp hR)]

/-! ## The Gaussian-weighted eigen-equation holds up to the tail -/

theorem norm_shiftSmear_gaussShiftWeight_le {σ : ℝ} (hσ : 0 < σ) (u R : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖shiftSmear (gaussShiftWeight σ u) R z‖ ≤
      ∫ v : ℝ, ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|) := by
  have hint := integrable_norm_gaussShiftWeight_mul_exp hσ u (1 / 2)
  refine (norm_integral_le_of_norm_le hint.integrableOn
    (ae_of_all _ fun v => norm_gaussShiftWeight_mul_cexp_le σ u v hz)).trans ?_
  exact setIntegral_le_integral hint (ae_of_all _ fun v => by positivity)

theorem norm_gaussFourier_le {σ : ℝ} (hσ : 0 < σ) (u : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖cexp (-(σ : ℂ) * z ^ 2) * cexp (-(I * z) * u)‖ ≤
      ∫ v : ℝ, ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|) := by
  rw [← integral_gaussShiftWeight_mul σ u hσ z]
  exact norm_integral_le_of_norm_le (integrable_norm_gaussShiftWeight_mul_exp hσ u (1 / 2))
    (ae_of_all _ fun v => norm_gaussShiftWeight_mul_cexp_le σ u v hz)

/-- **The Gaussian-weighted eigen-equation up to the tail.** If `G` is bounded by `B` on the strip
and satisfies the eigen-equation on the shifts `|v| ≤ R`, then the weight `G(z) e^{-σz²}` satisfies
it on `b̂(c - z) e^{-izu}` up to `(1 + ‖κ‖) B τ(R)` times a constant, where `τ(R)` is the Gaussian
tail beyond `R`. -/
theorem norm_gaussWeightedDefect_le {η B σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) {G : ℂ → ℂ} {κ : ℂ}
    (hGdiff : DifferentiableOn ℂ G (xiOneSidedStrip η))
    (hB : ∀ z ∈ xiOneSidedStrip η, ‖G z‖ ≤ B) (b : SuzukiSmoothCompactTest 1) (c u R : ℝ)
    (hid : ∀ v : ℝ, |v| ≤ R → ∑' q : XiZeroCopy, G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * v)) =
      κ * ∫ s : ℝ, G (s : ℂ) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * v))) :
    ‖(∑' q : XiZeroCopy, (G (xiSpectralPoint q) * cexp (-(σ : ℂ) * xiSpectralPoint q ^ 2)) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))) -
      κ * ∫ s : ℝ, (G (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2)) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
      (1 + ‖κ‖) * (B * gaussShiftTail σ u R * eigenDefectConst b η c) := by
  set Ψg : ℂ → ℂ := fun z => cexp (-(σ : ℂ) * z ^ 2) * cexp (-(I * z) * u) with hΨg
  set ΨR : ℂ → ℂ := shiftSmear (gaussShiftWeight σ u) R with hΨR
  set τ₀ : ℝ := ∫ v : ℝ, ‖gaussShiftWeight σ u v‖ * Real.exp ((1 / 2) * |v|) with hτ₀
  have hγ := abs_im_xiSpectralPoint_le
  have hs : ∀ s : ℝ, |((s : ℂ)).im| ≤ 1 / 2 := fun s => by simp
  have heq : (∑' q : XiZeroCopy, (G (xiSpectralPoint q) * cexp (-(σ : ℂ) * xiSpectralPoint q ^ 2)) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))) -
      κ * ∫ s : ℝ, (G (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2)) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) =
      eigenDefect G κ b c Ψg := by
    unfold eigenDefect
    congr 1
    · exact tsum_congr fun q => by simp only [hΨg]; ring
    · congr 1
      exact integral_congr_ae (ae_of_all _ fun s => by simp only [hΨg]; ring)
  have h0 : eigenDefect G κ b c ΨR = 0 :=
    eigenDefect_shiftSmear_eq_zero hη hGdiff hB b c R (continuous_gaussShiftWeight σ u) hid
  have hRc : Continuous fun s : ℝ => ΨR (s : ℂ) := by
    simp only [hΨR, shiftSmear]
    exact continuous_parametric_integral_of_continuous
      (f := fun (s : ℝ) (v : ℝ) => gaussShiftWeight σ u v * cexp (-(I * (s : ℂ)) * v))
      (by have := continuous_gaussShiftWeight σ u; fun_prop) isCompact_Icc
  have hgc : Continuous fun s : ℝ => Ψg (s : ℂ) := by simp only [hΨg]; fun_prop
  have hsub := eigenDefect_sub (κ := κ) hη hGdiff hB b c (Ψ₁ := Ψg) (Ψ₂ := ΨR) (ε₁ := τ₀) (ε₂ := τ₀)
    (fun q => norm_gaussFourier_le hσ u (hγ q)) (fun s => norm_gaussFourier_le hσ u (hs s)) hgc
    (fun q => norm_shiftSmear_gaussShiftWeight_le hσ u R (hγ q))
    (fun s => norm_shiftSmear_gaussShiftWeight_le hσ u R (hs s)) hRc
  rw [h0, sub_zero] at hsub
  rw [heq, hsub]
  exact norm_eigenDefect_le hη hB b c
    (fun q => norm_gauss_sub_shiftSmear_le hσ u R (hγ q))
    (fun s => norm_gauss_sub_shiftSmear_le hσ u R (hs s))

/-! ## The receiver -/

/-- **Real-rooted eigenvector transforms of Gaussian growth force RH.** -/
theorem riemannHypothesis_of_realRootedEigen_gaussianGrowth
    {η A K M : ℝ} (hη : 0 < η) (hA : 0 ≤ A) (hK : 0 ≤ K)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {G : ℕ → ℂ → ℂ} {κ : ℕ → ℂ}
    (hGdiff : ∀ j, DifferentiableOn ℂ (G j) (xiOneSidedStrip η))
    (hGgauss : ∀ j, ∀ z ∈ xiOneSidedStrip η, ‖G j z‖ ≤ M * Real.exp (A * z.re ^ 2))
    (hGpw : ∀ j, ∀ z ∈ xiOneSidedStrip η, ‖G j z‖ ≤ M * Real.exp (K * a j))
    (hGreal : ∀ j, ∀ z ∈ xiOneSidedStrip η, G j z = 0 → z.im = 0)
    (hG0 : ∀ j, G j 0 = 1)
    (heigen : ∀ j (R : ℝ), 0 ≤ R → R < a j → ∀ w : SuzukiSmoothCompactTest R,
      ∑' q : XiZeroCopy, G j (xiSpectralPoint q) * suzukiSmoothFourier w (-xiSpectralPoint q) =
        κ j * ∫ s : ℝ, G j (s : ℂ) * suzukiSmoothFourier w (-(s : ℂ))) :
    RiemannHypothesis := by
  set σ : ℝ := A + 1 with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  obtain ⟨b, hb0⟩ := exists_suzukiSmoothCompactTest_fourier_zero_ne
  set Y : ℝ := 1 / 2 + η with hY
  refine riemannHypothesis_of_realRootedApproxEigen (η := η) (C := M * Real.exp (σ * Y ^ 2)) hη
    (G := fun j z => G j z * cexp (-(σ : ℂ) * z ^ 2)) (κ := κ) b hb0 ?_ ?_ ?_ ?_ ?_
  · intro j
    exact (hGdiff j).mul
      (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-(σ : ℂ) * z ^ 2)).differentiableOn
  · intro j z hz
    show ‖G j z * cexp (-(σ : ℂ) * z ^ 2)‖ ≤ M * Real.exp (σ * Y ^ 2)
    rw [norm_mul, norm_cexp_neg_ofReal_mul_sq]
    have hz' : |z.im| < Y := hz
    have hy : z.im ^ 2 ≤ Y ^ 2 := by
      have h0 : 0 ≤ |z.im| := abs_nonneg _
      have := mul_self_le_mul_self h0 hz'.le
      nlinarith [sq_abs z.im]
    have hM : 0 ≤ M := by
      have := le_trans (norm_nonneg _) (hGgauss j z hz)
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    calc ‖G j z‖ * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2)))
        ≤ M * Real.exp (A * z.re ^ 2) * Real.exp (-(σ * (z.re ^ 2 - z.im ^ 2))) := by
          gcongr
          exact hGgauss j z hz
      _ = M * Real.exp (σ * z.im ^ 2 - (σ - A) * z.re ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ M * Real.exp (σ * Y ^ 2) := by
          gcongr
          have : 0 ≤ (σ - A) * z.re ^ 2 := by
            have : 0 ≤ σ - A := by rw [hσdef]; linarith
            positivity
          nlinarith
  · intro j z hz hzero
    have h : G j z = 0 := (mul_eq_zero.mp hzero).resolve_right (Complex.exp_ne_zero _)
    exact hGreal j z hz h
  · intro j
    simp [hG0 j]
  · intro c u
    have hsub : Tendsto (fun j => a j - 2) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-2) ha
    refine ⟨fun j => M * Real.exp (K * a j) * gaussShiftTail σ u (a j - 2) *
      eigenDefectConst b η c, ?_, fun j => ?_⟩
    · have h1 := ((tendsto_exp_mul_gaussShiftTail hσ hK u).comp hsub).const_mul
        (M * Real.exp (K * 2) * eigenDefectConst b η c)
      rw [mul_zero] at h1
      refine h1.congr fun j => ?_
      have he : Real.exp (K * a j) = Real.exp (K * (a j - 2)) * Real.exp (K * 2) := by
        rw [← Real.exp_add]; ring_nf
      simp only [Function.comp_apply]
      rw [he]
      ring
    · have hid : ∀ v : ℝ, |v| ≤ a j - 2 → ∑' q : XiZeroCopy, G j (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * v)) =
          κ j * ∫ s : ℝ, G j (s : ℂ) *
            (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * v)) :=
        fun v hv => eigen_shiftMod b v c (heigen j) (by linarith)
      have h := norm_gaussWeightedDefect_le (κ := κ j) hη hσ (hGdiff j) (hGpw j) b c u (a j - 2) hid
      refine h.trans (le_of_eq ?_)
      ring

end

end RHTower
