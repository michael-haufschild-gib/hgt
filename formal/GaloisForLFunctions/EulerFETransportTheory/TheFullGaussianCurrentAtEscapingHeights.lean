import GaloisForLFunctions.EulerFETransportTheory.GaussianRenormalizationAtZeros
import GaloisForLFunctions.EulerFETransportTheory.TheArchimedeanDampingErrorIsUniform
import GaloisForLFunctions.RHTower.XiFarFieldSecondMoment
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# The complete Gaussian finite part at escaping heights

The Gamma-subtracted prime current has an error of size
`O(y * (1 + y) * (1 + log (im s)))` on a positive strip away from the divisor.
Local zero counts and the full far-field second moment control the translated
resolvent, so neither the prime sum nor the nontrivial-zero field is truncated.
-/

open Complex Filter Topology MeasureTheory Set RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private theorem reciprocal_square_le {a : ℂ} {d : ℝ} (hd : 0 < d) (ha : d ≤ ‖a‖) :
    ‖a⁻¹‖ ^ 2 ≤ 1 / d ^ 2 := by
  rw [norm_inv]
  have hi := inv_anti₀ hd ha
  have hn : 0 ≤ ‖a‖⁻¹ := by positivity
  calc
    _ ≤ (d⁻¹) ^ 2 := by nlinarith
    _ = 1 / d ^ 2 := by simp [one_div, inv_pow]

/-- Away from the divisor, the complete squared resolvent costs only a
logarithm of height. No zero-free half-plane is assumed. -/
theorem exists_zeroResolvent_logHeight_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 4 ≤ s.im →
      (∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖) →
      (∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2) ≤ C * (1 + Real.log s.im) := by
  classical
  obtain ⟨D, hD, hfar⟩ := exists_sum_inv_sq_far_le
  let K : ℝ := 80 * Real.log 360 + 80 + smallHeightCount
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K / δ ^ 2 + D, by positivity, fun s ht hsep => ?_⟩
  apply (summable_norm_inv_xiZero_sub_sq s).tsum_le_of_sum_le
  intro F
  let P : XiZeroCopy → Prop := fun q => |s.im - (q.1 : ℂ).im| < 1
  have hlog : 0 ≤ Real.log s.im := Real.log_nonneg (by linarith)
  have hcount : ((F.filter P).card : ℝ) ≤ K * (1 + Real.log s.im) := by
    have hn := card_zeroWindow_le ht 0 (F.filter P) (fun q hq => by
      simpa only [Nat.cast_zero, zero_add] using
        And.intro (abs_nonneg (s.im - (q.1 : ℂ).im)) (Finset.mem_filter.mp hq).2)
    have hlogsplit : Real.log (180 * (s.im + 1)) ≤ Real.log 360 + Real.log s.im := by
      calc
        _ ≤ Real.log (360 * s.im) := Real.log_le_log (by linarith) (by linarith)
        _ = _ := Real.log_mul (by norm_num) (by linarith)
    simp only [Nat.cast_zero, add_zero] at hn
    dsimp [K]
    have h360 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 360)
    have hsmall : 0 ≤ (smallHeightCount : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h360 hlog, mul_nonneg hsmall hlog]
  have hnear : (∑ q ∈ F.filter P, ‖(xiZero q - s)⁻¹‖ ^ 2) ≤
      K / δ ^ 2 * (1 + Real.log s.im) := by
    calc
      _ ≤ ∑ _q ∈ F.filter P, 1 / δ ^ 2 :=
        Finset.sum_le_sum fun q _ => reciprocal_square_le hδ (hsep q)
      _ = ((F.filter P).card : ℝ) / δ ^ 2 := by simp [div_eq_mul_inv]
      _ ≤ (K * (1 + Real.log s.im)) / δ ^ 2 :=
        div_le_div_of_nonneg_right hcount (sq_nonneg δ)
      _ = _ := by ring
  have hfar' : (∑ q ∈ F.filter (fun q => ¬ P q), ‖(xiZero q - s)⁻¹‖ ^ 2) ≤
      D * (1 + Real.log s.im) := by
    have hf : ∀ q ∈ F.filter (fun q => ¬ P q), 1 ≤ |s.im - (q.1 : ℂ).im| := by
      intro q hq
      exact le_of_not_gt (Finset.mem_filter.mp hq).2
    refine (Finset.sum_le_sum fun q hq => ?_).trans (hfar s.im ht _ hf)
    have hnorm : |s.im - (q.1 : ℂ).im| ≤ ‖xiZero q - s‖ := by
      simpa only [Complex.sub_im, norm_sub_rev, xiZero] using Complex.abs_im_le_norm (s - xiZero q)
    have h := reciprocal_square_le (lt_of_lt_of_le zero_lt_one (hf q hq)) hnorm
    simpa only [sq_abs] using h
  calc
    _ = (∑ q ∈ F.filter P, ‖(xiZero q - s)⁻¹‖ ^ 2) +
        ∑ q ∈ F.filter (fun q => ¬ P q), ‖(xiZero q - s)⁻¹‖ ^ 2 := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ K / δ ^ 2 * (1 + Real.log s.im) + D * (1 + Real.log s.im) := add_le_add hnear hfar'
    _ = _ := by ring

private theorem zero_sub_ne_zero {s : ℂ} (hs : xi s ≠ 0) (q : XiZeroCopy) :
    xiZero q - s ≠ 0 := by
  intro h
  exact hs (by rw [← sub_eq_zero.mp h]; exact xi_xiZero q)

private theorem zero_sub_add_two_ne_zero {s : ℂ} (hs : s.re ≤ 1) (q : XiZeroCopy) :
    xiZero q - s + 2 ≠ 0 := by
  have hq : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  intro h
  have hh := congrArg Complex.re h
  simp at hh
  linarith

/-- A shift by two controls the product of translated reciprocal distances
by the squared unshifted reciprocal distance throughout the positive strip. -/
theorem reciprocal_shift_product_le {s : ℂ} (hs : s.re ≤ 1)
    (hxi : xi s ≠ 0) (q : XiZeroCopy) :
    ‖(xiZero q - s)⁻¹‖ * ‖(xiZero q - s + 2)⁻¹‖ ≤
      3 * ‖(xiZero q - s)⁻¹‖ ^ 2 := by
  have hq : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  have hshift : 1 ≤ ‖xiZero q - s + 2‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
    linarith
  have ha := norm_pos_iff.mpr (zero_sub_ne_zero hxi q)
  have hb : 0 < ‖xiZero q - s + 2‖ := by linarith
  have hab : ‖xiZero q - s‖ ≤ 3 * ‖xiZero q - s + 2‖ := by
    have h := norm_sub_le (xiZero q - s + 2) (2 : ℂ)
    rw [add_sub_cancel_right, Complex.norm_two] at h
    linarith
  have hi : 1 / ‖xiZero q - s + 2‖ ≤ 3 / ‖xiZero q - s‖ := by
    rw [div_le_div_iff₀ hb ha]
    simpa only [one_mul] using hab
  simp only [norm_inv]
  have h := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (norm_nonneg (xiZero q - s)))
  simpa only [div_eq_mul_inv, one_mul, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

private theorem complexGaussianFinitePart_eq {s : ℂ} (hxi : xi s ≠ 0) (q : XiZeroCopy) :
    complexGaussianFinitePart s q = (xiZero q - 1 / 2)⁻¹ + (s - xiZero q)⁻¹ := by
  have hk := XiAtlasFinitePart.xiZero_sub_half_ne_zero q
  have ha := zero_sub_ne_zero hxi q
  rw [show s - xiZero q = -(xiZero q - s) by ring, inv_neg]
  unfold complexGaussianFinitePart
  rw [show 1 / 2 - s = (xiZero q - s) - (xiZero q - 1 / 2) by ring]
  generalize xiZero q - 1 / 2 = κ at hk ⊢
  generalize xiZero q - s = a at ha ⊢
  field_simp
  ring

/-- The error in a single Gamma-subtracted, endpoint-normalized zero germ. -/
def complexGaussianModeError (s : ℂ) (y : ℝ) (q : XiZeroCopy) : ℂ :=
  complexGaussianGerm s y q - gaussianMBKernel y (xiZero q - s) -
    (Real.exp (-y) : ℂ) * complexGaussianFinitePart s q

private theorem norm_complexGaussianModeError_le {s : ℂ} (hs : s.re ≤ 1)
    (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖complexGaussianModeError s y q‖ ≤
      6 * y * (1 + y) * ‖(xiZero q - s)⁻¹‖ ^ 2 := by
  have ha := zero_sub_ne_zero hxi q
  have hq : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  have h := norm_zeroGerm_sub_gamma_le hy
    (show -2 < (xiZero q - s).re by simp; linarith) ha
  have he : complexGaussianModeError s y q =
      (Real.exp (-y) : ℂ) / (xiZero q - s) + gaussianIncompleteMellin y (xiZero q - s) -
        gaussianMBKernel y (xiZero q - s) := by
    rw [complexGaussianModeError, complexGaussianGerm, complexGaussianFinitePart_eq hxi]
    rw [show s - xiZero q = -(xiZero q - s) by ring, inv_neg]
    ring
  rw [he, gaussianMBKernel]
  calc
    _ ≤ (2 * y + 2 * y ^ 2) / (‖xiZero q - s‖ * ‖xiZero q - s + 2‖) := h
    _ = (2 * y + 2 * y ^ 2) *
        (‖(xiZero q - s)⁻¹‖ * ‖(xiZero q - s + 2)⁻¹‖) := by
      simp only [norm_inv, div_eq_mul_inv, mul_inv]
    _ ≤ (2 * y + 2 * y ^ 2) * (3 * ‖(xiZero q - s)⁻¹‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (reciprocal_shift_product_le hs hxi q) (by positivity)
    _ = _ := by ring

theorem summable_norm_complexGaussianModeError {s : ℂ} (hs : s.re ≤ 1)
    (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy => ‖complexGaussianModeError s y q‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => norm_complexGaussianModeError_le hs hxi hy q)
    ((summable_norm_inv_xiZero_sub_sq s).mul_left (6 * y * (1 + y)))

/-- Absolute admission of the whole paired germ field at every regular point
of the positive strip. Two recursions retain an inverse-square majorant. -/
theorem summable_norm_complexGaussianGerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1)
    (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy => ‖complexGaussianGerm s y q‖) := by
  let M : ℝ := y ^ (-(4 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((4 + 1 : ℝ) / 2)
  let e : ℂ := (Real.exp (-y) : ℂ)
  let H : XiZeroCopy → ℂ := fun q => -2 * (y : ℂ) * e +
    4 * (y : ℂ) ^ 2 * gaussianIncompleteMellin y (xiZero q - s + 2 + 2)
  let K : ℝ := ‖-2 * (y : ℂ) * e‖ + ‖4 * (y : ℂ) ^ 2‖ * M
  have hH : ∀ q, ‖H q‖ ≤ K := by
    intro q
    have hq : (xiZero q).re < 1 := xiZeroCopy_re_lt_one q
    have hE := norm_gaussianIncompleteMellin_le hy (r := 4) (by norm_num)
      (b := xiZero q - s + 2 + 2) (by simp; linarith)
    calc
      _ ≤ ‖-2 * (y : ℂ) * e‖ +
          ‖4 * (y : ℂ) ^ 2 * gaussianIncompleteMellin y (xiZero q - s + 2 + 2)‖ :=
        norm_add_le _ _
      _ ≤ K := by
        rw [norm_mul (4 * (y : ℂ) ^ 2)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
  have hid : ∀ q, complexGaussianGerm s y q = e * complexGaussianFinitePart s q +
      (xiZero q - s)⁻¹ * (xiZero q - s + 2)⁻¹ * H q := by
    intro q
    have ha := zero_sub_ne_zero hxi q
    have ha2 := zero_sub_add_two_ne_zero hs1 q
    rw [complexGaussianGerm, complexGaussianFinitePart_eq hxi]
    rw [gaussianIncompleteMellin_recursion hy ha,
      gaussianIncompleteMellin_recursion hy ha2]
    rw [show s - xiZero q = -(xiZero q - s) by ring, inv_neg]
    dsimp only [H, e]
    ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    (((summable_norm_complexGaussianFinitePart s).mul_left ‖e‖).add
      ((summable_norm_inv_xiZero_sub_sq s).mul_left (3 * K)))
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul e, norm_mul, norm_mul]
  apply add_le_add le_rfl
  calc
    _ ≤ (3 * ‖(xiZero q - s)⁻¹‖ ^ 2) * K :=
      mul_le_mul (reciprocal_shift_product_le hs1 hxi q) (hH q) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The complete Gamma field at a complex observation point. -/
def complexGaussianModes (s : ℂ) (y : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, gaussianMBKernel y (xiZero q - s)

theorem summable_norm_complexGaussianModes {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1)
    (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy => ‖gaussianMBKernel y (xiZero q - s)‖) := by
  have hR : Summable (fun q : XiZeroCopy =>
      ‖complexGaussianModeError s y q + (Real.exp (-y) : ℂ) * complexGaussianFinitePart s q‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      ((summable_norm_complexGaussianModeError hs1 hxi hy).add
        ((summable_norm_complexGaussianFinitePart s).mul_left ‖(Real.exp (-y) : ℂ)‖))
    simpa only [norm_mul] using norm_add_le (complexGaussianModeError s y q)
      ((Real.exp (-y) : ℂ) * complexGaussianFinitePart s q)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    ((summable_norm_complexGaussianGerm hs0 hs1 hxi hy).add hR)
  have h := norm_sub_le (complexGaussianGerm s y q)
    (complexGaussianModeError s y q + (Real.exp (-y) : ℂ) * complexGaussianFinitePart s q)
  simpa only [complexGaussianModeError, sub_add_cancel, sub_sub_cancel] using h

/-- Exact full-field decomposition of the normalized prime finite part. -/
theorem gaussianPrimeGap_add_modes_sub_finitePart {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    gaussianPrimeContinuumGap s y + complexGaussianModes s y -
        (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s) =
      (gaussianArchimedeanMB y 2 s -
        (Real.exp (-y) : ℂ) * gaussianArchimedeanCurrent s) -
        ∑' q : XiZeroCopy, complexGaussianModeError s y q := by
  have hex := gaussianPrimeCurrent_sub_continuum_eq hy two_pos
    (by linarith : 1 < s.re + 2)
  change gaussianPrimeContinuumGap s y = gaussianArchimedeanMB y 2 s -
    ∑' q, complexGaussianGerm s y q at hex
  have hG := (summable_norm_complexGaussianGerm hs0 hs1 hxi hy).of_norm
  have hB := (summable_norm_complexGaussianModes hs0 hs1 hxi hy).of_norm
  have hF := (summable_norm_complexGaussianFinitePart s).of_norm.mul_left (Real.exp (-y) : ℂ)
  have he : (∑' q, complexGaussianModeError s y q) =
      (∑' q, complexGaussianGerm s y q) - complexGaussianModes s y -
        (Real.exp (-y) : ℂ) * logDeriv xi s := by
    simp only [complexGaussianModeError]
    rw [(hG.sub hB).tsum_sub hF, hG.tsum_sub hB,
      tsum_mul_left, logDeriv_xi_eq_partialFraction hxi]
    rw [show (fun q => complexGaussianFinitePart s q) =
      (fun q => (xiZero q - 1 / 2)⁻¹ + (s - xiZero q)⁻¹) by
        funext q; exact complexGaussianFinitePart_eq hxi q]
    rfl
  rw [hex, he]
  ring

/-- Error after retaining every Gamma mode and the normalized continued
polar–archimedean background. -/
def complexGaussianFinitePartError (s : ℂ) (y : ℝ) : ℂ :=
  gaussianPrimeContinuumGap s y + complexGaussianModes s y -
    (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)

/-- The actual prime-current error is controlled by the complete translated
squared resolvent and the height-uniform archimedean remainder. -/
theorem norm_complexGaussianFinitePartError_le {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    ‖complexGaussianFinitePartError s y‖ ≤ y * Real.exp (-y) / s.re +
      6 * y * (1 + y) * ∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2 := by
  have hE := summable_norm_complexGaussianModeError hs1 hxi hy
  have hb : ‖∑' q : XiZeroCopy, complexGaussianModeError s y q‖ ≤
      6 * y * (1 + y) * ∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2 := by
    refine (norm_tsum_le_tsum_norm hE).trans ?_
    rw [← tsum_mul_left]
    exact hE.tsum_le_tsum (fun q => norm_complexGaussianModeError_le hs1 hxi hy q)
      ((summable_norm_inv_xiZero_sub_sq s).mul_left (6 * y * (1 + y)))
  rw [complexGaussianFinitePartError, gaussianPrimeGap_add_modes_sub_finitePart hs0 hs1 hxi hy]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_archimedeanDampingError_le hy two_pos hs0) hb)

/-- A positive high strip with a fixed aperture around every divisor point
removed. Its definition uses the full actual zero set. -/
def gaussianRegularHighStrip (σ δ : ℝ) : Set ℂ :=
  {s | σ ≤ s.re ∧ s.re ≤ 1 ∧ 4 ≤ s.im ∧ ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖}

/-- Positive distance from every actual zero copy excludes a zero of Xi. -/
theorem xi_ne_zero_of_separated {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hsep : ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖) : xi s ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  have h := hsep q
  change δ ≤ ‖(q.1 : ℂ) - s‖ at h
  rw [hq, sub_self, norm_zero] at h
  linarith

/-- Joint height/damping control of the full prime and zero fields. -/
theorem exists_gaussianFinitePartError_logHeight_bound {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ∀ s ∈ gaussianRegularHighStrip σ δ,
      ‖complexGaussianFinitePartError s y‖ ≤ C * y * (1 + y) * (1 + Real.log s.im) := by
  obtain ⟨D, hD, hres⟩ := exists_zeroResolvent_logHeight_bound hδ
  refine ⟨1 / σ + 6 * D, by positivity, fun y hy s hs => ?_⟩
  obtain ⟨hsσ, hs1, ht, hsep⟩ := hs
  have hs0 : 0 < s.re := hσ.trans_le hsσ
  have hxi := xi_ne_zero_of_separated hδ hsep
  have hexp : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlog : 0 ≤ Real.log s.im := Real.log_nonneg (by linarith)
  have hA : y * Real.exp (-y) / s.re ≤ y / σ := by
    calc
      _ ≤ y / s.re := div_le_div_of_nonneg_right
        (mul_le_of_le_one_right hy.le hexp) hs0.le
      _ ≤ _ := div_le_div_of_nonneg_left hy.le hσ hsσ
  have hfirst : y / σ ≤ (1 / σ) * y * (1 + y) * (1 + Real.log s.im) := by
    have hyL : y ≤ y * (1 + y) * (1 + Real.log s.im) := by
      nlinarith [mul_nonneg (sq_nonneg y) hlog]
    have h := mul_le_mul_of_nonneg_left hyL (show 0 ≤ 1 / σ by positivity)
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  calc
    _ ≤ y * Real.exp (-y) / s.re +
        6 * y * (1 + y) * ∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2 :=
      norm_complexGaussianFinitePartError_le hs0 hs1 hxi hy
    _ ≤ y / σ + 6 * y * (1 + y) * (D * (1 + Real.log s.im)) :=
      add_le_add hA (mul_le_mul_of_nonneg_left (hres s ht hsep) (by positivity))
    _ ≤ (1 / σ) * y * (1 + y) * (1 + Real.log s.im) +
        6 * y * (1 + y) * (D * (1 + Real.log s.im)) := add_le_add hfirst le_rfl
    _ = _ := by ring

/-- After division by logarithmic height, the complete finite-part error
vanishes uniformly on the whole regular high strip. -/
theorem tendstoUniformlyOn_gaussianFinitePartError_logHeight {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun y : ℝ => fun s : ℂ =>
      complexGaussianFinitePartError s y / ((1 + Real.log s.im : ℝ) : ℂ))
      (fun _ => 0) (𝓝[>] 0) (gaussianRegularHighStrip σ δ) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianFinitePartError_logHeight_bound hσ hδ
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεC : 0 < min 1 (ε / (2 * C)) := lt_min zero_lt_one (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hεC).filter_mono nhdsWithin_le_nhds] with y hy hyε
  change 0 < y at hy
  have hy1 : y < 1 := hyε.trans_le (min_le_left _ _)
  have hyC : y < ε / (2 * C) := hyε.trans_le (min_le_right _ _)
  intro s hs
  have ht : 4 ≤ s.im := hs.2.2.1
  have hL : 0 < 1 + Real.log s.im := by
    have := Real.log_nonneg (show 1 ≤ s.im by linarith)
    linarith
  rw [dist_zero_left, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  calc
    _ ≤ C * y * (1 + y) := (div_le_iff₀ hL).mpr (hb y hy s hs)
    _ ≤ 2 * C * y := by nlinarith [mul_nonneg (mul_nonneg hC.le hy.le) (sub_nonneg.mpr hy1.le)]
    _ < ε := by rw [lt_div_iff₀ (by positivity)] at hyC; nlinarith

/-- Absolute error vanishes along every regular path whose damping times
logarithmic height tends to zero; no bound on the heights themselves is needed. -/
theorem tendsto_gaussianFinitePartError_of_joint_scale
    {ι : Type*} {l : Filter ι} {s : ι → ℂ} {y : ι → ℝ} {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hy : Tendsto y l (𝓝[>] 0))
    (hs : ∀ᶠ i in l, s i ∈ gaussianRegularHighStrip σ δ)
    (hscale : Tendsto (fun i => y i * (1 + Real.log (s i).im)) l (𝓝 0)) :
    Tendsto (fun i => complexGaussianFinitePartError (s i) (y i)) l (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianFinitePartError_logHeight_bound hσ hδ
  have hy0 : Tendsto y l (𝓝 0) := hy.mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun i => C * (y i * (1 + Real.log (s i).im)) * (1 + y i)) l (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_mul] using
      (hscale.const_mul C).mul (tendsto_const_nhds.add hy0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hy.eventually self_mem_nhdsWithin, hs] with i hiy his
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb (y i) hiy (s i) his

/-- Failure of AAL supplies a whole high strip strictly left of an actual
exceptional zero on which the full joint finite-part estimate holds. -/
theorem not_asymptoticAbscissaLaw_has_jointGaussianControl
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ H C : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ 0 < H ∧ 0 < C ∧
      (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      (∀ y : ℝ, 0 < y → ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → H ≤ s.im →
        ‖complexGaussianFinitePartError s y‖ ≤ C * y * (1 + y) * (1 + Real.log s.im)) ∧
      TendstoUniformlyOn (fun y : ℝ => fun s : ℂ =>
        complexGaussianFinitePartError s y / ((1 + Real.log s.im : ℝ) : ℂ))
        (fun _ => 0) (𝓝[>] 0) {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ H ≤ s.im} := by
  unfold AsymptoticAbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hfin, q, hq⟩ := hnot
  obtain ⟨M, hM⟩ := (hfin.image fun p : XiZeroCopy => |(p.1 : ℂ).im|).bddAbove
  let β : ℝ := 1 / 2 + h
  let σ : ℝ := (β + (q.1 : ℂ).re) / 2
  let δ : ℝ := ((q.1 : ℂ).re - β) / 4
  let H : ℝ := max M 0 + δ + 4
  have hβ : 1 / 2 ≤ β := by dsimp [β]; linarith
  have hqβ : β < (q.1 : ℂ).re := hq
  have hq1 := (xi_divisor_support_re_mem_open_unit q.1).2
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hdomain : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → H ≤ s.im →
      s ∈ gaussianRegularHighStrip σ δ := by
    intro s hsσ hs1 hsH
    have ht : 4 ≤ s.im := by dsimp [H] at hsH; linarith [le_max_right M 0]
    refine ⟨hsσ, hs1, ht, fun p => ?_⟩
    by_cases hp : (p.1 : ℂ).re ≤ β
    · have hre : δ ≤ s.re - (p.1 : ℂ).re := by dsimp [σ] at hsσ; dsimp [δ]; linarith
      have hnorm := Complex.re_le_norm (s - (p.1 : ℂ))
      rw [Complex.sub_re, norm_sub_rev] at hnorm
      exact hre.trans hnorm
    · have hp' : p ∈ {p : XiZeroCopy | 1 / 2 + h < (p.1 : ℂ).re} := lt_of_not_ge hp
      have hpM : |(p.1 : ℂ).im| ≤ M := hM ⟨p, hp', rfl⟩
      have him : δ ≤ s.im - (p.1 : ℂ).im := by
        dsimp [H] at hsH
        linarith [le_max_left M 0, le_abs_self (p.1 : ℂ).im]
      have hnorm := Complex.im_le_norm (s - (p.1 : ℂ))
      rw [Complex.sub_im, norm_sub_rev] at hnorm
      exact him.trans hnorm
  have hσ0 : 0 < σ := by linarith
  obtain ⟨C, hC, hbound⟩ := exists_gaussianFinitePartError_logHeight_bound hσ0 hδ
  refine ⟨σ, H, C, hσ, hσ1, hH, hC, ⟨q, by dsimp [σ]; linarith⟩,
    fun y hy s hsσ hs1 hsH => hbound y hy s (hdomain s hsσ hs1 hsH), ?_⟩
  have hu := tendstoUniformlyOn_gaussianFinitePartError_logHeight hσ0 hδ
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with y hy s hs
  exact hy s (hdomain s hs.1 hs.2.1 hs.2.2)

#print axioms exists_zeroResolvent_logHeight_bound
#print axioms gaussianPrimeGap_add_modes_sub_finitePart
#print axioms exists_gaussianFinitePartError_logHeight_bound
#print axioms tendstoUniformlyOn_gaussianFinitePartError_logHeight
#print axioms tendsto_gaussianFinitePartError_of_joint_scale
#print axioms not_asymptoticAbscissaLaw_has_jointGaussianControl

end GaloisForLFunctions.EulerFETransportTheory
