import GaloisForLFunctions.RHTower.WeilInsertionEvenBump
import GaloisForLFunctions.RHTower.WeilDeletionCCMCrossing

/-!
# Inserting a prime power at any scale into the restricted Weil operator forces a sign change

Mirror of the deletion crossing.  For a real scale `x > 1` and a weight `w`, the *inserted*
restricted Weil operator carries an extra translation block `w · T_x`,
`T_x = x^{−1/2}(τ_{log x} + τ_{−log x})` compressed to the aperture, present exactly when
`x ≤ e^{2a}`: a fictitious prime power of weight `w` at the scale `x`, which need not be an integer.
Below the visibility threshold the inserted operator is the literal one, so its ground energy is
positive at small apertures.  At the aperture `½ log x + s + 1` the even two-bump source makes it
negative as soon as `w ≥ log x`, because the literal source quadratic is bounded by the zero-side
constant while the inserted block contributes `−(w/√x)·2∫φ²`.

Together with the deletion crossing this pins the prime block of the restricted Weil operator at
every scale `x ≥ e^{18}` from both sides: neither removing the weight of a prime nor adding the
weight of a prime at a non-prime scale preserves the positivity of the ground energy across
apertures.
-/

open Complex MeasureTheory Set
open scoped Convolution
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilDeletion

/-! ## The scale transport operator and the inserted block -/

/-- The symmetric translation block at a real scale `x`, normalised by `x^{−1/2}`. -/
noncomputable def ccmScaleTransportOperator (a : SuzukiPositiveAperture) (x : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ((1 / Real.sqrt x : ℝ) : ℂ) •
    ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log x))

theorem inner_ccmScaleTransportOperator (a : SuzukiPositiveAperture) (x : ℝ)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmScaleTransportOperator a x f) g =
      ((1 / Real.sqrt x : ℝ) : ℂ) *
        (inner ℂ (logTranslationCLM (Real.log x) f.1) g.1 +
          inner ℂ (logTranslationCLM (-Real.log x) f.1) g.1) := by
  rw [ccmScaleTransportOperator, smul_apply, inner_smul_left, Complex.conj_ofReal,
    inner_ccmApertureCompression]
  simp only [ccmSymmetricLogTranslation, add_apply, inner_add_left]

theorem ccmScaleTransportOperator_isSelfAdjoint (a : SuzukiPositiveAperture) (x : ℝ) :
    IsSelfAdjoint (ccmScaleTransportOperator a x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  have hself := ccmApertureCompression_isSelfAdjoint a
    (ccmSymmetricLogTranslation_isSelfAdjoint (Real.log x))
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
  rw [ccmScaleTransportOperator, ContinuousLinearMap.adjoint.map_smulₛₗ, hself, Complex.conj_ofReal]

open Classical in
/-- The inserted block of weight `w` at the scale `x`, present exactly when `x ≤ e^{2a}`. -/
noncomputable def ccmInsertedBlock (a : SuzukiPositiveAperture) (x w : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  if x ≤ Real.exp (2 * a.1) then (w : ℂ) • ccmScaleTransportOperator a x else 0

theorem ccmInsertedBlock_isSelfAdjoint (a : SuzukiPositiveAperture) (x w : ℝ) :
    IsSelfAdjoint (ccmInsertedBlock a x w) := by
  unfold ccmInsertedBlock
  split_ifs with h
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    have hself := ccmScaleTransportOperator_isSelfAdjoint a x
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ, hself, Complex.conj_ofReal]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp

theorem ccmInsertedBlock_of_invisible (a : SuzukiPositiveAperture) {x : ℝ} (w : ℝ)
    (h : ¬ x ≤ Real.exp (2 * a.1)) : ccmInsertedBlock a x w = 0 := by
  unfold ccmInsertedBlock
  exact if_neg h

/-- The bounded remainder with the block of a fictitious prime power inserted (the prime block
enters the remainder with a minus sign). -/
noncomputable def ccmInsertedRemainder (a : SuzukiPositiveAperture) (x w : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a - ccmInsertedBlock a x w

theorem ccmInsertedRemainder_isSelfAdjoint (a : SuzukiPositiveAperture) (x w : ℝ) :
    IsSelfAdjoint (ccmInsertedRemainder a x w) := by
  unfold ccmInsertedRemainder
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  have h2 := ccmInsertedBlock_isSelfAdjoint a x w
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [ContinuousLinearMap.adjoint.map_sub, h1, h2]

theorem ccmInsertedRemainder_of_invisible (a : SuzukiPositiveAperture) {x : ℝ} (w : ℝ)
    (h : ¬ x ≤ Real.exp (2 * a.1)) :
    ccmInsertedRemainder a x w = ccmRestrictedWeilBoundedRemainder a := by
  unfold ccmInsertedRemainder
  rw [ccmInsertedBlock_of_invisible a w h, sub_zero]

/-! ## The inserted ground energy -/

/-- Bottom spectral value of the inserted restricted Weil operator. -/
noncomputable def ccmInsertedGroundEnergy (a : SuzukiPositiveAperture) (x w : ℝ) : ℝ :=
  ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a)
      (ccmInsertedRemainder a x w) (ccmInsertedRemainder_isSelfAdjoint a x w)‖⁻¹ -
    boundedPerturbedFormShift (ccmInsertedRemainder a x w)

theorem ccmInsertedGroundEnergy_of_invisible (a : SuzukiPositiveAperture) {x : ℝ} (w : ℝ)
    (h : ¬ x ≤ Real.exp (2 * a.1)) :
    ccmInsertedGroundEnergy a x w = ccmRestrictedWeilGroundEnergy a := by
  have he := ccmInsertedRemainder_of_invisible a w h
  unfold ccmInsertedGroundEnergy ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) he _
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), he]

theorem ccmInsertedGroundEnergy_mul_formNorm_sq_le (a : SuzukiPositiveAperture) (x w : ℝ)
    (u : CCMArchimedeanFormDomain a) :
    ccmInsertedGroundEnergy a x w * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤
      ccmRestrictedWeilSourceQuadratic a u -
        (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  have hfloor := boundedPerturbedForm_ground_mul_norm_sq_le
    (ccmArchimedeanFormToAperture a) (ccmInsertedRemainder a x w)
    (ccmInsertedRemainder_isSelfAdjoint a x w)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a) u
  have hsplit : (inner ℂ u u + inner ℂ (ccmInsertedRemainder a x w (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re =
      (ccmRestrictedWeilForm a u u).re -
        (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
    show (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u) -
      ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re = _
    rw [inner_sub_left, ← add_sub_assoc, Complex.sub_re]
    rfl
  change ccmInsertedGroundEnergy a x w * ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) ≤ _ at hfloor
  rw [hsplit, ccmRestrictedWeilForm_self_re_eq_source] at hfloor
  exact hfloor

/-! ## The even two-bump as a smooth interior source -/

noncomputable def evenBumpSource (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) : CCMComplexSmoothInteriorSource a where
  toFun := fun x => (evenBump (phiN n) u₀ x : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (evenBump_contDiff_top (phiN_contDiff_top n) u₀)
  hasCompactSupport :=
    (evenBump_hasCompactSupport (support_phiN_subset n) hu).comp_left Complex.ofReal_zero
  tsupport_subset := by
    have h1 : Function.support (fun x => (evenBump (phiN n) u₀ x : ℂ)) ⊆
        Icc (-(u₀ / 2 + sN n)) (u₀ / 2 + sN n) := by
      intro x hx
      apply support_evenBump_subset (support_phiN_subset n) hu
      rw [Function.mem_support] at hx ⊢
      exact fun h => hx (by rw [h]; simp)
    refine (closure_minimal h1 isClosed_Icc).trans ?_
    exact Icc_subset_Ioo (by linarith) ha

theorem evenBumpSource_apply (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) (x : ℝ) :
    (evenBumpSource n hu a ha : ℝ → ℂ) x = (evenBump (phiN n) u₀ x : ℂ) := rfl

theorem ccmRestrictedWeilSourceQuadratic_evenBumpSource_eq_tsum (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀)
    (a : SuzukiPositiveAperture) (ha : u₀ / 2 + sN n < a.1) :
    ccmRestrictedWeilSourceQuadratic a (evenBumpSource n hu a ha).toCCMFormVector =
      (∑' q : XiZeroCopy,
        Zeta23.paperFT (fun x => (autocorr (evenBump (phiN n) u₀) x : ℂ)) (xiSpectralPoint q)).re := by
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm, suzukiScrewSmoothForm_eq_tsum]
  congr 1
  refine tsum_congr fun q => ?_
  exact rayCoef_product_derivative_eq_paperFT_autocorr (evenBumpSource n hu a ha)
    (fun x => rfl) (evenBump_contDiff_top (phiN_contDiff_top n) u₀)
    (support_evenBump_subset (support_phiN_subset n) hu) q

theorem abs_ccmRestrictedWeilSourceQuadratic_evenBumpSource_le (n : ℕ) {u₀ p : ℝ} (hu : 0 ≤ u₀)
    (hexp_half : Real.exp (u₀ / 2) = Real.sqrt p) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) :
    |ccmRestrictedWeilSourceQuadratic a (evenBumpSource n hu a ha).toCCMFormVector| ≤
      (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) * (33 / 100) := by
  rw [ccmRestrictedWeilSourceQuadratic_evenBumpSource_eq_tsum]
  set C : ℝ := 4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set F : XiZeroCopy → ℂ := fun q =>
    Zeta23.paperFT (fun x => (autocorr (evenBump (phiN n) u₀) x : ℂ)) (xiSpectralPoint q) with hF
  have hterm : ∀ q : XiZeroCopy, ‖F q‖ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := fun q =>
    norm_paperFT_autocorr_evenBump_le n hu hexp_half (xiSpectralPoint_ne_zero q)
      (abs_xiSpectralPoint_im_lt_half q).le (fortyOne_div_two_lt_normSq_spectralPoint q)
  have hg_summ : Summable (fun q : XiZeroCopy => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hnorm_summ : Summable (fun q : XiZeroCopy => ‖F q‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm hg_summ
  have h1 : |(∑' q, F q).re| ≤ ‖∑' q, F q‖ := Complex.abs_re_le_norm _
  have h2 : ‖∑' q, F q‖ ≤ ∑' q, ‖F q‖ := norm_tsum_le_tsum_norm hnorm_summ
  have h3 : ∑' q, ‖F q‖ ≤ ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    hnorm_summ.tsum_le_tsum hterm hg_summ
  have h4 : ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ≤ C * (33 / 100) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left tsum_inv_normSq_spectralPoint_lt.le hC0
  linarith

/-! ## The inserted block on the even two-bump source -/

theorem re_inner_insertedBlock_evenBumpSource {x : ℝ} (w : ℝ) (n : ℕ)
    (hu2 : 2 * sN n < Real.log x) (a : SuzukiPositiveAperture)
    (ha : Real.log x / 2 + sN n < a.1) (hvis : x ≤ Real.exp (2 * a.1)) :
    let u := evenBumpSource n (by linarith [sN_pos n] : 0 ≤ Real.log x) a ha
    (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u.toCCMFormVector))
      (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re =
      w * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by
  intro u
  set f := ccmArchimedeanFormToAperture a u.toCCMFormVector with hf
  have hfae : ((f : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun y => (evenBump (phiN n) (Real.log x) y : ℂ) :=
    u.toCCMFormVector_physical_coeFn
  unfold ccmInsertedBlock
  rw [if_pos hvis, smul_apply, inner_smul_left, Complex.conj_ofReal,
    inner_ccmScaleTransportOperator]
  rw [inner_logTranslation_eq_autocorr _ hfae, inner_logTranslation_eq_autocorr _ hfae]
  rw [autocorr_evenBump_apply (sN_pos n).le (support_phiN_subset n) hu2,
    autocorr_evenBump_apply_neg (sN_pos n).le (support_phiN_subset n) hu2]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

theorem exists_evenBump_ne_zero (n : ℕ) {u₀ : ℝ} (hu2 : 2 * sN n < u₀) :
    ∃ y : ℝ, evenBump (phiN n) u₀ y ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_phiN_ne_zero n
  have hymem : y ∈ Icc (-sN n) (sN n) := support_phiN_subset n hy
  refine ⟨y + u₀ / 2, ?_⟩
  unfold evenBump
  have h1 : y + u₀ / 2 - u₀ / 2 = y := by ring
  have h2 : phiN n (y + u₀ / 2 + u₀ / 2) = 0 := by
    have hnot : y + u₀ / 2 + u₀ / 2 ∉ Icc (-sN n) (sN n) := by
      intro hmem
      have := hmem.2
      have := hymem.1
      linarith
    exact Function.notMem_support.mp fun hs => hnot (support_phiN_subset n hs)
  rw [h1, h2, add_zero]
  exact hy

/-! ## Main theorems -/

/-- Below the visibility threshold the inserted ground energy is the literal one, hence positive
at small apertures. -/
theorem exists_small_aperture_ccmInsertedGroundEnergy_pos {x : ℝ} (hx : 1 < x) (w : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ → 0 < ccmInsertedGroundEnergy a x w := by
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  have hlog : 0 < Real.log x := Real.log_pos hx
  refine ⟨min δ₀ (Real.log x / 2), lt_min hδ₀ (by linarith), fun a ha => ?_⟩
  have ha0 : a.1 < δ₀ := lt_of_lt_of_le ha (min_le_left _ _)
  have ha1 : a.1 < Real.log x / 2 := lt_of_lt_of_le ha (min_le_right _ _)
  have hinv : ¬ x ≤ Real.exp (2 * a.1) := by
    rw [not_le]
    have : 2 * a.1 < Real.log x := by linarith
    rw [Real.lt_log_iff_exp_lt (by linarith)] at this
    exact this
  rw [ccmInsertedGroundEnergy_of_invisible a w hinv]
  exact hpos a ha0

/-- **Inserting a prime power of weight `w ≥ log x` at any scale `x ≥ e^{18}` makes the
restricted Weil ground energy negative** at an aperture at most `log x + 1`. -/
theorem ccmInsertedGroundEnergy_neg_of_large {x : ℝ} (hx18 : Real.exp 18 ≤ x) {w : ℝ}
    (hw : Real.log x ≤ w) :
    ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log x + 1 ∧ ccmInsertedGroundEnergy a x w < 0 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx18
  have hu18 : 18 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx18
  have hu0 : 0 ≤ Real.log x := by linarith
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hexp_half : Real.exp (Real.log x / 2) = Real.sqrt x := by
    have hsq : Real.exp (Real.log x / 2) ^ (2 : ℕ) = x := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx0]
    have h := Real.sqrt_sq (Real.exp_pos (Real.log x / 2)).le
    rw [hsq] at h
    exact h.symm
  obtain ⟨h2s, hexpo⟩ := params_ok hu18
  set n : ℕ := ⌊(Real.log x - 4 / 5) / (39 / 25)⌋₊ - 2 with hn
  have hsN := sN_pos n
  set a : SuzukiPositiveAperture := ⟨Real.log x / 2 + sN n + 1, by positivity⟩ with ha_def
  have ha : Real.log x / 2 + sN n < a.1 := by
    show Real.log x / 2 + sN n < Real.log x / 2 + sN n + 1
    linarith
  have hale : a.1 ≤ Real.log x + 1 := by
    show Real.log x / 2 + sN n + 1 ≤ Real.log x + 1
    linarith
  have hvis : x ≤ Real.exp (2 * a.1) := by
    have h2a : (2 : ℝ) * a.1 = Real.log x + (2 * sN n + 2) := by
      show (2 : ℝ) * (Real.log x / 2 + sN n + 1) = _
      ring
    rw [h2a, Real.exp_add, Real.exp_log hx0]
    have : 1 ≤ Real.exp (2 * sN n + 2) := Real.one_le_exp (by linarith)
    nlinarith
  refine ⟨a, hale, ?_⟩
  set u := evenBumpSource n hu0 a ha with hu_def
  set v := ccmArchimedeanFormToAperture a u.toCCMFormVector with hv
  have hv0 : v ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_evenBump_ne_zero n h2s
    exact ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero u
      (x := y) (by rw [evenBumpSource_apply]; exact Complex.ofReal_ne_zero.mpr hy)
  have hvpos : 0 < ‖v‖ ^ (2 : ℕ) := by positivity
  have hray := ccmInsertedGroundEnergy_mul_formNorm_sq_le a x w u.toCCMFormVector
  rw [← hv] at hray
  set X : ℝ := (1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hsource := abs_ccmRestrictedWeilSourceQuadratic_evenBumpSource_le n hu0 hexp_half a ha
  rw [← hX] at hsource
  have hsource' : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      4 * Real.sqrt x * (3 / 2) * X * (33 / 100) := le_trans (le_abs_self _) hsource
  have hblock := re_inner_insertedBlock_evenBumpSource w n h2s a ha hvis
  simp only at hblock
  rw [← hv] at hblock
  have hint : 1 / (2 * sN n) ≤ ∫ y, phiN n y ^ (2 : ℕ) := integral_phiN_sq_ge n
  have hint' : 1 / Real.log x ≤ ∫ y, phiN n y ^ (2 : ℕ) := by
    refine le_trans ?_ hint
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hprod : 2 / Real.sqrt x ≤ w * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by
    have h1 : Real.log x * (1 / Real.sqrt x) * (2 * (1 / Real.log x)) ≤
        Real.log x * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : Real.log x * (1 / Real.sqrt x) * (2 * (1 / Real.log x)) = 2 / Real.sqrt x := by
      field_simp
    have h3 : Real.log x * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) ≤
        w * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by
      have hpos : 0 ≤ (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by
        have : 0 ≤ ∫ y, phiN n y ^ (2 : ℕ) := le_trans (by positivity) hint
        positivity
      calc Real.log x * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ))
          = Real.log x * ((1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ))) := by ring
        _ ≤ w * ((1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ))) :=
            mul_le_mul_of_nonneg_right hw hpos
        _ = w * (1 / Real.sqrt x) * (2 * ∫ y, phiN n y ^ (2 : ℕ)) := by ring
    linarith
  have hxX : x * X ≤ 1 := by
    have := exp_mul_X_le_one n hexpo
    rwa [Real.exp_log hx0] at this
  have hC : 4 * Real.sqrt x * (3 / 2) * X * (33 / 100) < 2 / Real.sqrt x := by
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    rw [lt_div_iff₀ hsqrt_pos]
    calc 4 * Real.sqrt x * (3 / 2) * X * (33 / 100) * Real.sqrt x
        = (99 / 50) * ((Real.sqrt x * Real.sqrt x) * X) := by ring
      _ = (99 / 50) * (x * X) := by rw [hsq]
      _ ≤ 99 / 50 := by linarith
      _ < 2 := by norm_num
  have hneg : ccmInsertedGroundEnergy a x w * ‖v‖ ^ (2 : ℕ) < 0 := by
    rw [hblock] at hray
    linarith
  rcases lt_or_ge (ccmInsertedGroundEnergy a x w) 0 with hlt | hge
  · exact hlt
  · exfalso
    have := mul_nonneg hge hvpos.le
    linarith

/-- **Forced sign change of the inserted family.**  For every real scale `x ≥ e^{18}` and every
weight `w ≥ log x`, the restricted Weil operator with a fictitious prime power of weight `w`
inserted at the scale `x` has ground energy positive on an initial aperture range and negative at
an aperture below `log x + 1`. -/
theorem ccmInsertedGroundEnergy_sign_change {x : ℝ} (hx18 : Real.exp 18 ≤ x) {w : ℝ}
    (hw : Real.log x ≤ w) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ → 0 < ccmInsertedGroundEnergy a x w) ∧
      ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log x + 1 ∧ ccmInsertedGroundEnergy a x w < 0 := by
  have hx1 : 1 < x := lt_of_lt_of_le (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)) hx18
  exact ⟨exists_small_aperture_ccmInsertedGroundEnergy_pos hx1 w,
    ccmInsertedGroundEnergy_neg_of_large hx18 hw⟩

end RHTower.WeilDeletion
