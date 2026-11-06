import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.LowHeightGammaPF54
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSchurQuarticSpectralDecayEquivalence

/-!
# Sixth-order suppression of the theta Schur charge

Reciprocal Xi zeros lie in a parabola at the origin. Their positive quartic
charge is therefore of sixth order in spectral size. Compact convergence of
the honest theta determinants transfers this bound to every late Schur packet.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Metric Set Topology Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource
open GaloisForLFunctions.HTGeometry _root_.RHTower.HedenmalmHilbertSchmidt

private theorem spectral_im_sq (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ 2 = ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  have h : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  rw [h]
  ring

private theorem spectral_normSq (q : XiZeroCopy) :
    Complex.normSq (xiSpectralPoint q) =
      (q.1 : ℂ).im ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  simp only [Complex.normSq_apply, ← pow_two, spectral_im_sq]
  have h : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint, Complex.mul_re]
  rw [h]

-- The low-height depth bounds improve the reciprocal transverse ceiling.
private theorem spectral_transverse_bounds (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ 2 ≤ 1 / 4 ∧
      250000 * (xiSpectralPoint q).im ^ 2 ≤ Complex.normSq (xiSpectralPoint q) ^ 2 ∧
      100 * (xiSpectralPoint q).im ^ 2 ≤ Complex.normSq (xiSpectralPoint q) := by
  have hd := (xi_divisor_support_centered_re_sq_lt_quarter q.1).le
  rw [spectral_im_sq, spectral_normSq]
  refine ⟨hd, ?_, ?_⟩
  · by_cases hl : (q.1 : ℂ).re = 1 / 2
    · simp only [hl, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      positivity
    have hh := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hl
    have h14 : 14 ≤ |(q.1 : ℂ).im| := by
      rw [← sq_abs] at hh
      nlinarith only [hh, abs_nonneg ((q.1 : ℂ).im)]
    have hbound (D H : ℝ) (hD : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ D)
        (hH : H ≤ (q.1 : ℂ).im ^ 2) (hH0 : 0 ≤ H) (hpay : 250000 * D ≤ H ^ 2) :
        250000 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤
          ((q.1 : ℂ).im ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
      have hn : H ≤ (q.1 : ℂ).im ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
        hH.trans (le_add_of_nonneg_right (sq_nonneg _))
      have hs := pow_le_pow_left₀ hH0 hn 2
      linarith only [hD, hpay, hs]
    by_cases h16 : |(q.1 : ℂ).im| ≤ 16
    · have hb := pow_le_pow_left₀ (abs_nonneg _) (xiZeroCopy_depth_le_five_twelfths q h14 h16) 2
      rw [sq_abs] at hb
      exact hbound _ 210 hb (by linarith only [hh]) (by norm_num) (by norm_num)
    by_cases h18 : |(q.1 : ℂ).im| ≤ 18
    · have hb := pow_le_pow_left₀ (abs_nonneg _) (xiZeroCopy_depth_le_seven_sixteenths q h14 h18) 2
      rw [sq_abs] at hb
      have hv : (256 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
        rw [← sq_abs]
        nlinarith only [not_le.mp h16, abs_nonneg ((q.1 : ℂ).im)]
      exact hbound _ 256 hb hv (by norm_num) (by norm_num)
    have hv : (324 : ℝ) ≤ (q.1 : ℂ).im ^ 2 := by
      rw [← sq_abs]
      nlinarith only [not_le.mp h18, abs_nonneg ((q.1 : ℂ).im)]
    exact hbound _ 324 hd hv (by norm_num) (by norm_num)
  · by_cases hl : (q.1 : ℂ).re = 1 / 2
    · simp only [hl, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
      positivity
    have hh := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hl
    nlinarith only [hh, hd, sq_nonneg ((q.1 : ℂ).re - 1 / 2)]

private theorem inverse_im_sq (z : ℂ) :
    (z⁻¹).im ^ 2 = z.im ^ 2 / Complex.normSq z ^ 2 := by
  rw [Complex.inv_im, div_pow, neg_sq]

/-- Reciprocal Xi zeros obey both the parabolic strip bound and an absolute transverse ceiling. -/
theorem xi_reciprocal_transverse_bounds {z : ℂ} (hz : XiC z = 0) :
    (z⁻¹).im ^ 2 ≤ Complex.normSq (z⁻¹) ^ 2 / 4 ∧
      (z⁻¹).im ^ 2 ≤ 1 / 250000 ∧
      100 * (z⁻¹).im ^ 2 ≤ Complex.normSq (z⁻¹) := by
  obtain ⟨q, rfl⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
  have h := spectral_transverse_bounds q
  have hn : 0 < Complex.normSq (xiSpectralPoint q) :=
    Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hn2 := sq_pos_of_pos hn
  rw [inverse_im_sq, Complex.normSq_inv]
  constructor
  · apply (div_le_iff₀ hn2).mpr
    have he : ((Complex.normSq (xiSpectralPoint q))⁻¹ ^ 2 / 4) *
        Complex.normSq (xiSpectralPoint q) ^ 2 = (1 / 4 : ℝ) := by
      field_simp [hn.ne']
    rw [he]
    exact h.1
  constructor
  · apply (div_le_iff₀ hn2).mpr
    linarith only [h.2.1]
  · have hh := div_le_div_of_nonneg_right h.2.2 hn2.le
    have he : Complex.normSq (xiSpectralPoint q) / Complex.normSq (xiSpectralPoint q) ^ 2 =
        (Complex.normSq (xiSpectralPoint q))⁻¹ := by field_simp [hn.ne']
    rw [he] at hh
    simpa only [mul_div_assoc] using hh

private theorem charge_eq (w : ℂ) :
    sourcePairPositiveQuarticCharge w.re w.im =
      600 * Complex.normSq w * w.im ^ 2 + 1700 * (w.im ^ 2) ^ 2 := by
  unfold sourcePairPositiveQuarticCharge
  rw [Complex.normSq_apply]
  ring

/-- The critical strip improves the spectral quartic charge to sixth order. -/
theorem xi_reciprocal_charge_le_sixth {z : ℂ} (hz : XiC z = 0) :
    sourcePairPositiveQuarticCharge (z⁻¹).re (z⁻¹).im ≤
      150 * Complex.normSq (z⁻¹) ^ 3 + (425 / 4 : ℝ) * Complex.normSq (z⁻¹) ^ 4 := by
  have h := (xi_reciprocal_transverse_bounds hz).1
  have h1 := mul_le_mul_of_nonneg_left h
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 600) (Complex.normSq_nonneg (z⁻¹)))
  have h2 := pow_le_pow_left₀ (sq_nonneg (z⁻¹).im) h 2
  rw [charge_eq]
  nlinarith only [h1, h2]

/-- Low-height Gamma bounds give a strict, unconditional per-mass quartic ceiling. -/
theorem xi_reciprocal_charge_le_mass {z : ℂ} (hz : XiC z = 0) :
    sourcePairPositiveQuarticCharge (z⁻¹).re (z⁻¹).im ≤
      (617 / 250000 : ℝ) * Complex.normSq (z⁻¹) := by
  obtain ⟨_, hv, hvn⟩ := xi_reciprocal_transverse_bounds hz
  have h1 := mul_le_mul_of_nonneg_left hv (Complex.normSq_nonneg (z⁻¹))
  have h2 := mul_le_mul_of_nonneg_right hvn (sq_nonneg (z⁻¹).im)
  rw [charge_eq]
  nlinarith only [h1, h2]

-- A positive per-mass tolerance handles the small nodes; compact determinant
-- convergence excludes every remaining violation, uniformly over Schur packets.
private theorem eventually_charge_le_coefficient
    (f : ℝ → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    (hfε : ∀ n : ℝ, 0 ≤ n → ε ≤ f n)
    (hzf : ∀ z : ℂ, XiC z = 0 →
      sourcePairPositiveQuarticCharge (z⁻¹).re (z⁻¹).im <
        f (Complex.normSq (z⁻¹)) * Complex.normSq (z⁻¹)) :
    ∀ᶠ k : ℕ in atTop, ∀ (S : ThetaSourceStageSchurPacket k)
      (i : Fin (Fintype.card ↥(thetaSourceSignedCutoff k))),
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        f (Complex.normSq (S.T i i)) * Complex.normSq (S.T i i) := by
  let δ : ℝ := ε / 4600
  have hδ : 0 < δ := div_pos hε (by norm_num)
  let K : Set ℂ := (closedBall 0 thetaSourceSignedHSCeiling ∩
      {w | δ ≤ Complex.normSq w}) ∩
      {w | f (Complex.normSq w) * Complex.normSq w ≤
        sourcePairPositiveQuarticCharge w.re w.im}
  have hcharge : Continuous (fun w : ℂ => sourcePairPositiveQuarticCharge w.re w.im) := by
    unfold sourcePairPositiveQuarticCharge
    fun_prop
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) thetaSourceSignedHSCeiling).inter_right
      (isClosed_le continuous_const Complex.continuous_normSq)).inter_right
      (isClosed_le ((hf.comp Complex.continuous_normSq).mul Complex.continuous_normSq) hcharge)
  have hnz (w : ℂ) (hw : w ∈ K) : w ≠ 0 :=
    Complex.normSq_pos.mp (hδ.trans_le hw.1.2)
  have hKinv : IsCompact ((fun w : ℂ => w⁻¹) '' K) :=
    hK.image_of_continuousOn (fun w hw => (continuousAt_id.inv₀ (hnz w hw)).continuousWithinAt)
  have hfree : ∀ᶠ k in atTop, ∀ z ∈ (fun w : ℂ => w⁻¹) '' K,
      thetaSourceSignedOrdinaryDet k z ≠ 0 := by
    apply eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformly hKinv
      (XiC_analytic.continuous.div_const (XiC 0)).continuousOn
    · rintro z ⟨w, hw, rfl⟩
      apply div_ne_zero _ XiC_zero_ne
      intro hz
      have h := hzf (w⁻¹) hz
      rw [inv_inv] at h
      exact (not_lt_of_ge hw.2) h
    · exact thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC
  filter_upwards [hfree] with k hk
  intro S i
  have hn := Complex.normSq_nonneg (S.T i i)
  by_cases hs : Complex.normSq (S.T i i) ≤ δ
  · have hq := sourcePairPositiveQuarticCharge_le_normSq_sq (S.T i i)
    have hm := mul_le_mul_of_nonneg_right hs hn
    have hp := mul_le_mul_of_nonneg_right (hfε _ hn) hn
    dsimp [δ] at hm
    nlinarith only [hq, hm, hp, mul_nonneg hε.le hn]
  · by_contra hnot
    have hw : S.T i i ∈ K := by
      refine ⟨⟨?_, (lt_of_not_ge hs).le⟩, (lt_of_not_ge hnot).le⟩
      rw [mem_closedBall, dist_zero_right]
      exact norm_thetaSourceStageSchurDiagonal_le_ceiling S i
    exact hk (S.T i i)⁻¹ ⟨S.T i i, hw, rfl⟩
      (thetaSourceSignedOrdinaryDet_inv_schurDiagonal_eq_zero S i (hnz _ hw))

/-- Every sufficiently late theta stage spends at most one four-hundredth of its Hilbert–Schmidt mass. -/
theorem eventually_thetaSchur_charge_le_stage_mass :
    ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
      thetaSourceStageSchurPositiveQuarticCharge S ≤
        matHSNormSq (thetaSourceSignedStageFinMatrix k) / 400 := by
  have h := eventually_charge_le_coefficient (fun _ => (1 / 400 : ℝ)) continuous_const
    (ε := 1 / 400) (by norm_num) (fun _ _ => le_rfl) (by
      intro z hz
      have hz0 : z ≠ 0 := by rintro rfl; exact XiC_zero_ne hz
      have hn : 0 < Complex.normSq (z⁻¹) := Complex.normSq_pos.mpr (inv_ne_zero hz0)
      exact (xi_reciprocal_charge_le_mass hz).trans_lt
        (mul_lt_mul_of_pos_right (by norm_num : (617 / 250000 : ℝ) < 1 / 400) hn))
  filter_upwards [h] with k hk
  intro S
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset _)) => hk S i)
  have hdiag : (∑ i, Complex.normSq (S.T i i)) ≤
      matHSNormSq (thetaSourceSignedStageFinMatrix k) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_stage
  rw [← Finset.mul_sum] at hsum
  change thetaSourceStageSchurPositiveQuarticCharge S ≤ _ at hsum
  have hm := mul_le_mul_of_nonneg_left hdiag (by norm_num : (0 : ℝ) ≤ 1 / 400)
  linarith only [hsum, hm]

/-- A fixed unconditional ceiling for the charge of every late theta Schur packet. -/
theorem eventually_thetaSchur_charge_le_ceiling :
    ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
      thetaSourceStageSchurPositiveQuarticCharge S ≤ thetaSourceSignedHSCeiling ^ 2 / 400 := by
  filter_upwards [eventually_thetaSchur_charge_le_stage_mass] with k hk
  intro S
  exact (hk S).trans (div_le_div_of_nonneg_right
    (matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k) (by norm_num))

/-- The small-spectrum charge has an asymptotic quadratic ceiling in squared spectral size. -/
theorem eventually_thetaSchur_small_charge_le_sixth {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
      finiteMatrixSchurPositiveQuarticSmallSpectrumCharge δ S.toFiniteMatrixSchurPacket ≤
        (150 * δ ^ 2 + (425 / 4 : ℝ) * δ ^ 3 + ε) * thetaSourceSignedHSCeiling ^ 2 := by
  let f : ℝ → ℝ := fun n => 150 * n ^ 2 + (425 / 4 : ℝ) * n ^ 3 + ε
  have hf : Continuous f := by dsimp [f]; fun_prop
  have h := eventually_charge_le_coefficient f hf hε (by
    intro n hn
    dsimp [f]
    have h3 := pow_nonneg hn 3
    nlinarith only [sq_nonneg n, h3]) (by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact XiC_zero_ne hz
    have hn := Complex.normSq_pos.mpr (inv_ne_zero hz0)
    have hq := xi_reciprocal_charge_le_sixth hz
    have hp := mul_pos hε hn
    dsimp [f]
    nlinarith only [hq, hp])
  filter_upwards [h] with k hk
  intro S
  let s := Finset.univ.filter (fun i => Complex.normSq (S.T i i) ≤ δ)
  have hpoint (i) (hi : i ∈ s) :
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        f δ * Complex.normSq (S.T i i) := by
    have hn := Complex.normSq_nonneg (S.T i i)
    have hiδ := (Finset.mem_filter.mp hi).2
    have h2 := pow_le_pow_left₀ hn hiδ 2
    have h3 := pow_le_pow_left₀ hn hiδ 3
    apply (hk S i).trans
    apply mul_le_mul_of_nonneg_right _ hn
    dsimp [f]
    linarith only [h2, h3]
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : (∑ i ∈ s, Complex.normSq (S.T i i)) ≤ ∑ i, Complex.normSq (S.T i i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Complex.normSq_nonneg (S.T i i))
  have hdiag : (∑ i, Complex.normSq (S.T i i)) ≤
      matHSNormSq (thetaSourceSignedStageFinMatrix k) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_stage
  have hmass := hfilter.trans (hdiag.trans (matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k))
  have hfδ : 0 ≤ f δ := by dsimp [f]; positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfδ
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans hm

#print axioms xi_reciprocal_charge_le_sixth
#print axioms xi_reciprocal_charge_le_mass
#print axioms eventually_thetaSchur_charge_le_stage_mass
#print axioms eventually_thetaSchur_charge_le_ceiling
#print axioms eventually_thetaSchur_small_charge_le_sixth

end GaloisForLFunctions.SquareRootThreshold
