import GaloisForLFunctions.RHTower.SuzukiTaV2PrescribedEnergySource
import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureRieszTransport

/-!
# Full complex profile of the actual mixed-aperture metric response

Covariance reciprocity moves the larger-aperture inverse from the extended
unknown response onto its explicit exponential source. The actual source
profiles then control every complex V2 sign pairing jointly. The signed
shift charge is retained exactly; arbitrary gaps use the larger-aperture
scale, and bounded gaps also admit the smaller-aperture scale.

This concerns the prescribed coercive shifts. It establishes no unshifted
positivity, near-floor shell cancellation, or Xi identification.
-/

open Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Exact reciprocity for the retained metric response. The larger covariance
is moved onto its literal exponential source, leaving two actual responses. -/
theorem suzukiTaRiesz_metricShiftCorrection_source_pairing
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (s t : ℝ) :
    inner ℂ (suzukiTaExponentialL2 b t)
      (suzukiWeilIntervalFormEmbedding b (suzukiTaRiesz_metricShiftCorrection hab s)) =
      ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b) : ℝ) : ℂ) *
        inner ℂ (suzukiTaMovableCompletedCovarianceSource b t)
          (suzukiTaMovableCompletedCovarianceSource a s) := by
  rw [suzukiWeilIntervalFormEmbedding_metricShiftCorrection_eq_covariance,
    inner_smul_right]
  congr 1
  have hsym := (suzukiWeilIntervalCovariance_isPositive b).isSymmetric
    (suzukiTaExponentialL2 b t)
    (suzukiWeilIntervalFormEmbedding b (ccmArchimedeanFormDomain_extension hab
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s))))
  calc
    _ = inner ℂ ((suzukiWeilIntervalCovariance b) (suzukiTaExponentialL2 b t))
        (suzukiWeilIntervalFormEmbedding b (ccmArchimedeanFormDomain_extension hab
          (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s)))) := hsym.symm
    _ = inner ℂ (suzukiTaMovableCompletedCovarianceSource b t)
        (suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding b
          (ccmArchimedeanFormDomain_extension hab
            (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s))))) :=
      (inner_suzukiApertureZeroExtendL2 _ _).symm
    _ = _ := by
      rw [suzukiApertureZeroExtendL2_formEmbedding_extension_eq,
        suzukiTaMovableCompletedCovarianceSource_eq_rawDeficiency a s]
      rfl

private theorem v2_source_norm (a : SuzukiPositiveAperture) (r : Bool) :
    ‖ccmPolarApertureVector a (if r then 1 else -1)‖ ≤ Real.exp a.1 := by
  cases r
  · exact norm_ccmPolarApertureVector_neg_one_le a
  · exact norm_ccmPolarApertureVector_one_le a

private theorem v2_profile_norm (a : SuzukiPositiveAperture) (r : Bool) :
    ‖(ccmSourceShiftProfile a (ccmPolarApertureVector a (if r then 1 else -1)) : SoninL2)‖ ≤ 2 := by
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  change ‖((c⁻¹ : ℝ) : ℂ) • ccmPolarL2Vector a (if r then 1 else -1)‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ c⁻¹ * Real.exp a.1 := mul_le_mul_of_nonneg_left (v2_source_norm a r) (by positivity)
    _ ≤ 2 := by
      rw [← div_eq_inv_mul]
      exact (div_le_iff₀ hc).2 (exp_aperture_le_twice_suzukiWeilIntervalShift a)

private theorem eventually_v2_whole_profile (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ hx : 0 < x, ∀ r : Bool,
      ‖suzukiTaMovableCompletedCovarianceSource ⟨x, hx⟩ (if r then 1 else -1) -
        (ccmSourceShiftProfile ⟨x, hx⟩
          (ccmPolarApertureVector ⟨x, hx⟩ (if r then 1 else -1)) : SoninL2)‖ < δ := by
  filter_upwards [eventually_suzukiTaSourceResponse_source_profile (δ ^ 2 / 2)
    (by positivity)] with x hxProfile
  intro hx r
  let a : SuzukiPositiveAperture := ⟨x, hx⟩
  let s : ℝ := if r then 1 else -1
  have hs : |s| = 1 := by cases r <;> norm_num [s]
  have hb : CCMFiniteExponentialBudget (ccmPolarL2Vector a s) (Real.exp x) := by
    simpa only [hs, one_mul] using CCMFiniteExponentialBudget.polar a s
  have h := hxProfile hx (ccmPolarApertureVector a s) (Real.exp x)
    (v2_source_norm a r) hb
  rw [suzukiTaSourceResponse_polar] at h
  have he : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at h
  have herr : ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a s)‖ ^ 2 ≤ δ ^ 2 / 2 := by
    apply le_of_mul_le_mul_left (a := Real.exp (2 * x)) ?_ (Real.exp_pos _)
    simpa only [mul_comm (δ ^ 2 / 2)] using h
  have hn : ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a s)‖ < δ := by
    nlinarith only [herr, hδ, sq_nonneg (δ - ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a s)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a s)‖)]
  have hF := ccmArchimedeanFormToAperture_movableCompletedCovarianceCCMResponse_eq_source a s
  rw [← hF]
  exact hn

private theorem inner_profile_error {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (f g p q : H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hf : ‖f - p‖ < δ) (hg : ‖g - q‖ < δ)
    (hp : ‖p‖ ≤ 2) (hq : ‖q‖ ≤ 2) :
    ‖inner ℂ f g - inner ℂ p q‖ ≤ 5 * δ := by
  have hn : ‖g‖ ≤ 3 := by
    have h := norm_add_le (g - q) q
    rw [sub_add_cancel] at h
    linarith
  calc
    _ = ‖inner ℂ (f - p) g + inner ℂ p (g - q)‖ := by
      rw [inner_sub_left, inner_sub_right]
      congr 1
      ring
    _ ≤ ‖inner ℂ (f - p) g‖ + ‖inner ℂ p (g - q)‖ := norm_add_le _ _
    _ ≤ ‖f - p‖ * ‖g‖ + ‖p‖ * ‖g - q‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ δ * 3 + 2 * δ := add_le_add
      (mul_le_mul hf.le hn (norm_nonneg _) hδ.le)
      (mul_le_mul hp hg.le (norm_nonneg _) (by positivity))
    _ = 5 * δ := by ring

/-- Full complex mixed Gram profile, jointly uniform in independent large
apertures and both actual V2 source signs. -/
theorem suzukiTaV2_mixed_response_profile (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a b : SuzukiPositiveAperture, A ≤ a.1 → A ≤ b.1 → ∀ r u : Bool,
      ‖inner ℂ (suzukiTaMovableCompletedCovarianceSource b (if u then 1 else -1))
          (suzukiTaMovableCompletedCovarianceSource a (if r then 1 else -1)) -
        inner ℂ (ccmSourceShiftProfile b
          (ccmPolarApertureVector b (if u then 1 else -1)) : SoninL2)
          (ccmSourceShiftProfile a
            (ccmPolarApertureVector a (if r then 1 else -1)) : SoninL2)‖ < ε := by
  let δ := min 1 (ε / 10)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨A, hA⟩ := eventually_atTop.1 (eventually_v2_whole_profile δ hδ)
  refine ⟨A, ?_⟩
  intro a b ha hb r u
  have h := inner_profile_error
    (suzukiTaMovableCompletedCovarianceSource b (if u then 1 else -1))
    (suzukiTaMovableCompletedCovarianceSource a (if r then 1 else -1))
    (ccmSourceShiftProfile b (ccmPolarApertureVector b (if u then 1 else -1)) : SoninL2)
    (ccmSourceShiftProfile a (ccmPolarApertureVector a (if r then 1 else -1)) : SoninL2)
    hδ (min_le_left _ _) (hA _ hb b.2 u) (hA _ ha a.2 r)
    (v2_profile_norm b u) (v2_profile_norm a r)
  exact h.trans_lt (by have hsmall := min_le_right (1 : ℝ) (ε / 10); dsimp [δ]; linarith)

private theorem profile_pairing (a b : SuzukiPositiveAperture) (s t : ℝ) :
    inner ℂ (ccmSourceShiftProfile b (ccmPolarApertureVector b t) : SoninL2)
      (ccmSourceShiftProfile a (ccmPolarApertureVector a s) : SoninL2) =
      (((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b))⁻¹ : ℝ) : ℂ) *
          inner ℂ (ccmPolarL2Vector b t) (ccmPolarL2Vector a s) := by
  change inner ℂ ((_ : ℂ) • ccmPolarL2Vector b t) ((_ : ℂ) • ccmPolarL2Vector a s) = _
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, mul_inv_rev,
    Complex.ofReal_mul, mul_assoc]

/-- The literal mixed-aperture metric response has an explicit signed
source profile at the larger-aperture scale. This holds for every later
aperture, with no bound on the aperture gap or unknown-response premise. -/
theorem suzukiTaV2_mixed_metric_source_profile (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a b : SuzukiPositiveAperture, A ≤ a.1 →
      ∀ hab : a.1 ≤ b.1, ∀ r u : Bool,
      let s : ℝ := if r then 1 else -1
      let t : ℝ := if u then 1 else -1
      let ca := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
      let cb := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b)
      Real.exp (-b.1) * ‖inner ℂ (suzukiTaExponentialL2 b t)
          (suzukiWeilIntervalFormEmbedding b (suzukiTaRiesz_metricShiftCorrection hab s)) -
        (((ca - cb) / (ca * cb) : ℝ) : ℂ) *
          inner ℂ (ccmPolarL2Vector b t) (ccmPolarL2Vector a s)‖ < ε := by
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  have hC : 0 < C := by dsimp [C]; positivity
  let η := ε / (2 * C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hA⟩ := suzukiTaV2_mixed_response_profile η hη
  refine ⟨A, ?_⟩
  intro a b ha hab r u
  let ca := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let cb := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b)
  let s : ℝ := if r then 1 else -1
  let t : ℝ := if u then 1 else -1
  let G := inner ℂ (suzukiTaMovableCompletedCovarianceSource b t)
    (suzukiTaMovableCompletedCovarianceSource a s) -
    inner ℂ (ccmSourceShiftProfile b (ccmPolarApertureVector b t) : SoninL2)
      (ccmSourceShiftProfile a (ccmPolarApertureVector a s) : SoninL2)
  have hG : ‖G‖ < η := hA a b ha (ha.trans hab) r u
  have hca : ca ≤ C * Real.exp b.1 :=
    (suzukiWeilIntervalShift_le_exp a).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) hC.le)
  have hcb : cb ≤ C * Real.exp b.1 := suzukiWeilIntervalShift_le_exp b
  have habs : |ca - cb| ≤ 2 * C * Real.exp b.1 := by
    have h := abs_sub_le ca 0 cb
    rw [sub_zero, zero_sub, abs_neg,
      abs_of_pos (boundedPerturbedFormShift_pos _),
      abs_of_pos (boundedPerturbedFormShift_pos _)] at h
    linarith
  have hfactor : Real.exp (-b.1) * |ca - cb| ≤ 2 * C := by
    calc
      _ ≤ Real.exp (-b.1) * (2 * C * Real.exp b.1) :=
        mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
      _ = 2 * C := by
        rw [show Real.exp (-b.1) * (2 * C * Real.exp b.1) =
          (2 * C) * (Real.exp (-b.1) * Real.exp b.1) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hid : inner ℂ (suzukiTaExponentialL2 b t)
      (suzukiWeilIntervalFormEmbedding b (suzukiTaRiesz_metricShiftCorrection hab s)) -
      (((ca - cb) / (ca * cb) : ℝ) : ℂ) *
        inner ℂ (ccmPolarL2Vector b t) (ccmPolarL2Vector a s) =
      ((ca - cb : ℝ) : ℂ) * G := by
    rw [suzukiTaRiesz_metricShiftCorrection_source_pairing]
    dsimp only [G]
    rw [profile_pairing, mul_sub, div_eq_mul_inv, Complex.ofReal_mul, mul_assoc]
  dsimp only
  change Real.exp (-b.1) * ‖_‖ < ε
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
  calc
    _ ≤ 2 * C * η := mul_le_mul hfactor hG.le (norm_nonneg _) (by positivity)
    _ < ε := by
      have heq : η * (2 * C + 1) = ε := by dsimp [η]; field_simp
      nlinarith only [heq, hη]

/-- On every fixed aperture-gap window the same full complex metric profile
holds at the smaller-aperture scale, uniformly over both V2 signs. -/
theorem suzukiTaV2_mixed_metric_source_profile_bounded_gap
    (L ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a b : SuzukiPositiveAperture, A ≤ a.1 →
      ∀ hab : a.1 ≤ b.1, b.1 - a.1 ≤ L → ∀ r u : Bool,
      let s : ℝ := if r then 1 else -1
      let t : ℝ := if u then 1 else -1
      let ca := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
      let cb := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder b)
      Real.exp (-a.1) * ‖inner ℂ (suzukiTaExponentialL2 b t)
          (suzukiWeilIntervalFormEmbedding b (suzukiTaRiesz_metricShiftCorrection hab s)) -
        (((ca - cb) / (ca * cb) : ℝ) : ℂ) *
          inner ℂ (ccmPolarL2Vector b t) (ccmPolarL2Vector a s)‖ < ε := by
  obtain ⟨A, hA⟩ := suzukiTaV2_mixed_metric_source_profile (ε / Real.exp L) (by positivity)
  refine ⟨A, ?_⟩
  intro a b ha hab hgap r u
  have h := hA a b ha hab r u
  dsimp only at h ⊢
  have hscale : Real.exp (-a.1) ≤ Real.exp L * Real.exp (-b.1) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  refine (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans_lt ?_
  rw [mul_assoc]
  exact (mul_lt_mul_of_pos_left h (Real.exp_pos L)).trans_eq (by field_simp)

end RHTower
end
