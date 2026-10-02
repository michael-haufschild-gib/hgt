import GaloisForLFunctions.RHTower.CCMEulerEventualCarrier
import GaloisForLFunctions.RHTower.CCMScatteringEulerCurrent

/-!
# Exact radical of the Euler current on its moving simultaneous carrier

The finite simultaneous carrier is nonzero, but the actual relative source
annihilates it. Therefore carrier restriction alone discards the source whose
cubic character is needed: its complementary boundary data must be retained.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

/-- The actual adjoint Euler polynomial is injective by finite scattering cancellation. -/
theorem adjoint_ccmFiniteEulerDenominator_injective (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective (ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)) := by
  have hA := (ContinuousLinearMap.isUnit_iff_bijective.mp
    (ccmFiniteEulerDenominator_isUnit S)).1
  have hVA := ccmFiniteEulerPhysicalUnitary_mul_denominator S
  intro f g hfg
  apply hA
  apply (ccmFiniteEulerPhysicalUnitary S).injective
  exact (DFunLike.congr_fun hVA f).trans
    (hfg.trans (DFunLike.congr_fun hVA g).symm)

/-- Exact current action on the original Sonin carrier; the forward-adjoint leg vanishes. -/
theorem ccmFiniteEulerSourceCurrent_apply_sonin
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b)
    {f : evenSubspace} (hf : f ∈ evenCentralSoninCarrier b) :
    ccmFiniteEulerSourceCurrent S f =
      -ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)
        (evenFourierCutoff 1 (ccmFiniteEulerDenominator S f)) := by
  have hQf : evenCentralSoninProjection b f = f := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hf
  have hzero := DFunLike.congr_fun
    (evenFourierCutoff_mul_adjoint_ccmFiniteEulerDenominator_mul_soninProjection S hb) f
  change evenFourierCutoff 1
    (ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)
      (evenCentralSoninProjection b f)) = 0 at hzero
  rw [hQf] at hzero
  change ccmFiniteEulerDenominator S
      (evenFourierCutoff 1 (ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) f)) -
    ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)
      (evenFourierCutoff 1 (ccmFiniteEulerDenominator S f)) = _
  rw [hzero, map_zero, zero_sub]

/-- The complete current, not just its quadratic compression, has exactly the enlarged-gap kernel. -/
theorem ccmFiniteEulerSourceCurrent_sonin_kernel_iff
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b)
    {f : evenSubspace} (hf : f ∈ evenCentralSoninCarrier b) :
    ccmFiniteEulerSourceCurrent S f = 0 ↔
      evenFourierCutoff (ccmFiniteEulerCarrierScale S) f = 0 := by
  rw [ccmFiniteEulerSourceCurrent_apply_sonin S hb hf, neg_eq_zero]
  have hadj : ∀ y : evenSubspace,
      ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S) y = 0 ↔ y = 0 := by
    intro y
    constructor
    · intro h
      exact adjoint_ccmFiniteEulerDenominator_injective S (h.trans (map_zero _).symm)
    · rintro rfl
      exact map_zero _
  rw [hadj]
  have hgap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp hf).2
  simpa only [mul_one] using
    ccmFiniteEulerDenominator_fourierGap_iff S zero_lt_one (zero_lt_one.trans_le hb) hgap

/-- The exact finite simultaneous domain, with both the source vector and its Euler image in K_b. -/
def ccmEulerSimultaneousCarrier (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    Submodule ℂ evenSubspace :=
  evenCentralSoninCarrier b ⊓
    (evenCentralSoninCarrier b).comap (ccmFiniteEulerDenominator S).toLinearMap

theorem ccmEulerSimultaneousCarrier_isClosed
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    IsClosed (ccmEulerSimultaneousCarrier S b : Set evenSubspace) :=
  (evenCentralSoninCarrier_isClosed b).inter
    ((evenCentralSoninCarrier_isClosed b).preimage (ccmFiniteEulerDenominator S).continuous)

instance ccmEulerSimultaneousCarrier_completeSpace
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    CompleteSpace (ccmEulerSimultaneousCarrier S b) :=
  (ccmEulerSimultaneousCarrier_isClosed S b).completeSpace_coe

instance ccmEulerSimultaneousCarrier_hasOrthogonalProjection
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    (ccmEulerSimultaneousCarrier S b).HasOrthogonalProjection := by infer_instance

/-- Canonical orthogonal projection onto the actual stage-dependent simultaneous carrier. -/
def ccmEulerSimultaneousProjection (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (ccmEulerSimultaneousCarrier S b).starProjection

/-- Every finite simultaneous domain remains nonzero. -/
theorem ccmEulerSimultaneousProjection_ne_zero
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 0 < b) :
    ccmEulerSimultaneousProjection S b ≠ 0 := by
  intro hzero
  obtain ⟨f, hf0, hf, hAf⟩ := ccmFiniteEulerDenominator_exists_nonzero_commonCarrier S hb
  have hmem : f ∈ ccmEulerSimultaneousCarrier S b := ⟨hf, hAf⟩
  have hfix := Submodule.starProjection_eq_self_iff.mpr hmem
  change ccmEulerSimultaneousProjection S b f = f at hfix
  rw [hzero] at hfix
  exact hf0 hfix.symm

/-- Moving to the exact simultaneous carrier annihilates the complete cleared source. -/
theorem ccmFiniteEulerSourceCurrent_mul_simultaneousProjection
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    ccmFiniteEulerSourceCurrent S * ccmEulerSimultaneousProjection S b = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  let g := ccmEulerSimultaneousProjection S b f
  have hg : g ∈ ccmEulerSimultaneousCarrier S b :=
    (ccmEulerSimultaneousCarrier S b).starProjection_apply_mem f
  change ccmFiniteEulerSourceCurrent S g = 0
  rw [ccmFiniteEulerSourceCurrent_apply_sonin S hb hg.1]
  have hgap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b _).mp hg.2).2
  change evenFourierCutoff b (ccmFiniteEulerDenominator S g) = 0 at hgap
  have hsmall : evenFourierCutoff 1 (ccmFiniteEulerDenominator S g) = 0 := by
    calc
      _ = evenFourierCutoff 1 (evenFourierCutoff b (ccmFiniteEulerDenominator S g)) :=
        (DFunLike.congr_fun (evenFourierCutoff_mul_of_le 1 b hb)
          (ccmFiniteEulerDenominator S g)).symm
      _ = 0 := by rw [hgap, map_zero]
  rw [hsmall, map_zero, neg_zero]

/-- The original scattering current also vanishes after transporting this simultaneous carrier. -/
theorem ccmFiniteScatteringRelativeCurrent_mul_euler_simultaneousProjection
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    ccmFiniteScatteringRelativeCurrent S * ccmFiniteEulerDenominator S *
      ccmEulerSimultaneousProjection S b = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply adjoint_ccmFiniteEulerDenominator_injective S
  have h := DFunLike.congr_fun (ccmFiniteScatteringRelativeCurrent_euler_congruence S)
    (ccmEulerSimultaneousProjection S b f)
  have hz := DFunLike.congr_fun (ccmFiniteEulerSourceCurrent_mul_simultaneousProjection S hb) f
  exact h.trans (hz.trans (map_zero _).symm)

private theorem larger_fourierCutoff_sonin_ne_zero {b c : ℝ}
    (hb : 0 < b) (hbc : b < c) :
    evenFourierCutoff c * evenCentralSoninProjection b ≠ 0 := by
  intro hzero
  have hFourier (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier b) :
      evenFourierCutoff c f = 0 := by
    have hQf : evenCentralSoninProjection b f = f := by
      rw [evenCentralSoninProjection_eq_starProjection]
      exact Submodule.starProjection_eq_self_iff.mpr hf
    have h := DFunLike.congr_fun hzero f
    change evenFourierCutoff c (evenCentralSoninProjection b f) = 0 at h
    rwa [hQf] at h
  have hPhysical (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier b) :
      evenIndicatorCutoff c f = 0 := by
    have h := hFourier (evenFourierTransform f)
      (evenFourierTransform_mem_evenCentralSoninCarrier b hf)
    rw [evenFourierCutoff_eq_reflectedCutoff] at h
    change evenFourierTransform
      (evenIndicatorCutoff c (evenFourierTransform (evenFourierTransform f))) = 0 at h
    rw [evenFourierTransform_involutive] at h
    have h' := congrArg evenFourierTransform h
    simpa only [evenFourierTransform_involutive, map_zero] using h'
  have hfix : evenCentralSoninProjection c * evenCentralSoninProjection b =
      evenCentralSoninProjection b := by
    apply ContinuousLinearMap.ext
    intro f
    have hf : evenCentralSoninProjection b f ∈ evenCentralSoninCarrier b := by
      rw [evenCentralSoninProjection_eq_starProjection]
      exact (evenCentralSoninCarrier b).starProjection_apply_mem f
    have hfc : evenCentralSoninProjection b f ∈ evenCentralSoninCarrier c :=
      (mem_evenCentralSoninCarrier_iff_cutoffs_zero c _).mpr
        ⟨hPhysical _ hf, hFourier _ hf⟩
    change evenCentralSoninProjection c (evenCentralSoninProjection b f) = _
    rw [evenCentralSoninProjection_eq_starProjection c]
    exact Submodule.starProjection_eq_self_iff.mpr hfc
  have heq : evenCentralSoninProjection b = evenCentralSoninProjection c :=
    hfix.symm.trans (evenCentralSoninProjection_mul_of_le hbc.le).1
  let r := c / b + 1
  have hr : 1 < r := by
    have hdiv : 0 < c / b := div_pos (hb.trans hbc) hb
    dsimp only [r]
    linarith
  have hrb : r * b = c + b := by dsimp only [r]; field_simp
  have hcross : c < r * b := by rw [hrb]; linarith
  apply evenSoninApertureLostTransition_not_isCompactOperator hb hbc hr hcross
  rw [evenSoninApertureLostTransition, evenSoninApertureLayer, heq, sub_self, zero_mul, zero_mul]
  exact isCompactOperator_zero

/-- Sharp non-vacuity: the full source is erased on K_b exactly when its whole Euler scale
lies below the aperture; beyond it, a genuine boundary channel survives. -/
theorem ccmFiniteEulerSourceCurrent_mul_sonin_eq_zero_iff
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    ccmFiniteEulerSourceCurrent S * evenCentralSoninProjection b = 0 ↔
      ccmFiniteEulerCarrierScale S ≤ b := by
  have hmem (f : evenSubspace) :
      evenCentralSoninProjection b f ∈ evenCentralSoninCarrier b := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier b).starProjection_apply_mem f
  constructor
  · intro hzero
    by_contra hscale
    have hbc : b < ccmFiniteEulerCarrierScale S := lt_of_not_ge hscale
    apply larger_fourierCutoff_sonin_ne_zero (zero_lt_one.trans_le hb) hbc
    apply ContinuousLinearMap.ext
    intro f
    exact (ccmFiniteEulerSourceCurrent_sonin_kernel_iff S hb (hmem f)).mp
      (DFunLike.congr_fun hzero f)
  · intro hscale
    apply ContinuousLinearMap.ext
    intro f
    apply (ccmFiniteEulerSourceCurrent_sonin_kernel_iff S hb (hmem f)).mpr
    have hgap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b _).mp (hmem f)).2
    calc
      _ = evenFourierCutoff (ccmFiniteEulerCarrierScale S)
          (evenFourierCutoff b (evenCentralSoninProjection b f)) :=
        (DFunLike.congr_fun
          (evenFourierCutoff_mul_of_le (ccmFiniteEulerCarrierScale S) b hscale)
            (evenCentralSoninProjection b f)).symm
      _ = 0 := by rw [hgap, map_zero]

end RHTower
