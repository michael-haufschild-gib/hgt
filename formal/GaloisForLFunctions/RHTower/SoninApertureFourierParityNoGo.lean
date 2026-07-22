import GaloisForLFunctions.RHTower.SoninApertureWardPotential
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering

/-!
# Fourier-parity no-go for invariant Suzuki aperture traces

The symmetric Sonin dilation channel and every aperture layer are Fourier-even.  Consequently the
successive-layer transition and its canonical Ward channel commute with cosine Fourier reflection.
By contrast, the forward-minus-inverse bilateral aperture holonomy is Fourier-odd.

This parity separation has a sharp scalar consequence.  Every complex-linear reader invariant
under Fourier conjugation annihilates the bilateral holonomy.  Such a reader can equal the
positive Ward energy only when the successive-layer transition, and hence aperture curvature,
vanishes literally.  Therefore a reflection-invariant linear relative trace cannot be the
RH-oriented Burnol/co-Poisson reader.  Any surviving reader must be fibre-pointed and break the
global reflection averaging, as the co-Poisson Berezin diagonal does.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- Membership in the even Sonin carrier is exactly simultaneous annihilation by its physical
and Fourier cutoffs. -/
theorem mem_evenCentralSoninCarrier_iff_cutoffs_zero
    (a : ℝ) (f : evenSubspace) :
    f ∈ evenCentralSoninCarrier a ↔
      evenIndicatorCutoff a f = 0 ∧ evenFourierCutoff a f = 0 := by
  change (f : SoninL2) ∈ centralSoninCarrier a ↔ _
  unfold centralSoninCarrier
  constructor
  · intro hf
    constructor
    · apply Subtype.ext
      change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralPhysicalForbidden a)).mpr hf.1
    · apply Subtype.ext
      change fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralFourierForbidden a)).mpr hf.2
  · rintro ⟨hP, hB⟩
    constructor
    · apply (Submodule.starProjection_apply_eq_zero_iff
        (K := centralPhysicalForbidden a)).mp
      unfold centralPhysicalForbidden
      rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
      simpa only [centralInterval] using congrArg Subtype.val hP
    · apply (Submodule.starProjection_apply_eq_zero_iff
        (K := centralFourierForbidden a)).mp
      unfold centralFourierForbidden
      rw [← fourierCutoff_eq_fourierForbidden_starProjection]
      simpa only [centralInterval] using congrArg Subtype.val hB

/-- Cosine Fourier reflection preserves the even Sonin carrier. -/
theorem evenFourierTransform_mem_evenCentralSoninCarrier
    (a : ℝ) {f : evenSubspace} (hf : f ∈ evenCentralSoninCarrier a) :
    evenFourierTransform f ∈ evenCentralSoninCarrier a := by
  rw [mem_evenCentralSoninCarrier_iff_cutoffs_zero] at hf ⊢
  rcases hf with ⟨hP, hB⟩
  constructor
  · have hB' := hB
    rw [evenFourierCutoff_eq_reflectedCutoff] at hB'
    change evenFourierTransform
      (evenIndicatorCutoff a (evenFourierTransform f)) = 0 at hB'
    have h := congrArg evenFourierTransform hB'
    simpa using h
  · rw [evenFourierCutoff_eq_reflectedCutoff]
    change evenFourierTransform
      (evenIndicatorCutoff a (evenFourierTransform (evenFourierTransform f))) = 0
    rw [evenFourierTransform_involutive, hP, map_zero]

/-- Cosine Fourier reflection also preserves the orthogonal complement of the Sonin carrier. -/
theorem evenFourierTransform_mem_evenCentralSoninCarrier_orthogonal
    (a : ℝ) {f : evenSubspace} (hf : f ∈ (evenCentralSoninCarrier a)ᗮ) :
    evenFourierTransform f ∈ (evenCentralSoninCarrier a)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hf ⊢
  intro g hg
  exact (evenFourierTransform_symmetric f g).trans
    (hf (evenFourierTransform g)
      (evenFourierTransform_mem_evenCentralSoninCarrier a hg))

/-- The exact even Sonin projection commutes with cosine Fourier reflection. -/
theorem evenFourierTransform_evenCentralSoninProjection
    (a : ℝ) (f : evenSubspace) :
    evenFourierTransform (evenCentralSoninProjection a f) =
      evenCentralSoninProjection a (evenFourierTransform f) := by
  rw [evenCentralSoninProjection_eq_starProjection]
  symm
  apply (evenCentralSoninCarrier a).eq_starProjection_of_mem_orthogonal
  · exact evenFourierTransform_mem_evenCentralSoninCarrier a
      ((evenCentralSoninCarrier a).starProjection_apply_mem f)
  · simpa only [map_sub] using
      evenFourierTransform_mem_evenCentralSoninCarrier_orthogonal a
        ((evenCentralSoninCarrier a).sub_starProjection_mem_orthogonal f)

/-- The symmetric forward-plus-inverse dilation channel is Fourier-even. -/
theorem evenFourierTransform_evenDilationSum
    (r : ℝ) (hr : 1 < r) (f : evenSubspace) :
    evenFourierTransform (evenDilationSum r hr f) =
      evenDilationSum r hr (evenFourierTransform f) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hforward :
      evenFourierTransform (evenDilationCLM r hr0 f) =
        evenDilationCLM r⁻¹ (inv_pos.mpr hr0) (evenFourierTransform f) := by
    simpa only [evenDilationCLM] using
      evenFourierTransform_evenDilation r hr0 f
  have hinverse :
      evenFourierTransform
          (evenDilationCLM r⁻¹ (inv_pos.mpr hr0) f) =
        evenDilationCLM r hr0 (evenFourierTransform f) := by
    simpa only [evenDilationCLM, inv_inv] using
      evenFourierTransform_evenDilation r⁻¹ (inv_pos.mpr hr0) f
  rw [evenDilationSum_eq]
  simp only [ContinuousLinearMap.add_apply, evenFourierTransform.map_add]
  rw [hforward, hinverse]
  abel

/-- The successive-layer transition is Fourier-even. -/
theorem evenFourierTransform_evenSoninApertureSuccessiveLayerTransition
    (a b c r : ℝ) (hr : 1 < r) (f : evenSubspace) :
    evenFourierTransform
        (evenSoninApertureSuccessiveLayerTransition a b c r hr f) =
      evenSoninApertureSuccessiveLayerTransition a b c r hr
        (evenFourierTransform f) := by
  unfold evenSoninApertureSuccessiveLayerTransition evenSoninApertureLayer
  simp only [ContinuousLinearMap.mul_apply, sub_apply]
  rw [map_sub, evenFourierTransform_evenCentralSoninProjection,
    evenFourierTransform_evenCentralSoninProjection,
    evenFourierTransform_evenDilationSum,
    map_sub, evenFourierTransform_evenCentralSoninProjection,
    evenFourierTransform_evenCentralSoninProjection]

theorem ccmCommutator_evenSoninApertureSuccessiveLayerTransition_evenFourier
    (a b c r : ℝ) (hr : 1 < r) :
    ccmCommutator
      (evenSoninApertureSuccessiveLayerTransition a b c r hr)
      evenFourierTransform = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  unfold ccmCommutator
  simp only [sub_apply, ContinuousLinearMap.mul_apply]
  rw [← evenFourierTransform_evenSoninApertureSuccessiveLayerTransition]
  simp

/-- The self-adjoint Ward channel is Fourier-even. -/
theorem ccmCommutator_evenSoninApertureSymmetricSuccessiveLayerChannel_evenFourier
    (a b c r : ℝ) (hr : 1 < r) :
    ccmCommutator
      (evenSoninApertureSymmetricSuccessiveLayerChannel a b c r hr)
      evenFourierTransform = 0 := by
  let Z := evenSoninApertureSuccessiveLayerTransition a b c r hr
  let J := evenFourierTransform
  have hZ : Z * J = J * Z := by
    apply sub_eq_zero.mp
    simpa only [Z, J] using
      ccmCommutator_evenSoninApertureSuccessiveLayerTransition_evenFourier
        a b c r hr
  have hZadj : ContinuousLinearMap.adjoint Z * J =
      J * ContinuousLinearMap.adjoint Z := by
    have h := congrArg ContinuousLinearMap.adjoint hZ
    change ContinuousLinearMap.adjoint (Z ∘L J) =
      ContinuousLinearMap.adjoint (J ∘L Z) at h
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      adjoint_evenFourierTransform] at h
    exact h.symm
  change ccmCommutator (Z + ContinuousLinearMap.adjoint Z) J = 0
  unfold ccmCommutator
  noncomm_ring [hZ, hZadj]

/-- Forward-minus-inverse finite dilation holonomy at one exact Sonin aperture. -/
def evenSoninBilateralApertureHolonomy
    (a r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let Q := evenCentralSoninProjection a
  U * Q * ContinuousLinearMap.adjoint U -
    ContinuousLinearMap.adjoint U * Q * U

theorem evenFourierTransform_mul_evenCentralSoninProjection (a : ℝ) :
    evenFourierTransform * evenCentralSoninProjection a =
      evenCentralSoninProjection a * evenFourierTransform := by
  apply ContinuousLinearMap.ext
  intro f
  exact evenFourierTransform_evenCentralSoninProjection a f

theorem evenFourierTransform_mul_evenDilationCLM
    (r : ℝ) (hr : 1 < r) :
    evenFourierTransform * evenDilationCLM r (zero_lt_one.trans hr) =
      ContinuousLinearMap.adjoint
        (evenDilationCLM r (zero_lt_one.trans hr)) * evenFourierTransform := by
  apply ContinuousLinearMap.ext
  intro f
  have h := evenFourierTransform_evenDilation r (zero_lt_one.trans hr) f
  rw [adjoint_evenDilationCLM]
  exact h

theorem evenFourierTransform_mul_adjoint_evenDilationCLM
    (r : ℝ) (hr : 1 < r) :
    evenFourierTransform * ContinuousLinearMap.adjoint
        (evenDilationCLM r (zero_lt_one.trans hr)) =
      evenDilationCLM r (zero_lt_one.trans hr) * evenFourierTransform := by
  apply ContinuousLinearMap.ext
  intro f
  rw [adjoint_evenDilationCLM]
  have h := evenFourierTransform_evenDilation r⁻¹
    (inv_pos.mpr (zero_lt_one.trans hr)) f
  simpa only [evenDilationCLM, inv_inv] using h

/-- **Fourier-oddness of bilateral aperture holonomy.** -/
theorem evenSoninBilateralApertureHolonomy_fourier_odd
    (a r : ℝ) (hr : 1 < r) :
    evenFourierTransform * evenSoninBilateralApertureHolonomy a r hr *
        evenFourierTransform =
      -evenSoninBilateralApertureHolonomy a r hr := by
  let J := evenFourierTransform
  let Q := evenCentralSoninProjection a
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let V := ContinuousLinearMap.adjoint U
  have hJ2 : J * J = 1 := by
    simpa only [J] using evenFourierTransform_mul_self
  have hJQ : J * Q = Q * J := by
    simpa only [J, Q] using evenFourierTransform_mul_evenCentralSoninProjection a
  have hJU : J * U = V * J := by
    simpa only [J, U, V] using evenFourierTransform_mul_evenDilationCLM r hr
  have hJV : J * V = U * J := by
    simpa only [J, U, V] using
      evenFourierTransform_mul_adjoint_evenDilationCLM r hr
  have hJQJ : J * Q * J = Q := by
    calc
      J * Q * J = Q * (J * J) := by rw [hJQ]; noncomm_ring
      _ = Q := by rw [hJ2, mul_one]
  have hJUJ : J * U * J = V := by
    calc
      J * U * J = V * (J * J) := by rw [hJU]; noncomm_ring
      _ = V := by rw [hJ2, mul_one]
  have hJVJ : J * V * J = U := by
    calc
      J * V * J = U * (J * J) := by rw [hJV]; noncomm_ring
      _ = U := by rw [hJ2, mul_one]
  have hconj_mul (A B : evenSubspace →L[ℂ] evenSubspace) :
      J * (A * B) * J = (J * A * J) * (J * B * J) := by
    calc
      J * (A * B) * J = J * A * B * J := by noncomm_ring
      _ = J * A * (J * J) * B * J := by rw [hJ2]; simp
      _ = (J * A * J) * (J * B * J) := by noncomm_ring
  change J * (U * Q * V - V * Q * U) * J =
    -(U * Q * V - V * Q * U)
  calc
    J * (U * Q * V - V * Q * U) * J =
        J * (U * Q * V) * J - J * (V * Q * U) * J := by
      rw [mul_sub, sub_mul]
    _ = (J * U * J) * (J * Q * J) * (J * V * J) -
          (J * V * J) * (J * Q * J) * (J * U * J) := by
      rw [hconj_mul (U * Q) V, hconj_mul U Q,
        hconj_mul (V * Q) U, hconj_mul V Q]
    _ = V * Q * U - U * Q * V := by rw [hJUJ, hJQJ, hJVJ]
    _ = -(U * Q * V - V * Q * U) := by module

/-- **Non-vacuity of bilateral holonomy.**  At every positive aperture and every nontrivial
dilation scale, forward and inverse conjugations of the Sonin projection are distinct. -/
theorem evenSoninBilateralApertureHolonomy_ne_zero
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    evenSoninBilateralApertureHolonomy a r hr ≠ 0 := by
  let Q := evenCentralSoninProjection a
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let V := ContinuousLinearMap.adjoint U
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hVU : V * U = 1 := by
    dsimp only [V, U]
    rw [adjoint_evenDilationCLM]
    exact evenDilationCLM_inv_mul r hr0
  have hUV : U * V = 1 := by
    dsimp only [V, U]
    rw [adjoint_evenDilationCLM, evenDilationCLM_mul]
    have hscale : evenDilationCLM (r * r⁻¹)
        (mul_pos hr0 (inv_pos.mpr hr0)) =
          evenDilationCLM 1 zero_lt_one := by
      congr 1
      exact mul_inv_cancel₀ hr0.ne'
    rw [hscale, evenDilationCLM_one]
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    simpa only [Q] using adjoint_evenCentralSoninProjection a
  intro hzero
  have heq : U * Q * V = V * Q * U := by
    apply sub_eq_zero.mp
    simpa only [evenSoninBilateralApertureHolonomy, Q, U, V] using hzero
  have hU2Q : (U * U) * Q = Q * (U * U) := by
    calc
      (U * U) * Q = U * (U * Q * V) * U := by
        noncomm_ring [hVU]
      _ = U * (V * Q * U) * U := by rw [heq]
      _ = (U * V) * Q * (U * U) := by noncomm_ring
      _ = Q * (U * U) := by rw [hUV, one_mul]
  have hV2Q : (V * V) * Q = Q * (V * V) := by
    have h := congrArg ContinuousLinearMap.adjoint hU2Q
    change ContinuousLinearMap.adjoint ((U * U) ∘L Q) =
      ContinuousLinearMap.adjoint (Q ∘L (U * U)) at h
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp] at h
    have hUU : ContinuousLinearMap.adjoint (U * U) = V * V := by
      change ContinuousLinearMap.adjoint (U ∘L U) = V * V
      rw [ContinuousLinearMap.adjoint_comp]
      rfl
    rw [hUU, hQadj] at h
    exact h.symm
  have hr2 : 1 < r * r := by nlinarith
  let U2 := evenDilationCLM (r * r) (zero_lt_one.trans hr2)
  let V2 := evenDilationCLM (r * r)⁻¹
    (inv_pos.mpr (zero_lt_one.trans hr2))
  have hU2 : U * U = U2 := by
    dsimp only [U, U2]
    exact evenDilationCLM_mul r r hr0 hr0
  have hV2 : V * V = V2 := by
    dsimp only [V, U, V2]
    rw [adjoint_evenDilationCLM, evenDilationCLM_mul]
    congr 1
    field_simp
  have hDcomm : evenDilationSum (r * r) hr2 * Q =
      Q * evenDilationSum (r * r) hr2 := by
    rw [evenDilationSum_eq]
    change (U2 + V2) * Q = Q * (U2 + V2)
    rw [← hU2, ← hV2]
    noncomm_ring [hU2Q, hV2Q]
  have hQid : IsIdempotentElem Q := by
    dsimp only [Q]
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).isIdempotentElem_starProjection
  have hcorner : evenCentralSoninDilationCorner a (r * r) hr2 = 0 := by
    rw [evenCentralSoninDilationCorner_eq_crossBoundary]
    exact crossBoundary_eq_zero_of_commute hQid hDcomm
  have hnot := evenCentralSoninDilationCorner_not_isCompactOperator
    a (r * r) ha hr2
  apply hnot
  rw [hcorner]
  exact isCompactOperator_zero

/-- **Invariant-reader annihilation law.**  Every Fourier-conjugation-invariant complex-linear
reader annihilates bilateral aperture holonomy. -/
theorem reflectionInvariantLinearReader_evenSoninBilateralApertureHolonomy_eq_zero
    (Phi : (evenSubspace →L[ℂ] evenSubspace) →ₗ[ℂ] ℂ)
    (hPhi : ∀ T, Phi (evenFourierTransform * T * evenFourierTransform) = Phi T)
    (a r : ℝ) (hr : 1 < r) :
    Phi (evenSoninBilateralApertureHolonomy a r hr) = 0 := by
  let H := evenSoninBilateralApertureHolonomy a r hr
  have hodd : evenFourierTransform * H * evenFourierTransform = -H := by
    simpa only [H] using evenSoninBilateralApertureHolonomy_fourier_odd a r hr
  have h := hPhi H
  rw [hodd, map_neg] at h
  have htwo : (2 : ℂ) * Phi H = 0 := by
    calc
      (2 : ℂ) * Phi H = Phi H + Phi H := by ring
      _ = -Phi H + Phi H := congrArg (fun z : ℂ => z + Phi H) h.symm
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- **Fourier-parity no-go.**  A Fourier-invariant linear finite part identifies the odd
bilateral holonomy with the positive aperture Ward energy exactly in the flat case. -/
theorem reflectionInvariantLinearReader_holonomy_eq_apertureWardEnergy_iff_flat
    (Phi : (evenSubspace →L[ℂ] evenSubspace) →ₗ[ℂ] ℂ)
    (hPhi : ∀ T, Phi (evenFourierTransform * T * evenFourierTransform) = Phi T)
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * a) :
    Phi (evenSoninBilateralApertureHolonomy a r hr) =
        (hsNormSq
          (ccmCommutator
            (evenSoninApertureSymmetricSuccessiveLayerChannel a b c r hr)
            (evenSoninApertureLayer a b)) : ℂ) ↔
      evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 := by
  let Z := evenSoninApertureSuccessiveLayerTransition a b c r hr
  let W := ccmCommutator
    (evenSoninApertureSymmetricSuccessiveLayerChannel a b c r hr)
    (evenSoninApertureLayer a b)
  have hPhiH :=
    reflectionInvariantLinearReader_evenSoninBilateralApertureHolonomy_eq_zero
      Phi hPhi a r hr
  have hZhs : Z.IsHilbertSchmidt := by
    simpa only [Z] using
      evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
        ha hab hbc hr hcr
  have hward : hsNormSq W = 2 * hsNormSq Z := by
    simpa only [W, Z] using
      hsNormSq_apertureWardCommutator_eq_two_mul_successiveLayerTransition
        ha hab hbc hr hcr
  constructor
  · intro heq
    have henergyC : (hsNormSq W : ℂ) = 0 := by
      rw [← heq, hPhiH]
    have henergy : hsNormSq W = 0 := Complex.ofReal_eq_zero.mp henergyC
    have hZzero : hsNormSq Z = 0 := by linarith
    exact (hsNormSq_eq_zero_iff hZhs).mp hZzero
  · intro hZzero
    have hZzero' : Z = 0 := by simpa only [Z] using hZzero
    have henergy : hsNormSq W = 0 := by
      rw [hward, hZzero']
      simp [hsNormSq]
    rw [hPhiH]
    rw [henergy]
    simp

end RHTower
