import GaloisForLFunctions.RHTower.CHMDFixedApertureQuotientLanding
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLimitingLogMixedReality
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilMixedSourceForm

/-!
# The real restricted Weil domain in the arithmetic source graph

The closure of the real smooth aperture core is exactly the part of the
complete restricted Weil domain with a real physical representative.
Orthogonal projection onto that closure is physical real-part extraction.
This identifies the domain of the completed inverse-Doob lift intrinsically.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower

set_option autoImplicit false
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDPolar


private theorem aperture_core_physical_inner_im (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
  change (inner ℂ (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u))
    (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0
  rw [L2.inner_def]
  have he : (∫ x, inner ℂ
      (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u) x)
      (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a v) x)) =
      ((∫ x, u x * v x : ℝ) : ℂ) := by
    calc
      _ = ∫ x, ((u x * v x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u,
          ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a v]
          with x hu hv
        change ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u) x = _ at hu
        change ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a v) x = _ at hv
        rw [hu, hv]
        simp [RCLike.inner_apply, mul_comm]
      _ = _ := integral_ofReal
  rw [he, Complex.ofReal_im]

private theorem aperture_core_prime_inner_im (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ
      (ccmFinitePrimeOperator a
        (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u)))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
  classical
  unfold ccmFinitePrimeOperator
  generalize Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, add_apply, inner_add_left,
        Complex.add_im, ih, add_zero, smul_apply, inner_smul_left]
      simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero,
        inner_ccmPrimeTransportOperator_realCore_mixed_im_eq_zero, mul_zero]

/-- The archimedean form inner product is real on real smooth sources.
The finite prime, polar and scalar terms are all real separately. -/
theorem aperture_core_inner_im_eq_zero (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ (suzukiRestrictedWeilCoreCCMFormVector a u)
      (suzukiRestrictedWeilCoreCCMFormVector a v)).im = 0 := by
  have hpolar : (inner ℂ
      (ccmPolarOperator a
        (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u)))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
    rw [inner_ccmPolarOperator_mixed]
    simp_rw [inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal]
    simp
  have h := ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u v
  unfold ccmRestrictedWeilForm at h
  rw [inner_ccmRestrictedWeilBoundedRemainder_mixed] at h
  simpa only [Complex.add_im, Complex.sub_im, ccmArchimedeanRemainderScalar,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    aperture_core_physical_inner_im, aperture_core_prime_inner_im, hpolar,
    mul_zero, add_zero, sub_zero] using h

/-- Mixed inner products remain real after completion of the real core. -/
theorem apertureWeilCompletion_inner_im_eq_zero (a : SuzukiPositiveAperture)
    {p q : CCMArchimedeanFormDomain a}
    (hp : p ∈ apertureWeilCompletion a) (hq : q ∈ apertureWeilCompletion a) :
    (inner ℂ p q).im = 0 := by
  have hcore {r s : CCMArchimedeanFormDomain a}
      (hr : r ∈ apertureWeilCore a) (hs : s ∈ apertureWeilCore a) :
      (inner ℂ r s).im = 0 := by
    obtain ⟨r, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := hs
    exact aperture_core_inner_im_eq_zero a (Classical.choose r.property)
      (Classical.choose s.property)
  have hleft {s : CCMArchimedeanFormDomain a} (hs : s ∈ apertureWeilCore a) :
      (inner ℂ p s).im = 0 := by
    exact closure_minimal (fun r hr => hcore hr hs)
      (isClosed_eq (Complex.continuous_im.comp
        ((continuous_id : Continuous (fun x : CCMArchimedeanFormDomain a => x)).inner
          (𝕜 := ℂ) continuous_const)) continuous_const) hp
  exact closure_minimal (fun s hs => hleft hs)
    (isClosed_eq (Complex.continuous_im.comp
      ((continuous_const : Continuous (fun _ : CCMArchimedeanFormDomain a => p)).inner
        (𝕜 := ℂ) continuous_id)) continuous_const) hq

theorem suzukiCore_mem_apertureWeilCompletion (a : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore a.1) :
    suzukiRestrictedWeilCoreCCMFormVector a u ∈ apertureWeilCompletion a :=
  (apertureWeilCore a).le_topologicalClosure
    ⟨⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩, apertureCoreWeilCoordinate_core a u⟩

local instance apertureFormRealInner (a : SuzukiPositiveAperture) :
    InnerProductSpace ℝ (CCMArchimedeanFormDomain a) :=
  InnerProductSpace.complexToReal

/-- Orthogonal projection onto the completed real aperture core. -/
def apertureRealPart (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℝ] CCMArchimedeanFormDomain a :=
  (apertureWeilCompletion a).starProjection

theorem apertureRealPart_smooth (a : SuzukiPositiveAperture)
    (u : CCMComplexSmoothInteriorSource a) :
    apertureRealPart a u.toCCMFormVector =
      suzukiRestrictedWeilCoreCCMFormVector a u.realCore := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (suzukiCore_mem_apertureWeilCompletion a u.realCore)
  intro w hw
  rw [u.toCCMFormVector_eq_real_add_I_imag, add_sub_cancel_left]
  change (inner ℂ (I • suzukiRestrictedWeilCoreCCMFormVector a u.imagCore) w).re = 0
  rw [inner_smul_left (suzukiRestrictedWeilCoreCCMFormVector a u.imagCore) w I]
  have him := apertureWeilCompletion_inner_im_eq_zero a
    (suzukiCore_mem_apertureWeilCompletion a u.imagCore) hw
  simp only [Complex.conj_I, Complex.neg_re, Complex.I_re, neg_zero,
    Complex.neg_im, Complex.I_im, Complex.mul_re, zero_mul, him, mul_zero, sub_zero]

/-- Real-part extraction on physical complex `L²`. -/
def physicalRealPart : SoninL2 →L[ℝ] SoninL2 :=
  (Complex.ofRealCLM.compLpL 2 volume).comp (Complex.reCLM.compLpL 2 volume)

theorem physicalRealPart_ae (f : SoninL2) :
    physicalRealPart f =ᵐ[volume] fun x => ((f x).re : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := volume)
    (Complex.reCLM.compLpL 2 volume f),
    Complex.reCLM.coeFn_compLpL (p := 2) (μ := volume) f] with x h₁ h₂
  change (Complex.ofRealCLM.compLpL 2 volume (Complex.reCLM.compLpL 2 volume f)) x = _
  rw [h₁, h₂]
  rfl

/-- Orthogonal real-part extraction in the form domain is the literal
real-part operation on the physical source. -/
theorem apertureRealPart_physical (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormEmbedding a (apertureRealPart a q) =
      physicalRealPart (ccmArchimedeanFormEmbedding a q) := by
  have hclosed : IsClosed {q : CCMArchimedeanFormDomain a |
      ccmArchimedeanFormEmbedding a (apertureRealPart a q) =
        physicalRealPart (ccmArchimedeanFormEmbedding a q)} :=
    isClosed_eq ((ccmArchimedeanFormEmbedding a).continuous.comp (apertureRealPart a).continuous)
      (physicalRealPart.continuous.comp (ccmArchimedeanFormEmbedding a).continuous)
  apply closure_minimal ?_ hclosed (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a q)
  rintro _ ⟨u, rfl⟩
  change ccmArchimedeanFormEmbedding a (apertureRealPart a u.toCCMFormVector) =
    physicalRealPart (ccmArchimedeanFormEmbedding a u.toCCMFormVector)
  rw [apertureRealPart_smooth]
  apply Lp.ext
  filter_upwards [ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u.realCore,
    u.toCCMFormVector_physical_coeFn,
    physicalRealPart_ae (ccmArchimedeanFormEmbedding a u.toCCMFormVector)] with x hr hu hp
  change ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u.realCore) x = _ at hr
  change ccmArchimedeanFormEmbedding a u.toCCMFormVector x = _ at hu
  rw [hr, hp, hu]
  rfl

/-- Intrinsic description of the complete real aperture domain. -/
theorem mem_apertureWeilCompletion_iff_physicalRealPart (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a) :
    q ∈ apertureWeilCompletion a ↔
      physicalRealPart (ccmArchimedeanFormEmbedding a q) = ccmArchimedeanFormEmbedding a q := by
  constructor
  · intro hq
    have heq : apertureRealPart a q = q :=
      (Submodule.starProjection_eq_self_iff (K := apertureWeilCompletion a) (v := q)).mpr hq
    rw [← apertureRealPart_physical, heq]
  · intro hq
    have heq : apertureRealPart a q = q :=
      ccmArchimedeanFormEmbedding_injective a ((apertureRealPart_physical a q).trans hq)
    exact (Submodule.starProjection_eq_self_iff (K := apertureWeilCompletion a) (v := q)).mp heq

/-- Every real physical representative in the CCM form domain belongs to the
completion of the real smooth core. -/
theorem mem_apertureWeilCompletion_iff_im_eq_zero_ae (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a) :
    q ∈ apertureWeilCompletion a ↔
      ∀ᵐ x ∂volume, (ccmArchimedeanFormEmbedding a q x).im = 0 := by
  rw [mem_apertureWeilCompletion_iff_physicalRealPart]
  constructor
  · intro h
    filter_upwards [physicalRealPart_ae (ccmArchimedeanFormEmbedding a q)] with x hx
    rw [h] at hx
    exact congrArg Complex.im hx |>.trans (Complex.ofReal_im _)
  · intro h
    apply Lp.ext
    filter_upwards [physicalRealPart_ae (ccmArchimedeanFormEmbedding a q), h] with x hx hi
    rw [hx]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hi.symm

/-- The completed graph/Weil correspondence preserves the literal physical source. -/
theorem apertureGraphWeilEquiv_physical (a : SuzukiPositiveAperture)
    (p : apertureGraphCompletion a) :
    ccmArchimedeanFormEmbedding a (apertureGraphWeilEquiv a p).val =
      graphPhysicalSource p.val := by
  have hclosed : IsClosed {p : apertureGraphCompletion a |
      ccmArchimedeanFormEmbedding a (apertureGraphWeilEquiv a p).val =
        graphPhysicalSource p.val} :=
    isClosed_eq ((ccmArchimedeanFormEmbedding a).continuous.comp
      (continuous_subtype_val.comp (apertureGraphWeilEquiv a).continuous))
      (graphPhysicalSource.continuous.comp continuous_subtype_val)
  apply closure_minimal ?_ hclosed (denseRange_apertureGraphCoreInclusion a p)
  rintro _ ⟨v, rfl⟩
  change ccmArchimedeanFormEmbedding a
    (apertureGraphWeilEquiv a (apertureGraphCoreInclusion a v)).val = graphPhysicalSource v.val
  rw [apertureGraphWeilEquiv_core]
  exact apertureCoreWeilVector_embedding a v

/-- Every real CCM form vector has a unique fixed-aperture CHMD inverse-Doob
lift. Its full Weil energy agrees with that of its signed quotient class. -/
theorem existsUnique_real_aperture_lift (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a)
    (hq : ∀ᵐ x ∂volume, (ccmArchimedeanFormEmbedding a q x).im = 0) :
    ∃! p : apertureGraphCompletion a,
      graphPhysicalSource p.val = ccmArchimedeanFormEmbedding a q ∧
        quotientWeilForm (signedQuotientMk p.val) = (ccmRestrictedWeilForm a q q).re := by
  let qR : apertureWeilCompletion a :=
    ⟨q, (mem_apertureWeilCompletion_iff_im_eq_zero_ae a q).mpr hq⟩
  let p := (apertureGraphWeilEquiv a).symm qR
  have hp : apertureGraphWeilEquiv a p = qR := (apertureGraphWeilEquiv a).apply_symm_apply qR
  have hphysical : graphPhysicalSource p.val = ccmArchimedeanFormEmbedding a q := by
    rw [← apertureGraphWeilEquiv_physical, hp]
  refine ⟨p, ⟨hphysical, apertureWeilSignedQuotient_weil a qR⟩, ?_⟩
  intro p' hp'
  exact Subtype.ext (graphPhysicalSource_injective (hp'.1.trans hphysical.symm))

/-- The complete complex form domain is the orthogonal complexification of
the completed real source domain. -/
theorem exists_apertureWeilCompletion_complex_decomposition (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a) :
    ∃ r s : apertureWeilCompletion a, q = r.val + I • s.val ∧
      ‖q‖ ^ 2 = ‖r‖ ^ 2 + ‖s‖ ^ 2 := by
  let r : apertureWeilCompletion a :=
    ⟨apertureRealPart a q, (apertureWeilCompletion a).starProjection_apply_mem q⟩
  let s : apertureWeilCompletion a :=
    ⟨apertureRealPart a (-I • q), (apertureWeilCompletion a).starProjection_apply_mem (-I • q)⟩
  have heq : q = r.val + I • s.val := by
    apply ccmArchimedeanFormEmbedding_injective a
    rw [map_add, map_smul]
    change ccmArchimedeanFormEmbedding a q =
      ccmArchimedeanFormEmbedding a (apertureRealPart a q) +
        I • ccmArchimedeanFormEmbedding a (apertureRealPart a (-I • q))
    rw [apertureRealPart_physical, apertureRealPart_physical, map_smul]
    set f := ccmArchimedeanFormEmbedding a q
    apply Lp.ext
    filter_upwards [physicalRealPart_ae f, physicalRealPart_ae (-I • f),
      Lp.coeFn_smul (-I) f, Lp.coeFn_smul I (physicalRealPart (-I • f)),
      Lp.coeFn_add (physicalRealPart f) (I • physicalRealPart (-I • f))]
        with x hr hs hneg him hadd
    rw [hadd, Pi.add_apply, him, Pi.smul_apply, hr, hs, hneg, Pi.smul_apply]
    apply Complex.ext <;>
      simp [smul_eq_mul, Complex.mul_re, Complex.mul_im]
  refine ⟨r, s, heq, ?_⟩
  rw [heq, norm_add_sq (𝕜 := ℂ), inner_smul_right r.val s.val I]
  change ‖r.val‖ ^ 2 + 2 * (I * inner ℂ r.val s.val).re + ‖I • s.val‖ ^ 2 =
    ‖r.val‖ ^ 2 + ‖s.val‖ ^ 2
  have him := apertureWeilCompletion_inner_im_eq_zero a r.property s.property
  simp only [norm_smul, Complex.norm_I, one_mul, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, him, sub_zero, mul_zero, add_zero]

/-- The full signed Weil form is real on the completed real domain. -/
theorem apertureWeilCompletion_weil_im_eq_zero (a : SuzukiPositiveAperture)
    {p q : CCMArchimedeanFormDomain a}
    (hp : p ∈ apertureWeilCompletion a) (hq : q ∈ apertureWeilCompletion a) :
    (ccmRestrictedWeilForm a p q).im = 0 := by
  have hcont : Continuous (fun z : CCMArchimedeanFormDomain a × CCMArchimedeanFormDomain a =>
      ccmRestrictedWeilForm a z.1 z.2) := by
    unfold ccmRestrictedWeilForm
    exact (continuous_fst.inner (𝕜 := ℂ) continuous_snd).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp
        ((ccmArchimedeanFormToAperture a).continuous.comp continuous_fst)).inner
          ((ccmArchimedeanFormToAperture a).continuous.comp continuous_snd))
  have hcore {r s : CCMArchimedeanFormDomain a}
      (hr : r ∈ apertureWeilCore a) (hs : s ∈ apertureWeilCore a) :
      (ccmRestrictedWeilForm a r s).im = 0 := by
    obtain ⟨r, rfl⟩ := hr
    obtain ⟨s, rfl⟩ := hs
    exact ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a
      (Classical.choose r.property) (Classical.choose s.property)
  have hleft {s : CCMArchimedeanFormDomain a} (hs : s ∈ apertureWeilCore a) :
      (ccmRestrictedWeilForm a p s).im = 0 := by
    exact closure_minimal (fun r hr => hcore hr hs)
      (isClosed_eq (Complex.continuous_im.comp
        (hcont.comp (continuous_id.prodMk continuous_const))) continuous_const) hp
  exact closure_minimal (fun s hs => hleft hs)
    (isClosed_eq (Complex.continuous_im.comp
      (hcont.comp (continuous_const.prodMk continuous_id))) continuous_const) hq

/-- Every complex restricted-Weil state admits two actual real CHMD graph
lifts. Their quotient energies add to its complete Weil energy. -/
theorem exists_aperture_graph_pair_preserving_weil (a : SuzukiPositiveAperture)
    (q : CCMArchimedeanFormDomain a) :
    ∃ p r : apertureGraphCompletion a,
      ccmArchimedeanFormEmbedding a q = graphPhysicalSource p.val + I • graphPhysicalSource r.val ∧
      (ccmRestrictedWeilForm a q q).re =
        quotientWeilForm (signedQuotientMk p.val) + quotientWeilForm (signedQuotientMk r.val) := by
  obtain ⟨u, v, hq, -⟩ := exists_apertureWeilCompletion_complex_decomposition a q
  let p := (apertureGraphWeilEquiv a).symm u
  let r := (apertureGraphWeilEquiv a).symm v
  have hp : apertureGraphWeilEquiv a p = u := (apertureGraphWeilEquiv a).apply_symm_apply u
  have hr : apertureGraphWeilEquiv a r = v := (apertureGraphWeilEquiv a).apply_symm_apply v
  have hpu : graphPhysicalSource p.val = ccmArchimedeanFormEmbedding a u.val := by
    rw [← apertureGraphWeilEquiv_physical, hp]
  have hrv : graphPhysicalSource r.val = ccmArchimedeanFormEmbedding a v.val := by
    rw [← apertureGraphWeilEquiv_physical, hr]
  refine ⟨p, r, ?_, ?_⟩
  · rw [hq, map_add, map_smul, hpu, hrv]
  · have hWp : quotientWeilForm (signedQuotientMk p.val) =
        (ccmRestrictedWeilForm a u.val u.val).re := apertureWeilSignedQuotient_weil a u
    have hWr : quotientWeilForm (signedQuotientMk r.val) =
        (ccmRestrictedWeilForm a v.val v.val).re := apertureWeilSignedQuotient_weil a v
    rw [hWp, hWr, hq, ccmRestrictedWeilForm_realImag_expansion]
    have huv := apertureWeilCompletion_weil_im_eq_zero a u.property v.property
    have hvu := apertureWeilCompletion_weil_im_eq_zero a v.property u.property
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, huv, hvu, sub_zero, add_zero]


end RHTower
