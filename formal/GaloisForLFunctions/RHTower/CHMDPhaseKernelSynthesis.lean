import GaloisForLFunctions.RHTower.CHMDFiniteSampleRange

/-!
# Finite-dimensional synthesis of literal Fourier kernels

All translated phase kernels at a fixed nonzero frequency lie in a space
spanned by four real Fourier kernels. Their span is closed, and exponential
pair separation proves that it contains all four kernels. At Xi zeros these
are actual signed generator images of finite-sample sources.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

abbrev MassSmallShift := {t : ℝ // |t| ≤ CHMDThetaTranslate.radius}

def massPhaseReadout (w : MassSpace) (a : MassSamplePoint) (t : ℝ) : ℂ :=
  (exp (-(I*a.val)*(t : ℂ)) * massFourierReadout w a.val +
    exp ((I*a.val)*(t : ℂ)) * massFourierReadout w (-a.val))/2

theorem massShiftedCosineRealKernel_pair_mass (a : MassSamplePoint) (t : ℝ) (w : MassSpace) :
    ⟪massShiftedCosineRealKernel a t, w⟫_ℝ = (massPhaseReadout w a t).re := by
  rw [massShiftedCosineRealKernel, inner_add_left, massWeightedRealKernel_pair,
    massWeightedRealKernel_pair, ← Complex.add_re]
  change (_ + exp ((I*a.val)*(t : ℂ))/2 * massFourierReadout w (-a.val)).re = _
  unfold massPhaseReadout
  congr 1
  ring

theorem massShiftedCosineImagKernel_pair_mass (a : MassSamplePoint) (t : ℝ) (w : MassSpace) :
    ⟪massShiftedCosineImagKernel a t, w⟫_ℝ = (massPhaseReadout w a t).im := by
  rw [massShiftedCosineImagKernel, inner_add_left, massWeightedImagKernel_pair,
    massWeightedImagKernel_pair, ← Complex.add_im]
  change (_ + exp ((I*a.val)*(t : ℂ))/2 * massFourierReadout w (-a.val)).im = _
  unfold massPhaseReadout
  congr 1
  ring

def massPhaseSpan (a : MassSamplePoint) : Submodule ℝ MassSpace :=
  Submodule.span ℝ (Set.range (fun t : MassSmallShift => massShiftedCosineRealKernel a t) ∪
    Set.range (fun t : MassSmallShift => massShiftedCosineImagKernel a t))

def massOrbitKernelSet (a : MassSamplePoint) : Set MassSpace :=
  {massSampleRealKernel a, massSampleImagKernel a,
    massSampleRealKernel (negMassSamplePoint a), massSampleImagKernel (negMassSamplePoint a)}

theorem massPhaseSpan_le_four_kernel_span (a : MassSamplePoint) :
    massPhaseSpan a ≤ Submodule.span ℝ (massOrbitKernelSet a) := by
  let P := Submodule.span ℝ (massOrbitKernelSet a)
  have hr : massSampleRealKernel a ∈ P := Submodule.subset_span (by simp [massOrbitKernelSet])
  have hi : massSampleImagKernel a ∈ P := Submodule.subset_span (by simp [massOrbitKernelSet])
  have hnr : massSampleRealKernel (negMassSamplePoint a) ∈ P :=
    Submodule.subset_span (by simp [massOrbitKernelSet])
  have hni : massSampleImagKernel (negMassSamplePoint a) ∈ P :=
    Submodule.subset_span (by simp [massOrbitKernelSet])
  apply Submodule.span_le.mpr
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact P.add_mem (massWeightedRealKernel_mem_submodule P _ a hr hi)
      (massWeightedRealKernel_mem_submodule P _ _ hnr hni)
  · exact P.add_mem (massWeightedImagKernel_mem_submodule P _ a hr hi)
      (massWeightedImagKernel_mem_submodule P _ _ hnr hni)

instance finiteDimensional_massPhaseSpan (a : MassSamplePoint) :
    FiniteDimensional ℝ (massPhaseSpan a) := by
  letI : FiniteDimensional ℝ (Submodule.span ℝ (massOrbitKernelSet a)) :=
    FiniteDimensional.span_of_finite ℝ (by simp [massOrbitKernelSet])
  exact Submodule.finiteDimensional_of_le (massPhaseSpan_le_four_kernel_span a)

theorem isClosed_massPhaseSpan (a : MassSamplePoint) : IsClosed (massPhaseSpan a : Set MassSpace) :=
  Submodule.closed_of_finiteDimensional _

theorem massPhaseSpan_orthogonal_samples {a : MassSamplePoint} (ha : a.val ≠ 0)
    {w : MassSpace} (hw : w ∈ (massPhaseSpan a)ᗮ) :
    massFourierReadout w a.val = 0 ∧ massFourierReadout w (-a.val) = 0 := by
  apply exponential_pair_separation ha CHMDThetaTranslate.radius_pos
  intro t ht
  have hr := hw (massShiftedCosineRealKernel a t)
    (Submodule.subset_span (Or.inl ⟨⟨t, ht⟩, rfl⟩))
  have hi := hw (massShiftedCosineImagKernel a t)
    (Submodule.subset_span (Or.inr ⟨⟨t, ht⟩, rfl⟩))
  rw [massShiftedCosineRealKernel_pair_mass] at hr
  rw [massShiftedCosineImagKernel_pair_mass] at hi
  have he : massPhaseReadout w a t = 0 := Complex.ext hr hi
  simpa only [massPhaseReadout, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using he

/-- Exact membership in the phase span, not only its topological closure. -/
theorem massSampleKernels_mem_phaseSpan (a : MassSamplePoint) (ha : a.val ≠ 0) :
    massSampleRealKernel a ∈ massPhaseSpan a ∧
    massSampleImagKernel a ∈ massPhaseSpan a ∧
    massSampleRealKernel (negMassSamplePoint a) ∈ massPhaseSpan a ∧
    massSampleImagKernel (negMassSamplePoint a) ∈ massPhaseSpan a := by
  have he : (massPhaseSpan a)ᗮᗮ = massPhaseSpan a :=
    (Submodule.orthogonal_orthogonal_eq_closure _).trans
      (isClosed_massPhaseSpan a).submodule_topologicalClosure_eq
  have hmem (x : MassSpace) (hx : ∀ w ∈ (massPhaseSpan a)ᗮ, ⟪x, w⟫_ℝ = 0) :
      x ∈ massPhaseSpan a := by
    rw [← he]
    intro w hw
    rw [real_inner_comm]
    exact hx w hw
  refine ⟨hmem _ ?_, hmem _ ?_, hmem _ ?_, hmem _ ?_⟩
  · intro w hw
    rw [← massSample_re_eq_inner, (massPhaseSpan_orthogonal_samples ha hw).1]
    rfl
  · intro w hw
    rw [← massSample_im_eq_inner, (massPhaseSpan_orthogonal_samples ha hw).1]
    rfl
  · intro w hw
    rw [← massSample_re_eq_inner]
    change (massFourierReadout w (-a.val)).re = 0
    rw [(massPhaseSpan_orthogonal_samples ha hw).2]
    rfl
  · intro w hw
    rw [← massSample_im_eq_inner]
    change (massFourierReadout w (-a.val)).im = 0
    rw [(massPhaseSpan_orthogonal_samples ha hw).2]
    rfl

theorem massPhaseSpan_le_finiteSampleImageSpace {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    massPhaseSpan ⟨a, Or.inl hz⟩ ≤ finiteSampleImageSpace := by
  apply Submodule.span_le.mpr
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact (phase_kernels_mem_finiteSampleImageSpace ha hz t t.property).1
  · exact (phase_kernels_mem_finiteSampleImageSpace ha hz t t.property).2

/-- Every literal Xi-zero Fourier kernel has an actual finite-sample preimage
under the signed arithmetic generator, without a reality or simplicity premise. -/
theorem zero_sample_kernels_mem_finiteSampleImageSpace {z : ℂ} (hz : XiC z = 0) :
    massSampleRealKernel ⟨z, Or.inl hz⟩ ∈ finiteSampleImageSpace ∧
    massSampleImagKernel ⟨z, Or.inl hz⟩ ∈ finiteSampleImageSpace := by
  rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with hn | hp
  · have hzn : XiC (-z) = 0 := by rw [XiC_even, hz]
    have hpos : 0 < (-z).re := by simpa using neg_pos.mpr hn
    have hne : (-z) ≠ 0 := by intro he; simp [he] at hpos
    have hK := massSampleKernels_mem_phaseSpan ⟨-z, Or.inl hzn⟩ hne
    have hS := massPhaseSpan_le_finiteSampleImageSpace hpos hzn
    have he : negMassSamplePoint ⟨-z, Or.inl hzn⟩ = ⟨z, Or.inl hz⟩ :=
      Subtype.ext (neg_neg z)
    exact ⟨by simpa only [he] using hS hK.2.2.1,
      by simpa only [he] using hS hK.2.2.2⟩
  · have hne : z ≠ 0 := by intro he; simp [he] at hp
    have hK := massSampleKernels_mem_phaseSpan ⟨z, Or.inl hz⟩ hne
    have hS := massPhaseSpan_le_finiteSampleImageSpace hp hz
    exact ⟨hS hK.1, hS hK.2.1⟩

end RHTower.CHMDDoobGraph
