import GaloisForLFunctions.RHTower.CHMDPhaseKernelSynthesis

/-!
# Exact algebraic inverse of the signed arithmetic generator

The signed generator images of finite-sample sources are exactly the algebraic
span of the literal divisor and polar Fourier kernels. Every vector in that
span has a unique maximal-domain preimage orthogonal to the critical eigenspace;
that preimage automatically has finite sample support.
No closed-range assumption or infinite cardinal expansion is used.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem zero_samples_polar_image_mem {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    massPolarImage w ∈ finiteSampleImageSpace := by
  refine ⟨∅, w, ?_, mass_zero_samples_resolvent_identity hz⟩
  intro ρ _
  have he := CHMDStage16.XiC_gammaOf_eq_zero ρ
  exact ⟨hz _ he, hz _ (by rw [XiC_even, he])⟩

theorem polar_real_kernels_mem_finiteSampleImageSpace :
    massSampleRealKernel ⟨I/2, Or.inr (Or.inl rfl)⟩ ∈ finiteSampleImageSpace ∧
    massSampleRealKernel ⟨-I/2, Or.inr (Or.inr rfl)⟩ ∈ finiteSampleImageSpace := by
  let kp := massSampleRealKernel ⟨I/2, Or.inr (Or.inl rfl)⟩
  let km := massSampleRealKernel ⟨-I/2, Or.inr (Or.inr rfl)⟩
  have hground : massPolarImage (sourceMap (constantLift 1)) ∈ finiteSampleImageSpace := by
    apply zero_samples_polar_image_mem
    intro z hz
    rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hz).le]
    exact ground_mem_fullSpectralNullspace z hz
  have hodd : massPolarImage (sourceMap oddPolarVector) ∈ finiteSampleImageSpace := by
    apply zero_samples_polar_image_mem
    intro z hz
    rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hz).le]
    exact oddPolarVector_mem_fullSpectralNullspace z hz
  have hgm : graphFourierReadout (constantLift 1) (-I/2) = 1/2 := by
    rw [neg_div, graphFourierReadout_neg_of_even evenGraphSource_ground, ground_fourier_pole]
  have hg : massPolarImage (sourceMap (constantLift 1)) =
      (-1/2 : ℝ) • km - (1/2 : ℝ) • kp := by
    rw [massPolarImage,
      massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2),
      massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2),
      ground_fourier_pole, hgm]
    norm_num [kp, km]
  have ho : massPolarImage (sourceMap oddPolarVector) =
      (1/2 : ℝ) • km - (1/2 : ℝ) • kp := by
    rw [massPolarImage,
      massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2),
      massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2),
      oddPolarVector_fourier_plus_pole, oddPolarVector_fourier_minus_pole]
    norm_num [kp, km]
  have hp : -(massPolarImage (sourceMap (constantLift 1)) +
      massPolarImage (sourceMap oddPolarVector)) = kp := by rw [hg, ho]; module
  have hm : massPolarImage (sourceMap oddPolarVector) -
      massPolarImage (sourceMap (constantLift 1)) = km := by rw [hg, ho]; module
  constructor
  · change kp ∈ finiteSampleImageSpace
    rw [← hp]
    exact finiteSampleImageSpace.neg_mem (finiteSampleImageSpace.add_mem hground hodd)
  · change km ∈ finiteSampleImageSpace
    rw [← hm]
    exact finiteSampleImageSpace.sub_mem hodd hground

theorem massSampleImagKernel_eq_zero_of_re_zero (a : MassSamplePoint) (ha : a.val.re = 0) :
    massSampleImagKernel a = 0 := by
  have he : ⟪massSampleImagKernel a, massSampleImagKernel a⟫_ℝ = 0 := by
    rw [← massSample_im_eq_inner]
    exact massFourierReadout_real_of_re_zero _ ha
  exact inner_self_eq_zero.mp he

theorem massSampleKernels_mem_finiteSampleImageSpace (a : MassSamplePoint) :
    massSampleRealKernel a ∈ finiteSampleImageSpace ∧
    massSampleImagKernel a ∈ finiteSampleImageSpace := by
  rcases a with ⟨z, hz⟩
  rcases hz with hz | hp | hm
  · exact zero_sample_kernels_mem_finiteSampleImageSpace hz
  · subst z
    refine ⟨polar_real_kernels_mem_finiteSampleImageSpace.1, ?_⟩
    rw [massSampleImagKernel_eq_zero_of_re_zero _ (by norm_num)]
    exact finiteSampleImageSpace.zero_mem
  · subst z
    refine ⟨polar_real_kernels_mem_finiteSampleImageSpace.2, ?_⟩
    rw [massSampleImagKernel_eq_zero_of_re_zero _ (by norm_num)]
    exact finiteSampleImageSpace.zero_mem

/-- Exact algebraic surjectivity, with actual finite-sample source preimages. -/
theorem finiteSampleImageSpace_eq_samplingSpan : finiteSampleImageSpace = massSamplingSpan := by
  apply le_antisymm finiteSampleImageSpace_le_samplingSpan
  apply Submodule.span_le.mpr
  rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact (massSampleKernels_mem_finiteSampleImageSpace a).1
  · exact (massSampleKernels_mem_finiteSampleImageSpace a).2

theorem FiniteMassSampleSupport.reduced {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hw : FiniteMassSampleSupport S w) :
    FiniteMassSampleSupport S (massReducedSource w) := by
  intro ρ hρ
  constructor
  · exact (massReducedSource_samples w (zeroMassSamplePoint ρ)).trans (hw ρ hρ).1
  · exact (massReducedSource_samples w (negMassSamplePoint (zeroMassSamplePoint ρ))).trans (hw ρ hρ).2

theorem reduced_resolvent_preimage {w b : MassSpace}
    (hw : resolvent ((2 : ℝ) • w + b) = w) :
    resolvent ((2 : ℝ) • massReducedSource w + b) = massReducedSource w := by
  have hc := (mem_massCriticalSpace _).mp (massCriticalProjection_mem w)
  change resolvent ((2 : ℝ) • (w-massCriticalProjection w) + b) = w-massCriticalProjection w
  calc
    _ = resolvent (((2 : ℝ) • w + b) - (2 : ℝ) • massCriticalProjection w) :=
      congrArg resolvent (by module)
    _ = _ := by rw [map_sub, hw, map_smul, hc, smul_smul]; norm_num

theorem critical_difference_of_resolvent_preimages {u v b : MassSpace}
    (hru : resolvent ((2 : ℝ) • u + b) = u)
    (hrv : resolvent ((2 : ℝ) • v + b) = v) : u-v ∈ massCriticalSpace := by
  have hd : resolvent ((2 : ℝ) • (u-v)) = u-v := by
    calc
      _ = resolvent (((2 : ℝ) • u + b) - ((2 : ℝ) • v + b)) :=
        congrArg resolvent (by module)
      _ = _ := by rw [map_sub, hru, hrv]
  have he : resolvent (u-v) = (1/2 : ℝ) • (u-v) := by
    have h := congrArg (fun x : MassSpace => (1/2 : ℝ) • x) hd
    rw [map_smul, smul_smul] at h
    norm_num at h
    simpa only [map_sub] using h
  exact (mem_massCriticalSpace _).mpr he

theorem samples_eq_of_resolvent_preimages {u v b : MassSpace}
    (hru : resolvent ((2 : ℝ) • u + b) = u)
    (hrv : resolvent ((2 : ℝ) • v + b) = v) (a : MassSamplePoint) :
    massFourierReadout u a = massFourierReadout v a := by
  have hc := critical_difference_of_resolvent_preimages hru hrv
  have hs := mass_silent_of_resolvent_half ((mem_massCriticalSpace _).mp hc)
  have h := (mass_silent_iff_all_samples _).mp hs a
  rw [← massFourierReadoutCLM_apply _ (massSamplePoint_strip a), map_sub,
    massFourierReadoutCLM_apply, massFourierReadoutCLM_apply] at h
  exact sub_eq_zero.mp h

theorem reduced_resolvent_preimage_unique {u v b : MassSpace}
    (hu : u ∈ massCriticalSpaceᗮ) (hv : v ∈ massCriticalSpaceᗮ)
    (hru : resolvent ((2 : ℝ) • u + b) = u)
    (hrv : resolvent ((2 : ℝ) • v + b) = v) : u = v := by
  have hc := critical_difference_of_resolvent_preimages hru hrv
  have ho : u-v ∈ massCriticalSpaceᗮ := massCriticalSpaceᗮ.sub_mem hu hv
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hc ho))

/-- Every algebraic sampling vector has one reduced finite-sample mass preimage. -/
theorem exists_unique_reduced_finite_sample_preimage (b : MassSpace) (hb : b ∈ massSamplingSpan) :
    ∃! w : MassSpace, w ∈ massCriticalSpaceᗮ ∧
      (∃ S : Finset zetaZeroConfig.carrier, FiniteMassSampleSupport S w) ∧
      resolvent ((2 : ℝ) • w + b) = w := by
  rw [← finiteSampleImageSpace_eq_samplingSpan] at hb
  obtain ⟨S, w, hw, hr⟩ := hb
  refine ⟨massReducedSource w, ⟨massReducedSource_mem w, ⟨S, hw.reduced⟩,
    reduced_resolvent_preimage hr⟩, ?_⟩
  intro v hv
  exact reduced_resolvent_preimage_unique hv.1 (massReducedSource_mem w) hv.2.2
    (reduced_resolvent_preimage hr)

/-- The exact inverse is an element of the actual maximal operator domain.
The only removed ambiguity is the complete critical eigenspace. -/
theorem exists_unique_reduced_finite_sample_generator_inverse (b : MassSpace)
    (hb : b ∈ massSamplingSpan) :
    ∃! u : arithmeticGenerator.domain, (u : MassSpace) ∈ massCriticalSpaceᗮ ∧
      (∃ S : Finset zetaZeroConfig.carrier, FiniteMassSampleSupport S u) ∧
      arithmeticGenerator u - (u : MassSpace) = b := by
  obtain ⟨w, ⟨hw, hs, hr⟩, huniq⟩ := exists_unique_reduced_finite_sample_preimage b hb
  refine ⟨⟨w, mem_arithmetic_domain_of_resolvent_preimage hr⟩, ⟨hw, hs, ?_⟩, ?_⟩
  · rw [arithmeticGenerator_of_resolvent_preimage hr]
    abel
  · intro u hu
    apply Subtype.ext
    apply huniq
    refine ⟨hu.1, hu.2.1, ?_⟩
    have he : arithmeticGenerator u = (u : MassSpace) + b := by
      calc
        _ = (u : MassSpace) + (arithmeticGenerator u - (u : MassSpace)) := by abel
        _ = _ := by rw [hu.2.2]
    have h := arithmeticGenerator_identity u
    rw [he] at h
    simpa only [two_smul, add_assoc] using h

theorem finite_samples_of_sampling_forcing {w b : MassSpace}
    (hb : b ∈ massSamplingSpan) (hw : resolvent ((2 : ℝ) • w + b) = w) :
    ∃ S : Finset zetaZeroConfig.carrier, FiniteMassSampleSupport S w := by
  obtain ⟨v, ⟨_, ⟨S, hS⟩, hv⟩, _⟩ := exists_unique_reduced_finite_sample_preimage b hb
  refine ⟨S, fun ρ hρ => ⟨?_, ?_⟩⟩
  · exact (samples_eq_of_resolvent_preimages hw hv (zeroMassSamplePoint ρ)).trans (hS ρ hρ).1
  · exact (samples_eq_of_resolvent_preimages hw hv
      (negMassSamplePoint (zeroMassSamplePoint ρ))).trans (hS ρ hρ).2

/-- Within the actual maximal domain, an algebraic sampling image is
equivalent to finite sample support of the source. -/
theorem finite_sample_generator_image_iff (u : arithmeticGenerator.domain) :
    arithmeticGenerator u - (u : MassSpace) ∈ massSamplingSpan ↔
      ∃ S : Finset zetaZeroConfig.carrier, FiniteMassSampleSupport S u := by
  constructor
  · intro hb
    apply finite_samples_of_sampling_forcing hb
    calc
      _ = resolvent ((u : MassSpace) + arithmeticGenerator u) :=
        congrArg resolvent (by module)
      _ = _ := arithmeticGenerator_identity u
  · rintro ⟨S, hS⟩
    have he : arithmeticGenerator u = (u : MassSpace) + massFiniteImage S u :=
      arithmeticGenerator_finite_samples hS
    rw [he, add_sub_cancel_left]
    exact massFiniteImage_mem_samplingSpan S u

/-- The signed arithmetic generator has an exact reduced inverse on the
algebraic sampling span, unique among all maximal-domain vectors. -/
theorem exists_unique_reduced_generator_inverse (b : MassSpace) (hb : b ∈ massSamplingSpan) :
    ∃! u : arithmeticGenerator.domain, (u : MassSpace) ∈ massCriticalSpaceᗮ ∧
      arithmeticGenerator u - (u : MassSpace) = b := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_reduced_finite_sample_generator_inverse b hb
  refine ⟨u, ⟨hu.1, hu.2.2⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, ?_, hv.2⟩
  apply (finite_sample_generator_image_iff v).mp
  rw [hv.2]
  exact hb

end RHTower.CHMDDoobGraph
