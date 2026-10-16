import GaloisForLFunctions.RHTower.CHMDMassSpectralAdmission

/-!
# Complete mass-space sampling after removing the critical band

The closed span of the literal real and imaginary Fourier kernels at Xi zeros
and the two polar points is exactly the mass-orthogonal complement of the
critical eigenspace. Every mass vector has a canonical reduced representative
with the same samples, and those samples determine that representative uniquely.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def massCriticalSpace : Submodule ℝ MassSpace :=
  Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) (1/2)

theorem mem_massCriticalSpace (w : MassSpace) :
    w ∈ massCriticalSpace ↔ resolvent w = (1/2 : ℝ) • w :=
  Module.End.mem_eigenspace_iff

theorem massCriticalSpace_eq_silent :
    (massCriticalSpace : Set MassSpace) = {w | MassSpectrallySilent w} := by
  ext w
  exact (mem_massCriticalSpace w).trans (mass_silent_iff_resolvent_half w).symm

theorem isClosed_massCriticalSpace : IsClosed (massCriticalSpace : Set MassSpace) := by
  have he : (massCriticalSpace : Set MassSpace) =
      {w | resolvent w = (1/2 : ℝ) • w} := by
    ext w
    exact mem_massCriticalSpace w
  rw [he]
  exact isClosed_eq resolvent.continuous (continuous_id.const_smul (1/2 : ℝ))

instance complete_massCriticalSpace : CompleteSpace massCriticalSpace :=
  isClosed_massCriticalSpace.completeSpace_coe

abbrev MassSamplePoint := {z : ℂ // XiC z = 0 ∨ z = I/2 ∨ z = -I/2}

theorem massSamplePoint_strip (a : MassSamplePoint) : |(a : ℂ).im| ≤ 1/2 := by
  rcases a.property with hz | hp | hm
  · exact (abs_im_lt_half_of_XiC_eq_zero hz).le
  · rw [hp]
    norm_num
  · rw [hm]
    norm_num

def massSampleRealKernel (a : MassSamplePoint) : MassSpace :=
  (fourierKernel_memLp (massSamplePoint_strip a)).re.toLp (fun x => (fourierKernel a x).re)

def massSampleImagKernel (a : MassSamplePoint) : MassSpace :=
  (fourierKernel_memLp (massSamplePoint_strip a)).im.toLp (fun x => (fourierKernel a x).im)

theorem massSample_eq_inner (w : MassSpace) (a : MassSamplePoint) :
    massFourierReadout w a = (⟪massSampleRealKernel a, w⟫_ℝ : ℂ) +
      I * (⟪massSampleImagKernel a, w⟫_ℝ : ℂ) := by
  rw [← massFourierReadoutCLM_apply w (massSamplePoint_strip a)]
  rfl

def massSamplingSpan : Submodule ℝ MassSpace :=
  Submodule.span ℝ (Set.range massSampleRealKernel ∪ Set.range massSampleImagKernel)

theorem mass_silent_iff_all_samples (w : MassSpace) :
    MassSpectrallySilent w ↔ ∀ a : MassSamplePoint, massFourierReadout w a = 0 := by
  constructor
  · intro hw a
    rcases a.property with hz | hp | hm
    · exact hw.1 a hz
    · simpa only [hp] using hw.2.1
    · simpa only [hm] using hw.2.2
  · intro h
    exact ⟨fun z hz => h ⟨z, Or.inl hz⟩,
      h ⟨I/2, Or.inr (Or.inl rfl)⟩, h ⟨-I/2, Or.inr (Or.inr rfl)⟩⟩

theorem mem_massSamplingSpan_orthogonal (w : MassSpace) :
    w ∈ massSamplingSpanᗮ ↔ ∀ a : MassSamplePoint, massFourierReadout w a = 0 := by
  constructor
  · intro hw a
    have hr := hw (massSampleRealKernel a) (Submodule.subset_span (Or.inl ⟨a, rfl⟩))
    have hi := hw (massSampleImagKernel a) (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
    rw [massSample_eq_inner, hr, hi]
    simp
  · intro h
    have hk : massSamplingSpan ≤ (innerSL ℝ w).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · have he := h a
        rw [massSample_eq_inner] at he
        change ⟪w, massSampleRealKernel a⟫_ℝ = 0
        rw [real_inner_comm]
        simpa using congrArg Complex.re he
      · have he := h a
        rw [massSample_eq_inner] at he
        change ⟪w, massSampleImagKernel a⟫_ℝ = 0
        rw [real_inner_comm]
        simpa using congrArg Complex.im he
    intro u hu
    have he : ⟪w, u⟫_ℝ = 0 := hk hu
    rwa [real_inner_comm] at he

theorem massSamplingSpan_orthogonal : massSamplingSpanᗮ = massCriticalSpace := by
  ext w
  rw [mem_massSamplingSpan_orthogonal, ← mass_silent_iff_all_samples,
    mass_silent_iff_resolvent_half, mem_massCriticalSpace]

/-- The actual sampling kernels are complete on the entire noncritical mass
space, not merely on sources already admitted to the energy graph. -/
theorem massSamplingSpan_closure :
    massSamplingSpan.topologicalClosure = massCriticalSpaceᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, massSamplingSpan_orthogonal]

def massCriticalProjection : MassSpace →L[ℝ] MassSpace := massCriticalSpace.starProjection

def massReducedSource : MassSpace →L[ℝ] MassSpace :=
  ContinuousLinearMap.id ℝ MassSpace - massCriticalProjection

theorem massCriticalProjection_mem (w : MassSpace) : massCriticalProjection w ∈ massCriticalSpace :=
  (massCriticalSpace.orthogonalProjectionOnto w).property

theorem massReducedSource_mem (w : MassSpace) : massReducedSource w ∈ massCriticalSpaceᗮ :=
  Submodule.sub_starProjection_mem_orthogonal w

theorem massCriticalProjection_silent (w : MassSpace) : MassSpectrallySilent (massCriticalProjection w) :=
  mass_silent_of_resolvent_half ((mem_massCriticalSpace _).mp (massCriticalProjection_mem w))

/-- Removing the complete critical eigenspace preserves every divisor and polar sample. -/
theorem massReducedSource_samples (w : MassSpace) (a : MassSamplePoint) :
    massFourierReadout (massReducedSource w) a = massFourierReadout w a := by
  have hz := (mass_silent_iff_all_samples _).mp (massCriticalProjection_silent w) a
  rw [← massFourierReadoutCLM_apply _ (massSamplePoint_strip a),
    ← massFourierReadoutCLM_apply _ (massSamplePoint_strip a)]
  change massFourierReadoutCLM a (massSamplePoint_strip a) (w - massCriticalProjection w) = _
  rw [map_sub, massFourierReadoutCLM_apply, massFourierReadoutCLM_apply, hz, sub_zero]

/-- Literal samples determine a reduced mass source uniquely. -/
theorem mass_samples_injective_on_reduced {u v : MassSpace}
    (hu : u ∈ massCriticalSpaceᗮ) (hv : v ∈ massCriticalSpaceᗮ)
    (hs : ∀ a : MassSamplePoint, massFourierReadout u a = massFourierReadout v a) : u = v := by
  have hsilent : MassSpectrallySilent (u-v) := by
    apply (mass_silent_iff_all_samples _).mpr
    intro a
    rw [← massFourierReadoutCLM_apply _ (massSamplePoint_strip a), map_sub,
      massFourierReadoutCLM_apply, massFourierReadoutCLM_apply, hs, sub_self]
  have hc : u-v ∈ massCriticalSpace :=
    (mem_massCriticalSpace _).mpr (resolvent_half_of_mass_silent hsilent)
  have ho : u-v ∈ massCriticalSpaceᗮ := massCriticalSpaceᗮ.sub_mem hu hv
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hc ho))

/-- Canonical, unconditional reconstruction modulo the exact critical band. -/
theorem exists_unique_reduced_mass_source (w : MassSpace) :
    ∃! v : MassSpace, v ∈ massCriticalSpaceᗮ ∧
      ∀ a : MassSamplePoint, massFourierReadout v a = massFourierReadout w a := by
  refine ⟨massReducedSource w, ⟨massReducedSource_mem w, massReducedSource_samples w⟩, ?_⟩
  intro v hv
  exact mass_samples_injective_on_reduced hv.1 (massReducedSource_mem w)
    (fun a => (hv.2 a).trans (massReducedSource_samples w a).symm)

theorem critical_lift_norm_sq {w : MassSpace} (hw : w ∈ massCriticalSpace) :
    ‖(2 : ℝ) • rieszLift w‖^2 = 2 * ‖w‖^2 := by
  have he := (mem_massCriticalSpace w).mp hw
  have hn := radical_norm_sq (critical_lift_mem_signedRadical he)
  change ‖(2 : ℝ) • rieszLift w‖^2 = 2 * ‖sourceMap ((2 : ℝ) • rieszLift w)‖^2 at hn
  rwa [critical_lift_source he] at hn

end RHTower.CHMDDoobGraph
