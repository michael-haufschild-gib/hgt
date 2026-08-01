import GaloisForLFunctions.RHTower.CCMFirstClockSourcePhasedExteriorCurrent

/-!
# Source-phase coherence dissipation

The source-phased exterior current is not only positive before phase wrap.  It is exactly the
negative derivative of the coherent packet intensity.  Its initial derivative is the weighted
pairwise height variance.

For a finite packet with amplitudes `Aᵢ`, heights `hᵢ`, and phase
`uᵢ(τ) = exp(i τ hᵢ)`, put

`I(τ) = |∑ᵢ Aᵢ uᵢ(τ)|²`.

Then

`-I'(τ) = ∑ᵢⱼ Aᵢ Aⱼ (hᵢ-hⱼ) sin(τ(hᵢ-hⱼ))`.

This identifies the source-defined positive Julia--Gamma current with an exact coherence-loss
rate.  At the unphased point its first nonzero response is the weighted pairwise height variance.
-/

open Set Finset
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Coherent source amplitude of a finite phased height packet. -/
def sourceHeightCoherentAmplitude
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (τ : ℝ) : ℂ :=
  ∑ i ∈ packet, (amplitude i : ℂ) * sourceHeightPhase τ height i

/-- Real cosine expansion of coherent source intensity. -/
def sourceHeightCoherentIntensity
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑ i ∈ packet, ∑ j ∈ packet,
    amplitude i * amplitude j *
      Real.cos (τ * (height i - height j))

/-- Weighted ordered pairwise height variance of a finite packet. -/
def sourceHeightPairwiseVariance
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) : ℝ :=
  ∑ i ∈ packet, ∑ j ∈ packet,
    amplitude i * amplitude j * (height i - height j) ^ 2

/-- The cosine double sum is literally the squared norm of the coherent source amplitude. -/
theorem sourceHeightCoherentIntensity_eq_norm_sq
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (τ : ℝ) :
    sourceHeightCoherentIntensity packet amplitude height τ =
      ‖sourceHeightCoherentAmplitude packet amplitude height τ‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  unfold sourceHeightCoherentAmplitude sourceHeightCoherentIntensity
  rw [Complex.re_sum, Complex.im_sum]
  simp only [sourceHeightPhase, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one,
    zero_add, one_mul]
  symm
  calc
    (∑ i ∈ packet, amplitude i * Real.cos (τ * height i)) ^ 2 +
        (∑ i ∈ packet, amplitude i * Real.sin (τ * height i)) ^ 2 =
      ∑ i ∈ packet, ∑ j ∈ packet,
        ((amplitude i * Real.cos (τ * height i)) *
            (amplitude j * Real.cos (τ * height j)) +
          (amplitude i * Real.sin (τ * height i)) *
            (amplitude j * Real.sin (τ * height j))) := by
      rw [pow_two, pow_two, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ i ∈ packet, ∑ j ∈ packet,
        amplitude i * amplitude j *
          Real.cos (τ * (height i - height j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [show τ * (height i - height j) =
        τ * height i - τ * height j by ring, Real.cos_sub]
      ring

/-- The phased exterior scalar current is exactly the negative derivative of coherent intensity. -/
theorem hasDerivAt_sourceHeightCoherentIntensity
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (τ : ℝ) :
    HasDerivAt
      (sourceHeightCoherentIntensity packet amplitude height)
      (-sourcePhasedExteriorScalarEnergy packet amplitude height τ) τ := by
  unfold sourceHeightCoherentIntensity sourcePhasedExteriorScalarEnergy
  have hterm : ∀ i j : ι,
      HasDerivAt
        (fun t : ℝ =>
          amplitude i * amplitude j *
            Real.cos (t * (height i - height j)))
        (-(amplitude i * amplitude j * (height i - height j) *
          Real.sin (τ * (height i - height j)))) τ := by
    intro i j
    have hinner :
        HasDerivAt (fun t : ℝ => t * (height i - height j))
          (height i - height j) τ := by
      simpa using (hasDerivAt_id τ).mul_const (height i - height j)
    have hcos :=
      (Real.hasDerivAt_cos (τ * (height i - height j))).comp τ hinner
    convert hcos.const_mul (amplitude i * amplitude j) using 1 <;> ring
  have houter := HasDerivAt.sum (u := packet) fun i hi =>
    HasDerivAt.sum (u := packet) fun j hj => hterm i j
  convert houter using 1
  simp only [Finset.sum_neg_distrib]

/-- The initial growth of the phased exterior current is the weighted pairwise height variance. -/
theorem hasDerivAt_sourcePhasedExteriorScalarEnergy_zero
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) :
    HasDerivAt
      (sourcePhasedExteriorScalarEnergy packet amplitude height)
      (sourceHeightPairwiseVariance packet amplitude height) 0 := by
  unfold sourcePhasedExteriorScalarEnergy sourceHeightPairwiseVariance
  have hterm : ∀ i j : ι,
      HasDerivAt
        (fun t : ℝ =>
          amplitude i * amplitude j * (height i - height j) *
            Real.sin (t * (height i - height j)))
        (amplitude i * amplitude j * (height i - height j) ^ 2) 0 := by
    intro i j
    have hinner :
        HasDerivAt (fun t : ℝ => t * (height i - height j))
          (height i - height j) 0 := by
      simpa using (hasDerivAt_id 0).mul_const (height i - height j)
    have hsin :=
      (Real.hasDerivAt_sin (0 * (height i - height j))).comp 0 hinner
    convert hsin.const_mul
      (amplitude i * amplitude j * (height i - height j)) using 1 <;>
      simp <;> ring
  exact HasDerivAt.sum (u := packet) fun i hi =>
    HasDerivAt.sum (u := packet) fun j hj => hterm i j

/-- The complete finite source-phase law: coherent intensity, its exact dissipation current, and
the initial weighted variance are one object. -/
theorem sourcePhaseCoherenceDissipation_law
    {ι : Type*} (packet : Finset ι) (amplitude height : ι → ℝ) (τ : ℝ) :
    sourceHeightCoherentIntensity packet amplitude height τ =
        ‖sourceHeightCoherentAmplitude packet amplitude height τ‖ ^ 2 ∧
      HasDerivAt
        (sourceHeightCoherentIntensity packet amplitude height)
        (-sourcePhasedExteriorScalarEnergy packet amplitude height τ) τ ∧
      HasDerivAt
        (sourcePhasedExteriorScalarEnergy packet amplitude height)
        (sourceHeightPairwiseVariance packet amplitude height) 0 := by
  exact ⟨sourceHeightCoherentIntensity_eq_norm_sq packet amplitude height τ,
    hasDerivAt_sourceHeightCoherentIntensity packet amplitude height τ,
    hasDerivAt_sourcePhasedExteriorScalarEnergy_zero packet amplitude height⟩

end RHTower
