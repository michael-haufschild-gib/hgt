import GaloisForLFunctions.RHTower.CHMDGraphMixedExplicitFormula
import GaloisForLFunctions.RHTower.CHMDGraphPolarReadout
import GaloisForLFunctions.RHTower.CHMDUniversalCardinalPairing

/-!
# Exact even spectral nullspace of the original CHMD graph

An even graph source invisible at every Xi zero is a uniquely determined
multiple of the ground vector plus an element of the full signed radical.
Its polar cosine sample determines that multiple and its entire signed pairing.
All identities concern the original maximal graph, without additional source
regularity, a spectral expansion assumption, or positivity of the primitive form.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

def evenSpectralNullspace : Set SourceGraph :=
  {p | EvenGraphSource p ∧ ∀ z : ℂ, XiC z = 0 → graphCosineReadout p z = 0}

def groundResidual (p : SourceGraph) : SourceGraph :=
  p - (2 * (graphCosineReadout p (I/2)).re) • constantLift 1

theorem ground_mem_evenSpectralNullspace : constantLift 1 ∈ evenSpectralNullspace := by
  refine ⟨evenGraphSource_ground, fun z hz => ?_⟩
  rw [graphCosineReadout_ground (abs_im_lt_half_of_XiC_eq_zero hz).le, hz]

theorem graphMixedZeroTerm_eq_zero_of_even_nullspace {p : SourceGraph}
    (hp : p ∈ evenSpectralNullspace) (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) :
    graphMixedZeroTerm p f ρ = 0 := by
  have hzero : graphFourierReadout p (gammaOf ρ) = 0 :=
    (graphFourierReadout_eq_cosine_of_even hp.1 (gammaOf_mem_closedStrip ρ)).trans
      (hp.2 _ (CHMDStage16.XiC_gammaOf_eq_zero ρ))
  simp only [graphMixedZeroTerm, graphFourierReadout_neg_of_even hp.1, hzero, mul_zero, add_zero]

theorem graphFourierReadout_poles_of_even {p : SourceGraph} (hp : EvenGraphSource p) :
    graphFourierReadout p (I/2) = ((graphCosineReadout p (I/2)).re : ℂ) ∧
    graphFourierReadout p (-I/2) = ((graphCosineReadout p (I/2)).re : ℂ) := by
  have h : graphFourierReadout p (I/2) = ((graphCosineReadout p (I/2)).re : ℂ) := by
    rw [graphFourierReadout_eq_cosine_of_even hp (by norm_num)]
    apply Complex.ext <;> simp [graphCosineReadout_pole_im]
  refine ⟨h, ?_⟩
  rw [neg_div, graphFourierReadout_neg_of_even hp, h]

theorem even_nullspace_pair_compact {p : SourceGraph} (hp : p ∈ evenSpectralNullspace)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair p (testLift f hf hc) =
      -2 * (graphCosineReadout p (I/2)).re * (graphCosineReadout (testLift f hf hc) (I/2)).re := by
  rw [sourcePair_testLift_eq_mixed p hf hc, mixedGraphFunctional_eq p hf hc]
  simp_rw [graphMixedZeroTerm_eq_zero_of_even_nullspace hp f]
  obtain ⟨hpole, hmole⟩ := graphFourierReadout_poles_of_even hp.1
  rw [hpole, hmole, graphCosineReadout_eq_half_fourier (testLift f hf hc)
    (by norm_num : |(I/2 : ℂ).im| ≤ 1/2)]
  simp only [graphFourierReadout_testLift, neg_div, tsum_zero, zero_div,
    Complex.sub_re, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.add_re]
  ring

/-- Every pairing of an even zero-silent source is determined by one polar scalar. -/
theorem even_nullspace_pair {p : SourceGraph} (hp : p ∈ evenSpectralNullspace) (q : SourceGraph) :
    sourcePair p q = -2 * (graphCosineReadout p (I/2)).re * (graphCosineReadout q (I/2)).re := by
  have he : (fun q => sourcePair p q) =
      (fun q => -2 * (graphCosineReadout p (I/2)).re * (graphCosineReadout q (I/2)).re) := by
    apply Continuous.ext_on dense_compactTests
      (continuous_sourcePair.comp (continuous_const.prodMk continuous_id))
      (continuous_const.mul (Complex.continuous_re.comp (continuous_graphCosineReadout (I/2))))
    rintro q ⟨v, hv, hc, rfl⟩
    rw [← testLift_phi v hv hc]
    exact even_nullspace_pair_compact hp (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc)
  exact congrFun he q

/-- Subtracting the forced ground component lands in the full signed radical. -/
theorem groundResidual_mem_signedRadical {p : SourceGraph} (hp : p ∈ evenSpectralNullspace) :
    groundResidual p ∈ signedRadical := by
  intro q
  rw [groundResidual, sourcePair_sub_left, sourcePair_smul_left,
    even_nullspace_pair hp q, sourcePair_ground_eq_graphCosine]
  ring

theorem even_nullspace_energy {p : SourceGraph} (hp : p ∈ evenSpectralNullspace) :
    sourceEnergy p = -2 * (graphCosineReadout p (I/2)).re ^ 2 := by
  rw [← sourcePair_self, even_nullspace_pair hp p]
  ring

theorem radical_graphCosineReadout_pole_zero {p : SourceGraph} (hp : p ∈ signedRadical) :
    graphCosineReadout p (I/2) = 0 := by
  have h : sourcePair p (constantLift 1) = 0 := hp _
  rw [sourcePair_symm, sourcePair_ground_eq_graphCosine, neg_eq_zero] at h
  apply Complex.ext <;> simp [h, graphCosineReadout_pole_im]

theorem even_radical_iff_samples_zero {p : SourceGraph} (hp : EvenGraphSource p) :
    p ∈ signedRadical ↔ (∀ z : ℂ, XiC z = 0 → graphCosineReadout p z = 0) ∧
      graphCosineReadout p (I/2) = 0 := by
  constructor
  · intro hr
    exact ⟨fun _ hz => radical_graphCosineReadout_zero hr hz, radical_graphCosineReadout_pole_zero hr⟩
  · rintro ⟨hz, hc⟩
    have h := groundResidual_mem_signedRadical ⟨hp, hz⟩
    simpa only [groundResidual, hc, Complex.zero_re, mul_zero, zero_smul, sub_zero] using h

theorem ground_coefficient_eq_of_residual_radical {p : SourceGraph} {c : ℝ}
    (hr : p - c • constantLift 1 ∈ signedRadical) :
    c = 2 * (graphCosineReadout p (I/2)).re := by
  have h : sourcePair (p - c • constantLift 1) (constantLift 1) = 0 := hr _
  rw [sourcePair_sub_left, sourcePair_smul_left, sourcePair_self,
    constantLift_energy, sourcePair_symm p (constantLift 1), sourcePair_ground_eq_graphCosine] at h
  norm_num at h
  linarith

theorem even_nullspace_unique_ground_coefficient {p : SourceGraph} (hp : p ∈ evenSpectralNullspace) :
    ∃! c : ℝ, p - c • constantLift 1 ∈ signedRadical := by
  exact ⟨2 * (graphCosineReadout p (I/2)).re, groundResidual_mem_signedRadical hp,
    fun _ hc => ground_coefficient_eq_of_residual_radical hc⟩

/-- Exact set classification; there is no unaccounted even spectral component. -/
theorem evenSpectralNullspace_eq_ground_add_radical :
    evenSpectralNullspace = {p | EvenGraphSource p ∧
      ∃ c : ℝ, ∃ r : SourceGraph, r ∈ signedRadical ∧ p = c • constantLift 1 + r} := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1, 2 * (graphCosineReadout p (I/2)).re, groundResidual p,
      groundResidual_mem_signedRadical hp, by unfold groundResidual; abel⟩
  · rintro ⟨he, c, r, hr, hp⟩
    refine ⟨he, fun z hz => ?_⟩
    rw [hp, graphCosineReadout_add, graphCosineReadout_smul,
      graphCosineReadout_ground (abs_im_lt_half_of_XiC_eq_zero hz).le,
      hz, radical_graphCosineReadout_zero hr hz]
    simp

/-- The even radical is precisely the joint kernel of Xi-zero and polar samples. -/
theorem even_signedRadical_eq_joint_kernel :
    {p : SourceGraph | EvenGraphSource p ∧ p ∈ signedRadical} =
      {p : SourceGraph | p ∈ evenSpectralNullspace ∧ graphCosineReadout p (I/2) = 0} := by
  ext p
  constructor
  · rintro ⟨he, hr⟩
    obtain ⟨hz, hc⟩ := (even_radical_iff_samples_zero he).mp hr
    exact ⟨⟨he, hz⟩, hc⟩
  · rintro ⟨⟨he, hz⟩, hc⟩
    exact ⟨he, (even_radical_iff_samples_zero he).mpr ⟨hz, hc⟩⟩

end RHTower.CHMDDoobGraph
