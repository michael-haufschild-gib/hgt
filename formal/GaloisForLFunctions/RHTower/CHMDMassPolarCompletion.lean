import GaloisForLFunctions.RHTower.CHMDMassSamplingCompleteness

/-!
# Automatic domain admission for the entire zero-sample kernel

Vanishing Xi-zero samples alone force a mass vector into the maximal arithmetic
operator domain. The two polar moments supply an explicit rank-two signed
generator image. Subtracting the corresponding actual polar graph vector leaves
the exact critical eigenspace.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem massFourierReadout_real_of_re_zero (w : MassSpace) {z : ℂ} (hz : z.re = 0) :
    (massFourierReadout w z).im = 0 := by
  rw [massFourierReadout_eq_paperFT]
  have he : -conj z = z := by apply Complex.ext <;> simp [hz]
  have h := congrArg Complex.im (conj_paperFT_ofReal (phiDoobTest w) z)
  rw [he, Complex.conj_im] at h
  linarith

def massPolarCosine (w : MassSpace) : ℝ :=
  ((massFourierReadout w (I/2)).re + (massFourierReadout w (-I/2)).re)/2

def massPolarSine (w : MassSpace) : ℝ :=
  ((massFourierReadout w (-I/2)).re - (massFourierReadout w (I/2)).re)/2

def massPolarGraph (w : MassSpace) : SourceGraph :=
  (2*massPolarCosine w) • constantLift 1 + (2*massPolarSine w) • oddPolarVector

def massPolarRemainder (w : MassSpace) : MassSpace := w - sourceMap (massPolarGraph w)

theorem massPolarGraph_zero_samples (w : MassSpace) : massPolarGraph w ∈ fullSpectralNullspace := by
  intro z hz
  have hs := (abs_im_lt_half_of_XiC_eq_zero hz).le
  rw [massPolarGraph, graphFourierReadout_add _ _ hs,
    graphFourierReadout_smul _ _ hs, graphFourierReadout_smul _ _ hs,
    ground_mem_fullSpectralNullspace z hz, oddPolarVector_mem_fullSpectralNullspace z hz]
  simp

theorem massPolarGraph_poles (w : MassSpace) :
    graphFourierReadout (massPolarGraph w) (I/2) = massFourierReadout w (I/2) ∧
      graphFourierReadout (massPolarGraph w) (-I/2) = massFourierReadout w (-I/2) := by
  have hp := massFourierReadout_real_of_re_zero w (z := I/2) (by norm_num)
  have hm := massFourierReadout_real_of_re_zero w (z := -I/2) (by norm_num)
  have hg : graphFourierReadout (constantLift 1) (-I/2) = 1/2 := by
    rw [neg_div, graphFourierReadout_neg_of_even evenGraphSource_ground, ground_fourier_pole]
  constructor
  · rw [massPolarGraph, graphFourierReadout_add _ _ (by norm_num),
      graphFourierReadout_smul _ _ (by norm_num), graphFourierReadout_smul _ _ (by norm_num),
      ground_fourier_pole, oddPolarVector_fourier_plus_pole]
    apply Complex.ext <;> simp [massPolarCosine, massPolarSine, hp]
    ring
  · rw [massPolarGraph, graphFourierReadout_add _ _ (by norm_num),
      graphFourierReadout_smul _ _ (by norm_num), graphFourierReadout_smul _ _ (by norm_num),
      hg, oddPolarVector_fourier_minus_pole]
    apply Complex.ext <;> simp [massPolarCosine, massPolarSine, hm]
    ring

theorem massFourierReadout_sub_source (w : MassSpace) (p : SourceGraph) {z : ℂ}
    (hz : |z.im| ≤ 1/2) :
    massFourierReadout (w-sourceMap p) z = massFourierReadout w z - graphFourierReadout p z := by
  rw [← massFourierReadoutCLM_apply _ hz, map_sub,
    massFourierReadoutCLM_apply, massFourierReadoutCLM_apply, massFourierReadout_source _ hz]

theorem massPolarRemainder_silent {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    MassSpectrallySilent (massPolarRemainder w) := by
  refine ⟨fun z hzero => ?_, ?_, ?_⟩
  · rw [massPolarRemainder,
      massFourierReadout_sub_source _ _ (abs_im_lt_half_of_XiC_eq_zero hzero).le,
      hz z hzero, massPolarGraph_zero_samples w z hzero, sub_self]
  · rw [massPolarRemainder, massFourierReadout_sub_source _ _ (by norm_num),
      (massPolarGraph_poles w).1, sub_self]
  · rw [massPolarRemainder, massFourierReadout_sub_source _ _ (by norm_num),
      (massPolarGraph_poles w).2, sub_self]

/-- Every mass vector with vanishing Xi-zero samples has an actual energy-graph
source. The source is constructed from its polar component and a critical lift. -/
theorem mass_zero_samples_graph_admission {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    ∃ p : SourceGraph, sourceMap p = w ∧ p ∈ fullSpectralNullspace := by
  have hr := resolvent_half_of_mass_silent (massPolarRemainder_silent hz)
  let p := massPolarGraph w + (2 : ℝ) • rieszLift (massPolarRemainder w)
  have hs : sourceMap p = w := by
    change sourceMap (massPolarGraph w + (2 : ℝ) • rieszLift (massPolarRemainder w)) = w
    rw [map_add, critical_lift_source hr, massPolarRemainder]
    abel
  refine ⟨p, hs, fun z hzero => ?_⟩
  rw [← massFourierReadout_source p (abs_im_lt_half_of_XiC_eq_zero hzero).le, hs]
  exact hz z hzero

theorem massSample_re_eq_inner (w : MassSpace) (a : MassSamplePoint) :
    (massFourierReadout w a).re = ⟪massSampleRealKernel a, w⟫_ℝ := by
  rw [massSample_eq_inner]
  simp

def massPolarImage (w : MassSpace) : MassSpace :=
  -((massFourierReadout w (I/2)).re) • massSampleRealKernel ⟨-I/2, Or.inr (Or.inr rfl)⟩ -
    ((massFourierReadout w (-I/2)).re) • massSampleRealKernel ⟨I/2, Or.inr (Or.inl rfl)⟩

theorem massPolarImage_pair (w : MassSpace) (q : SourceGraph) :
    ⟪massPolarImage w, sourceMap q⟫_ℝ =
      -((massFourierReadout w (I/2)).re * (graphFourierReadout q (-I/2)).re +
        (massFourierReadout w (-I/2)).re * (graphFourierReadout q (I/2)).re) := by
  rw [massPolarImage, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    ← massSample_re_eq_inner, ← massSample_re_eq_inner,
    massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2),
    massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2)]
  ring

theorem zero_samples_sourcePair_eq_massPolarImage {p : SourceGraph}
    (hp : p ∈ fullSpectralNullspace) (q : SourceGraph) :
    sourcePair p q = ⟪massPolarImage (sourceMap p), sourceMap q⟫_ℝ := by
  rw [massPolarImage_pair, full_nullspace_pair_poles hp q,
    massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2),
    massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2)]

/-- The entire zero-sample kernel has a literal resolvent preimage; the defect
from the critical equation is exactly the displayed rank-two polar image. -/
theorem mass_zero_samples_resolvent_identity {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    resolvent ((2 : ℝ) • w + massPolarImage w) = w := by
  obtain ⟨p, hs, hp⟩ := mass_zero_samples_graph_admission hz
  have hr : rieszLift ((2 : ℝ) • w + massPolarImage w) = p := by
    apply rieszLift_unique
    intro q
    have h := zero_samples_sourcePair_eq_massPolarImage hp q
    rw [sourcePair_eq_graph_inner, hs] at h
    rw [inner_add_left, real_inner_smul_left]
    change ⟪p, q⟫_ℝ = 2 * ⟪w, sourceMap q⟫_ℝ + ⟪massPolarImage w, sourceMap q⟫_ℝ
    linarith
  change sourceMap (rieszLift ((2 : ℝ) • w + massPolarImage w)) = w
  rw [hr, hs]

theorem mass_zero_samples_mem_arithmetic_domain {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    w ∈ arithmeticGenerator.domain :=
  ⟨(2 : ℝ) • w + massPolarImage w, mass_zero_samples_resolvent_identity hz⟩

/-- Maximal-domain regularity and the exact generator image are consequences
of zero samples, with no prior energy or operator-domain assumption. -/
theorem arithmeticGenerator_zero_samples {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    arithmeticGenerator ⟨w, mass_zero_samples_mem_arithmetic_domain hz⟩ = w + massPolarImage w := by
  have h := resolvent_injective ((arithmeticGenerator_identity
    ⟨w, mass_zero_samples_mem_arithmetic_domain hz⟩).trans
      (mass_zero_samples_resolvent_identity hz).symm)
  rw [two_smul] at h
  exact add_left_cancel (h.trans (add_assoc _ _ _))

/-- Unique full-mass decomposition into actual polar sources and the critical band. -/
theorem mass_zero_samples_unique_polar_decomposition {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) :
    ∃! r : MassSpace, r ∈ massCriticalSpace ∧ w = sourceMap (massPolarGraph w) + r := by
  refine ⟨massPolarRemainder w,
    ⟨(mem_massCriticalSpace _).mpr (resolvent_half_of_mass_silent (massPolarRemainder_silent hz)), ?_⟩,
    ?_⟩
  · unfold massPolarRemainder
    abel
  · intro r hr
    unfold massPolarRemainder
    calc
      r = (sourceMap (massPolarGraph w) + r) - sourceMap (massPolarGraph w) := by abel
      _ = w - sourceMap (massPolarGraph w) :=
        congrArg (fun u : MassSpace => u - sourceMap (massPolarGraph w)) hr.2.symm

end RHTower.CHMDDoobGraph
