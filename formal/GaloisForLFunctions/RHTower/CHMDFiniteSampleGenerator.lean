import GaloisForLFunctions.RHTower.CHMDMassWeakGenerator
import GaloisForLFunctions.RHTower.CHMDMassWeightedKernels

/-!
# Exact arithmetic operator action from finite Xi samples

An arbitrary mass vector whose nonzero Xi samples are carried by a finite set
belongs to the maximal arithmetic generator domain. Its signed generator image
is a finite sum of literal Fourier kernels and the polar image. No energy or
operator-domain regularity is assumed, and all zero multiplicities are retained.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def FiniteMassSampleSupport (S : Finset zetaZeroConfig.carrier) (w : MassSpace) : Prop :=
  ∀ ρ ∉ S, massFourierReadout w (gammaOf ρ) = 0 ∧ massFourierReadout w (-gammaOf ρ) = 0

def massZeroImage (w : MassSpace) (ρ : zetaZeroConfig.carrier) : MassSpace :=
  massWeightedRealKernel (((zetaZeroConfig.mult ρ : ℂ)/2) * massFourierReadout w (gammaOf ρ))
      (negMassSamplePoint (zeroMassSamplePoint ρ)) +
    massWeightedRealKernel (((zetaZeroConfig.mult ρ : ℂ)/2) * massFourierReadout w (-gammaOf ρ))
      (zeroMassSamplePoint ρ)

theorem massZeroImage_pair_mass (w v : MassSpace) (ρ : zetaZeroConfig.carrier) :
    ⟪massZeroImage w ρ, v⟫_ℝ =
      (((zetaZeroConfig.mult ρ : ℂ)/2) *
        (massFourierReadout w (gammaOf ρ) * massFourierReadout v (-gammaOf ρ) +
         massFourierReadout w (-gammaOf ρ) * massFourierReadout v (gammaOf ρ))).re := by
  rw [massZeroImage, inner_add_left, massWeightedRealKernel_pair,
    massWeightedRealKernel_pair, ← Complex.add_re]
  congr 1
  change _ * massFourierReadout v (-gammaOf ρ) +
    _ * massFourierReadout v (gammaOf ρ) = _
  ring

theorem massZeroImage_pair_test (w : MassSpace) (ρ : zetaZeroConfig.carrier)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ⟪massZeroImage w ρ, sourceMap (testLift f hf hc)⟫_ℝ =
      ((1/2 : ℂ) * massMixedZeroOperator f ρ w).re := by
  rw [massZeroImage_pair_mass,
    massFourierReadout_source _ (neg_gammaOf_mem_closedStrip ρ),
    massFourierReadout_source _ (gammaOf_mem_closedStrip ρ),
    graphFourierReadout_testLift, graphFourierReadout_testLift]
  simp only [massMixedZeroOperator, add_apply, smul_apply, smul_eq_mul,
    massFourierReadoutCLM_apply]
  congr 1
  ring

def massFiniteImage (S : Finset zetaZeroConfig.carrier) (w : MassSpace) : MassSpace :=
  (∑ ρ ∈ S, massZeroImage w ρ) + massPolarImage w

theorem massMixedZeroOperator_eq_zero_outside {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) (f : ℝ → ℝ)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∉ S) : massMixedZeroOperator f ρ w = 0 := by
  obtain ⟨hp, hn⟩ := hS ρ hρ
  simp only [massMixedZeroOperator, add_apply, smul_apply, smul_eq_mul,
    massFourierReadoutCLM_apply, hp, hn, mul_zero, add_zero]

/-- The infinite mixed series reduces exactly to the finite literal mass image. -/
theorem massMixedFunctional_finite_samples {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    massMixedFunctional f w = ⟪massFiniteImage S w, sourceMap (testLift f hf hc)⟫_ℝ := by
  have hs : (∑' ρ, massMixedZeroOperator f ρ) w =
      ∑ ρ ∈ S, massMixedZeroOperator f ρ w := by
    calc
      _ = ∑' ρ, massMixedZeroOperator f ρ w := by
        simpa only [ContinuousLinearMap.apply_apply] using
          (ContinuousLinearMap.apply ℝ ℂ w).map_tsum (summable_massMixedZeroOperator hf hc)
      _ = _ := tsum_eq_sum (fun ρ hρ => massMixedZeroOperator_eq_zero_outside hS f hρ)
  have hre : ((1/2 : ℂ) * (∑ ρ ∈ S, massMixedZeroOperator f ρ w)).re =
      ∑ ρ ∈ S, ((1/2 : ℂ) * massMixedZeroOperator f ρ w).re := by
    rw [Finset.mul_sum]
    exact map_sum Complex.reCLM _ _
  have hp := massFourierReadout_real_of_re_zero w (z := I/2) (by norm_num)
  have hm := massFourierReadout_real_of_re_zero w (z := -I/2) (by norm_num)
  rw [massFiniteImage, inner_add_left, sum_inner, massPolarImage_pair]
  simp_rw [massZeroImage_pair_test w _ hf hc, graphFourierReadout_testLift]
  simp only [massMixedFunctional, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, Complex.reCLM_apply, smul_eq_mul, massFourierReadoutCLM_apply, hs,
    Complex.sub_re, hre, Complex.mul_re, hp, hm, mul_zero, sub_zero]
  ring

theorem finite_samples_compact_pair {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ⟪genImageL v hv hc, w⟫_ℝ = ⟪massFiniteImage S w, sourceMap (compactLift v hv hc)⟫_ℝ := by
  rw [← massMixedFunctional_eq_genImage hv hc,
    massMixedFunctional_finite_samples hS (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc),
    testLift_phi v hv hc]

/-- Explicit arithmetic resolvent inversion for every finite-sample mass vector. -/
theorem finite_samples_resolvent_identity {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) :
    resolvent ((2 : ℝ) • w + massFiniteImage S w) = w :=
  resolvent_preimage_of_compact_pair (finite_samples_compact_pair hS)

theorem finite_samples_mem_arithmetic_domain {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) : w ∈ arithmeticGenerator.domain :=
  mem_arithmetic_domain_of_resolvent_preimage (finite_samples_resolvent_identity hS)

theorem arithmeticGenerator_finite_samples {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) :
    arithmeticGenerator ⟨w, finite_samples_mem_arithmetic_domain hS⟩ = w + massFiniteImage S w :=
  arithmeticGenerator_of_resolvent_preimage (finite_samples_resolvent_identity hS)

def finiteSampleGraphLift (S : Finset zetaZeroConfig.carrier) (w : MassSpace) : SourceGraph :=
  rieszLift ((2 : ℝ) • w + massFiniteImage S w)

theorem finiteSampleGraphLift_source {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) :
    sourceMap (finiteSampleGraphLift S w) = w := finite_samples_resolvent_identity hS

theorem finiteSampleGraphLift_pair {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) (q : SourceGraph) :
    sourcePair (finiteSampleGraphLift S w) q = ⟪massFiniteImage S w, sourceMap q⟫_ℝ :=
  sourcePair_rieszLift_of_resolvent_preimage (finite_samples_resolvent_identity hS) q

theorem finiteSampleGraphLift_energy {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) :
    sourceEnergy (finiteSampleGraphLift S w) = ⟪massFiniteImage S w, w⟫_ℝ :=
  sourceEnergy_rieszLift_of_resolvent_preimage (finite_samples_resolvent_identity hS)

/-- The full arithmetic energy is the finite signed divisor sum with the
literal polar product. Multiplicities are unchanged. -/
theorem finiteSampleGraphLift_energy_eq_divisor {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) :
    sourceEnergy (finiteSampleGraphLift S w) =
      (∑ ρ ∈ S, ((zetaZeroConfig.mult ρ : ℂ) * massFourierReadout w (gammaOf ρ) *
        massFourierReadout w (-gammaOf ρ)).re) -
      2 * (massFourierReadout w (I/2)).re * (massFourierReadout w (-I/2)).re := by
  have ht : ∀ ρ : zetaZeroConfig.carrier, ⟪massZeroImage w ρ, w⟫_ℝ =
      ((zetaZeroConfig.mult ρ : ℂ) * massFourierReadout w (gammaOf ρ) *
        massFourierReadout w (-gammaOf ρ)).re := by
    intro ρ
    rw [massZeroImage_pair_mass]
    congr 1
    ring
  rw [finiteSampleGraphLift_energy hS, massFiniteImage, inner_add_left, sum_inner,
    massPolarImage_pair_mass]
  simp_rw [ht]
  ring

theorem massFiniteImage_independent_support {S T : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) (hT : FiniteMassSampleSupport T w) :
    massFiniteImage S w = massFiniteImage T w :=
  add_left_cancel (resolvent_injective
    ((finite_samples_resolvent_identity hS).trans (finite_samples_resolvent_identity hT).symm))

theorem finiteSampleGraphLift_unique {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hS : FiniteMassSampleSupport S w) {p : SourceGraph}
    (hp : sourceMap p = w) : p = finiteSampleGraphLift S w :=
  source_projection_injective (hp.trans (finiteSampleGraphLift_source hS).symm)

end RHTower.CHMDDoobGraph
