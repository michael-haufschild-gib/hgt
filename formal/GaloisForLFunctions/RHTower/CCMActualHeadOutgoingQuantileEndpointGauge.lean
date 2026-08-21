import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam
import GaloisForLFunctions.RHTower.CCMActualHeadCoherentCompletedGammaProducer

/-!
# Terminal endpoint gauge nullity for outgoing quantile symbols

On a physical aperture head, the spectral cosine coordinate at the diameter translation is
quadratically null. Consequently the terminal completion atom in the outgoing quantile symbol is a
gauge coordinate: it can be removed from the quadratic source without a pointwise identity or sign
claim. The final theorem rewrites the actual Gamma-wall outgoing producer with the endpoint-free
continuous-minus-prime characteristic representative.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem integrable_ccmActualHeadCosineSpectralDensity
    (s : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      Real.cos (2 * Real.pi * s * xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hsq : Integrable (fun xi : ℝ =>
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) :=
    integrable_norm_sq (fourierUnitary f)
  exact Integrable.mul_bdd (c := 1) hsq
    (by exact (by fun_prop : Continuous fun xi : ℝ =>
      Real.cos (2 * Real.pi * s * xi)).aestronglyMeasurable)
    (by
      filter_upwards with xi
      simpa [Real.norm_eq_abs] using
        Real.abs_cos_le_one (2 * Real.pi * s * xi)) |>.congr
          (Filter.Eventually.of_forall fun xi => by ring)

/-- Diameter translation is disjoint on the physical aperture, so its spectral cosine coordinate
is exactly null. -/
theorem integral_ccmActualHeadDiameterCosineSpectralDensity_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∫ xi : ℝ,
      Real.cos (2 * Real.pi * (2 * a.1) * xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  let g : SoninL2 := fourierUnitary (f : SoninL2)
  have hfg : fourierUnitary.symm g = (f : SoninL2) := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply (f : SoninL2)
  have hspectral :=
    ccmActualHeadSymmetricAutocorrelation_fourierUnitary_symm (2 * a.1) g
  rw [hfg, ccmActualHeadSymmetricAutocorrelation_two_aperture_eq_zero a f] at hspectral
  simpa only [g] using hspectral.symm

/-- Any scalar multiple of the diameter cosine is a null gauge for integrable spectral symbols on
the physical aperture space. -/
theorem integral_add_ccmActualHeadDiameterCosineGauge_eq
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (Phi : ℝ → ℝ) (c : ℝ)
    (hPhi : Integrable (fun xi : ℝ =>
      Phi xi * ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2)) :
    (∫ xi : ℝ,
      (Phi xi + c * Real.cos (2 * Real.pi * (2 * a.1) * xi)) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
      ∫ xi : ℝ,
        Phi xi * ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  have hcos := integrable_ccmActualHeadCosineSpectralDensity
    (2 * a.1) (f : SoninL2)
  have hgauge : Integrable (fun xi : ℝ =>
      c * (Real.cos (2 * Real.pi * (2 * a.1) * xi) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2)) :=
    hcos.const_mul c
  rw [show (fun xi : ℝ =>
      (Phi xi + c * Real.cos (2 * Real.pi * (2 * a.1) * xi)) *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
      fun xi : ℝ =>
        Phi xi * ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 +
          c * (Real.cos (2 * Real.pi * (2 * a.1) * xi) *
            ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) by
    funext xi
    ring,
    integral_add hPhi hgauge,
    integral_const_mul,
    integral_ccmActualHeadDiameterCosineSpectralDensity_eq_zero a f]
  ring

/-- Endpoint-free outgoing characteristic representative of the completed quantile source. -/
def ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
    (N : ℕ) (T xi : ℝ) : ℝ :=
  ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi +
    (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) *
      Real.cos (2 * Real.pi * T * xi)

theorem ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_eq_characteristicDiscrepancy
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N T xi =
      (∫ h in (0 : ℝ)..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      ∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * Real.log n * xi) := by
  unfold ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_eq_characteristicDiscrepancy]
  ring

theorem ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_zero
    (N : ℕ) (T : ℝ) :
    ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N T 0 =
      2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N) := by
  unfold ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_zero]
  simp

theorem ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_neg
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N T (-xi) =
      ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N T xi := by
  unfold ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_neg]
  rw [show 2 * Real.pi * T * -xi = -(2 * Real.pi * T * xi) by ring,
    Real.cos_neg]

theorem integrable_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_mul_density
    (N : ℕ) (T : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N T xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hcompleted :=
    integrable_ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_mul_density N T f
  have hcos := integrable_ccmActualHeadCosineSpectralDensity T f
  have hgauge := hcos.const_mul
    (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N))
  exact (hcompleted.add hgauge).congr
    (Filter.Eventually.of_forall fun xi => by
      simp only [Pi.add_apply]
      unfold ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
      ring)

/-- On the physical aperture space, completed and endpoint-free characteristic symbols define the
same quadratic form. This is gauge equivalence, not pointwise equality. -/
theorem integral_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_eq_completed
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) :
    (∫ xi : ℝ,
      ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) =
      ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi *
          ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  unfold ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol
  exact integral_add_ccmActualHeadDiameterCosineGauge_eq a f
    (ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1))
    (2 * Real.exp ((2 * a.1) / 2) - (2 + ccmOutgoingPrimeCumulative N))
    (integrable_ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_mul_density
      N (2 * a.1) (f : SoninL2))

/-- The actual outgoing producer depends only on the endpoint-free gauge representative. Terminal
completed-error mismatch has disappeared from the quadratic source, while fixed Gamma scalar and
higher-mode energy remain untouched. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_endpointFreeCosinePhaseSymbol
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        4 * ‖f‖ ^ 2 +
        2 * ∫ xi : ℝ,
          ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi *
            ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  dsimp only
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hproducer :=
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_completedCosinePhaseSymbol a u
  have hgauge :=
    integral_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_eq_completed a N f
  dsimp only at hproducer
  change ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u = _ at hproducer
  change (∫ xi : ℝ,
      ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol N (2 * a.1) xi *
        ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = _ at hgauge
  rw [← hgauge] at hproducer
  simpa only [f, N] using hproducer

end RHTower
