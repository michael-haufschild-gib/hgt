import GaloisForLFunctions.RHTower.CHMDMassFourierReadout
import GaloisForLFunctions.RHTower.CHMDGraphMixedExplicitFormula
import GaloisForLFunctions.RHTower.CHMDGeneratorWeilOperator
import GaloisForLFunctions.RHTower.CHMDStationaryOperatorDomain

/-!
# Mixed explicit formula without an energy-domain premise

For a compact C2 test, the mixed zero series converges in the dual of the full
mass space. Its value is the mass pairing against the actual signed generator
image. Thus a mass vector with zero divisor and polar samples solves the
critical generator equation weakly on every compact C2 test.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def massMixedZeroOperator (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) : MassSpace →L[ℝ] ℂ :=
  ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)) •
      massFourierReadoutCLM (gammaOf ρ) (gammaOf_mem_closedStrip ρ) +
    ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)) •
      massFourierReadoutCLM (-gammaOf ρ) (neg_gammaOf_mem_closedStrip ρ)

theorem norm_smul_massFourierReadoutCLM_le (c : ℂ) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    ‖c • massFourierReadoutCLM z hz‖ ≤ ‖c‖ * massStripReadoutBound :=
  (ContinuousLinearMap.opNorm_smul_le c _).trans
    (mul_le_mul_of_nonneg_left (norm_massFourierReadoutCLM_le hz) (norm_nonneg c))

theorem norm_massMixedZeroOperator_le (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖massMixedZeroOperator f ρ‖ ≤
      (‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)‖ +
       ‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)‖) *
        massStripReadoutBound := by
  unfold massMixedZeroOperator
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_smul_massFourierReadoutCLM_le _ (gammaOf_mem_closedStrip ρ))
    (norm_smul_massFourierReadoutCLM_le _ (neg_gammaOf_mem_closedStrip ρ))).trans_eq
      (add_mul _ _ _).symm)

theorem summable_massMixedZeroOperator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : Summable (massMixedZeroOperator f) := by
  have hp := (summable_compactFourierCoeffs hf hc).norm
  have hn := (summable_compactFourierCoeffs_neg hf hc).norm
  exact Summable.of_norm_bounded (E := MassSpace →L[ℝ] ℂ)
    ((hn.add hp).mul_right massStripReadoutBound) (norm_massMixedZeroOperator_le f)

theorem massMixedZeroOperator_source (p : SourceGraph) (f : ℝ → ℝ)
    (ρ : zetaZeroConfig.carrier) :
    massMixedZeroOperator f ρ (sourceMap p) = mixedZeroOperator f ρ p := rfl

theorem tsum_massMixedZeroOperator_source (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∑' ρ, massMixedZeroOperator f ρ) (sourceMap p) = ∑' ρ, graphMixedZeroTerm p f ρ := by
  simpa only [ContinuousLinearMap.apply_apply, massMixedZeroOperator_source,
    mixedZeroOperator_apply] using
    (ContinuousLinearMap.apply ℝ ℂ (sourceMap p)).map_tsum (summable_massMixedZeroOperator hf hc)

def massMixedFunctional (f : ℝ → ℝ) : MassSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp ((1/2 : ℂ) • (∑' ρ, massMixedZeroOperator f ρ) -
    paperFT (fun x => (f x : ℂ)) (-I/2) • massFourierReadoutCLM (I/2) (by norm_num) -
    paperFT (fun x => (f x : ℂ)) (I/2) • massFourierReadoutCLM (-I/2) (by norm_num))

theorem massMixedFunctional_source (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    massMixedFunctional f (sourceMap p) = mixedGraphFunctional f p := by
  rw [mixedGraphFunctional_eq p hf hc]
  simp only [massMixedFunctional, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, Complex.reCLM_apply, smul_eq_mul, massFourierReadoutCLM_apply,
    massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2),
    massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2),
    tsum_massMixedZeroOperator_source p hf hc]
  congr 1
  ring

/-- The mixed divisor expression equals the actual signed generator pairing
on every mass vector, including vectors outside the energy domain. -/
theorem massMixedFunctional_eq_genImage {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) (w : MassSpace) :
    massMixedFunctional (phiDoobTest v) w = ⟪genImageL v hv hc, w⟫_ℝ := by
  have hd : Dense (Set.range sourceMap) := dense_sourceMap_range
  have he : (fun w => massMixedFunctional (phiDoobTest v) w) =
      (fun w => ⟪genImageL v hv hc, w⟫_ℝ) := by
    apply Continuous.ext_on hd (massMixedFunctional _).continuous
      (continuous_const.inner continuous_id)
    rintro _ ⟨p, rfl⟩
    rw [massMixedFunctional_source p (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc),
      ← sourcePair_testLift_eq_mixed p (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc),
      testLift_phi v hv hc, sourcePair_symm, sourcePair_compactLift hv hc p]
    rfl
  exact congrFun he w

theorem massMixedZeroOperator_eq_zero_of_samples {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0)
    (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) : massMixedZeroOperator f ρ w = 0 := by
  have hρ := CHMDStage16.XiC_gammaOf_eq_zero ρ
  have hn : XiC (-gammaOf ρ) = 0 := by rw [XiC_even, hρ]
  simp only [massMixedZeroOperator, add_apply, smul_apply, smul_eq_mul,
    massFourierReadoutCLM_apply, hz _ hρ, hz _ hn, mul_zero, add_zero]

theorem massMixedFunctional_eq_zero_of_samples {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0)
    (hp : massFourierReadout w (I/2) = 0) (hm : massFourierReadout w (-I/2) = 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    massMixedFunctional f w = 0 := by
  have hs := (ContinuousLinearMap.apply ℝ ℂ w).map_tsum (summable_massMixedZeroOperator hf hc)
  simp only [ContinuousLinearMap.apply_apply, massMixedZeroOperator_eq_zero_of_samples hz,
    tsum_zero] at hs
  simp only [massMixedFunctional, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, Complex.reCLM_apply, smul_eq_mul, massFourierReadoutCLM_apply, hs, hp, hm,
    mul_zero, sub_zero, Complex.zero_re]

theorem inner_genImage_eq_zero_of_samples {w : MassSpace}
    (hz : ∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0)
    (hp : massFourierReadout w (I/2) = 0) (hm : massFourierReadout w (-I/2) = 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ⟪genImageL v hv hc, w⟫_ℝ = 0 := by
  rw [← massMixedFunctional_eq_genImage hv hc]
  exact massMixedFunctional_eq_zero_of_samples hz hp hm
    (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc)

end RHTower.CHMDDoobGraph
