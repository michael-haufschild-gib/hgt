import GaloisForLFunctions.RHTower.CHMDStripFourierReadout
import GaloisForLFunctions.RHTower.CHMDCompactCardinalPairing

/-!
# The full mixed zero sum is a continuous graph functional

Compact-test Fourier coefficients are absolutely summable on the literal zero
carrier. Uniform strip readout bounds therefore make the mixed series converge
in operator norm, before any passage from compact tests to graph completion.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

theorem gammaOf_mem_closedStrip (ρ : zetaZeroConfig.carrier) : |(gammaOf ρ).im| ≤ 1/2 :=
  (WeilEF.abs_gammaOf_im_lt ⟨ρ.property.2.1, ρ.property.2.2⟩).le

theorem neg_gammaOf_mem_closedStrip (ρ : zetaZeroConfig.carrier) : |(-gammaOf ρ).im| ≤ 1/2 := by
  simpa only [Complex.neg_im, abs_neg] using gammaOf_mem_closedStrip ρ

theorem summable_compactFourierCoeffs {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)) := by
  have hfC : ContDiff ℝ 2 (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcC : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  simpa only [zetaZeroConfig] using WeilEF.EF_zero_sum_summable zetaSeam hfC hcC

theorem summable_compactFourierCoeffs_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)) := by
  have hn : ContDiff ℝ 2 (fun x => f (-x)) := hf.comp contDiff_neg
  have hnc : HasCompactSupport (fun x => f (-x)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
  apply (summable_compactFourierCoeffs hn hnc).congr
  intro ρ
  exact congrArg (fun w => (zetaZeroConfig.mult ρ : ℂ) * w)
    (paperFT_comp_neg (fun x => (f x : ℂ)) (gammaOf ρ))

def mixedZeroOperator (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) : SourceGraph →L[ℝ] ℂ :=
  ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)) •
      graphFourierReadoutCLM (gammaOf ρ) (gammaOf_mem_closedStrip ρ) +
    ((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)) •
      graphFourierReadoutCLM (-gammaOf ρ) (neg_gammaOf_mem_closedStrip ρ)

theorem norm_smul_graphFourierReadoutCLM_le (c : ℂ) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    ‖c • graphFourierReadoutCLM z hz‖ ≤ ‖c‖ * stripReadoutBound := by
  exact (ContinuousLinearMap.opNorm_smul_le c _).trans
    (mul_le_mul_of_nonneg_left (norm_graphFourierReadoutCLM_le hz) (norm_nonneg c))

theorem norm_mixedZeroOperator_le (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖mixedZeroOperator f ρ‖ ≤
      (‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)‖ +
       ‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)‖) * stripReadoutBound := by
  unfold mixedZeroOperator
  calc
    _ ≤ ‖((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)) •
        graphFourierReadoutCLM (gammaOf ρ) (gammaOf_mem_closedStrip ρ)‖ +
      ‖((zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)) •
        graphFourierReadoutCLM (-gammaOf ρ) (neg_gammaOf_mem_closedStrip ρ)‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ)‖ * stripReadoutBound +
      ‖(zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ)‖ * stripReadoutBound := by
      exact add_le_add
        (norm_smul_graphFourierReadoutCLM_le _ (gammaOf_mem_closedStrip ρ))
        (norm_smul_graphFourierReadoutCLM_le _ (neg_gammaOf_mem_closedStrip ρ))
    _ = _ := (add_mul _ _ _).symm

theorem summable_mixedZeroOperator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Summable (mixedZeroOperator f) := by
  have hp := (summable_compactFourierCoeffs hf hc).norm
  have hn := (summable_compactFourierCoeffs_neg hf hc).norm
  exact Summable.of_norm_bounded (E := SourceGraph →L[ℝ] ℂ)
    ((hn.add hp).mul_right stripReadoutBound) (norm_mixedZeroOperator_le f)

def graphMixedZeroTerm (p : SourceGraph) (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (-gammaOf ρ) * graphFourierReadout p (gammaOf ρ) +
    (zetaZeroConfig.mult ρ : ℂ) * paperFT (fun x => (f x : ℂ)) (gammaOf ρ) * graphFourierReadout p (-gammaOf ρ)

theorem mixedZeroOperator_apply (p : SourceGraph) (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) :
    mixedZeroOperator f ρ p = graphMixedZeroTerm p f ρ := by
  simp [mixedZeroOperator, graphMixedZeroTerm, graphFourierReadoutCLM_apply, smul_eq_mul]

theorem summable_graphMixedZeroTerm (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : Summable (graphMixedZeroTerm p f) := by
  simpa only [ContinuousLinearMap.apply_apply, mixedZeroOperator_apply] using
    Summable.mapL (ContinuousLinearMap.apply ℝ ℂ p) (summable_mixedZeroOperator hf hc)

theorem tsum_mixedZeroOperator_apply (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∑' ρ, mixedZeroOperator f ρ) p = ∑' ρ, graphMixedZeroTerm p f ρ := by
  simpa only [ContinuousLinearMap.apply_apply, mixedZeroOperator_apply] using
    (ContinuousLinearMap.apply ℝ ℂ p).map_tsum (summable_mixedZeroOperator hf hc)

def mixedGraphFunctional (f : ℝ → ℝ) : SourceGraph →L[ℝ] ℝ :=
  Complex.reCLM.comp ((1/2 : ℂ) • (∑' ρ, mixedZeroOperator f ρ) -
    paperFT (fun x => (f x : ℂ)) (-I/2) • graphFourierReadoutCLM (I/2) (by norm_num) -
    paperFT (fun x => (f x : ℂ)) (I/2) • graphFourierReadoutCLM (-I/2) (by norm_num))

theorem mixedGraphFunctional_eq (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    mixedGraphFunctional f p = ((∑' ρ, graphMixedZeroTerm p f ρ)/2 -
      paperFT (fun x => (f x : ℂ)) (-I/2) * graphFourierReadout p (I/2) -
      paperFT (fun x => (f x : ℂ)) (I/2) * graphFourierReadout p (-I/2)).re := by
  simp only [mixedGraphFunctional, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, Complex.reCLM_apply, smul_eq_mul,
    graphFourierReadoutCLM_apply, tsum_mixedZeroOperator_apply p hf hc]
  congr 1
  ring

end RHTower.CHMDDoobGraph
