import GaloisForLFunctions.RHTower.CHMDMixedZeroOperator

/-!
# Mixed explicit formula on the original graph completion

One compact slot suffices for absolute convergence of the mixed zero series.
The operator sum is continuous in the other slot, so compact-test density gives
the literal formula for every graph vector, with both polar terms retained.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

theorem conj_paperFT_plus_pole (f : ℝ → ℝ) :
    conj (paperFT (fun x => (f x : ℂ)) (I/2)) = paperFT (fun x => (f x : ℂ)) (I/2) := by
  simp only [conj_paperFT_ofReal, map_div₀, map_ofNat, conj_I, neg_div, neg_neg]

theorem conj_paperFT_minus_pole (f : ℝ → ℝ) :
    conj (paperFT (fun x => (f x : ℂ)) (-I/2)) = paperFT (fun x => (f x : ℂ)) (-I/2) := by
  simp only [conj_paperFT_ofReal, map_div₀, map_ofNat, map_neg, conj_I, neg_div, neg_neg]

theorem Wsummand_add_compact {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hd : HasCompactSupport g)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun x => ((f+g) x : ℂ)) (fun x => ((f+g) x : ℂ)) ρ =
      zetaZeroConfig.Wsummand (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) ρ +
      zetaZeroConfig.Wsummand (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) ρ +
      graphMixedZeroTerm (testLift f hf hc) g ρ := by
  have ef := compact_expMomentSource (Complex.continuous_ofReal.comp hf.continuous)
    (hc.comp_left Complex.ofReal_zero)
  have eg := compact_expMomentSource (Complex.continuous_ofReal.comp hg.continuous)
    (hd.comp_left Complex.ofReal_zero)
  simp only [ZeroConfig.Wsummand, map_add, conj_paperFT_ofReal, conj_conj,
    paperFT_ofReal_add ef eg, graphMixedZeroTerm, graphFourierReadout_testLift]
  ring

theorem W_add_compact {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hd : HasCompactSupport g) :
    zetaZeroConfig.W (fun x => ((f+g) x : ℂ)) (fun x => ((f+g) x : ℂ)) =
      zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) +
      zetaZeroConfig.W (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) +
      ∑' ρ, graphMixedZeroTerm (testLift f hf hc) g ρ := by
  have hfC : ContDiff ℝ 2 (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hgC : ContDiff ℝ 2 (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hff := WeilConditional.summable_Wsummand hfC
    (hc.comp_left Complex.ofReal_zero)
  have hgg := WeilConditional.summable_Wsummand hgC
    (hd.comp_left Complex.ofReal_zero)
  have hcross := summable_graphMixedZeroTerm (testLift f hf hc) hg hd
  unfold ZeroConfig.W
  simp_rw [Wsummand_add_compact hf hc hg hd]
  rw [(hff.add hgg).tsum_add hcross, hff.tsum_add hgg]

theorem compact_sourcePair_eq_mixed {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hd : HasCompactSupport g) :
    sourcePair (testLift f hf hc) (testLift g hg hd) =
      mixedGraphFunctional g (testLift f hf hc) := by
  rw [sourcePair_eq_signedZeroPair (compact_expDecayTest hf hc) (compact_expDecayTest hg hd)
    (compact_source_lipschitz hf hc) (compact_source_lipschitz hg hd)
    (compact_source_thetaBound hf.continuous hc) (compact_source_thetaBound hg.continuous hd)
    (testLift_source f hf hc) (testLift_source g hg hd), mixedGraphFunctional_eq _ hg hd]
  have ef := compact_expMomentSource (Complex.continuous_ofReal.comp hf.continuous)
    (hc.comp_left Complex.ofReal_zero)
  have eg := compact_expMomentSource (Complex.continuous_ofReal.comp hg.continuous)
    (hd.comp_left Complex.ofReal_zero)
  unfold signedZeroPair signedZeroEnergy
  rw [W_add_compact hf hc hg hd]
  simp only [paperFT_ofReal_add ef eg, map_add, conj_paperFT_plus_pole,
    conj_paperFT_minus_pole, graphFourierReadout_testLift,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re]
  ring

/-- Full graph extension; no source decay, smoothness, or theta bound is required. -/
theorem sourcePair_testLift_eq_mixed (p : SourceGraph) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair p (testLift f hf hc) = mixedGraphFunctional f p := by
  have he : (fun p => sourcePair p (testLift f hf hc)) =
      (fun p => mixedGraphFunctional f p) := by
    apply Continuous.ext_on dense_compactTests
      (continuous_sourcePair.comp (continuous_id.prodMk continuous_const))
      (mixedGraphFunctional f).continuous
    rintro p ⟨v, hv, hvc, rfl⟩
    rw [← testLift_phi v hv hvc]
    exact compact_sourcePair_eq_mixed (contDiff_phiDoobTest hv)
      (hasCompactSupport_phiDoobTest hvc) hf hc
  exact congrFun he p

end RHTower.CHMDDoobGraph
