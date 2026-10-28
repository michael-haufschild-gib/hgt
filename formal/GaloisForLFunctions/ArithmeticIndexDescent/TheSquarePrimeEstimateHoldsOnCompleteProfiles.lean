import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeSourceRetainsGammaEnergy
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothCompleteWeilTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment

/-!
# Square-prime coercivity on compact BV and complete cell profiles

The same pole-preserving smoothing has one common support interval, so
only finitely many square-prime lags occur throughout the approximation.
Its ordinary mean converges by the exact convolution integral. Existing
L², correlation and Gamma convergence then transfer both coercive bounds
to every original compact BV profile, including complete cell profiles.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Convolution
open _root_.RHTower hiding mollifier
open _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.RHTower ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry SpacingScaleHarmonicAnalysis

/-- Pole normalization rescales the ordinary mean by its explicit scalar and nothing else. -/
theorem integral_poleSmooth {f : ℝ → ℝ} (hf : Integrable f) (n : ℕ) :
    (∫ x : ℝ, poleSmooth f n x) = (poleNormalizer n)⁻¹ * ∫ x : ℝ, f x := by
  have hs : (∫ x : ℝ, smooth f n x) = ∫ x : ℝ, f x := by
    have h := integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_integrable n) hf
    simpa only [smooth, lineConvolution, convolution_def, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul, mollifier_integral, one_mul] using h
  simp only [poleSmooth, integral_const_mul, hs]

/-- The ordinary mean converges along the same smoothing that preserves both exponential poles. -/
theorem tendsto_poleSmooth_mean {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n => ∫ x : ℝ, poleSmooth f n x) atTop (𝓝 (∫ x : ℝ, f x)) := by
  simp_rw [integral_poleSmooth hf]
  simpa only [inv_one, one_mul] using
    (poleNormalizer_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).mul_const (∫ x : ℝ, f x)

private theorem poleSmooth_contDiff_infty {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    ContDiff ℝ ∞ (poleSmooth f n) := by
  have hs : ContDiff ℝ ∞ (smooth f n) :=
    (mollifier_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (show ContDiff ℝ ∞ (CHMDDoobGraph.mollifier n) from (WeilOneSided.narrowBump n).contDiff_normed)
      (hf.locallyIntegrable (by norm_num))
  exact contDiff_const.mul hs

private theorem support_subset_Icc_of_supported {f : ℝ → ℝ} {R : ℝ} (hR : SupportedIn R f) :
    Function.support f ⊆ Icc (-R) R := by
  intro x hx
  apply abs_le.mp
  by_contra h
  exact hx (hR x (lt_of_not_ge h))

/-- The actual smoothed profile, regarded as a smooth core in one fixed enlarged aperture. -/
def squarePrimeSmoothCore {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : SupportedIn R f) (n : ℕ) : SuzukiRestrictedWeilCore (R + 1) where
  toFun := poleSmooth f n
  smooth := poleSmooth_contDiff_infty hf n
  supportRadius := R + 1 / 2
  supportRadius_nonneg := by linarith only [hR0]
  supportRadius_lt_aperture := by linarith
  support_subset := support_subset_Icc_of_supported (poleSmooth_supported hR n)

/-- Every compact source admits a nonnegative support radius. -/
theorem exists_nonneg_supported_radius {f : ℝ → ℝ} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ SupportedIn R f := by
  obtain ⟨L, hL⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max 0 L, le_max_left _ _, ?_⟩
  intro x hx
  by_contra hn
  have hmem := hL (subset_tsupport f hn)
  have hb : |x| ≤ L := by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hmem
  exact (not_lt_of_ge (hb.trans (le_max_right _ _))) hx

private theorem square_correlation_zero_of_exp_lt {f : ℝ → ℝ} {R : ℝ}
    (hR : SupportedIn R f) {n : ℕ} (hn : Real.exp R < (n : ℝ)) :
    screwCrossCorr f f (2 * Real.log n) = 0 := by
  have hnpos : (0 : ℝ) < n := (Real.exp_pos R).trans hn
  have hl : R < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hn
  exact screwCrossCorr_eq_zero_of_support_radius_pos (support_subset_Icc_of_supported hR)
    (support_subset_Icc_of_supported hR) (by linarith only [hl])

/-- Common support and L² correlation convergence recover the literal finite square source. -/
theorem tendsto_poleSmooth_squarePrimeSource {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {R : ℝ} (hR : SupportedIn R f) :
    Tendsto (fun n => squarePrimeSource (poleSmooth f n)) atTop (𝓝 (squarePrimeSource f)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (R + 1 / 2))
  have he {g : ℝ → ℝ} (hg : SupportedIn (R + 1 / 2) g) :
      squarePrimeSource g = 2 * ∑ k ∈ Finset.range N,
        (ArithmeticFunction.vonMangoldt k / (k : ℝ)) * screwCrossCorr g g (2 * Real.log k) := by
    unfold squarePrimeSource
    congr 1
    apply tsum_eq_sum
    intro k hk
    have hNk : N ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [square_correlation_zero_of_exp_lt hg (hN.trans_le (Nat.cast_le.mpr hNk)), mul_zero]
  have hfR : SupportedIn (R + 1 / 2) f := fun x hx => hR x (by linarith only [hx])
  simp_rw [he (poleSmooth_supported hR _), he hfR]
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro k _
  have h := (tendsto_poleSmooth_correlation hf (2 * Real.log k)).const_mul
    (ArithmeticFunction.vonMangoldt k / (k : ℝ))
  simpa only [screwCrossCorr, add_comm] using h

/-- Square-prime coercivity passes to every original compact BV profile. -/
theorem squarePrimeSource_gamma_gap_bv {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) :
    Real.eulerMascheroniConstant * (∫ x : ℝ, f x ^ 2) ≤
      levyEnergy f - squarePrimeSource f + (1 / 2 : ℝ) * (∫ x : ℝ, f x) ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_nonneg_supported_radius hc
  have hf2 := memLp_compact_bv hv hc
  have hf1 : Integrable f := by
    simpa only [mul_one] using integrable_compact_bv_mul hv hc
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hleft := (tendsto_poleSmooth_square_mass hf2).const_mul Real.eulerMascheroniConstant
  have hright := ((tendsto_poleSmooth_levyEnergy hv hc).sub
    (tendsto_poleSmooth_squarePrimeSource hf2 hR)).add
      (((tendsto_poleSmooth_mean hf1).pow 2).const_mul (1 / 2 : ℝ))
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall fun n => squarePrimeSource_gamma_gap_core (squarePrimeSmoothCore hf2 hR0 hR n)

/-- The same positive Gamma share is retained uniformly on all compact BV profiles. -/
theorem exists_squarePrime_retained_gamma_bv :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : ℝ → ℝ), BoundedVariationOn f univ → HasCompactSupport f →
      δ * levyEnergy f + (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, f x ^ 2) ≤
        levyEnergy f - squarePrimeSource f + (1 / 2 : ℝ) * (∫ x : ℝ, f x) ^ 2 := by
  obtain ⟨δ, hδ, hcore⟩ := exists_squarePrime_retained_gamma_core
  refine ⟨δ, hδ, ?_⟩
  intro f hv hc
  obtain ⟨R, hR0, hR⟩ := exists_nonneg_supported_radius hc
  have hf2 := memLp_compact_bv hv hc
  have hf1 : Integrable f := by
    simpa only [mul_one] using integrable_compact_bv_mul hv hc
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hleft := ((tendsto_poleSmooth_levyEnergy hv hc).const_mul δ).add
    ((tendsto_poleSmooth_square_mass hf2).const_mul (Real.eulerMascheroniConstant / 2))
  have hright := ((tendsto_poleSmooth_levyEnergy hv hc).sub
    (tendsto_poleSmooth_squarePrimeSource hf2 hR)).add
      (((tendsto_poleSmooth_mean hf1).pow 2).const_mul (1 / 2 : ℝ))
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall fun n => hcore (R + 1) (squarePrimeSmoothCore hf2 hR0 hR n)

/-- No profile projection is used: averages and details both remain in the square estimate. -/
theorem squarePrimeSource_gamma_gap_complete (q d : ℕ → ℝ) (X : ℕ) :
    Real.eulerMascheroniConstant * (∫ x : ℝ, completePairProfile q d X x ^ 2) ≤
      levyEnergy (completePairProfile q d X) - squarePrimeSource (completePairProfile q d X) +
        (1 / 2 : ℝ) * (∫ x : ℝ, completePairProfile q d X x) ^ 2 :=
  squarePrimeSource_gamma_gap_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)

theorem exists_squarePrime_retained_gamma_complete :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      δ * levyEnergy (completePairProfile q d X) +
        (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, completePairProfile q d X x ^ 2) ≤
      levyEnergy (completePairProfile q d X) - squarePrimeSource (completePairProfile q d X) +
        (1 / 2 : ℝ) * (∫ x : ℝ, completePairProfile q d X x) ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := exists_squarePrime_retained_gamma_bv
  exact ⟨δ, hδ, fun q d X => h _ (completePairProfile_bv q d X) (completePairProfile_compact q d X)⟩

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.tendsto_poleSmooth_mean
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.tendsto_poleSmooth_squarePrimeSource
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.squarePrimeSource_gamma_gap_bv
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_squarePrime_retained_gamma_bv
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_squarePrime_retained_gamma_complete
