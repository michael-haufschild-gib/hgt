import GaloisForLFunctions.RHTower.CCMCoherentGammaPhysicalStability
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurModulation

/-!
# A surviving coherent Gamma cost on the Schur pole profile

The test retains the complete coherent field. Its pairing with the positive
pole profile has nonnegative bulk terms, a strictly positive prime-two term,
and an exactly zero terminal term. Support projection preserves this pairing.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem pole_edge_zero (a : SuzukiPositiveAperture) (h : ℝ) :
    ccmPrimePoleEdgeEnergy a h (ccmSchurPoleVector a).1 = 0 := by
  have hm : ccmApertureModulation a 0 (ccmSchurPoleVector a) = ccmSchurPoleVector a :=
    Subtype.ext (modulationMul_zero_apply _)
  have he := ccmPrimePoleEdgeEnergy_modulatedPole a 0 h
  simpa only [hm, modulationSymbol_zero, sub_self, norm_zero, zero_pow two_ne_zero,
    zero_mul] using he

private theorem pole_pair_nonneg (a : SuzukiPositiveAperture) (h : ℝ) :
    0 ≤ (inner ℂ (logTranslationCLM h (ccmSchurPoleVector a).1)
      (ccmSchurPoleVector a).1).re := by
  have he := ccmPrimePoleEdgeEnergy_eq_rows_sub_pair a h (ccmSchurPoleVector a)
  rw [pole_edge_zero] at he
  have h1 : 0 ≤ ∫ x : ℝ, ccmPrimePoleRowDensity a h (ccmSchurPoleVector a).1 x :=
    integral_nonneg (fun x => (ccmPrimePoleRowDensity_bound a h
      (ccmSchurPoleVector a).1 x).1)
  have h2 : 0 ≤ ∫ x : ℝ, ccmPrimePoleRowDensity a (-h) (ccmSchurPoleVector a).1 x :=
    integral_nonneg (fun x => (ccmPrimePoleRowDensity_bound a (-h)
      (ccmSchurPoleVector a).1 x).1)
  linarith

private theorem pole_pair_pos (a : SuzukiPositiveAperture) (h : ℝ)
    (hh : 0 ≤ h) (hha : h < 2*a.1) :
    0 < (inner ℂ (logTranslationCLM h (ccmSchurPoleVector a).1)
      (ccmSchurPoleVector a).1).re := by
  let F := ccmPrimePoleRowDensity a h (ccmSchurPoleVector a).1
  have hF : 0 < ∫ x : ℝ, F x := by
    rw [integral_pos_iff_support_of_nonneg
      (fun x => (ccmPrimePoleRowDensity_bound a h (ccmSchurPoleVector a).1 x).1)
      (integrable_ccmPrimePoleRowDensity a h (ccmSchurPoleVector a).1)]
    have hsub : ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) (a.1-h) → x ∈ Function.support F := by
      filter_upwards [ccmSchurPoleVector_coeFn a] with x hw hx
      have hxi : x ∈ centralInterval a.1 := ⟨hx.1.le, by linarith [hx.2]⟩
      have hxh : x+h ∈ centralInterval a.1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      apply Function.mem_support.mpr
      apply ne_of_gt
      dsimp only [F, ccmPrimePoleRowDensity]
      rw [indicator_of_mem hxh, hw, indicator_of_mem hxi, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (primePoleProfile_pos x)]
      exact mul_pos (div_pos (primePoleProfile_pos _) (primePoleProfile_pos _))
        (sq_pos_of_pos (primePoleProfile_pos _))
    have hv : 0 < volume (Ioo (-a.1) (a.1-h)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    exact hv.trans_le (measure_mono_ae hsub)
  have he := ccmPrimePoleEdgeEnergy_eq_rows_sub_pair a h (ccmSchurPoleVector a)
  rw [pole_edge_zero] at he
  have h2 : 0 ≤ ∫ x : ℝ, ccmPrimePoleRowDensity a (-h) (ccmSchurPoleVector a).1 x :=
    integral_nonneg (fun x => (ccmPrimePoleRowDensity_bound a (-h)
      (ccmSchurPoleVector a).1 x).1)
  dsimp only [F] at hF
  linarith

theorem ccmIncrementSupportProjection_aperture (a : SuzukiPositiveAperture)
    (r : ℝ) (f : suzukiApertureHilbert a) :
    ccmIncrementSupportProjection a r f.1 = f.1 := by
  apply Lp.ext
  have hf := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  filter_upwards [hf, indicatorCutoff_ae (ccmIncrementSupport a r)
    (measurableSet_ccmIncrementSupport a r) f.1] with x hf hp
  change (ccmIncrementSupportProjection a r f.1) x =
    (ccmIncrementSupport a r).indicator (fun y => f.1 y) x at hp
  rw [hp]
  by_cases hx : x ∈ ccmIncrementSupport a r
  · rw [indicator_of_mem hx]
  · have hxi : x ∉ centralInterval a.1 := fun h => hx (Or.inl h)
    rw [indicator_of_notMem hx, hf, indicator_of_notMem hxi]

private theorem projected_pair (a : SuzukiPositiveAperture) (r : ℝ)
    (f : suzukiApertureHilbert a) (v : SoninL2) :
    inner ℂ (ccmIncrementSupportProjection a r v) f.1 = inner ℂ v f.1 := by
  have h := indicatorCutoff_symmetric (ccmIncrementSupport a r)
    (measurableSet_ccmIncrementSupport a r) v f.1
  change inner ℂ (ccmIncrementSupportProjection a r v) f.1 =
    inner ℂ v (ccmIncrementSupportProjection a r f.1) at h
  rwa [ccmIncrementSupportProjection_aperture] at h

private theorem supported_pole_pair_lower (a : SuzukiPositiveAperture) (N : ℕ)
    (hN : 3 ≤ N) (r : ℝ) :
    ccmOutgoingQuantileDisplacementCellDensity 2 r *
      (inner ℂ (logTranslationCLM (-Real.log 2) (ccmSchurPoleVector a).1)
        (ccmSchurPoleVector a).1).re ≤
      (inner ℂ (ccmActualHeadSupportedCoherentField a N (ccmSchurPoleVector a).1 r)
        (ccmSchurPoleVector a).1).re := by
  have ht : inner ℂ (logTranslationCLM (-(2*a.1)) (ccmSchurPoleVector a).1)
      (ccmSchurPoleVector a).1 = 0 := by
    rw [inner_logTranslationCLM, neg_neg]
    exact inner_eq_zero_symm.mp (inner_logTranslationCLM_two_aperture_eq_zero a _)
  rw [ccmActualHeadSupportedCoherentField, projected_pair,
    ccmActualHeadQuantileCompletedCoherentField, ccmActualHeadQuantileBulkCoherentField,
    ccmActualHeadQuantileTerminalCoherentField, inner_add_left, inner_smul_left, ht,
    mul_zero, add_zero]
  simp only [sum_inner, ccmActualHeadQuantileCellCoherentField, inner_smul_left,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.single_le_sum
    (fun n _ => mul_nonneg (ccmOutgoingQuantileDisplacementCellDensity_nonneg n r)
      (pole_pair_nonneg a (-Real.log n))) (show 2 ∈ Finset.range N by simp; omega)

private theorem prime_two_cell_width_pos :
    ccmOutgoingPrimeQuantileBoundary 2 < ccmOutgoingPrimeQuantileBoundary 3 := by
  have hP := ccmOutgoingPrimeCumulative_nonneg 2
  have hw := criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  change ccmOutgoingPrimeQuantileBoundary 2 < ccmOutgoingPrimeQuantileBoundary (2+1)
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [ccmOutgoingPrimeCumulative_succ 2]
  exact mul_lt_mul_of_pos_left (Real.log_lt_log (by linarith) (by linarith)) (by positivity)

/-- The complete supported coherent cost is strictly positive on the pole
profile once prime two fits inside the aperture. The terminal is retained. -/
theorem ccmActualHeadSupportedCoherentGammaCost_schurPole_pos
    (a : SuzukiPositiveAperture) (ha : Real.log 2 < 2*a.1)
    (N : ℕ) (hN : 3 ≤ N) :
    0 < ccmActualHeadSupportedCoherentGammaCost a N (ccmSchurPoleVector a).1 := by
  let w := ccmSchurPoleVector a
  have hp : 0 < (inner ℂ (logTranslationCLM (-Real.log 2) w.1) w.1).re := by
    have hpos := pole_pair_pos a (Real.log 2) (Real.log_nonneg (by norm_num)) ha
    rw [inner_logTranslationCLM, neg_neg]
    change 0 < RCLike.re (inner ℂ w.1 (logTranslationCLM (Real.log 2) w.1))
    rw [inner_re_symm (𝕜 := ℂ)]
    exact hpos
  let D : ℝ → ℝ := fun r => ‖ccmActualHeadSupportedCoherentField a N w.1 r‖ ^ 2 *
    ccmGammaHigherBinetDualDensity |r|
  have hnn : 0 ≤ D := fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  change 0 < ∫ r : ℝ, D r
  rw [integral_pos_iff_support_of_nonneg hnn
    (integrable_ccmActualHeadSupportedCoherentGammaDensity a N w.1)]
  let J := Ioo (ccmOutgoingPrimeQuantileBoundary 2-Real.log 2)
    (ccmOutgoingPrimeQuantileBoundary 3-Real.log 2)
  have hsub : J \ {0} ⊆ Function.support D := by
    intro r hr
    have hcell : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary 2-Real.log 2)
        (ccmOutgoingPrimeQuantileBoundary (2+1)-Real.log 2) := ⟨hr.1.1,hr.1.2.le⟩
    have hρ : 0 < ccmOutgoingQuantileDisplacementCellDensity 2 r := by
      simp only [ccmOutgoingQuantileDisplacementCellDensity, Nat.cast_ofNat,
        indicator_of_mem hcell]
      exact Real.exp_pos _
    have hpair := (mul_pos hρ hp).trans_le (supported_pole_pair_lower a N hN r)
    have hv : ccmActualHeadSupportedCoherentField a N w.1 r ≠ 0 := by
      intro hz
      rw [hz, inner_zero_left, Complex.zero_re] at hpair
      exact (lt_irrefl 0 hpair)
    have hr0 : 0 < |r| := abs_pos.mpr (by simpa only [mem_singleton_iff] using hr.2)
    have hd : 0 < ccmGammaHigherBinetDualDensity |r| := by
      unfold ccmGammaHigherBinetDualDensity
      exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
    exact Function.mem_support.mpr (ne_of_gt (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) hd))
  have hJ : 0 < volume J := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [prime_two_cell_width_pos])
  have hJ0 : volume (J \ {0}) = volume J := measure_sdiff_null (by simp)
  exact (hJ0.symm ▸ hJ).trans_le (measure_mono hsub)

end RHTower
