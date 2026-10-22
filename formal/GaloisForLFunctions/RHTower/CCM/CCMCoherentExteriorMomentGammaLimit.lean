import GaloisForLFunctions.RHTower.CCM.CCMCoherentExteriorMomentSpectrum

/-!
# Vanishing Gamma energy of exact moment corrections

The literal finite prime-plus-terminal moment has finite reciprocal-Gamma
energy. Moving its cancelling exterior pair outward makes the whole integrated
correction cost tend to zero, with an explicit inverse-square bound. This is
stronger than the displacement-by-displacement Hilbert norm limit, and retains
the exact support and current invariance already established.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

private theorem memLp_indicator_continuous (lo hi : ℝ) (F : ℝ → ℝ) (hF : Continuous F) :
    MemLp ((Ioc lo hi).indicator F) 2 (volume : Measure ℝ) := by
  have hs : HasCompactSupport ((Ioc lo hi).indicator F) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := lo) (b := hi)) fun x hx => ?_
    exact indicator_of_notMem (fun h => hx ⟨h.1.le, h.2⟩) _
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn hF.continuousOn
  apply hs.memLp_of_bound ((hF.measurable.indicator measurableSet_Ioc).aestronglyMeasurable) (max C 0)
  filter_upwards with x
  by_cases hx : x ∈ Ioc lo hi
  · rw [indicator_of_mem hx]
    exact (hC x ⟨hx.1.le, hx.2⟩).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

private theorem cell_moment_memLp (n : ℕ) :
    MemLp (fun r : ℝ => ccmOutgoingQuantileDisplacementCellDensity n r *
      (2*Real.pi*(Real.log n+r/2)) * Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  let F := fun r : ℝ => Real.exp ((r+Real.log n)/2) *
    (2*Real.pi*(Real.log n+r/2)) * Real.sqrt (ccmGammaHigherBinetDualDensity |r|)
  have hF : Continuous F := by unfold F ccmGammaHigherBinetDualDensity; fun_prop
  have h := memLp_indicator_continuous (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) F hF
  refine h.ae_eq (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) <;>
    simp [ccmOutgoingQuantileDisplacementCellDensity, F, hr]

private theorem terminal_moment_memLp (T : ℝ) (N : ℕ) :
    MemLp (fun r : ℝ => ccmActualHeadQuantileTerminalDisplacementDensity T N r *
      (2*Real.pi*(T+r/2)) * Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  let F := fun r : ℝ => Real.exp ((r+T)/2) *
    (2*Real.pi*(T+r/2)) * Real.sqrt (ccmGammaHigherBinetDualDensity |r|)
  have hF : Continuous F := by unfold F ccmGammaHigherBinetDualDensity; fun_prop
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · have h := memLp_indicator_continuous (ccmOutgoingPrimeQuantileBoundary N-T) 0 F hF
    refine h.ae_eq (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary N-T) 0 <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr, F]
  · have h := (memLp_indicator_continuous 0 (ccmOutgoingPrimeQuantileBoundary N-T) F hF).neg
    refine h.ae_eq (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N-T) <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr, F]

/-- Actual prime and oriented terminal moments belong to the weighted `L²` space. -/
theorem memLp_ccmActualHeadSignedMoment_mul_sqrtDual (T : ℝ) (N : ℕ) :
    MemLp (fun r : ℝ => ccmActualHeadMidpointSignedMoment T N r *
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  have hsum := memLp_finsetSum (Finset.range N) (fun n _ => cell_moment_memLp n)
  refine (hsum.add (terminal_moment_memLp T N)).ae_eq (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, ccmActualHeadMidpointSignedMoment, add_mul, Finset.sum_mul]

theorem integrable_ccmActualHeadSignedMomentGammaDensity (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => (ccmActualHeadMidpointSignedMoment T N r)^2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  have h := (memLp_ccmActualHeadSignedMoment_mul_sqrtDual T N).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  refine h.congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))]

def ccmActualHeadSignedMomentGammaEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, (ccmActualHeadMidpointSignedMoment T N r)^2 * ccmGammaHigherBinetDualDensity |r|

theorem ccmActualHeadSignedMomentGammaEnergy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmActualHeadSignedMomentGammaEnergy T N :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

/-- A displacement-uniform lower bound on the exterior frequency. -/
theorem ccmMidpointExteriorFrequencyAt_lower (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) :
    2*Real.pi*((n : ℝ)+1) ≤ ccmMidpointExteriorFrequencyAt a r n := by
  unfold ccmMidpointExteriorFrequencyAt ccmMidpointExteriorShiftAt ccmMidpointExteriorShift
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith [a.2, abs_nonneg r, neg_abs_le r]

private theorem coefficient_bound (a : SuzukiPositiveAperture) (f : SoninL2) (r : ℝ) (n : ℕ) :
    (‖f‖^2/2)/(ccmMidpointExteriorFrequencyAt a r n)^2 ≤
      (‖f‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2 := by
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (ccmMidpointExteriorFrequencyAt_lower a r n) 2

private theorem density_eq (a : SuzukiPositiveAperture) (N : ℕ)
    (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ‖ccmActualHeadMomentCorrectionAt a N f.1 r n‖^2 * ccmGammaHigherBinetDualDensity |r| =
      ((‖f.1‖^2/2)/(ccmMidpointExteriorFrequencyAt a r n)^2) *
        ((ccmActualHeadMidpointSignedMoment (2*a.1) N r)^2 * ccmGammaHigherBinetDualDensity |r|) := by
  rw [norm_sq_ccmActualHeadMomentCorrectionAt, div_pow]
  ring

theorem integrable_ccmActualHeadMomentCorrectionGammaDensity
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (n : ℕ) :
    Integrable (fun r : ℝ => ‖ccmActualHeadMomentCorrectionAt a N f.1 r n‖^2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  have hm : Measurable (fun r : ℝ => (‖f.1‖^2/2)/(ccmMidpointExteriorFrequencyAt a r n)^2) := by
    unfold ccmMidpointExteriorFrequencyAt ccmMidpointExteriorShiftAt ccmMidpointExteriorShift
    fun_prop
  have h := (integrable_ccmActualHeadSignedMomentGammaDensity (2*a.1) N).bdd_mul
    (c := (‖f.1‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2) hm.aestronglyMeasurable
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact coefficient_bound a f.1 r n)
  exact h.congr (Eventually.of_forall fun r => (density_eq a N f r n).symm)

def ccmActualHeadMomentCorrectionGammaCost (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (n : ℕ) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadMomentCorrectionAt a N f r n‖^2 * ccmGammaHigherBinetDualDensity |r|

theorem ccmActualHeadMomentCorrectionGammaCost_nonneg (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (n : ℕ) :
    0 ≤ ccmActualHeadMomentCorrectionGammaCost a N f n :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

/-- Explicit inverse-square decay of the entire integrated correction cost. -/
theorem ccmActualHeadMomentCorrectionGammaCost_le (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) (n : ℕ) :
    ccmActualHeadMomentCorrectionGammaCost a N f.1 n ≤
      ((‖f.1‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2) * ccmActualHeadSignedMomentGammaEnergy (2*a.1) N := by
  calc
    _ ≤ ∫ r : ℝ, ((‖f.1‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2) *
        ((ccmActualHeadMidpointSignedMoment (2*a.1) N r)^2 * ccmGammaHigherBinetDualDensity |r|) := by
      apply integral_mono (integrable_ccmActualHeadMomentCorrectionGammaDensity a N f n)
        ((integrable_ccmActualHeadSignedMomentGammaDensity (2*a.1) N).const_mul _)
      intro r
      dsimp only
      rw [density_eq]
      exact mul_le_mul_of_nonneg_right (coefficient_bound a f.1 r n)
        (mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))
    _ = _ := by rw [integral_const_mul]; rfl

/-- The whole Gamma-weighted cost tends to zero, with every finite arithmetic term retained. -/
theorem tendsto_ccmActualHeadMomentCorrectionGammaCost_zero (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) :
    Tendsto (fun n => ccmActualHeadMomentCorrectionGammaCost a N f.1 n) atTop (𝓝 0) := by
  have hδ : Tendsto (fun n : ℕ => 2*Real.pi*((n : ℝ)+1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop
      (by positivity : 0 < 2*Real.pi)
  have hi : Tendsto (fun n : ℕ => 1/(2*Real.pi*((n : ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hδ
  have hb : Tendsto (fun n : ℕ => ((‖f.1‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2) *
      ccmActualHeadSignedMomentGammaEnergy (2*a.1) N) atTop (𝓝 0) := by
    have he : (fun n : ℕ => ((‖f.1‖^2/2)/(2*Real.pi*((n : ℝ)+1))^2) *
        ccmActualHeadSignedMomentGammaEnergy (2*a.1) N) = fun n : ℕ =>
        ((‖f.1‖^2/2)*ccmActualHeadSignedMomentGammaEnergy (2*a.1) N) *
          (1/(2*Real.pi*((n : ℝ)+1)))^2 := by
      funext n
      rw [div_pow]
      ring
    rw [he]
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hi.pow 2).const_mul ((‖f.1‖^2/2)*ccmActualHeadSignedMomentGammaEnergy (2*a.1) N)
  exact squeeze_zero (fun n => ccmActualHeadMomentCorrectionGammaCost_nonneg a N f.1 n)
    (fun n => ccmActualHeadMomentCorrectionGammaCost_le a N f n) hb

end RHTower
