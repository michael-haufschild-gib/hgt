import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointMomentAction

/-!
# Exterior moment gauges vanish under physical support projection

Moving the exterior translation pair farther out gives a whole family of
exact complex-current null directions. The support projection annihilates
each one. Consequently the first-moment correction changes only the invisible
part of the field; the supported energy is exactly unchanged.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped InnerProduct

namespace RHTower

def ccmMidpointExteriorShiftAt (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) : ℝ :=
  ccmMidpointExteriorShift a r+n

def ccmMidpointExteriorOddFieldAt (a : SuzukiPositiveAperture) (f : SoninL2)
    (r : ℝ) (n : ℕ) : SoninL2 :=
  ((1/2 : ℝ) : ℂ) • (logTranslationCLM (-ccmMidpointExteriorShiftAt a r n) f -
    logTranslationCLM (r+ccmMidpointExteriorShiftAt a r n) f)

theorem ccmMidpointExteriorShiftAt_separated (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) :
    2*a.1 < ccmMidpointExteriorShiftAt a r n ∧
      2*a.1 < r+ccmMidpointExteriorShiftAt a r n := by
  unfold ccmMidpointExteriorShiftAt ccmMidpointExteriorShift
  constructor <;> linarith [abs_nonneg r, neg_abs_le r, Nat.cast_nonneg (α := ℝ) n]

private theorem projection_translate_zero (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r h : ℝ)
    (h₀ : 2*a.1 < |h|) (h₁ : 2*a.1 < |h-r|) :
    ccmIncrementSupportProjection a r (logTranslationCLM h f.1) = 0 := by
  have hf := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  have hft := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae.eventually hf
  have ht : (logTranslationCLM h f.1 : ℝ → ℂ) =ᵐ[volume] fun x => f.1 (x+h) :=
    (Lp.coeFn_compMeasurePreserving f.1 (MellinL2.realTranslation_measurePreserving h)).trans
      (Eventually.of_forall fun _ => rfl)
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (ccmIncrementSupport a r)
      (measurableSet_ccmIncrementSupport a r) (logTranslationCLM h f.1), ht, hft,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hp ht hf hzero
  change ccmIncrementSupportProjection a r _ x = _ at hp ⊢
  rw [hp, hzero]
  by_cases hx : x ∈ ccmIncrementSupport a r
  · rw [indicator_of_mem hx, ht]
    change f.1 (x+h) = (centralInterval a.1).indicator _ (x+h) at hf
    have hout : x+h ∉ centralInterval a.1 := by
      intro hin
      rcases hx with hx | hx
      · have hb : |h| ≤ 2*a.1 := abs_le.mpr ⟨by linarith [hx.2, hin.1], by linarith [hx.1, hin.2]⟩
        exact (not_le_of_gt h₀) hb
      · change x+r ∈ centralInterval a.1 at hx
        have hb : |h-r| ≤ 2*a.1 := abs_le.mpr ⟨by linarith [hx.2, hin.1], by linarith [hx.1, hin.2]⟩
        exact (not_le_of_gt h₁) hb
    rw [hf, indicator_of_notMem hout]
    rfl
  · exact indicator_of_notMem hx _

/-- Every exterior pair vanishes as a field on the entire increment-support union. -/
theorem ccmIncrementSupportProjection_exteriorOddAt_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ccmIncrementSupportProjection a r (ccmMidpointExteriorOddFieldAt a f.1 r n) = 0 := by
  let s := ccmMidpointExteriorShiftAt a r n
  have hs := (ccmMidpointExteriorShiftAt_separated a r n).1
  have hsr := (ccmMidpointExteriorShiftAt_separated a r n).2
  have hspos : 0 < s := by dsimp only [s]; linarith [a.2]
  have hsrpos : 0 < r+s := by dsimp only [s]; linarith [a.2]
  have hleft : ccmIncrementSupportProjection a r (logTranslationCLM (-s) f.1) = 0 := by
    apply projection_translate_zero a f r (-s)
    · simpa only [abs_neg, abs_of_pos hspos] using hs
    · simpa only [show -s-r = -(r+s) by ring, abs_neg, abs_of_pos hsrpos] using hsr
  have hright : ccmIncrementSupportProjection a r (logTranslationCLM (r+s) f.1) = 0 := by
    apply projection_translate_zero a f r (r+s)
    · simpa only [abs_of_pos hsrpos] using hsr
    · simpa only [add_sub_cancel_left, abs_of_pos hspos] using hs
  change ccmIncrementSupportProjection a r (((1/2 : ℝ) : ℂ) •
    (logTranslationCLM (-s) f.1-logTranslationCLM (r+s) f.1)) = 0
  rw [map_smul, map_sub, hleft, hright, sub_self, smul_zero]

/-- The whole complex current vanishes, stronger than real-current cancellation. -/
theorem inner_increment_exteriorOddAt_zero (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    inner ℂ (logTranslationCLM r f.1-f.1) (ccmMidpointExteriorOddFieldAt a f.1 r n) = 0 := by
  rw [← inner_increment_ccmIncrementSupportProjection a f r,
    ccmIncrementSupportProjection_exteriorOddAt_zero, inner_zero_right]

/-- Every complex multiple is an exact action symmetry on physical sources. -/
theorem ccmGammaIncrementAction_exteriorOddAt_complex_invariant
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (v : SoninL2) (r : ℝ) (n : ℕ) (z : ℂ) :
    ccmGammaIncrementAction f.1 r (v+z • ccmMidpointExteriorOddFieldAt a f.1 r n) =
      ccmGammaIncrementAction f.1 r v := by
  apply (ccmGammaIncrementAction_eq_iff_current_eq _ _ _ _).mpr
  rw [inner_add_right, inner_smul_right, inner_increment_exteriorOddAt_zero, mul_zero, add_zero]

theorem ccmIncrementSupportProjection_exteriorOdd_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmIncrementSupportProjection a r (ccmMidpointExteriorOddField a f.1 r) = 0 := by
  simpa only [ccmMidpointExteriorOddFieldAt, ccmMidpointExteriorShiftAt, Nat.cast_zero,
    add_zero, ccmMidpointExteriorOddField] using
      ccmIncrementSupportProjection_exteriorOddAt_zero a f r 0

/-- Cancelling the first spectral moment leaves the supported arithmetic field unchanged. -/
theorem ccmIncrementSupportProjection_momentCancelledField
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmIncrementSupportProjection a r (ccmActualHeadMomentCancelledField a N f.1 r) =
      ccmIncrementSupportProjection a r (ccmActualHeadMidpointOddField (2*a.1) N f.1 r) := by
  rw [ccmActualHeadMomentCancelledField, map_sub, map_smul,
    ccmIncrementSupportProjection_exteriorOdd_zero, smul_zero, sub_zero]

/-- The correction can only change energy in the invisible complement. -/
theorem norm_sq_momentCancelledField_support_split
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    ‖ccmActualHeadMomentCancelledField a N f.1 r‖^2 =
      ‖ccmIncrementSupportProjection a r (ccmActualHeadMidpointOddField (2*a.1) N f.1 r)‖^2 +
      ‖ccmActualHeadMomentCancelledField a N f.1 r -
        ccmIncrementSupportProjection a r (ccmActualHeadMidpointOddField (2*a.1) N f.1 r)‖^2 := by
  rw [norm_sq_ccmIncrementSupportProjection a r (ccmActualHeadMomentCancelledField a N f.1 r),
    ccmIncrementSupportProjection_momentCancelledField]

/-- Pushing the exterior pair outward does not increase its norm. -/
theorem norm_ccmMidpointExteriorOddFieldAt_le (a : SuzukiPositiveAperture)
    (f : SoninL2) (r : ℝ) (n : ℕ) :
    ‖ccmMidpointExteriorOddFieldAt a f r n‖ ≤ ‖f‖ := by
  have hn (h : ℝ) : ‖logTranslationCLM h f‖ = ‖f‖ :=
    (MellinL2.additiveTranslationUnitary h).norm_map f
  rw [ccmMidpointExteriorOddFieldAt, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have ht := norm_sub_le (logTranslationCLM (-ccmMidpointExteriorShiftAt a r n) f)
    (logTranslationCLM (r+ccmMidpointExteriorShiftAt a r n) f)
  rw [hn, hn] at ht
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  linarith only [ht]

/-- The separated pair has exactly half the source energy at every outward position. -/
theorem norm_sq_ccmMidpointExteriorOddFieldAt (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ‖ccmMidpointExteriorOddFieldAt a f.1 r n‖^2 = ‖f.1‖^2/2 := by
  let s := ccmMidpointExteriorShiftAt a r n
  have hs := ccmMidpointExteriorShiftAt_separated a r n
  have hsep : 2*a.1 ≤ s+(r+s) := by
    dsimp only [s]
    linarith [hs.1, hs.2, a.2]
  have hp : (inner ℂ (logTranslationCLM (-s) f.1) (logTranslationCLM (r+s) f.1)).re = 0 := by
    rw [inner_logTranslationCLM, neg_neg, logTranslationCLM_add_apply]
    calc
      _ = (inner ℂ (logTranslationCLM (s+(r+s)) f.1) f.1).re :=
        inner_re_symm (𝕜 := ℂ) f.1 _
      _ = ccmActualHeadSymmetricAutocorrelation (s+(r+s)) f.1 :=
        (ccmActualHeadSymmetricAutocorrelation_eq_re_inner _ _).symm
      _ = 0 := ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f hsep
  have hn (h : ℝ) : ‖logTranslationCLM h f.1‖ = ‖f.1‖ :=
    (MellinL2.additiveTranslationUnitary h).norm_map f.1
  rw [ccmMidpointExteriorOddFieldAt, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, norm_sub_sq (𝕜 := ℂ), RCLike.re_eq_complex_re, hn, hn, hp]
  ring

end RHTower
