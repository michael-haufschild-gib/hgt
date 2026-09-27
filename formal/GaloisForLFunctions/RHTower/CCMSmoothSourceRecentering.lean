import GaloisForLFunctions.RHTower.CCMRestrictedWeilFullTranslationCovariance
import GaloisForLFunctions.RHTower.CCMThetaThreeEnergyComparison
import GaloisForLFunctions.RHTower.CCMSmoothSupportUncertainty

/-!
# Recentering actual smooth sources preserves the complete Weil energy

Two presentations of a translated physical source can use unrelated apertures.
Embedding their form vectors into one sufficiently large aperture proves exact
energy invariance. Thus the small-aperture positive gap applies uniformly to
sources near any center, independently of their ambient aperture.
-/

noncomputable section

open MeasureTheory Set Filter

namespace RHTower

theorem ccmTranslatedSmoothSource_physical_coeFn
    {a b : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (h : ℝ) (hfit : a.1 + |h| ≤ b.1) :
    (ccmArchimedeanFormEmbedding b (ccmArchimedeanFormTranslate h hfit u.toCCMFormVector) :
      ℝ → ℂ) =ᵐ[volume] fun x => u (x + h) := by
  change ((ccmArchimedeanFormToAperture b
    (ccmArchimedeanFormTranslate h hfit u.toCCMFormVector) : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  rw [ccmArchimedeanFormTranslate_physical]
  have ht : (logTranslationCLM h (ccmArchimedeanFormToAperture a u.toCCMFormVector) :
      ℝ → ℂ) =ᵐ[volume] fun x => (ccmArchimedeanFormToAperture a u.toCCMFormVector :
        SoninL2) (x + h) := by
    exact (Lp.coeFn_compMeasurePreserving _
      (MellinL2.realTranslation_measurePreserving h)).trans
        (Eventually.of_forall fun _ => rfl)
  have hu := u.toCCMFormVector_physical_coeFn.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ht, hu] with x hx hy
  exact hx.trans hy

/-- Full Gamma, prime, and polar energy is independent of center and aperture presentation. -/
theorem ccmSmoothSourceQuadratic_eq_of_translate
    {a b : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (v : CCMComplexSmoothInteriorSource b) (h : ℝ)
    (hv : ∀ x : ℝ, v x = u (x + h)) :
    ccmRestrictedWeilSourceQuadratic b v.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  let A : SuzukiPositiveAperture := ⟨a.1 + b.1 + |h|, by linarith [a.2, b.2, abs_nonneg h]⟩
  have huA : a.1 + |h| ≤ A.1 := by dsimp [A]; linarith [b.2]
  have hvA : b.1 + |(0 : ℝ)| ≤ A.1 := by dsimp [A]; rw [abs_zero]; linarith [a.2, abs_nonneg h]
  have he : ccmArchimedeanFormTranslate h huA u.toCCMFormVector =
      ccmArchimedeanFormTranslate 0 hvA v.toCCMFormVector := by
    apply ccmArchimedeanFormEmbedding_injective A
    apply Lp.ext
    filter_upwards [ccmTranslatedSmoothSource_physical_coeFn u h huA,
      ccmTranslatedSmoothSource_physical_coeFn v 0 hvA] with x hx hy
    rw [hx, hy, add_zero, hv]
  rw [← ccmRestrictedWeilSourceQuadratic_translate_full 0 hvA v.toCCMFormVector,
    ← he, ccmRestrictedWeilSourceQuadratic_translate_full]

theorem ccmSmoothSourcePhysicalMass_eq_of_translate
    {a b : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (v : CCMComplexSmoothInteriorSource b) (h : ℝ)
    (hv : ∀ x : ℝ, v x = u (x + h)) :
    ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2 =
      ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  rw [← ccmSmooth_integral_norm_sq_eq_physical v, ← ccmSmooth_integral_norm_sq_eq_physical u]
  simp_rw [hv]
  exact integral_add_right_eq_self (fun x : ℝ => ‖u x‖ ^ 2) h

/-- Literal recentering, with the smaller support aperture supplied by geometry. -/
def CCMComplexSmoothInteriorSource.recenter
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (b : SuzukiPositiveAperture) (c : ℝ)
    (hs : tsupport u ⊆ Ioo (c - b.1) (c + b.1)) : CCMComplexSmoothInteriorSource b where
  toFun x := u (x + c)
  smooth := u.smooth.comp (contDiff_id.add contDiff_const)
  hasCompactSupport := u.hasCompactSupport.comp_homeomorph (Homeomorph.addRight c)
  tsupport_subset := by
    intro x hx
    have hx' : x + c ∈ tsupport u :=
      tsupport_comp_subset_preimage u (continuous_id.add continuous_const) hx
    have hh := hs hx'
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

@[simp] theorem CCMComplexSmoothInteriorSource.recenter_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (b : SuzukiPositiveAperture) (c : ℝ)
    (hs : tsupport u ⊆ Ioo (c - b.1) (c + b.1)) (x : ℝ) :
    u.recenter b c hs x = u (x + c) := rfl

/-- A uniform positive energy gap for every sufficiently narrow translated smooth source.
Neither the center nor the ambient aperture enters the constant. -/
theorem exists_ccmSmoothSource_center_independent_gap :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) (c : ℝ),
        tsupport u ⊆ Metric.ball c delta →
        C * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  obtain ⟨d, hd, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  let b : SuzukiPositiveAperture := ⟨d / 2, half_pos hd⟩
  have hb : 0 < ccmRestrictedWeilGroundEnergy b := hpos b (half_lt_self hd)
  refine ⟨b.1, ccmRestrictedWeilGroundEnergy b, b.2, hb, fun a u c hs => ?_⟩
  have hs' : tsupport u ⊆ Ioo (c - b.1) (c + b.1) := by
    simpa only [Real.ball_eq_Ioo] using hs
  let v := u.recenter b c hs'
  have hv (x : ℝ) : v x = u (x + c) := rfl
  have hq := ccmSmoothSourceQuadratic_eq_of_translate u v c hv
  have hm := ccmSmoothSourcePhysicalMass_eq_of_translate u v c hv
  have hf := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source b v.toCCMFormVector
  change ccmRestrictedWeilGroundEnergy b *
    ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2 ≤ _ at hf
  rwa [hm, hq] at hf

end RHTower
