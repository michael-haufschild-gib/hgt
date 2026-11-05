import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelIncrementSolvesTheFullCollarEquation
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFullWeilFormControlsBothCollars

/-!
# The actual Weil kernel increment is controlled by collar forcing

The exact exterior equation and sharp interval decomposition retain the old
space and both collars. Cauchy–Schwarz on the two physical collars, followed
by the full Weil collar floor, bounds the new kernel mass by the restricted
actual forcing in one fixed enclosing aperture.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy

private theorem inner_positiveExtension (f g : SuzukiPositiveL2) :
    inner ℂ (suzukiPositiveZeroExtension f) (suzukiPositiveZeroExtension g) = inner ℂ f g := by
  let U : SuzukiPositiveL2 →ₗᵢ[ℂ] SoninL2 :=
    { suzukiPositiveZeroExtensionLinear with norm_map' := norm_suzukiPositiveZeroExtension }
  exact U.inner_map_map f g

private theorem inner_rightCoordinate_le {a h : ℝ} (f : SoninL2)
    (hf : ∀ᵐ x ∂volume, x ∉ Icc a (a+h) → f x = 0) (q : SuzukiPositiveL2) :
    ‖inner ℂ (soninHalfLine (logTranslationCLM a f)) q‖ ≤
      ‖f‖*‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc (suzukiPositiveZeroExtension q)‖ := by
  have hs := (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae.eventually hf
  have hcut : indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc (logTranslationCLM a f) =
      logTranslationCLM a f := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (Ioc (0 : ℝ) h) measurableSet_Ioc (logTranslationCLM a f),
      logarithmicTranslation_coeFn a f, hs, volume.ae_ne (0 : ℝ)] with x hc ht hs hx0
    rw [hc]
    by_cases hx : x ∈ Ioc (0 : ℝ) h
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, ht]
      symm
      apply hs
      change x+a ∉ Icc a (a+h)
      intro hp
      apply hx
      constructor
      · exact lt_of_le_of_ne (by linarith only [hp.1]) (Ne.symm hx0)
      · linarith only [hp.2]
  have hhalf : logTranslationCLM a f ∈ halfLineL2 := by
    rw [mem_halfLineL2_iff]
    filter_upwards [hs, logarithmicTranslation_coeFn a f] with x hs ht hx
    rw [ht]
    apply hs
    change x+a ∉ Icc a (a+h)
    intro hp
    linarith only [hp.1, hx]
  have he := suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2 hhalf
  rw [← inner_positiveExtension, he]
  have hi : inner ℂ
      (indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc (logTranslationCLM a f))
      (suzukiPositiveZeroExtension q) =
      inner ℂ (logTranslationCLM a f)
        (indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc (suzukiPositiveZeroExtension q)) :=
    indicatorCutoff_symmetric (Ioc (0 : ℝ) h) measurableSet_Ioc _ _
  rw [hcut] at hi
  rw [hi]
  have hn : ‖logTranslationCLM a f‖ = ‖f‖ :=
    (MellinL2.additiveTranslationUnitary a).norm_map f
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans_eq (by rw [hn])

private theorem reflected_interval_support {a h : ℝ} (f : SoninL2)
    (hf : ∀ᵐ x ∂volume, x ∉ Icc (-a-h) (-a) → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ Icc a (a+h) → l2Reflection f x = 0 := by
  have hs := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hf
  filter_upwards [hs, l2Reflection_ae f] with x hs hr hx
  rw [hr]
  apply hs
  intro hp
  apply hx
  constructor <;> linarith only [hp.1, hp.2]

private theorem scalar_collar_energy_bound {e m f k : ℝ}
    (he : 0 ≤ e) (hf : 0 ≤ f) (hk : 0 < k) (hdual : e^2 ≤ m*f) (hfloor : k*m ≤ e) :
    k*e ≤ f := by
  by_cases he0 : e = 0
  · simpa only [he0, mul_zero] using hf
  have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
  have h := (mul_le_mul_of_nonneg_left hdual hk.le).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfloor hf)
  by_contra hnot
  have hpos := mul_pos hepos (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [h, hpos]

namespace WeilHilbertBeforeContact

/-- The right exact residual pairs only with its actual collar restriction. -/
theorem norm_inner_increment_rightCollar_le {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) {h : ℝ} (z : ℂ) (u : WeilHilbertBeforeContact b)
    (hu : ∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
      ccmArchimedeanFormEmbedding b.1 (toForm b u) x = 0) :
    ‖inner ℂ u (evalVectorIncrement hab z)‖ ≤
      ‖ccmArchimedeanFormToAperture b.1 (toForm b u)‖ *
        ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
          (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hab z))‖ := by
  let f := ccmArchimedeanFormEmbedding b.1 (toForm b u)
  have hout : ∀ᵐ x ∂volume, x < a.1.1 → f x = 0 := by
    filter_upwards [hu] with x hx hout
    exact hx (fun hin => (not_le.mpr hout) hin.1)
  rw [inner_evalVectorIncrement_rightCollar hab z u _ (rightExterior_reconstruction a.1.1 f hout).symm]
  exact inner_rightCoordinate_le f hu _

/-- Reflection gives the same sharp restriction of the left actual residual. -/
theorem norm_inner_increment_leftCollar_le {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) {h : ℝ} (z : ℂ) (u : WeilHilbertBeforeContact b)
    (hu : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b u) x = 0) :
    ‖inner ℂ u (evalVectorIncrement hab z)‖ ≤
      ‖ccmArchimedeanFormToAperture b.1 (toForm b u)‖ *
        ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
          (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hab z))‖ := by
  let f := ccmArchimedeanFormEmbedding b.1 (toForm b u)
  have hout : ∀ᵐ x ∂volume, -a.1.1 < x → f x = 0 := by
    filter_upwards [hu] with x hx hout
    exact hx (fun hin => (not_le.mpr hout) hin.2)
  rw [inner_evalVectorIncrement_leftCollar hab z u _ (leftExterior_reconstruction a.1.1 f hout).symm]
  have hi := inner_rightCoordinate_le (l2Reflection f) (reflected_interval_support f hu)
    (evalVectorLeftCollarResidual hab z)
  have hn : ‖l2Reflection f‖ = ‖f‖ := l2ReflectionIsometry.norm_map f
  rw [hn] at hi
  exact hi

/-- In a fixed enclosure, the exact kernel increment obeys the full two-collar energy bound. -/
theorem norm_increment_sq_mul_collar_floor_le {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : b.1.1 = a.1.1+h)
    (z : ℂ) :
    (Real.log (1/h)-weilTwoCollarEnergyError a c)*‖evalVectorIncrement hab z‖^2 ≤
      ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
        (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual (hab.trans hbc) z))‖^2 +
      ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
        (suzukiPositiveZeroExtension (evalVectorRightCollarResidual (hab.trans hbc) z))‖^2 := by
  by_cases hk : 0 < Real.log (1/h)-weilTwoCollarEnergyError a c
  swap
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hk) (sq_nonneg _)).trans
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  let u := inclusion hbc (evalVectorIncrement hab z)
  have hu : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (a.1.1+h) →
      ccmArchimedeanFormEmbedding c.1 (toForm c u) x = 0 := by
    have he : ccmArchimedeanFormEmbedding c.1
        (apertureExt hbc (toForm b (evalVectorIncrement hab z))) =
        ccmArchimedeanFormEmbedding b.1 (toForm b (evalVectorIncrement hab z)) :=
      ccmArchimedeanFormToAperture_coe_eq_of_val_eq
        (apertureExt_val hbc (toForm b (evalVectorIncrement hab z)))
    change ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (a.1.1+h) →
      ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc (evalVectorIncrement hab z))) x = 0
    rw [toForm_inclusion, he]
    have hs : ccmArchimedeanFormEmbedding b.1 (toForm b (evalVectorIncrement hab z)) ∈
        physicalForbidden (centralInterval b.1.1) (measurableSet_centralInterval b.1.1) :=
      (ccmArchimedeanFormToAperture b.1 (toForm b (evalVectorIncrement hab z))).property
    rw [mem_physicalForbidden_iff] at hs
    simpa only [centralInterval, hb, neg_add, sub_eq_add_neg] using hs
  obtain ⟨p, l, r, he, hl, hr, hfloor⟩ :=
    exists_twoCollar_decomposition_with_floor (hab.trans hbc) hh hh1 u hu
  let X := ‖ccmArchimedeanFormToAperture c.1 (toForm c l)‖
  let Y := ‖ccmArchimedeanFormToAperture c.1 (toForm c r)‖
  let P := ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
    (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual (hab.trans hbc) z))‖
  let Q := ‖indicatorCutoff (Ioc (0 : ℝ) h) measurableSet_Ioc
    (suzukiPositiveZeroExtension (evalVectorRightCollarResidual (hab.trans hbc) z))‖
  have hlpair : ‖inner ℂ l (evalVectorIncrement (hab.trans hbc) z)‖ ≤ X*P :=
    norm_inner_increment_leftCollar_le (hab.trans hbc) z l hl
  have hrpair : ‖inner ℂ r (evalVectorIncrement (hab.trans hbc) z)‖ ≤ Y*Q :=
    norm_inner_increment_rightCollar_le (hab.trans hbc) z r hr
  have hp : inner ℂ (inclusion (hab.trans hbc) p) (evalVectorIncrement (hab.trans hbc) z) = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (E := WeilHilbertBeforeContact c),
      inner_evalVectorIncrement_inclusion, map_zero]
  have huPair : (inner ℂ u (evalVectorIncrement (hab.trans hbc) z)).re =
      ‖evalVectorIncrement hab z‖^2 := by
    rw [inner_inclusion_evalVectorIncrement hab hbc z]
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
      (E := WeilHilbertBeforeContact b) _).symm
  have hpair : ‖evalVectorIncrement hab z‖^2 ≤ X*P+Y*Q := by
    rw [← huPair, he, inner_add_left (E := WeilHilbertBeforeContact c),
      inner_add_left (E := WeilHilbertBeforeContact c), hp, add_zero, Complex.add_re]
    have hlre := (Complex.re_le_norm (inner ℂ l (evalVectorIncrement (hab.trans hbc) z))).trans hlpair
    have hrre := (Complex.re_le_norm (inner ℂ r (evalVectorIncrement (hab.trans hbc) z))).trans hrpair
    linarith only [hlre, hrre]
  have hdual : (‖evalVectorIncrement hab z‖^2)^2 ≤ (X^2+Y^2)*(P^2+Q^2) := by
    have hnonneg : 0 ≤ X*P+Y*Q := add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hs := (sq_le_sq₀ (sq_nonneg _) hnonneg).mpr hpair
    nlinarith only [hs, sq_nonneg (X*Q-Y*P)]
  have hn : ‖u‖^2 = ‖evalVectorIncrement hab z‖^2 := by
    dsimp only [u]
    rw [(inclusion hbc).norm_map]
  rw [hn] at hfloor
  exact scalar_collar_energy_bound (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    hk hdual hfloor

#print axioms norm_increment_sq_mul_collar_floor_le
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
