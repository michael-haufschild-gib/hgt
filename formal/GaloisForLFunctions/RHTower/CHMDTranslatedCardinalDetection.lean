import GaloisForLFunctions.RHTower.CHMDTranslatedRelativeGraph
import GaloisForLFunctions.RHTower.CHMDShiftedFourierReadout
import GaloisForLFunctions.RHTower.CHMDUniversalCardinalPairing

/-!
# Full Fourier detection by actual translated cardinal graph sources

Both cardinal sources admit every sufficiently small translation in the original
complete graph. Their universal pairings recover the phase-shifted cosine sample.
Consequently the full signed radical has zero Fourier samples at all Xi zeros,
with no parity assumption.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDTranslation

/-- The detecting vectors are constructed, including their literal translated sources. -/
theorem exists_translatedCardinalFrame {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) (ht : |t| ≤ CHMDThetaTranslate.radius) :
    ∃ u v : SourceGraph,
      u.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).re) t) ∧
      v.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).im) t) ∧
      (∀ p, sourcePair p u = cardinalOrbitMass a * (shiftedCosineReadout p a t).re) ∧
      (∀ p, sourcePair p v = cardinalOrbitMass a * (shiftedCosineReadout p a t).im) := by
  obtain ⟨F⟩ := exists_cardinalGraphFrame ha hz
  obtain ⟨_, hj, ⟨C, hC⟩, _, M, hM⟩ := divisorCardinalSource_regularity ha hz
  simp_rw [thetaCuspFullSource_eq_riemannKernelReal] at hM
  have hrl : ∃ A, LipschitzWith A (fun x => (divisorCardinalSource a x).re) :=
    ⟨1*C, RCLike.lipschitzWith_re.comp hC⟩
  have hil : ∃ A, LipschitzWith A (fun x => (divisorCardinalSource a x).im) :=
    ⟨1*C, RCLike.lipschitzWith_im.comp hC⟩
  have hrb : ∃ M, ∀ x, |(divisorCardinalSource a x).re| ≤ M * riemannKernelReal x :=
    ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩
  have hib : ∃ M, ∀ x, |(divisorCardinalSource a x).im| ≤ M * riemannKernelReal x :=
    ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩
  obtain ⟨u, hu, hus⟩ := exists_graph_translate hj.re.1 hrl hrb F.re_source t
    (CHMDThetaTranslate.small_shift ht)
  obtain ⟨v, hv, hvs⟩ := exists_graph_translate hj.im.1 hil hib F.im_source t
    (CHMDThetaTranslate.small_shift ht)
  have hstrip := (abs_im_lt_half_of_XiC_eq_zero hz).le
  refine ⟨u, v, hus, hvs, ?_, ?_⟩
  · have he : (fun p => sourcePair p u) =
        (fun p => cardinalOrbitMass a * (shiftedCosineReadout p a t).re) := by
      apply Continuous.ext_on dense_compactTests
        (continuous_sourcePair.comp (continuous_id.prodMk continuous_const))
        (continuous_const.mul (Complex.continuous_re.comp (continuous_shiftedCosineReadout hstrip t)))
      rintro p ⟨w, hw, hc, rfl⟩
      dsimp only [Function.comp_def, id_eq, Pi.mul_apply]
      rw [← testLift_phi w hw hc, sourcePair_symm,
        graph_translate_pair_test hj.re.1 hrl hrb F.re_source t hu,
        sourcePair_symm, F.pair_re ha hz,
        graphCosineReadout_translate_test (contDiff_phiDoobTest hw)
          (hasCompactSupport_phiDoobTest hc) hstrip]
    exact fun p => congrFun he p
  · have he : (fun p => sourcePair p v) =
        (fun p => cardinalOrbitMass a * (shiftedCosineReadout p a t).im) := by
      apply Continuous.ext_on dense_compactTests
        (continuous_sourcePair.comp (continuous_id.prodMk continuous_const))
        (continuous_const.mul (Complex.continuous_im.comp (continuous_shiftedCosineReadout hstrip t)))
      rintro p ⟨w, hw, hc, rfl⟩
      dsimp only [Function.comp_def, id_eq, Pi.mul_apply]
      rw [← testLift_phi w hw hc, sourcePair_symm,
        graph_translate_pair_test hj.im.1 hil hib F.im_source t hv,
        sourcePair_symm, F.pair_im ha hz,
        graphCosineReadout_translate_test (contDiff_phiDoobTest hw)
          (hasCompactSupport_phiDoobTest hc) hstrip]
    exact fun p => congrFun he p

theorem radical_shiftedCosineReadout_zero {p : SourceGraph} (hp : p ∈ signedRadical)
    {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) {t : ℝ}
    (ht : |t| ≤ CHMDThetaTranslate.radius) : shiftedCosineReadout p a t = 0 := by
  obtain ⟨u, v, _, _, hu, hv⟩ := exists_translatedCardinalFrame ha hz t ht
  have hr := hp u
  have hi := hp v
  rw [hu] at hr
  rw [hv] at hi
  have hm := (cardinalOrbitMass_pos ha hz).ne'
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_left hm
  · exact (mul_eq_zero.mp hi).resolve_left hm

theorem radical_graphFourierReadout_zero_of_pos {p : SourceGraph} (hp : p ∈ signedRadical)
    {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    graphFourierReadout p a = 0 ∧ graphFourierReadout p (-a) = 0 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  exact shiftedCosineReadout_separates p hn CHMDThetaTranslate.radius_pos
    (fun _ ht => radical_shiftedCosineReadout_zero hp ha hz ht)

/-- No evenness, regularity, frame existence, or spectral synthesis premise. -/
theorem radical_graphFourierReadout_zero {p : SourceGraph} (hp : p ∈ signedRadical)
    {a : ℂ} (hz : XiC a = 0) : graphFourierReadout p a = 0 := by
  rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with hneg | hpos
  · have hza : XiC (-a) = 0 := by rw [XiC_even, hz]
    have h := (radical_graphFourierReadout_zero_of_pos hp
      (a := -a) (by simpa using neg_pos.mpr hneg) hza).2
    simpa only [neg_neg] using h
  · exact (radical_graphFourierReadout_zero_of_pos hp hpos hz).1

end RHTower.CHMDDoobGraph
