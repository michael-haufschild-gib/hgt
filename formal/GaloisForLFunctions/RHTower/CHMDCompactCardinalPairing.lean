import GaloisForLFunctions.RHTower.CHMDCompactSourceClass
import GaloisForLFunctions.RHTower.CHMDCosineSourceFourier
import GaloisForLFunctions.RHTower.CHMDCardinalIncidencePairing

/-!
# Mixed compact/cardinal pairings with explicit summability

Cardinal support makes both cross terms finite. The compact diagonal remains
summable by the unconditional explicit formula. Only after establishing these
facts do we distribute the full zero sum and polarize it.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open WeilSpectral CHMDStage16

def paperCosineReadout (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  (paperFT (fun x => (f x : ℂ)) z + paperFT (fun x => (f x : ℂ)) (-z))/2

theorem paperCosineReadout_neg (f : ℝ → ℝ) (z : ℂ) :
    paperCosineReadout f (-z) = paperCosineReadout f z := by
  simp only [paperCosineReadout, neg_neg]
  ring

theorem paperCosineReadout_conj (f : ℝ → ℝ) (z : ℂ) :
    paperCosineReadout f (conj z) = conj (paperCosineReadout f z) := by
  simp only [paperCosineReadout, map_div₀, map_add, map_ofNat,
    conj_paperFT_ofReal, map_neg, neg_neg]
  ring

theorem cardinalRealSource_expMoment {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) (c : ℂ) :
    ExpMomentSource (fun x => (cardinalRealSource a c x : ℂ)) :=
  ((divisorCardinalSource_regularity ha hz).1.const_mul c).ofReal_re

theorem paperFT_ofReal_add {f g : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ)))
    (hg : ExpMomentSource (fun x => (g x : ℂ))) (z : ℂ) :
    paperFT (fun x => ((f+g) x : ℂ)) z =
      paperFT (fun x => (f x : ℂ)) z + paperFT (fun x => (g x : ℂ)) z := by
  simpa only [Pi.add_apply, Complex.ofReal_add] using paperFT_add_sources hf hg z

def cardinalCrossSummand (f : ℝ → ℝ) (a c : ℂ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  2 * (zetaZeroConfig.mult ρ : ℂ) *
    (paperCosineReadout f (gammaOf ρ) * cardinalOrbitValue a c (gammaOf ρ))

theorem summable_cardinalCrossSummand (f : ℝ → ℝ) (a c : ℂ) :
    Summable (cardinalCrossSummand f a c) := by
  apply summable_of_cardinalOrbit_support (a := a)
  intro ρ hρ
  simp [cardinalCrossSummand, cardinalOrbitValue_eq_zero hρ]

theorem Wsummand_add_cardinal {f : ℝ → ℝ} {a : ℂ}
    (ha : 0 < a.re) (hz : XiC a = 0)
    (hf : ExpMomentSource (fun x => (f x : ℂ))) (c : ℂ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun x => ((f+cardinalRealSource a c) x : ℂ))
      (fun x => ((f+cardinalRealSource a c) x : ℂ)) ρ =
    zetaZeroConfig.Wsummand (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) ρ +
    zetaZeroConfig.Wsummand (fun x => (cardinalRealSource a c x : ℂ))
      (fun x => (cardinalRealSource a c x : ℂ)) ρ + cardinalCrossSummand f a c ρ := by
  have hzero := XiC_gammaOf_eq_zero ρ
  have hconj : XiC (conj (gammaOf ρ)) = 0 := by rw [XiC_conj, hzero, map_zero]
  have hfc := conj_paperFT_ofReal f (conj (gammaOf ρ))
  simp only [conj_conj] at hfc
  simp only [ZeroConfig.Wsummand,
    paperFT_ofReal_add hf (cardinalRealSource_expMoment ha hz c),
    cardinalRealSource_paperFT ha hz c hzero, cardinalRealSource_paperFT ha hz c hconj,
    map_add, cardinalOrbitValue_conj, conj_conj, hfc,
    cardinalCrossSummand, paperCosineReadout]
  ring

theorem cardinalCrossSum_re (f : ℝ → ℝ) (a c : ℂ) :
    (∑' ρ, cardinalCrossSummand f a c ρ).re =
      2 * cardinalOrbitMass a * (c * paperCosineReadout f a).re := by
  rw [Complex.re_tsum (summable_cardinalCrossSummand f a c)]
  have heq (ρ : zetaZeroConfig.carrier) : (cardinalCrossSummand f a c ρ).re =
      2 * ((zetaZeroConfig.mult ρ : ℝ) *
        (paperCosineReadout f (gammaOf ρ) * cardinalOrbitValue a c (gammaOf ρ)).re) := by
    simp [cardinalCrossSummand, Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [heq]
  rw [tsum_mul_left, tsum_cardinalOrbitValue_mul_readout_re
    (paperCosineReadout_neg f) (paperCosineReadout_conj f)]
  ring

namespace CHMDDoobGraph

theorem signedZeroPair_cardinal {f : ℝ → ℝ} {a : ℂ}
    (ha : 0 < a.re) (hz : XiC a = 0)
    (hf : ExpMomentSource (fun x => (f x : ℂ)))
    (hff : Summable (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) ρ)) (c : ℂ) :
    signedZeroPair f (cardinalRealSource a c) =
      cardinalOrbitMass a * (c * paperCosineReadout f a).re := by
  have hg := cardinalRealSource_expMoment ha hz c
  have hgg := summable_cardinalRealSource_W ha hz c
  have hcross := summable_cardinalCrossSummand f a c
  have hW : zetaZeroConfig.W (fun x => ((f+cardinalRealSource a c) x : ℂ))
      (fun x => ((f+cardinalRealSource a c) x : ℂ)) =
      zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) +
      zetaZeroConfig.W (fun x => (cardinalRealSource a c x : ℂ))
        (fun x => (cardinalRealSource a c x : ℂ)) + ∑' ρ, cardinalCrossSummand f a c ρ := by
    unfold ZeroConfig.W
    simp_rw [Wsummand_add_cardinal ha hz hf c]
    rw [(hff.add hgg).tsum_add hcross, hff.tsum_add hgg]
  obtain ⟨hp, hm⟩ := cardinalRealSource_poles ha hz c
  unfold signedZeroPair signedZeroEnergy
  rw [hW]
  simp only [paperFT_ofReal_add hf hg, hp, hm, add_zero, map_zero,
    mul_zero, Complex.add_re, Complex.zero_re, sub_zero]
  rw [cardinalCrossSum_re]
  ring

theorem signedZeroPair_compact_cardinal {f : ℝ → ℝ} {a : ℂ}
    (ha : 0 < a.re) (hz : XiC a = 0) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (c : ℂ) :
    signedZeroPair f (cardinalRealSource a c) =
      cardinalOrbitMass a * (c * paperCosineReadout f a).re := by
  have hfC : ContDiff ℝ 2 (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcC : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  exact signedZeroPair_cardinal ha hz (compact_expMomentSource hfC.continuous hcC)
    (WeilConditional.summable_Wsummand hfC hcC) c

theorem graphCosineReadout_testLift {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (z : ℂ) :
    graphCosineReadout (testLift f hf hc) z = paperCosineReadout f z := by
  exact graphCosineReadout_of_source_eq_half
    (compact_expMomentSource (Complex.continuous_ofReal.comp hf.continuous)
      (hc.comp_left Complex.ofReal_zero)) (testLift_source f hf hc) z

theorem CardinalGraphFrame.compact_pair {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair (testLift f hf hc) F.reVector =
        cardinalOrbitMass a * (graphCosineReadout (testLift f hf hc) a).re ∧
      sourcePair (testLift f hf hc) F.imVector =
        cardinalOrbitMass a * (graphCosineReadout (testLift f hf hc) a).im := by
  obtain ⟨_, hj, ⟨L, hL⟩, _, ⟨M, hM⟩⟩ := divisorCardinalSource_regularity ha hz
  simp_rw [thetaCuspFullSource_eq_riemannKernelReal] at hM
  have hr : cardinalRealSource a 1 = fun x => (divisorCardinalSource a x).re := by
    funext x
    simp [cardinalRealSource]
  have hi : cardinalRealSource a (-I) = fun x => (divisorCardinalSource a x).im := by
    funext x
    simp [cardinalRealSource, Complex.mul_re]
  constructor
  · rw [sourcePair_eq_signedZeroPair (compact_expDecayTest hf hc) hj.re
      (compact_source_lipschitz hf hc) ⟨1*L, RCLike.lipschitzWith_re.comp hL⟩
      (compact_source_thetaBound hf.continuous hc)
      ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩ (testLift_source f hf hc) F.re_source,
      ← hr, signedZeroPair_compact_cardinal ha hz hf hc, graphCosineReadout_testLift]
    simp
  · rw [sourcePair_eq_signedZeroPair (compact_expDecayTest hf hc) hj.im
      (compact_source_lipschitz hf hc) ⟨1*L, RCLike.lipschitzWith_im.comp hL⟩
      (compact_source_thetaBound hf.continuous hc)
      ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩ (testLift_source f hf hc) F.im_source,
      ← hi, signedZeroPair_compact_cardinal ha hz hf hc, graphCosineReadout_testLift]
    simp

end CHMDDoobGraph
end RHTower
