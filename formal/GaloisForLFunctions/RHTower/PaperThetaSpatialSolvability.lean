import GaloisForLFunctions.RHTower.PaperThetaMeyerSpatialTransport
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-! # Native inhomogeneous theta equations with full multiplicities

Every finite word of imaginary spectral shifts is bijective on each actual
finite Xi packet. Its solutions are literal theta functions with admitted
compact AC representatives, and the Meyer comparison transports the same
equations. No spectral simplicity, positivity or RH premise is used.
-/

noncomputable section
open Complex Set
open scoped Classical

namespace RHTower.PaperThetaEndpoint
open GaloisForLFunctions.HTGeometry HedenmalmThetaSource HedenmalmQuantile

private theorem shiftedSynthesis_injective (S : Finset XiDivisorSupport) (t : ℝ) :
    Function.Injective
      ((thetaSpatialGenerator - (I*(t:ℂ)) • LinearMap.id).comp (thetaFiniteSynthesis S)) := by
  have hnr (rho : ↥S) : xiSpectralPointSupport rho.1 - I*(t:ℂ) ≠ 0 := by
    intro hh
    have hfreq : (xiSpectralPointSupport rho.1).re ≠ 0 := by
      simpa [xiSpectralPointSupport, mul_re] using xi_divisor_support_im_ne_zero rho.1
    apply hfreq
    have he := congrArg Complex.re (sub_eq_zero.mp hh)
    simpa using he
  have hli := generalizedLoweringChains_shift_linearIndependent thetaSpatialGenerator
    (fun rho : ↥S => xiSpectralPointSupport rho.1)
    (fun _ _ h => Subtype.ext (xiSpectralPointSupport_injective h))
    (fun rho n => thetaRightHasseJet (xiSpectralPointSupport rho.1) n)
    (fun rho => xiSupportMultiplicity rho.1)
    (fun rho => by simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      thetaSpatialGenerator_hasse_zero, sub_self])
    (fun rho n => by simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      thetaSpatialGenerator_hasse_succ, add_sub_cancel_left])
    (fun rho => thetaRightHasseJet_zero_ne_zero _) (I*(t:ℂ)) hnr
  have he :
      (thetaSpatialGenerator - (I*(t:ℂ)) • LinearMap.id).comp (thetaFiniteSynthesis S) =
      Fintype.linearCombination ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
        (thetaSpatialGenerator - (I*(t:ℂ)) • LinearMap.id : Module.End ℂ thetaRightJetSpace)
          (thetaRightHasseJet (xiSpectralPointSupport q.1.1) q.2.val)) := by
    ext c
    simp only [LinearMap.comp_apply, thetaFiniteSynthesis, Fintype.linearCombination_apply,
      map_sum, map_smul]
  rw [he]
  exact hli.fintypeLinearCombination_injective

/-- Every imaginary shift is invertible on the actual finite native differential module. -/
theorem thetaFiniteSpatialImaginaryShift_bijective (S : Finset XiDivisorSupport) (t : ℝ) :
    Function.Bijective (deningerMeyerGeneratorWord
      (V := LinearMap.range (thetaFiniteSynthesis S)) (thetaFiniteSpatialGenerator S)
        [Complex.I*(t:ℂ)]) := by
  have hinj : Function.Injective
      (deningerMeyerGeneratorWord (V := LinearMap.range (thetaFiniteSynthesis S))
        (thetaFiniteSpatialGenerator S) [Complex.I*(t:ℂ)]) := by
    intro f g hfg
    obtain ⟨c, hc⟩ := f.property
    obtain ⟨d, hd⟩ := g.property
    have he := congrArg Subtype.val hfg
    change (thetaSpatialGenerator - (I*(t:ℂ)) • LinearMap.id : Module.End ℂ thetaRightJetSpace)
      f.val = (thetaSpatialGenerator - (I*(t:ℂ)) • LinearMap.id : Module.End ℂ thetaRightJetSpace)
        g.val at he
    have hcd : c = d := shiftedSynthesis_injective S t (by simpa only [LinearMap.comp_apply, hc, hd] using he)
    apply Subtype.ext
    rw [← hc, ← hd, hcd]
  exact ⟨hinj, (LinearMap.injective_iff_surjective
    (K := ℂ) (V := LinearMap.range (thetaFiniteSynthesis S))
    (f := deningerMeyerGeneratorWord (V := LinearMap.range (thetaFiniteSynthesis S))
      (thetaFiniteSpatialGenerator S) [Complex.I*(t:ℂ)])).mp hinj⟩

theorem thetaFiniteSpatialImaginaryWord_bijective (S : Finset XiDivisorSupport) (L : List ℝ) :
    Function.Bijective (deningerMeyerGeneratorWord
      (V := LinearMap.range (thetaFiniteSynthesis S)) (thetaFiniteSpatialGenerator S)
      (L.map fun t : ℝ => Complex.I*(t:ℂ))) := by
  induction L with
  | nil => exact Function.bijective_id
  | cons t L ih =>
      exact (thetaFiniteSpatialImaginaryShift_bijective S t).comp ih

/-- Arbitrary admitted finite forcing has one native solution for every imaginary-shift word.
The equation is the literal differential expression on functions, not a matrix equation. -/
theorem thetaSpatialWord_existsUnique (S : Finset XiDivisorSupport) (L : List ℝ)
    (f : LinearMap.range (thetaFiniteSynthesis S)) :
    ∃! u : LinearMap.range (thetaFiniteSynthesis S),
      thetaSpatialWord (L.map fun t : ℝ => Complex.I*(t:ℂ)) u.val.val = f.val.val := by
  obtain ⟨u, hu, huniq⟩ := (thetaFiniteSpatialImaginaryWord_bijective S L).existsUnique f
  refine ⟨u, ?_, ?_⟩
  · change thetaSpatialWord (L.map fun t : ℝ => Complex.I*(t:ℂ)) u.val.val = f.val.val
    rw [← thetaFiniteSpatialWord_literal, hu]
  · intro v hv
    apply huniq v
    apply Subtype.ext
    apply Subtype.ext
    simpa only [thetaFiniteSpatialWord_literal] using hv

def thetaFiniteCompactRepresentative (S : Finset XiDivisorSupport)
    (f : LinearMap.range (thetaFiniteSynthesis S)) : ℝ → ℂ :=
  thetaFiniteCompact S ((thetaFiniteCoordinates S).symm f)

theorem thetaFiniteCompactRepresentative_interior (S : Finset XiDivisorSupport)
    (f : LinearMap.range (thetaFiniteSynthesis S)) (t : Ioo (0 : ℝ) 1) :
    thetaFiniteCompactRepresentative S f t.val = f.val.val (thetaSource.quantileFun t.val) := by
  rw [thetaFiniteCompactRepresentative, thetaFiniteCompact_interior]
  have he := congrArg Subtype.val ((thetaFiniteCoordinates S).apply_symm_apply f)
  exact congrArg (fun g : thetaRightJetSpace => g.val (thetaSource.quantileFun t.val)) he

theorem absolutelyContinuousOnInterval_thetaFiniteCompactRepresentative
    (S : Finset XiDivisorSupport) (f : LinearMap.range (thetaFiniteSynthesis S)) :
    AbsolutelyContinuousOnInterval (thetaFiniteCompactRepresentative S f) 0 1 :=
  absolutelyContinuousOnInterval_thetaFiniteCompact S _

/-- The entire solution class is admitted in the compact native domain, unconditionally. -/
theorem thetaSpatialWord_existsUnique_admitted (S : Finset XiDivisorSupport) (L : List ℝ)
    (f : LinearMap.range (thetaFiniteSynthesis S)) :
    ∃! u : LinearMap.range (thetaFiniteSynthesis S),
      thetaSpatialWord (L.map fun t : ℝ => Complex.I*(t:ℂ)) u.val.val = f.val.val ∧
        AbsolutelyContinuousOnInterval (thetaFiniteCompactRepresentative S u) 0 1 := by
  obtain ⟨u, hu, huniq⟩ := thetaSpatialWord_existsUnique S L f
  exact ⟨u, ⟨hu, absolutelyContinuousOnInterval_thetaFiniteCompactRepresentative S u⟩,
    fun v hv => huniq v hv.1⟩

end RHTower.PaperThetaEndpoint
