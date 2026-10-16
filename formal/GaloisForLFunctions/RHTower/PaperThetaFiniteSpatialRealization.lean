import GaloisForLFunctions.HTGeometry.LoweringChainIndependence
import GaloisForLFunctions.RHTower.PaperThetaSpatialModule
import GaloisForLFunctions.RHTower.PaperThetaConfluentAdmission
import GaloisForLFunctions.RHTower.DeningerMeyerHedenmalmSourceRealization

/-! # Faithful finite source realization in native theta functions

Every full Xi multiplicity is retained in the literal spatial theta module.
The same chain coordinates synthesize original Meyer source classes and
native theta functions, whose compact representatives are actually AC.
-/

noncomputable section
open Complex Set Filter Topology
open scoped Classical

namespace RHTower.PaperThetaEndpoint
open GaloisForLFunctions.HTGeometry HedenmalmThetaSource HedenmalmQuantile

theorem thetaFiniteHasseJets_linearIndependent (S : Finset XiDivisorSupport) :
    LinearIndependent ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
      thetaRightHasseJet (xiSpectralPointSupport q.1.1) q.2.val) := by
  apply generalizedLoweringChains_linearIndependent thetaSpatialGenerator
    (fun rho : ↥S => xiSpectralPointSupport rho.1)
    (fun _ _ h => Subtype.ext (xiSpectralPointSupport_injective h))
    (fun rho n => thetaRightHasseJet (xiSpectralPointSupport rho.1) n)
    (fun rho => xiSupportMultiplicity rho.1)
  · intro rho
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      thetaSpatialGenerator_hasse_zero, sub_self]
  · intro rho n
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      thetaSpatialGenerator_hasse_succ, add_sub_cancel_left]
  · exact fun rho => thetaRightHasseJet_zero_ne_zero _

def thetaFiniteSynthesis (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] thetaRightJetSpace :=
  Fintype.linearCombination ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
    thetaRightHasseJet (xiSpectralPointSupport q.1.1) q.2.val)

theorem thetaFiniteSynthesis_injective (S : Finset XiDivisorSupport) :
    Function.Injective (thetaFiniteSynthesis S) :=
  (thetaFiniteHasseJets_linearIndependent S).fintypeLinearCombination_injective

/-- Every full-multiplicity slot survives in the space of actual functions. -/
theorem thetaFiniteSynthesis_finrank (S : Finset XiDivisorSupport) :
    Module.finrank ℂ (LinearMap.range (thetaFiniteSynthesis S)) =
      Fintype.card (DeningerMeyerFiniteXiJetSlot S) := by
  rw [LinearMap.finrank_range_of_inj (thetaFiniteSynthesis_injective S)]
  exact Module.finrank_pi ℂ

def meyerFiniteHedenmalmSynthesis (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] DeningerMeyerStrongLogCohomology :=
  Fintype.linearCombination ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
    deningerMeyerHedenmalmClass q.1.1 ⟨q.2.val+1, by omega⟩)

private def reverseSlot (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetSlot S ≃ DeningerMeyerFiniteXiJetSlot S where
  toFun q := ⟨q.1, q.2.rev⟩
  invFun q := ⟨q.1, q.2.rev⟩
  left_inv q := by cases q; simp
  right_inv q := by cases q; simp

private theorem hedenmalmClass_eq_reversed (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerHedenmalmClass rho ⟨j.val+1, by omega⟩ =
      Complex.I^(j.val+1) • deningerMeyerXiJetSource rho j.rev := by
  rw [deningerMeyerHedenmalmClass_eq, deningerMeyerXiJetSource]
  have hj : xiSupportMultiplicity rho-j.rev.val = j.val+1 := by
    simp only [Fin.val_rev]
    omega
  simp only [hj]

theorem meyerFiniteHedenmalmSynthesis_injective (S : Finset XiDivisorSupport) :
    Function.Injective (meyerFiniteHedenmalmSynthesis S) := by
  have h := (deningerMeyerFiniteXiCausalSources_linearIndependent S).comp
    (reverseSlot S) (reverseSlot S).injective
  have hli : LinearIndependent ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
      deningerMeyerHedenmalmClass q.1.1 ⟨q.2.val+1, by omega⟩) := by
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro c hc q
    simp only [hedenmalmClass_eq_reversed, smul_smul] at hc
    have he := h (fun q => c q * Complex.I^(q.2.val+1)) hc q
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ I_ne_zero)
  exact hli.fintypeLinearCombination_injective

def thetaFiniteCoordinates (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S ≃ₗ[ℂ] LinearMap.range (thetaFiniteSynthesis S) :=
  LinearEquiv.ofInjective _ (thetaFiniteSynthesis_injective S)

def meyerFiniteHedenmalmCoordinates (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S ≃ₗ[ℂ] LinearMap.range (meyerFiniteHedenmalmSynthesis S) :=
  LinearEquiv.ofInjective _ (meyerFiniteHedenmalmSynthesis_injective S)

/-- Full-multiplicity comparison of actual source classes with literal native functions. -/
def meyerThetaFiniteEquiv (S : Finset XiDivisorSupport) :
    LinearMap.range (meyerFiniteHedenmalmSynthesis S) ≃ₗ[ℂ]
      LinearMap.range (thetaFiniteSynthesis S) :=
  (meyerFiniteHedenmalmCoordinates S).symm.trans (thetaFiniteCoordinates S)

/-- The compact representative uses the same actual parameter jets and coefficients. -/
def thetaFiniteCompact (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (t : ℝ) : ℂ :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S,
    (c q * (q.2.val.factorial : ℂ)⁻¹) • closedParameterJet q.2.val
      (xiSpectralPointSupport q.1.1) t

theorem thetaFiniteCompact_interior (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (t : Ioo (0 : ℝ) 1) :
    thetaFiniteCompact S c t.val =
      (thetaFiniteSynthesis S c).val (thetaSource.quantileFun t.val) := by
  simp only [thetaFiniteCompact, thetaFiniteSynthesis, Fintype.linearCombination_apply,
    Submodule.coe_sum, Submodule.coe_smul, thetaRightHasseJet, thetaRightJet,
    Finset.sum_apply, Pi.smul_apply, smul_smul, closedParameterJet_interior]

theorem absolutelyContinuousOnInterval_thetaFiniteCompact (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    AbsolutelyContinuousOnInterval (thetaFiniteCompact S c) 0 1 := by
  have hsum (s : Finset (DeningerMeyerFiniteXiJetSlot S)) :
      AbsolutelyContinuousOnInterval (fun t => ∑ q ∈ s,
        (c q * (q.2.val.factorial : ℂ)⁻¹) • closedParameterJet q.2.val
          (xiSpectralPointSupport q.1.1) t) 0 1 := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using (LipschitzWith.const (0 : ℂ)).lipschitzOnWith.absolutelyContinuousOnInterval
          (a := (0 : ℝ)) (b := 1)
    | insert q s hq ih =>
        simpa only [AbsolutelyContinuousOnInterval, Finset.sum_insert hq, Pi.add_apply] using
          ((absolutelyContinuousOnInterval_divisor_closedParameterJet q.1.1 q.2).const_smul
            (c q * (q.2.val.factorial : ℂ)⁻¹)).add ih
  exact hsum Finset.univ

end RHTower.PaperThetaEndpoint
