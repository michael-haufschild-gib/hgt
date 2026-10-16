import GaloisForLFunctions.RHTower.DeningerMeyerGaugeJets
import GaloisForLFunctions.RHTower.PaperThetaSpatialSolvability

/-! # Native theta solutions for global source convolution gauges

Global exponential convolution, constructed in the original all-weight
Meyer source, preserves every full-multiplicity finite native packet. Its
inverse therefore produces actual compact AC theta solutions. The packet
invariance is proved from the full jet formula and global Xi synthesis.
-/

noncomputable section
open Complex Set
open scoped Classical
namespace RHTower.PaperThetaEndpoint

private theorem hedenmalm_other_zero (rho tau : XiDivisorSupport) (hne : tau ≠ rho)
    (k : Fin (xiSupportMultiplicity rho+1)) (j : DeningerArithmeticJetIndex tau) :
    deningerMeyerXiSupportJetEvaluationLM tau j (deningerMeyerHedenmalmClass rho k) = 0 := by
  rw [deningerMeyerHedenmalmClass_eq, map_smul, deningerMeyerXiCausalClass,
    deningerMeyerXiSupportJetEvaluationLM_mk, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have hz := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho k.val (Nat.le_of_lt_succ k.isLt)).property
      _ (Set.mem_univ _))).mp
        (deningerMeyerXiCausalSource_order_other rho tau hne k.val (Nat.le_of_lt_succ k.isLt))
  simp only [hz.1 j.val j.isLt, smul_zero]

private theorem synthesis_other_zero (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (rho : XiDivisorSupport) (hrho : rho ∉ S)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (meyerFiniteHedenmalmSynthesis S c) = 0 := by
  simp only [meyerFiniteHedenmalmSynthesis, Fintype.linearCombination_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro q _
  rw [hedenmalm_other_zero q.1.1 rho (by intro he; exact hrho (he.symm ▸ q.1.2)), smul_zero]

private def synthesisJets (S : Finset XiDivisorSupport) :
    Module.End ℂ (DeningerMeyerFiniteXiJetPacket S) :=
  (deningerMeyerFiniteXiJetPacketLM S).comp (meyerFiniteHedenmalmSynthesis S)

private theorem synthesisJets_injective (S : Finset XiDivisorSupport) :
    Function.Injective (synthesisJets S) := by
  intro a b hab
  apply meyerFiniteHedenmalmSynthesis_injective S
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  by_cases hrho : rho ∈ S
  · exact congrFun hab ⟨⟨rho, hrho⟩, j⟩
  · rw [synthesis_other_zero S a rho hrho, synthesis_other_zero S b rho hrho]

/-- Exact characterization in actual cohomology, including every multiplicity slot. -/
theorem mem_meyerFiniteHedenmalmRange_iff (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    u ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis S) ↔
      ∀ rho ∉ S, ∀ j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0 := by
  refine ⟨?_, fun hu => ?_⟩
  · rintro ⟨c, rfl⟩
    exact synthesis_other_zero S c
  · have hsurj := (LinearMap.injective_iff_surjective (K := ℂ)
        (V := DeningerMeyerFiniteXiJetPacket S) (f := synthesisJets S)).mp
      (synthesisJets_injective S)
    obtain ⟨c, hc⟩ := hsurj (deningerMeyerFiniteXiJetPacketLM S u)
    refine ⟨c, deningerMeyerCohomology_eq_of_XiJets_eq fun rho j => ?_⟩
    by_cases hrho : rho ∈ S
    · exact congrFun hc ⟨⟨rho, hrho⟩, j⟩
    · rw [synthesis_other_zero S c rho hrho, hu rho hrho j]

theorem meyerFiniteSourceGauge_mem (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    deningerMeyerCohomologySourceGauge g u ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis S) := by
  apply (mem_meyerFiniteHedenmalmRange_iff S _).mpr
  intro rho hrho
  exact deningerMeyerSourceGauge_preserves_zero_packet g rho u
    ((mem_meyerFiniteHedenmalmRange_iff S u).mp u.property rho hrho)

def meyerFiniteSourceGaugeEquiv (S : Finset XiDivisorSupport) (g : DeningerMeyerStrongLogTarget) :
    LinearMap.range (meyerFiniteHedenmalmSynthesis S) ≃ₗ[ℂ]
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) where
  toFun u := ⟨deningerMeyerCohomologySourceGauge g u, meyerFiniteSourceGauge_mem S g u⟩
  invFun u := ⟨deningerMeyerCohomologySourceGauge (-g) u, meyerFiniteSourceGauge_mem S (-g) u⟩
  left_inv u := Subtype.ext ((deningerMeyerCohomologySourceGaugeEquiv g).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((deningerMeyerCohomologySourceGaugeEquiv g).apply_symm_apply u.val)
  map_add' u v := Subtype.ext ((deningerMeyerCohomologySourceGauge g).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((deningerMeyerCohomologySourceGauge g).map_smul c u.val)

/-- Full native realization of the globally admitted convolution gauge. -/
def thetaFiniteConvolutionGauge (S : Finset XiDivisorSupport) (g : DeningerMeyerStrongLogTarget) :
    LinearMap.range (thetaFiniteSynthesis S) ≃ₗ[ℂ] LinearMap.range (thetaFiniteSynthesis S) :=
  (meyerThetaFiniteEquiv S).symm.trans
    ((meyerFiniteSourceGaugeEquiv S g).trans (meyerThetaFiniteEquiv S))

/-- Native realization agrees with the genuine original-source operator. -/
theorem thetaFiniteConvolutionGauge_original (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (u : LinearMap.range (thetaFiniteSynthesis S)) :
    ((meyerThetaFiniteEquiv S).symm (thetaFiniteConvolutionGauge S g u)).val =
      deningerMeyerCohomologySourceGauge g ((meyerThetaFiniteEquiv S).symm u).val := by
  simp only [thetaFiniteConvolutionGauge, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- Every forcing in every admitted finite native packet has one actual compact AC solution. -/
theorem thetaConvolutionEquation_existsUnique_admitted (S : Finset XiDivisorSupport)
    (g : DeningerMeyerStrongLogTarget) (f : LinearMap.range (thetaFiniteSynthesis S)) :
    ∃! u : LinearMap.range (thetaFiniteSynthesis S),
      (thetaFiniteConvolutionGauge S g u).val.val = f.val.val ∧
        AbsolutelyContinuousOnInterval (thetaFiniteCompactRepresentative S u) 0 1 := by
  refine ⟨(thetaFiniteConvolutionGauge S g).symm f, ?_, ?_⟩
  · exact ⟨congrArg (fun u => u.val.val) ((thetaFiniteConvolutionGauge S g).apply_symm_apply f),
      absolutelyContinuousOnInterval_thetaFiniteCompactRepresentative S _⟩
  · intro u hu
    apply (thetaFiniteConvolutionGauge S g).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (Subtype.ext hu.1)

end RHTower.PaperThetaEndpoint
