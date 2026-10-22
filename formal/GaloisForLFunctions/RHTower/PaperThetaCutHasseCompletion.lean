import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGlobalHassePaugamPairing
import GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent

/-! # Literal theta current factors are total in native Meyer Hilbert cohomology

The factors in the compact BV cut-current identity generate a dense subspace
of the full Hasse Hilbert carrier. Under the global Paugam form they detect
every literal Meyer class. This is Hilbert totality of actual source factors;
no infinite BV-current sum or positive Hodge compatibility is asserted.
-/

noncomputable section
open Complex Set Topology
open scoped Classical

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def cutFactorOrder (q : DeningerArithmeticJetCoordinate) : Fin (xiSupportMultiplicity q.1 + 1) :=
  ⟨xiSupportMultiplicity q.1 - q.2.val, by omega⟩

def cutFactorSource (q : DeningerArithmeticJetCoordinate) : DeningerMeyerStrongLogTarget :=
  deningerMeyerHedenmalmSource q.1 (cutFactorOrder q)

def cutFactorClass (q : DeningerArithmeticJetCoordinate) : DeningerMeyerStrongLogCohomology :=
  deningerMeyerHedenmalmClass q.1 (cutFactorOrder q)

/-- These generators are the exact factors of the already admitted native interior current. -/
theorem cutCharge_cutFactorSource (q : DeningerArithmeticJetCoordinate) (z : ℂ) (a : ℝ) :
    cutCharge z a =
      (-(I*z)*Complex.exp (-(I*z)*(a : ℂ)) / (thetaSource.k a : ℂ)) *
        (z - xiSpectralPointSupport q.1) ^ (cutFactorOrder q).val *
          deningerMeyerCenteredMellin (cutFactorSource q) z :=
  cutCharge_meyer_factorization q.1 (cutFactorOrder q) z a

private theorem cutFactorClass_eq (q : DeningerArithmeticJetCoordinate) :
    cutFactorClass q = I ^ (cutFactorOrder q).val • deningerMeyerXiJetSource q.1 q.2 :=
  deningerMeyerHedenmalmClass_eq q.1 (cutFactorOrder q)

def cutFactorHilbertSpan : Submodule ℂ DeningerArithmeticJetHilbert :=
  Submodule.span ℂ (Set.range (fun q => deningerMeyerHasseHilbertLM (cutFactorClass q)))

private theorem causalJet_mem_cutFactorHilbertSpan (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertLM (deningerMeyerXiJetSource q.1 q.2) ∈ cutFactorHilbertSpan := by
  have h : deningerMeyerHasseHilbertLM (cutFactorClass q) ∈ cutFactorHilbertSpan :=
    Submodule.subset_span ⟨q, rfl⟩
  have hs := cutFactorHilbertSpan.smul_mem (I ^ (cutFactorOrder q).val)⁻¹ h
  rw [cutFactorClass_eq, map_smul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ I_ne_zero), one_smul] at hs
  exact hs

private theorem causalSection_mem_cutFactorHilbertSpan (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerHasseHilbertLM (deningerMeyerFiniteXiCausalSection S c) ∈
      cutFactorHilbertSpan := by
  change deningerMeyerHasseHilbertLM (deningerMeyerFiniteXiCausalSynthesis S _) ∈ _
  rw [deningerMeyerFiniteXiCausalSynthesis_apply, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [map_smul]
  exact cutFactorHilbertSpan.smul_mem _ (causalJet_mem_cutFactorHilbertSpan ⟨q.1.1, q.2⟩)

private theorem hasseProjector_apply (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseHilbertLM (deningerMeyerFiniteXiCausalProjector S u) q =
      if q.1 ∈ S then deningerMeyerHasseHilbertLM u q else 0 := by
  change deningerMeyerXiSupportJetEvaluationLM q.1 q.2
      (deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketLM S u)) /
        (q.2.val.factorial : ℂ) = _
  by_cases hq : q.1 ∈ S
  · have h := congrFun (deningerMeyerFiniteXiCausalSection_jets S
      (deningerMeyerFiniteXiJetPacketLM S u)) ⟨⟨q.1, hq⟩, q.2⟩
    rw [if_pos hq]
    exact congrArg (fun z : ℂ => z / (q.2.val.factorial : ℂ)) h
  · rw [if_neg hq, deningerMeyerFiniteXiCausalSection_other_jet_zero S q.1 hq,
      zero_div]

/-- Every finite Hasse packet lies in the span of literal native-current factors. -/
theorem finitePacket_mem_cutFactorHilbertSpan (a : DeningerArithmeticJetTest) :
    deningerArithmeticJetTestToHilbert a ∈ cutFactorHilbertSpan := by
  let S : Finset XiDivisorSupport := a.support.image Sigma.fst
  obtain ⟨u, hu⟩ := deningerMeyerHasseHilbert_finite_packet a
  have he : deningerMeyerHasseHilbertLM (deningerMeyerFiniteXiCausalProjector S u) =
      deningerArithmeticJetTestToHilbert a := by
    apply lp.ext
    funext q
    rw [hasseProjector_apply, hu, deningerArithmeticJetTestToHilbert_apply]
    by_cases hq : q.1 ∈ S
    · rw [if_pos hq]
    · rw [if_neg hq]
      symm
      apply Finsupp.notMem_support_iff.mp
      intro ha
      exact hq (Finset.mem_image.mpr ⟨q, ha, rfl⟩)
  rw [← he]
  exact causalSection_mem_cutFactorHilbertSpan S _

/-- The RN current factors form a total family in the faithful HF Hilbert realization. -/
theorem cutFactorHilbertSpan_dense : Dense (cutFactorHilbertSpan : Set DeningerArithmeticJetHilbert) := by
  apply Dense.mono _ deningerArithmeticJetTestToHilbert_dense
  rintro _ ⟨a, rfl⟩
  exact finitePacket_mem_cutFactorHilbertSpan a

/-- Native-current factors separate all source classes under the global form. -/
theorem cutFactorPairing_detects (u : DeningerMeyerStrongLogCohomology)
    (h : ∀ q, deningerMeyerGlobalHassePaugamPairing u (cutFactorClass q) = 0) : u = 0 := by
  let L := deningerHasseHilbertPaugamCLM (deningerMeyerHasseHilbertLM u)
  have hs : (cutFactorHilbertSpan : Set DeningerArithmeticJetHilbert) ⊆ {y | L y = 0} := by
    change cutFactorHilbertSpan ≤ LinearMap.ker L.toLinearMap
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact h q
  have hz (y : DeningerArithmeticJetHilbert) : L y = 0 :=
    closure_minimal hs (isClosed_eq L.continuous continuous_const) (cutFactorHilbertSpan_dense y)
  have hu : u ∈ LinearMap.ker deningerMeyerGlobalHassePaugamPairing := by
    apply LinearMap.ext
    intro v
    exact hz (deningerMeyerHasseHilbertLM v)
  rwa [deningerMeyerGlobalHassePaugamPairing_ker, Submodule.mem_bot] at hu

theorem cutFactorPairing_injective : Function.Injective
    (fun u : DeningerMeyerStrongLogCohomology => fun q : DeningerArithmeticJetCoordinate =>
      deningerMeyerGlobalHassePaugamPairing u (cutFactorClass q)) := by
  intro u v h
  apply sub_eq_zero.mp
  apply cutFactorPairing_detects
  intro q
  have he := congrFun h q
  simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using he

end RHTower.PaperThetaEndpoint
