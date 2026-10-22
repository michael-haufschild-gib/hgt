import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertTopology

/-! # Exact finite sources are dense in the native Hasse Hilbert realization -/

noncomputable section
open Complex Set Topology

namespace RHTower
open scoped DeningerMeyerNaturalTopology

/-- Every finite Hasse packet is realized by an original source class, with
exactly zero jets outside its selected divisor support. -/
theorem deningerMeyerHasseHilbert_finite_packet (a : DeningerArithmeticJetTest) :
    ∃ u : DeningerMeyerStrongLogCohomology,
      deningerMeyerHasseHilbertLM u = deningerArithmeticJetTestToHilbert a := by
  classical
  let S : Finset XiDivisorSupport := a.support.image Sigma.fst
  let c : DeningerMeyerFiniteXiJetPacket S := fun q =>
    a ⟨q.1.1, q.2⟩ * (q.2.val.factorial : ℂ)
  refine ⟨deningerMeyerFiniteXiCausalSection S c, ?_⟩
  apply lp.ext
  funext q
  rw [deningerArithmeticJetTestToHilbert_apply]
  change deningerMeyerXiSupportJetEvaluationLM q.1 q.2
    (deningerMeyerFiniteXiCausalSection S c) / (q.2.val.factorial : ℂ) = a q
  by_cases hq : q.1 ∈ S
  · have h := congrFun (deningerMeyerFiniteXiCausalSection_jets S c) ⟨⟨q.1, hq⟩, q.2⟩
    change deningerMeyerXiSupportJetEvaluationLM q.1 q.2
      (deningerMeyerFiniteXiCausalSection S c) = a q * (q.2.val.factorial : ℂ) at h
    rw [h, mul_div_cancel_right₀]
    exact_mod_cast Nat.factorial_ne_zero q.2.val
  · rw [deningerMeyerFiniteXiCausalSection_other_jet_zero S q.1 hq q.2 c, zero_div]
    symm
    apply Finsupp.notMem_support_iff.mp
    intro ha
    exact hq (Finset.mem_image.mpr ⟨q, ha, rfl⟩)

/-- Every single Hilbert coordinate has an exact source representative. -/
theorem deningerMeyerHasseHilbert_single (q : DeningerArithmeticJetCoordinate) (z : ℂ) :
    ∃ u : DeningerMeyerStrongLogCohomology,
      deningerMeyerHasseHilbertLM u = lp.single 2 q z := by
  simpa only [deningerArithmeticJetTestToHilbert_single] using
    deningerMeyerHasseHilbert_finite_packet (Finsupp.single q z)

/-- The actual Poisson quotient has dense image in the complete, unweighted
full-multiplicity Hasse jet Hilbert space. -/
theorem deningerMeyerHasseHilbertLM_dense : DenseRange deningerMeyerHasseHilbertLM := by
  apply Dense.mono _ deningerArithmeticJetTestToHilbert_dense
  rintro _ ⟨a, rfl⟩
  exact deningerMeyerHasseHilbert_finite_packet a

theorem deningerMeyerHasseHilbertCLM_injective :
    Function.Injective deningerMeyerHasseHilbertCLM := deningerMeyerHasseHilbertLM_injective

theorem deningerMeyerHasseHilbertCLM_dense :
    DenseRange deningerMeyerHasseHilbertCLM := deningerMeyerHasseHilbertLM_dense

end RHTower
