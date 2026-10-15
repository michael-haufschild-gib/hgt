import GaloisForLFunctions.RHTower.DeningerMeyerHedenmalmSourceRealization

/-!
# Causal solvability on the complement of a finite Xi packet

The finite causal projector repairs the jets lost by first-order causal division.
Consequently every shift at a selected Xi zero is surjective on the kernel of the
full selected jet packet. Away from Xi zeros the exact Xi cap first cancels the
Mellin moment. This proves source solvability without assuming spectral synthesis
or excluding invisible homogeneous classes.
-/

open scoped Classical

namespace RHTower

noncomputable section

/-- The actual logarithmic generator shifted by an arbitrary complex scalar. -/
def deningerMeyerCohomologyShift (rho : ℂ) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  deningerMeyerCohomologyGenerator - rho • LinearMap.id

@[simp]
theorem deningerMeyerCohomologyShift_apply (rho : ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyShift rho u =
      deningerMeyerCohomologyGenerator u - rho • u := rfl

/-- A vanishing Mellin moment produces an actual source preimage. -/
theorem deningerMeyerCohomologyShift_causalDivide
    (g : DeningerMeyerStrongLogTarget) (rho : ℂ)
    (hz : deningerMeyerStrongLogMellin g rho = 0) :
    deningerMeyerCohomologyShift rho
        (Submodule.Quotient.mk (deningerMeyerCausalDivide g rho hz)) =
      Submodule.Quotient.mk g := by
  rw [deningerMeyerCohomologyShift_apply, deningerMeyerCohomologyGenerator_mk,
    deningerMeyerStrongLogGenerator_causalDivide]
  simp only [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
  module

/-- The exact Xi boundary cancels every nonresonant Mellin obstruction. -/
theorem deningerMeyerCohomologyShift_surjective_of_xi_ne_zero
    (rho : ℂ) (hrho : xi rho ≠ 0) :
    Function.Surjective (deningerMeyerCohomologyShift rho) := by
  intro u
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    let c := deningerMeyerStrongLogMellin g rho / xi rho
    let h := g - c • deningerMeyerStrongLogSumLM deningerMeyerXiCapSource
    have hz : deningerMeyerStrongLogMellin h rho = 0 := by
      change deningerMeyerStrongLogMellinLM rho
        (g - c • deningerMeyerStrongLogSumLM deningerMeyerXiCapSource) = 0
      rw [map_sub, map_smul]
      change deningerMeyerStrongLogMellin g rho -
        c * deningerMeyerBoundaryMellin deningerMeyerXiCapSource rho = 0
      rw [deningerMeyerXiCapSource_mellin]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ hrho).symm
    refine ⟨Submodule.Quotient.mk (deningerMeyerCausalDivide h rho hz), ?_⟩
    rw [deningerMeyerCohomologyShift_causalDivide]
    change Submodule.Quotient.mk
      (g - c • deningerMeyerStrongLogSumLM deningerMeyerXiCapSource) = _
    simp

/-- Every selected full jet kernel lies in the range of each selected shift. -/
theorem deningerMeyerCohomologyShift_preimage_of_packet_zero
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : deningerMeyerFiniteXiJetPacketLM S u = 0) :
    ∃ v, deningerMeyerCohomologyShift (rho.val : ℂ) v = u := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    let j : DeningerArithmeticJetIndex rho.val :=
      ⟨0, xiSupportMultiplicity_pos rho.val⟩
    have hz := congrFun hu (⟨rho, j⟩ : DeningerMeyerFiniteXiJetSlot S)
    change deningerMeyerStrongLogMellinJetLM 0 (rho.val : ℂ) g = 0 at hz
    rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] at hz
    exact ⟨Submodule.Quotient.mk (deningerMeyerCausalDivide g (rho.val : ℂ) hz),
      deningerMeyerCohomologyShift_causalDivide g (rho.val : ℂ) hz⟩

/-- Finite Xi localization commutes with every shifted generator. -/
theorem deningerMeyerFiniteXiCausalProjector_shift
    (S : Finset XiDivisorSupport) (rho : ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerCohomologyShift rho u) =
      deningerMeyerCohomologyShift rho (deningerMeyerFiniteXiCausalProjector S u) := by
  simp only [deningerMeyerCohomologyShift_apply, map_sub, map_smul,
    deningerMeyerFiniteXiCausalProjector_generator]

/-- The jet repair preserves the equation and puts its solution back in the full kernel. -/
theorem deningerMeyerCohomologyShift_preimage_in_packet_kernel
    (S : Finset XiDivisorSupport) (rho : ℂ)
    (hrho : xi rho ≠ 0 ∨ ∃ tau : ↥S, (tau.val : ℂ) = rho)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : deningerMeyerFiniteXiJetPacketLM S u = 0) :
    ∃ v, deningerMeyerFiniteXiJetPacketLM S v = 0 ∧
      deningerMeyerCohomologyShift rho v = u := by
  have hex : ∃ v, deningerMeyerCohomologyShift rho v = u := by
    rcases hrho with hn | ⟨tau, rfl⟩
    · exact deningerMeyerCohomologyShift_surjective_of_xi_ne_zero rho hn u
    · exact deningerMeyerCohomologyShift_preimage_of_packet_zero S tau u hu
  obtain ⟨v, hv⟩ := hex
  refine ⟨v - deningerMeyerFiniteXiCausalProjector S v, ?_, ?_⟩
  · rw [map_sub, deningerMeyerFiniteXiCausalProjector_jets, sub_self]
  · rw [map_sub, ← deningerMeyerFiniteXiCausalProjector_shift, hv]
    change u - deningerMeyerFiniteXiCausalSection S
      (deningerMeyerFiniteXiJetPacketLM S u) = u
    rw [hu, map_zero, sub_zero]

/-- Product of shifted generators, with repetitions retained. -/
def deningerMeyerGeneratorWord {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) : List ℂ → Module.End ℂ V
  | [] => LinearMap.id
  | rho :: L => (A - rho • LinearMap.id).comp (deningerMeyerGeneratorWord A L)

/-- The finite set of actual Xi zeros occurring in a word. -/
def deningerMeyerWordXiSupport : List ℂ → Finset XiDivisorSupport
  | [] => ∅
  | rho :: L =>
    if hz : xi rho = 0 then
      insert ⟨rho, mem_xi_divisor_support_of_eq_zero hz⟩ (deningerMeyerWordXiSupport L)
    else deningerMeyerWordXiSupport L

@[simp]
theorem mem_deningerMeyerWordXiSupport (L : List ℂ) (rho : XiDivisorSupport) :
    rho ∈ deningerMeyerWordXiSupport L ↔ (rho : ℂ) ∈ L := by
  classical
  induction L with
  | nil => simp [deningerMeyerWordXiSupport]
  | cons z L ih =>
    by_cases hz : xi z = 0
    · simp [deningerMeyerWordXiSupport, hz, ih, Subtype.ext_iff]
    · have hne : (rho : ℂ) ≠ z := by
        intro heq
        exact hz (heq ▸ xi_eq_zero_of_mem_divisor_support rho)
      simp [deningerMeyerWordXiSupport, hz, ih, hne]

/-- No additional forcing obstruction remains on the selected packet kernel. -/
theorem deningerMeyerGeneratorWord_preimage_in_packet_kernel
    (S : Finset XiDivisorSupport) (L : List ℂ)
    (hS : ∀ rho : XiDivisorSupport, (rho : ℂ) ∈ L → rho ∈ S)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : deningerMeyerFiniteXiJetPacketLM S u = 0) :
    ∃ v, deningerMeyerFiniteXiJetPacketLM S v = 0 ∧
      deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L v = u := by
  induction L generalizing u with
  | nil => exact ⟨u, hu, rfl⟩
  | cons z L ih =>
    have hz : xi z ≠ 0 ∨ ∃ rho : ↥S, (rho.val : ℂ) = z := by
      by_cases hz : xi z = 0
      · let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
        exact Or.inr ⟨⟨rho, hS rho (List.mem_cons_self)⟩, rfl⟩
      · exact Or.inl hz
    obtain ⟨w, hw, hzw⟩ :=
      deningerMeyerCohomologyShift_preimage_in_packet_kernel S z hz u hu
    obtain ⟨v, hv, hvw⟩ := ih (fun rho hrho => hS rho (List.mem_cons_of_mem z hrho)) w hw
    refine ⟨v, hv, ?_⟩
    change deningerMeyerCohomologyShift z
      (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L v) = u
    rw [hvw, hzw]

/-- Unconditional source solvability after removing exactly the word's Xi packet. -/
theorem deningerMeyerGeneratorWord_packet_kernel_surjective (L : List ℂ)
    (u : LinearMap.ker (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L))) :
    ∃ v : LinearMap.ker (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L)),
      deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L v = u := by
  obtain ⟨v, hv, heq⟩ := deningerMeyerGeneratorWord_preimage_in_packet_kernel
    (deningerMeyerWordXiSupport L) L
    (fun rho hrho => (mem_deningerMeyerWordXiSupport L rho).mpr hrho) u u.property
  exact ⟨⟨v, hv⟩, heq⟩

end
end RHTower
