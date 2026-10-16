import GaloisForLFunctions.RHTower.DeningerMeyerInvisibleTorsionFree
import GaloisForLFunctions.RHTower.DeningerMeyerStrictCoupledSolvability

/-!
# Complete finite-order calculus on literal Meyer cohomology

Eliminating invisible torsion upgrades the existing finite obstruction model:
every homogeneous solution, including for arbitrary finite packet coupling,
is an actual finite causal Xi packet. The explicit finite-rank repairs are
continuous automorphisms of the full literal quotient. No global arithmetic
complement is selected.
-/

open scoped Classical

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "A" => deningerMeyerCohomologyGenerator

private theorem word_zero_jets (L : List ℂ) (tau : XiDivisorSupport)
    (htau : (tau : ℂ) ∉ L) (u : Q)
    (hu : ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j
      (deningerMeyerGeneratorWord A L u) = 0) :
    ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j u = 0 := by
  induction L generalizing u with
  | nil => exact hu
  | cons rho L ih =>
    have hne : (tau : ℂ) ≠ rho := fun h => htau (List.mem_cons.mpr (Or.inl h))
    have htail : (tau : ℂ) ∉ L := fun h => htau (List.mem_cons.mpr (Or.inr h))
    exact ih htail u (deningerMeyerXiJets_zero_of_shift tau rho hne
      (deningerMeyerGeneratorWord A L u) hu)

theorem deningerMeyerLiteralWord_zero_of_packet_zero (L : List ℂ) (u : Q)
    (hpacket : deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) u = 0)
    (hword : deningerMeyerGeneratorWord A L u = 0) : u = 0 := by
  have hu : u ∈ DeningerMeyerInvisible := by
    apply (mem_deningerMeyerInvisible_iff u).mpr
    intro tau j
    by_cases ht : tau ∈ deningerMeyerWordXiSupport L
    · exact congrFun hpacket ⟨⟨tau, ht⟩, j⟩
    · exact word_zero_jets L tau
        (fun h => ht ((mem_deningerMeyerWordXiSupport L tau).mpr h)) u
        (fun k => by rw [hword, map_zero]) j
  have hw : deningerMeyerGeneratorWord deningerMeyerInvisibleGenerator L ⟨u, hu⟩ = 0 := by
    apply Subtype.ext
    change DeningerMeyerInvisible.subtype
      (deningerMeyerGeneratorWord deningerMeyerInvisibleGenerator L ⟨u, hu⟩) = 0
    rw [deningerMeyerGeneratorWord_intertwines deningerMeyerInvisibleGenerator A
      DeningerMeyerInvisible.subtype (fun _ => rfl)]
    exact hword
  have hi := (deningerMeyerInvisibleGeneratorWord_bijective L).1
  have hz := hi (hw.trans (map_zero _).symm)
  exact congrArg Subtype.val hz

/-- All homogeneous solutions of an arbitrary finite coupling are finite Xi packets. -/
theorem deningerMeyerLiteralCoupled_kernel_iff (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L)))
    (u : Q) :
    deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B u = 0 ↔
      u = deningerMeyerFiniteXiCausalProjector (deningerMeyerWordXiSupport L) u ∧
      deningerMeyerCoupledPacketOperator (deningerMeyerWordXiSupport L) L B
        (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) u) = 0 := by
  let S := deningerMeyerWordXiSupport L
  constructor
  · intro hu
    have hp : deningerMeyerCoupledPacketOperator S L B
        (deningerMeyerFiniteXiJetPacketLM S u) = 0 := by
      rw [← deningerMeyerCoupledSourceOperator_jets, hu, map_zero]
    refine ⟨?_, hp⟩
    apply sub_eq_zero.mp
    have hr : deningerMeyerFiniteXiJetPacketLM S
        (u - deningerMeyerFiniteXiCausalProjector S u) = 0 := by
      rw [map_sub, deningerMeyerFiniteXiCausalProjector_jets, sub_self]
    apply deningerMeyerLiteralWord_zero_of_packet_zero L _ hr
    rw [← deningerMeyerCoupledSourceOperator_of_packet_zero S L B _ hr, map_sub, hu]
    change 0 - deningerMeyerCoupledSourceOperator S L B
      (deningerMeyerFiniteXiCausalSection S _) = 0
    rw [deningerMeyerCoupledSourceOperator_section, hp, map_zero, sub_zero]
  · rintro ⟨he, hp⟩
    conv_lhs => rw [he]
    change deningerMeyerCoupledSourceOperator S L B
      (deningerMeyerFiniteXiCausalSection S _) = 0
    rw [deningerMeyerCoupledSourceOperator_section, hp, map_zero]

/-- The full literal kernel is exactly the image of the finite obstruction kernel. -/
theorem deningerMeyerLiteralCoupled_kernel (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    LinearMap.ker (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B) =
      (LinearMap.ker (deningerMeyerCoupledPacketOperator (deningerMeyerWordXiSupport L) L B)).map
        (deningerMeyerFiniteXiCausalSection (deningerMeyerWordXiSupport L)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨he, hp⟩ := (deningerMeyerLiteralCoupled_kernel_iff L B u).mp hu
    exact ⟨deningerMeyerFiniteXiJetPacketLM _ u, hp, he.symm⟩
  · rintro ⟨c, hc, rfl⟩
    change deningerMeyerCoupledSourceOperator _ L B (deningerMeyerFiniteXiCausalSection _ c) = 0
    rw [deningerMeyerCoupledSourceOperator_section, show deningerMeyerCoupledPacketOperator _ L B c = 0
      from hc, map_zero]

theorem deningerMeyerLiteralCoupled_kernel_finiteDimensional (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    FiniteDimensional ℂ (LinearMap.ker
      (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B)) := by
  rw [deningerMeyerLiteralCoupled_kernel]
  infer_instance

/-- The finite-rank repair removes both forcing obstruction and homogeneous ambiguity. -/
theorem deningerMeyerRegularizedSourceWord_bijective (L : List ℂ) :
    Function.Bijective (deningerMeyerRegularizedSourceWord L) := by
  refine ⟨?_, deningerMeyerRegularizedSourceWord_surjective L⟩
  intro u v huv
  apply sub_eq_zero.mp
  have hz : deningerMeyerRegularizedSourceWord L (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hp : deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) (u - v) = 0 := by
    rw [← deningerMeyerRegularizedSourceWord_jets L, hz, map_zero]
  apply deningerMeyerLiteralWord_zero_of_packet_zero L _ hp
  rw [← deningerMeyerCoupledSourceOperator_of_packet_zero _ L _ _ hp]
  exact hz

/-- Continuous two-sided solution operator on the full original Poisson quotient. -/
def deningerMeyerRegularizedSourceWordContinuousEquiv (L : List ℂ) : Q ≃L[ℂ] Q := by
  let e : Q ≃ₗ[ℂ] Q := LinearEquiv.ofBijective _ (deningerMeyerRegularizedSourceWord_bijective L)
  have hc : Continuous e := deningerMeyerCoupledSourceOperator_continuous _ L _
  have hci : Continuous e.symm :=
    GaloisForLFunctions.continuous_symm_of_continuous (𝕜 := ℂ) (E := Q) (F := Q) e hc
  exact { toLinearEquiv := e, continuous_toFun := hc, continuous_invFun := hci }

@[simp] theorem deningerMeyerRegularizedSourceWordContinuousEquiv_apply (L : List ℂ) (u : Q) :
    deningerMeyerRegularizedSourceWordContinuousEquiv L u = deningerMeyerRegularizedSourceWord L u := rfl

/-- Every datum has one exact source-class solution after the fixed finite repair. -/
theorem deningerMeyerRegularizedSourceWord_existsUnique (L : List ℂ) (f : Q) :
    ∃! u, deningerMeyerRegularizedSourceWord L u = f := by
  let e := deningerMeyerRegularizedSourceWordContinuousEquiv L
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro u hu
  exact e.injective (hu.trans (e.apply_symm_apply f).symm)

end
end RHTower
