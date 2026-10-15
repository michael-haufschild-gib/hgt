import GaloisForLFunctions.RHTower.DeningerMeyerFiniteXiCausalSolvability

/-!
# Exact finite obstruction model for coupled Meyer source equations

For every finite product W of shifted actual generators, let S contain exactly
its Xi roots, including their full Xi jet packets. The residual operator is
surjective on ker E_S. Hence arbitrary finite packet couplings J_S B E_S have
exactly the finite obstruction matrix W(T_S) + B. In particular the explicit
correction B = 1 - W(T_S) makes the actual source operator surjective.

These are unconditional solvability statements on literal Meyer cohomology.
They require neither a global synthesis theorem nor a claim that the residual
operator is injective or has a continuous inverse.
-/

open scoped Classical

namespace RHTower

noncomputable section

/-- Intertwining passes through every finite word in shifted generators. -/
theorem deningerMeyerGeneratorWord_intertwines
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (B : Module.End ℂ W) (E : V →ₗ[ℂ] W)
    (h : ∀ u, E (A u) = B (E u)) (L : List ℂ) (u : V) :
    E (deningerMeyerGeneratorWord A L u) = deningerMeyerGeneratorWord B L (E u) := by
  induction L with
  | nil => rfl
  | cons rho L ih =>
    change E (A (deningerMeyerGeneratorWord A L u) -
      rho • deningerMeyerGeneratorWord A L u) =
      B (deningerMeyerGeneratorWord B L (E u)) -
        rho • deningerMeyerGeneratorWord B L (E u)
    rw [map_sub, map_smul, h, ih]

theorem deningerMeyerGeneratorWord_jets (S : Finset XiDivisorSupport)
    (L : List ℂ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM S
        (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u) =
      deningerMeyerGeneratorWord (deningerMeyerFiniteXiPacketGenerator S) L
        (deningerMeyerFiniteXiJetPacketLM S u) :=
  deningerMeyerGeneratorWord_intertwines _ _ _
    (fun v => (deningerMeyerFiniteXiPacketGenerator_jets S v).symm) L u

theorem deningerMeyerGeneratorWord_section (S : Finset XiDivisorSupport)
    (L : List ℂ) (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L
        (deningerMeyerFiniteXiCausalSection S c) =
      deningerMeyerFiniteXiCausalSection S
        (deningerMeyerGeneratorWord (deningerMeyerFiniteXiPacketGenerator S) L c) :=
  (deningerMeyerGeneratorWord_intertwines _ _ _
    (fun d => (deningerMeyerFiniteXiCausalSection_generator S d).symm) L c).symm

/-- Actual source operator with arbitrary finite packet coupling. -/
def deningerMeyerCoupledSourceOperator (S : Finset XiDivisorSupport) (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L +
    deningerMeyerFiniteXiOperatorLift S B

/-- The finite obstruction operator, retaining every Xi multiplicity. -/
def deningerMeyerCoupledPacketOperator (S : Finset XiDivisorSupport) (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    Module.End ℂ (DeningerMeyerFiniteXiJetPacket S) :=
  deningerMeyerGeneratorWord (deningerMeyerFiniteXiPacketGenerator S) L + B

theorem deningerMeyerCoupledSourceOperator_jets (S : Finset XiDivisorSupport)
    (L : List ℂ) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S))
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM S (deningerMeyerCoupledSourceOperator S L B u) =
      deningerMeyerCoupledPacketOperator S L B (deningerMeyerFiniteXiJetPacketLM S u) := by
  change deningerMeyerFiniteXiJetPacketLM S
    (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u +
      deningerMeyerFiniteXiCausalSection S (B (deningerMeyerFiniteXiJetPacketLM S u))) = _
  rw [map_add, deningerMeyerGeneratorWord_jets, deningerMeyerFiniteXiCausalSection_jets]
  rfl

theorem deningerMeyerCoupledSourceOperator_section (S : Finset XiDivisorSupport)
    (L : List ℂ) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S))
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerCoupledSourceOperator S L B (deningerMeyerFiniteXiCausalSection S c) =
      deningerMeyerFiniteXiCausalSection S (deningerMeyerCoupledPacketOperator S L B c) := by
  change deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L
      (deningerMeyerFiniteXiCausalSection S c) +
    deningerMeyerFiniteXiCausalSection S
      (B (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSection S c))) = _
  rw [deningerMeyerGeneratorWord_section, deningerMeyerFiniteXiCausalSection_jets,
    ← map_add]
  rfl

theorem deningerMeyerCoupledSourceOperator_of_packet_zero (S : Finset XiDivisorSupport)
    (L : List ℂ) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S))
    (u : DeningerMeyerStrongLogCohomology) (hu : deningerMeyerFiniteXiJetPacketLM S u = 0) :
    deningerMeyerCoupledSourceOperator S L B u =
      deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u := by
  change deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u +
    deningerMeyerFiniteXiCausalSection S (B (deningerMeyerFiniteXiJetPacketLM S u)) = _
  rw [hu, map_zero, map_zero, add_zero]

/-- Exact range classification: all remaining obstructions are finite packet obstructions. -/
theorem deningerMeyerCoupledSourceOperator_range (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    LinearMap.range (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B) =
      (LinearMap.range
        (deningerMeyerCoupledPacketOperator (deningerMeyerWordXiSupport L) L B)).comap
          (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L)) := by
  let S := deningerMeyerWordXiSupport L
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨deningerMeyerFiniteXiJetPacketLM S v,
      (deningerMeyerCoupledSourceOperator_jets S L B v).symm⟩
  · rintro ⟨c, hc⟩
    let r := u - deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketLM S u)
    have hr : deningerMeyerFiniteXiJetPacketLM S r = 0 := by
      dsimp only [r]
      rw [map_sub, deningerMeyerFiniteXiCausalSection_jets, sub_self]
    obtain ⟨v, hv, hvr⟩ := deningerMeyerGeneratorWord_preimage_in_packet_kernel S L
      (fun rho hrho => (mem_deningerMeyerWordXiSupport L rho).mpr hrho) r hr
    refine ⟨deningerMeyerFiniteXiCausalSection S c + v, ?_⟩
    rw [map_add, deningerMeyerCoupledSourceOperator_section,
      deningerMeyerCoupledSourceOperator_of_packet_zero S L B v hv, hvr, hc]
    dsimp only [r]
    module

/-- Explicit finite-rank repair of any finite product of shifted generators. -/
def deningerMeyerRegularizedSourceWord (L : List ℂ) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L
    (LinearMap.id -
      deningerMeyerGeneratorWord
        (deningerMeyerFiniteXiPacketGenerator (deningerMeyerWordXiSupport L)) L)

/-- Every forcing has an actual cohomological solution after the explicit finite-rank repair. -/
theorem deningerMeyerRegularizedSourceWord_surjective (L : List ℂ) :
    Function.Surjective (deningerMeyerRegularizedSourceWord L) := by
  intro u
  change u ∈ LinearMap.range
    (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L _)
  rw [deningerMeyerCoupledSourceOperator_range]
  refine ⟨deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) u, ?_⟩
  simp only [deningerMeyerCoupledPacketOperator, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  module

/-- The repair is the identity on the full resonant Xi packet. -/
theorem deningerMeyerRegularizedSourceWord_jets (L : List ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L)
        (deningerMeyerRegularizedSourceWord L u) =
      deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) u := by
  rw [deningerMeyerRegularizedSourceWord, deningerMeyerCoupledSourceOperator_jets]
  simp only [deningerMeyerCoupledPacketOperator, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  module

/-- A linear right parametrix, with precisely the full finite Xi projector as defect.
Its values lie in the kernel of that packet; no continuity or left inverse is asserted. -/
theorem deningerMeyerGeneratorWord_exists_rightParametrix (L : List ℂ) :
    ∃ R : Module.End ℂ DeningerMeyerStrongLogCohomology,
      (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L).comp R =
        LinearMap.id - deningerMeyerFiniteXiCausalProjector (deningerMeyerWordXiSupport L) ∧
      (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L)).comp R = 0 := by
  let S := deningerMeyerWordXiSupport L
  obtain ⟨R, hR⟩ := (deningerMeyerRegularizedSourceWord L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (deningerMeyerRegularizedSourceWord_surjective L))
  let D : Module.End ℂ DeningerMeyerStrongLogCohomology :=
    LinearMap.id - deningerMeyerFiniteXiCausalProjector S
  have hRD (u : DeningerMeyerStrongLogCohomology) :
      deningerMeyerRegularizedSourceWord L (R (D u)) = D u :=
    LinearMap.congr_fun hR (D u)
  have hE (u : DeningerMeyerStrongLogCohomology) :
      deningerMeyerFiniteXiJetPacketLM S (R (D u)) = 0 := by
    rw [← deningerMeyerRegularizedSourceWord_jets L, hRD]
    change deningerMeyerFiniteXiJetPacketLM S
      (u - deningerMeyerFiniteXiCausalProjector S u) = 0
    rw [map_sub, deningerMeyerFiniteXiCausalProjector_jets, sub_self]
  refine ⟨R.comp D, ?_, ?_⟩
  · apply LinearMap.ext
    intro u
    change deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L (R (D u)) = D u
    rw [← deningerMeyerCoupledSourceOperator_of_packet_zero S L _ _ (hE u)]
    exact hRD u
  · apply LinearMap.ext
    intro u
    exact hE u

/-- The full infinite source cokernel is exactly the finite packet cokernel. -/
def deningerMeyerCoupledSourceCokernelEquiv (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    (DeningerMeyerStrongLogCohomology ⧸
      LinearMap.range (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B))
      ≃ₗ[ℂ]
    (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L) ⧸
      LinearMap.range (deningerMeyerCoupledPacketOperator (deningerMeyerWordXiSupport L) L B)) := by
  let S := deningerMeyerWordXiSupport L
  let M := deningerMeyerCoupledPacketOperator S L B
  let F := (LinearMap.range M).mkQ.comp (deningerMeyerFiniteXiJetPacketLM S)
  have hF : Function.Surjective F :=
    (LinearMap.range M).mkQ_surjective.comp (deningerMeyerFiniteXiJetPacketLM_surjective S)
  have hker : LinearMap.ker F = LinearMap.range (deningerMeyerCoupledSourceOperator S L B) := by
    rw [deningerMeyerCoupledSourceOperator_range]
    ext u
    change Submodule.Quotient.mk (deningerMeyerFiniteXiJetPacketLM S u) = 0 ↔
      deningerMeyerFiniteXiJetPacketLM S u ∈ LinearMap.range M
    rw [Submodule.Quotient.mk_eq_zero]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hF)

end
end RHTower
