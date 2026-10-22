import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerArithmeticSourceResolvent

/-!
# Canonical division on actual-source complements of resonant packets

Every finite generator word is bijective on the complement of its full Xi
packet in arithmetic Meyer cohomology. Causal surjectivity and exact homogeneous
classification remove both forcing and homogeneous ambiguity, including at Xi
zeros. No continuity of the global splitting is used.
-/

open scoped Classical

namespace RHTower
noncomputable section

local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "V" => DeningerMeyerArithmeticSource
local notation "A" => deningerMeyerArithmeticSourceGenerator
local notation "P" => deningerMeyerArithmeticCausalProjector

theorem deningerMeyerArithmeticSource_eq_zero (u : V)
    (hu : (u : Q) ∈ DeningerMeyerInvisible) : u = 0 := by
  apply Subtype.ext
  rw [← deningerMeyerArithmeticSource_fixed u]
  exact deningerMeyerArithmeticCausalProjector_invisible ⟨u, hu⟩

theorem deningerMeyerFiniteCausalModes_mem_arithmeticSource
    (u : DeningerMeyerFiniteCausalModes) : (u : Q) ∈ V :=
  ⟨u, deningerMeyerArithmeticCausalProjector_finite u⟩

theorem deningerMeyerFiniteXiCausalProjector_mem_finite
    (S : Finset XiDivisorSupport) (u : Q) :
    deningerMeyerFiniteXiCausalProjector S u ∈ DeningerMeyerFiniteCausalModes :=
  ⟨S, deningerMeyerFiniteXiCausalProjector_mem_range S u⟩

def deningerMeyerArithmeticPacketLM (S : Finset XiDivisorSupport) :
    V →ₗ[ℂ] DeningerMeyerFiniteXiJetPacket S :=
  (deningerMeyerFiniteXiJetPacketLM S).comp (V).subtype

def deningerMeyerArithmeticFiniteProjector (S : Finset XiDivisorSupport) : Module.End ℂ V where
  toFun u := ⟨deningerMeyerFiniteXiCausalProjector S u,
    deningerMeyerFiniteCausalModes_mem_arithmeticSource
      ⟨_, deningerMeyerFiniteXiCausalProjector_mem_finite S u⟩⟩
  map_add' u v := Subtype.ext ((deningerMeyerFiniteXiCausalProjector S).map_add u v)
  map_smul' z u := Subtype.ext ((deningerMeyerFiniteXiCausalProjector S).map_smul z u)

theorem deningerMeyerArithmeticFiniteProjector_coe (S : Finset XiDivisorSupport) (u : V) :
    (deningerMeyerArithmeticFiniteProjector S u : Q) =
      deningerMeyerFiniteXiCausalProjector S u := rfl

theorem deningerMeyerArithmeticFiniteProjector_jets (S : Finset XiDivisorSupport) (u : V) :
    deningerMeyerArithmeticPacketLM S (deningerMeyerArithmeticFiniteProjector S u) =
      deningerMeyerArithmeticPacketLM S u :=
  deningerMeyerFiniteXiCausalProjector_jets S u

@[simp]
theorem deningerMeyerArithmeticFiniteProjector_idempotent
    (S : Finset XiDivisorSupport) (u : V) :
    deningerMeyerArithmeticFiniteProjector S (deningerMeyerArithmeticFiniteProjector S u) =
      deningerMeyerArithmeticFiniteProjector S u :=
  Subtype.ext (deningerMeyerFiniteXiCausalProjector_idempotent S u)

theorem deningerMeyerArithmeticFiniteProjector_generator
    (S : Finset XiDivisorSupport) (u : V) :
    deningerMeyerArithmeticFiniteProjector S (A u) =
      A (deningerMeyerArithmeticFiniteProjector S u) :=
  Subtype.ext (deningerMeyerFiniteXiCausalProjector_generator S u)

theorem deningerMeyerArithmeticFiniteProjector_word
    (S : Finset XiDivisorSupport) (L : List ℂ) (u : V) :
    deningerMeyerArithmeticFiniteProjector S (deningerMeyerGeneratorWord A L u) =
      deningerMeyerGeneratorWord A L (deningerMeyerArithmeticFiniteProjector S u) :=
  deningerMeyerGeneratorWord_intertwines A A (deningerMeyerArithmeticFiniteProjector S)
    (deningerMeyerArithmeticFiniteProjector_generator S) L u

theorem deningerMeyerArithmeticFiniteProjector_zero_of_packet_zero
    (S : Finset XiDivisorSupport) (u : V) (hu : deningerMeyerArithmeticPacketLM S u = 0) :
    deningerMeyerArithmeticFiniteProjector S u = 0 := by
  apply Subtype.ext
  change deningerMeyerFiniteXiCausalSection S (deningerMeyerArithmeticPacketLM S u) = 0
  rw [hu, map_zero]

theorem deningerMeyerArithmeticGeneratorWord_coe (L : List ℂ) (u : V) :
    (deningerMeyerGeneratorWord A L u : Q) =
      deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u :=
  deningerMeyerGeneratorWord_intertwines _ _ (V).subtype (fun _ => rfl) L u

theorem deningerMeyerArithmeticGeneratorWord_jets
    (S : Finset XiDivisorSupport) (L : List ℂ) (u : V) :
    deningerMeyerArithmeticPacketLM S (deningerMeyerGeneratorWord A L u) =
      deningerMeyerGeneratorWord (deningerMeyerFiniteXiPacketGenerator S) L
        (deningerMeyerArithmeticPacketLM S u) := by
  change deningerMeyerFiniteXiJetPacketLM S
    (deningerMeyerGeneratorWord A L u : Q) = _
  rw [deningerMeyerArithmeticGeneratorWord_coe, deningerMeyerGeneratorWord_jets]
  rfl

/-- On the actual arithmetic source, no homogeneous ambiguity remains outside
the full resonant packet. -/
theorem deningerMeyerArithmeticWord_zero_of_packet_zero (L : List ℂ) (u : V)
    (hpacket : deningerMeyerArithmeticPacketLM (deningerMeyerWordXiSupport L) u = 0)
    (hword : deningerMeyerGeneratorWord A L u = 0) : u = 0 := by
  let E := deningerMeyerObservableArithmeticEquiv
  have hOldWord : deningerMeyerGeneratorWord deningerMeyerObservableSourceGenerator L
      (E.symm u) = 0 := by
    apply E.injective
    change E.toLinearMap
      (deningerMeyerGeneratorWord deningerMeyerObservableSourceGenerator L (E.symm u)) =
        E.toLinearMap 0
    rw [deningerMeyerGeneratorWord_intertwines _ _ E.toLinearMap
      deningerMeyerObservableArithmeticEquiv_generator]
    change deningerMeyerGeneratorWord A L (E (E.symm u)) = E 0
    rw [E.apply_symm_apply, hword, map_zero]
  have hOldPacket : deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L)
      (E.symm u) = 0 := by
    funext q
    change deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2
      (deningerMeyerGlobalCausalProjector u) = 0
    rw [deningerMeyerGlobalCausalProjector_jets]
    exact congrFun hpacket q
  have hfixed := ((deningerMeyerObservableGeneratorWord_kernel L (E.symm u)).mp hOldWord).1
  have hz : E.symm u = 0 := by
    apply Subtype.ext
    rw [hfixed]
    change deningerMeyerFiniteXiCausalSection (deningerMeyerWordXiSupport L)
      (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) (E.symm u)) = 0
    rw [hOldPacket, map_zero]
  have h := congrArg E hz
  simpa using h

/-- The actual full-packet kernel, inside the arithmetic source. -/
abbrev DeningerMeyerArithmeticPacketKernel (S : Finset XiDivisorSupport) :=
  LinearMap.ker (deningerMeyerArithmeticPacketLM S)

def deningerMeyerArithmeticPacketKernelWord (L : List ℂ) :
    Module.End ℂ (DeningerMeyerArithmeticPacketKernel (deningerMeyerWordXiSupport L)) :=
  (deningerMeyerGeneratorWord A L).restrict (by
    intro u hu
    change deningerMeyerArithmeticPacketLM _ (deningerMeyerGeneratorWord A L u) = 0
    rw [deningerMeyerArithmeticGeneratorWord_jets, show deningerMeyerArithmeticPacketLM _ u = 0
      from hu, map_zero])

/-- Every word, with arbitrary repeated Xi roots, acts bijectively on its
actual-source packet complement. -/
theorem deningerMeyerArithmeticPacketKernelWord_bijective (L : List ℂ) :
    Function.Bijective (deningerMeyerArithmeticPacketKernelWord L) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply deningerMeyerArithmeticWord_zero_of_packet_zero L
    · rw [map_sub, show deningerMeyerArithmeticPacketLM _ (u : V) = 0 from u.property,
        show deningerMeyerArithmeticPacketLM _ (v : V) = 0 from v.property, sub_self]
    · have h := congrArg Subtype.val huv
      change deningerMeyerGeneratorWord A L (u : V) = deningerMeyerGeneratorWord A L (v : V) at h
      rw [map_sub, h, sub_self]
  · intro u
    obtain ⟨v, hv, hvu⟩ := deningerMeyerGeneratorWord_preimage_in_packet_kernel
      (deningerMeyerWordXiSupport L) L
      (fun rho hrho => (mem_deningerMeyerWordXiSupport L rho).mpr hrho)
      (u : Q) u.property
    let w : V := ⟨P v, v, rfl⟩
    have hw : deningerMeyerArithmeticPacketLM (deningerMeyerWordXiSupport L) w = 0 := by
      funext q
      change deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2 (P v) = 0
      rw [deningerMeyerArithmeticCausalProjector_jets]
      exact congrFun hv q
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (deningerMeyerGeneratorWord A L w : Q) = (u : Q)
    rw [deningerMeyerArithmeticGeneratorWord_coe]
    change deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L (P v) = _
    rw [← deningerMeyerGeneratorWord_intertwines _ _ P
      deningerMeyerArithmeticCausalProjector_generator, hvu,
      deningerMeyerArithmeticSource_fixed]

def deningerMeyerArithmeticPacketKernelWordEquiv (L : List ℂ) :
    DeningerMeyerArithmeticPacketKernel (deningerMeyerWordXiSupport L) ≃ₗ[ℂ]
      DeningerMeyerArithmeticPacketKernel (deningerMeyerWordXiSupport L) :=
  LinearEquiv.ofBijective (deningerMeyerArithmeticPacketKernelWord L)
    (deningerMeyerArithmeticPacketKernelWord_bijective L)

/-- The canonical removal of the complete resonant packet. -/
def deningerMeyerArithmeticPacketRemainder (S : Finset XiDivisorSupport) :
    V →ₗ[ℂ] DeningerMeyerArithmeticPacketKernel S :=
  (LinearMap.id - deningerMeyerArithmeticFiniteProjector S).codRestrict _ (by
    intro u
    change deningerMeyerArithmeticPacketLM S
      (u - deningerMeyerArithmeticFiniteProjector S u) = 0
    rw [map_sub, deningerMeyerArithmeticFiniteProjector_jets, sub_self])

/-- Canonical source division, available even for resonant words. -/
def deningerMeyerArithmeticWordDivision (L : List ℂ) : Module.End ℂ V :=
  (DeningerMeyerArithmeticPacketKernel (deningerMeyerWordXiSupport L)).subtype.comp
    ((deningerMeyerArithmeticPacketKernelWordEquiv L).symm.toLinearMap.comp
      (deningerMeyerArithmeticPacketRemainder (deningerMeyerWordXiSupport L)))

theorem deningerMeyerArithmeticWordDivision_packet_zero (L : List ℂ) (u : V) :
    deningerMeyerArithmeticPacketLM (deningerMeyerWordXiSupport L)
      (deningerMeyerArithmeticWordDivision L u) = 0 :=
  ((deningerMeyerArithmeticPacketKernelWordEquiv L).symm
    (deningerMeyerArithmeticPacketRemainder (deningerMeyerWordXiSupport L) u)).property

/-- Right division has exactly the complete finite resonant projector as defect. -/
theorem deningerMeyerArithmeticWordDivision_right (L : List ℂ) (u : V) :
    deningerMeyerGeneratorWord A L (deningerMeyerArithmeticWordDivision L u) =
      u - deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L) u := by
  exact congrArg Subtype.val ((deningerMeyerArithmeticPacketKernelWordEquiv L).apply_symm_apply
    (deningerMeyerArithmeticPacketRemainder (deningerMeyerWordXiSupport L) u))

/-- Left division has the same defect: there is no invisible homogeneous error. -/
theorem deningerMeyerArithmeticWordDivision_left (L : List ℂ) (u : V) :
    deningerMeyerArithmeticWordDivision L (deningerMeyerGeneratorWord A L u) =
      u - deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L) u := by
  apply sub_eq_zero.mp
  apply deningerMeyerArithmeticWord_zero_of_packet_zero L
  · rw [map_sub, deningerMeyerArithmeticWordDivision_packet_zero, map_sub,
      deningerMeyerArithmeticFiniteProjector_jets, sub_self, sub_self]
  · rw [map_sub, deningerMeyerArithmeticWordDivision_right, map_sub,
      deningerMeyerArithmeticFiniteProjector_word, sub_self]

end
end RHTower
