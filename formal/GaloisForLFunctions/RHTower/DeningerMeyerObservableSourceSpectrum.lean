import GaloisForLFunctions.RHTower.DeningerMeyerGlobalObservableSource
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Exact algebraic spectrum on the global actual observable source space

The global source splitting removes invisible homogeneous ambiguity without
requiring the invisible sector to vanish. Every homogeneous finite-word
solution is its canonical finite resonant Xi packet. Off-divisor shifts are
bijective, and every divisor point has an actual nonzero eigenvector. Thus the
algebraic spectrum of the restricted actual generator is exactly the Xi divisor.

This is a source-space construction, not a claim of a continuous resolvent,
positive metric, or RH.
-/

open scoped Classical

namespace RHTower
noncomputable section

theorem deningerMeyerObservableGeneratorWord_coe (L : List ℂ)
    (u : DeningerMeyerObservableSource) :
    (deningerMeyerGeneratorWord deningerMeyerObservableSourceGenerator L u :
      DeningerMeyerStrongLogCohomology) =
      deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u :=
  deningerMeyerGeneratorWord_intertwines _ _ DeningerMeyerObservableSource.subtype
    (fun _ => rfl) L u

private theorem word_zero_jets (L : List ℂ) (tau : XiDivisorSupport)
    (htau : (tau : ℂ) ∉ L) (u : DeningerMeyerStrongLogCohomology)
    (hu : ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j
      (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u) = 0) :
    ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j u = 0 := by
  induction L generalizing u with
  | nil => exact hu
  | cons rho L ih =>
    have hne : (tau : ℂ) ≠ rho := fun h => htau (List.mem_cons.mpr (Or.inl h))
    have htail : (tau : ℂ) ∉ L := fun h => htau (List.mem_cons.mpr (Or.inr h))
    exact ih htail u (deningerMeyerXiJets_zero_of_shift tau rho hne
      (deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u) hu)

/-- Every homogeneous finite-word solution in the global actual source space
is exactly its finite resonant packet, with the full packet equation retained. -/
theorem deningerMeyerObservableGeneratorWord_kernel (L : List ℂ)
    (u : DeningerMeyerObservableSource) :
    deningerMeyerGeneratorWord deningerMeyerObservableSourceGenerator L u = 0 ↔
      ((u : DeningerMeyerStrongLogCohomology) =
        deningerMeyerFiniteXiCausalProjector (deningerMeyerWordXiSupport L) u) ∧
      deningerMeyerGeneratorWord
        (deningerMeyerFiniteXiPacketGenerator (deningerMeyerWordXiSupport L)) L
        (deningerMeyerFiniteXiJetPacketLM (deningerMeyerWordXiSupport L) u) = 0 := by
  let S := deningerMeyerWordXiSupport L
  constructor
  · intro hu
    have hword : deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L u = 0 := by
      rw [← deningerMeyerObservableGeneratorWord_coe, hu]
      rfl
    have hres : (u : DeningerMeyerStrongLogCohomology) -
        deningerMeyerFiniteXiCausalProjector S u ∈ DeningerMeyerInvisible := by
      apply (mem_deningerMeyerInvisible_iff _).mpr
      intro tau j
      rw [map_sub]
      by_cases htau : tau ∈ S
      · have h := congrFun (deningerMeyerFiniteXiCausalProjector_jets S u)
          ⟨⟨tau, htau⟩, j⟩
        change deningerMeyerXiSupportJetEvaluationLM tau j
          (deningerMeyerFiniteXiCausalProjector S u) =
            deningerMeyerXiSupportJetEvaluationLM tau j u at h
        rw [h, sub_self]
      · have hnot : (tau : ℂ) ∉ L := fun h =>
          htau ((mem_deningerMeyerWordXiSupport L tau).mpr h)
        have hz := word_zero_jets L tau hnot u (fun i => by rw [hword, map_zero])
        rw [hz j]
        change 0 - deningerMeyerXiSupportJetEvaluationLM tau j
          (deningerMeyerFiniteXiCausalSection S _) = 0
        rw [deningerMeyerFiniteXiCausalSection_other_jet_zero S tau htau, sub_zero]
    have hzero := deningerMeyerGlobalCausalProjector_invisible ⟨_, hres⟩
    rw [map_sub, deningerMeyerObservableSource_fixed,
      deningerMeyerGlobalCausalProjector_finite_left] at hzero
    refine ⟨sub_eq_zero.mp hzero, ?_⟩
    rw [← deningerMeyerGeneratorWord_jets, hword, map_zero]
  · rintro ⟨hsource, hpacket⟩
    apply Subtype.ext
    change (deningerMeyerGeneratorWord deningerMeyerObservableSourceGenerator L u :
      DeningerMeyerStrongLogCohomology) = 0
    rw [deningerMeyerObservableGeneratorWord_coe, hsource]
    change deningerMeyerGeneratorWord deningerMeyerCohomologyGenerator L
      (deningerMeyerFiniteXiCausalSection S _) = 0
    rw [deningerMeyerGeneratorWord_section, hpacket, map_zero]

/-- Every off-divisor shifted generator is bijective on the actual global
observable source space: no forcing obstruction and no homogeneous ambiguity. -/
theorem deningerMeyerObservableSource_shift_bijective_of_xi_ne_zero
    (rho : ℂ) (hrho : xi rho ≠ 0) :
    Function.Bijective (deningerMeyerObservableSourceGenerator -
      rho • (LinearMap.id : Module.End ℂ DeningerMeyerObservableSource)) := by
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply deningerMeyerObservableSource_eq_zero
    have hzero : deningerMeyerCohomologyShift rho
        ((u - v : DeningerMeyerObservableSource) : DeningerMeyerStrongLogCohomology) = 0 := by
      have h := congrArg (fun z : DeningerMeyerObservableSource =>
        (z : DeningerMeyerStrongLogCohomology)) huv
      change deningerMeyerCohomologyShift rho u = deningerMeyerCohomologyShift rho v at h
      change deningerMeyerCohomologyShift rho
        ((u : DeningerMeyerStrongLogCohomology) - v) = 0
      rw [map_sub, h, sub_self]
    apply (mem_deningerMeyerInvisible_iff _).mpr
    intro tau j
    have hne : (tau : ℂ) ≠ rho := by
      intro h
      exact hrho (h ▸ xi_eq_zero_of_mem_divisor_support tau)
    exact deningerMeyerXiJets_zero_of_shift tau rho hne _
      (fun i => by rw [hzero, map_zero]) j
  · intro u
    obtain ⟨v, hv⟩ := deningerMeyerCohomologyShift_surjective_of_xi_ne_zero rho hrho
      (u : DeningerMeyerStrongLogCohomology)
    refine ⟨⟨deningerMeyerGlobalCausalProjector v, v, rfl⟩, ?_⟩
    apply Subtype.ext
    change deningerMeyerCohomologyGenerator (deningerMeyerGlobalCausalProjector v) -
      rho • deningerMeyerGlobalCausalProjector v = (u : DeningerMeyerStrongLogCohomology)
    rw [← deningerMeyerGlobalCausalProjector_generator, ← map_smul, ← map_sub]
    change deningerMeyerGlobalCausalProjector (deningerMeyerCohomologyShift rho v) = _
    rw [hv, deningerMeyerObservableSource_fixed]

/-- A simultaneous algebraic resolvent on the whole actual observable source
space, including its non-finite source classes. -/
def deningerMeyerObservableResolvent (rho : {rho : ℂ // xi rho ≠ 0}) :
    DeningerMeyerObservableSource ≃ₗ[ℂ] DeningerMeyerObservableSource :=
  (LinearEquiv.ofBijective
    (deningerMeyerObservableSourceGenerator -
      rho.val • (LinearMap.id : Module.End ℂ DeningerMeyerObservableSource))
    (deningerMeyerObservableSource_shift_bijective_of_xi_ne_zero rho.val rho.property)).symm

theorem deningerMeyerObservableResolvent_equation
    (rho : {rho : ℂ // xi rho ≠ 0}) (u : DeningerMeyerObservableSource) :
    deningerMeyerObservableSourceGenerator (deningerMeyerObservableResolvent rho u) -
      rho.val • deningerMeyerObservableResolvent rho u = u := by
  change (deningerMeyerObservableResolvent rho).symm
    (deningerMeyerObservableResolvent rho u) = u
  exact (deningerMeyerObservableResolvent rho).symm_apply_apply u

/-- The resolvents obey the exact resolvent identity, rather than being unrelated
choices of preimages modulo invisible homogeneous solutions. -/
theorem deningerMeyerObservableResolvent_identity
    (rho tau : {rho : ℂ // xi rho ≠ 0}) (u : DeningerMeyerObservableSource) :
    deningerMeyerObservableResolvent rho u - deningerMeyerObservableResolvent tau u =
      (rho.val - tau.val) •
        deningerMeyerObservableResolvent rho (deningerMeyerObservableResolvent tau u) := by
  apply (deningerMeyerObservableSource_shift_bijective_of_xi_ne_zero rho.val rho.property).1
  rw [map_sub, map_smul]
  change
    (deningerMeyerObservableSourceGenerator (deningerMeyerObservableResolvent rho u) -
      rho.val • deningerMeyerObservableResolvent rho u) -
    (deningerMeyerObservableSourceGenerator (deningerMeyerObservableResolvent tau u) -
      rho.val • deningerMeyerObservableResolvent tau u) =
    (rho.val - tau.val) •
      (deningerMeyerObservableSourceGenerator
          (deningerMeyerObservableResolvent rho (deningerMeyerObservableResolvent tau u)) -
        rho.val • deningerMeyerObservableResolvent rho (deningerMeyerObservableResolvent tau u))
  rw [deningerMeyerObservableResolvent_equation, deningerMeyerObservableResolvent_equation]
  conv_lhs => arg 1; rw [← deningerMeyerObservableResolvent_equation tau u]
  module

/-- Every Xi point has a nonzero eigenvector in the chosen actual source space. -/
theorem deningerMeyerObservableSource_eigenvector (rho : XiDivisorSupport) :
    ∃ u : DeningerMeyerObservableSource, u ≠ 0 ∧
      deningerMeyerObservableSourceGenerator u = (rho : ℂ) • u := by
  let j : DeningerArithmeticJetIndex rho :=
    ⟨xiSupportMultiplicity rho - 1, by have := xiSupportMultiplicity_pos rho; omega⟩
  let v := deningerMeyerXiJetSource rho j
  have hvP : deningerMeyerGlobalCausalProjector v = v := by
    let q : DeningerMeyerFiniteXiJetSlot {rho} :=
      ⟨⟨rho, Finset.mem_singleton_self rho⟩, j⟩
    have hS : deningerMeyerFiniteXiCausalSynthesis {rho} (Pi.single q 1) = v := by
      simp [q, v]
    rw [← hS, deningerMeyerGlobalCausalProjector_synthesis]
  let u : DeningerMeyerObservableSource := ⟨v, v, hvP⟩
  refine ⟨u, ?_, ?_⟩
  · intro hu
    have hv : v = 0 := congrArg (fun z : DeningerMeyerObservableSource =>
      (z : DeningerMeyerStrongLogCohomology)) hu
    have hj := deningerMeyerXiJetSource_jet_ne_zero rho j
    exact hj (by rw [show deningerMeyerXiJetSource rho j = 0 from hv, map_zero])
  · apply Subtype.ext
    change deningerMeyerCohomologyGenerator (deningerMeyerXiJetSource rho j) =
      (rho : ℂ) • deningerMeyerXiJetSource rho j
    rw [deningerMeyerXiJetSource_generator, dif_neg, add_zero]
    dsimp [j]
    omega

theorem deningerMeyerObservableSource_shift_bijective_iff (rho : ℂ) :
    Function.Bijective (deningerMeyerObservableSourceGenerator -
      rho • (LinearMap.id : Module.End ℂ DeningerMeyerObservableSource)) ↔ xi rho ≠ 0 := by
  constructor
  · intro h hz
    let tau : XiDivisorSupport := ⟨rho, mem_xi_divisor_support_of_eq_zero hz⟩
    obtain ⟨u, hune, hu⟩ := deningerMeyerObservableSource_eigenvector tau
    apply hune
    apply h.1
    change deningerMeyerObservableSourceGenerator u - rho • u =
      deningerMeyerObservableSourceGenerator 0 - rho • 0
    rw [hu, map_zero, smul_zero, sub_self, sub_self]
  · exact deningerMeyerObservableSource_shift_bijective_of_xi_ne_zero rho

/-- Exact algebraic spectrum of a global invariant subspace of literal Meyer
cohomology. This space includes all finite causal chains and non-finite sources. -/
theorem deningerMeyerObservableSource_spectrum :
    spectrum ℂ deningerMeyerObservableSourceGenerator = {rho : ℂ | xi rho = 0} := by
  ext rho
  rw [spectrum.mem_iff, IsUnit.sub_iff, Algebra.algebraMap_eq_smul_one,
    Module.End.isUnit_iff]
  change (¬ Function.Bijective (deningerMeyerObservableSourceGenerator -
    rho • (LinearMap.id : Module.End ℂ DeningerMeyerObservableSource))) ↔ xi rho = 0
  rw [deningerMeyerObservableSource_shift_bijective_iff]
  exact not_not

end
end RHTower
