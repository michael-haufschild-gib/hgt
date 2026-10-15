import GaloisForLFunctions.RHTower.DeningerMeyerInvisiblePolynomialInjectivity

/-!
# A global generator-equivariant splitting preserving every causal Xi packet

Let `K` be the invisible comparison kernel and `F` the union of all finite
causal Xi ranges. Actual source independence gives `K ∩ F = 0`. Polynomial
injectivity of `K` therefore extends its identity across `Q/F`. Pulling this
extension back gives a retraction that kills `F`, hence one global spectral
projector with kernel `K` that fixes every finite causal packet.

No global spectral synthesis or continuity of the chosen projector is assumed.
-/

open Polynomial
open scoped Classical

namespace RHTower
noncomputable section

theorem deningerMeyerFiniteXiCausalRange_mono
    {S T : Finset XiDivisorSupport} (hST : S ⊆ T) :
    LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S) ≤
      LinearMap.range (deningerMeyerFiniteXiCausalSynthesis T) := by
  rintro u ⟨c, rfl⟩
  rw [deningerMeyerFiniteXiCausalSynthesis_apply]
  apply Submodule.sum_mem
  intro q _
  apply Submodule.smul_mem
  refine ⟨Pi.single ⟨⟨q.1.1, hST q.1.2⟩, q.2⟩ 1, ?_⟩
  simp

/-- The actual finite causal modes, allowing arbitrary finite Xi support. -/
def DeningerMeyerFiniteCausalModes : Submodule ℂ DeningerMeyerStrongLogCohomology where
  carrier := {u | ∃ S : Finset XiDivisorSupport,
    u ∈ LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S)}
  zero_mem' := ⟨∅, Submodule.zero_mem _⟩
  add_mem' := by
    rintro u v ⟨S, hS⟩ ⟨T, hT⟩
    exact ⟨S ∪ T, Submodule.add_mem _
      (deningerMeyerFiniteXiCausalRange_mono Finset.subset_union_left hS)
      (deningerMeyerFiniteXiCausalRange_mono Finset.subset_union_right hT)⟩
  smul_mem' := by
    rintro c u ⟨S, hS⟩
    exact ⟨S, Submodule.smul_mem _ c hS⟩

theorem deningerMeyerFiniteCausalModes_generator_mem
    (u : DeningerMeyerFiniteCausalModes) :
    deningerMeyerCohomologyGenerator u ∈ DeningerMeyerFiniteCausalModes := by
  obtain ⟨S, hS⟩ := u.property
  exact ⟨S, deningerMeyerFiniteXiCausalRange_generator S u hS⟩

def deningerMeyerFiniteCausalModesGenerator : Module.End ℂ DeningerMeyerFiniteCausalModes :=
  deningerMeyerCohomologyGenerator.restrict
    (fun u hu => deningerMeyerFiniteCausalModes_generator_mem ⟨u, hu⟩)

/-- No nonzero finite causal mode is invisible. -/
theorem deningerMeyerFiniteCausalModes_invisible_eq_zero
    (u : DeningerMeyerStrongLogCohomology)
    (hF : u ∈ DeningerMeyerFiniteCausalModes) (hK : u ∈ DeningerMeyerInvisible) :
    u = 0 := by
  obtain ⟨S, c, rfl⟩ := hF
  have hE : deningerMeyerFiniteXiJetPacketLM S
      (deningerMeyerFiniteXiCausalSynthesis S c) = 0 := by
    funext q
    exact (mem_deningerMeyerInvisible_iff _).mp hK q.1.1 q.2
  rw [← deningerMeyerFiniteXiCausalProjector_synthesis S c]
  change deningerMeyerFiniteXiCausalSection S
    (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSynthesis S c)) = 0
  rw [hE, map_zero]

private def finiteCausalPolynomialInclusion :
    Module.AEval' deningerMeyerFiniteCausalModesGenerator →ₗ[ℂ[X]]
      DeningerMeyerCohomologyPolynomialModule :=
  LinearMap.ofAEval deningerMeyerFiniteCausalModesGenerator
    ((Module.AEval'.of deningerMeyerCohomologyGenerator).toLinearMap.comp
      DeningerMeyerFiniteCausalModes.subtype)
    (fun u => (Module.AEval'.X_smul_of deningerMeyerCohomologyGenerator
      (u : DeningerMeyerStrongLogCohomology)).symm)

private def finiteCausalPolynomialRange :
    Submodule ℂ[X] DeningerMeyerCohomologyPolynomialModule :=
  LinearMap.range finiteCausalPolynomialInclusion

private theorem mem_finiteCausalPolynomialRange
    (u : DeningerMeyerCohomologyPolynomialModule) :
    u ∈ finiteCausalPolynomialRange ↔
      (Module.AEval'.of deningerMeyerCohomologyGenerator).symm u ∈
        DeningerMeyerFiniteCausalModes := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ((Module.AEval'.of deningerMeyerFiniteCausalModesGenerator).symm v).property
  · intro hu
    exact ⟨Module.AEval'.of deningerMeyerFiniteCausalModesGenerator
      ⟨(Module.AEval'.of deningerMeyerCohomologyGenerator).symm u, hu⟩, rfl⟩

private def invisibleModuloFinite :
    DeningerMeyerInvisiblePolynomialModule →ₗ[ℂ[X]]
      DeningerMeyerCohomologyPolynomialModule ⧸ finiteCausalPolynomialRange :=
  finiteCausalPolynomialRange.mkQ.comp deningerMeyerInvisiblePolynomialInclusion

private theorem invisibleModuloFinite_injective :
    Function.Injective invisibleModuloFinite := by
  intro u v huv
  have hF : deningerMeyerInvisiblePolynomialInclusion u -
      deningerMeyerInvisiblePolynomialInclusion v ∈ finiteCausalPolynomialRange :=
    Submodule.Quotient.eq.mp huv
  rw [← map_sub] at hF
  apply sub_eq_zero.mp
  apply (Module.AEval'.of deningerMeyerInvisibleGenerator).symm.injective
  apply Subtype.ext
  exact deningerMeyerFiniteCausalModes_invisible_eq_zero _
    ((mem_finiteCausalPolynomialRange _).mp hF)
    ((Module.AEval'.of deningerMeyerInvisibleGenerator).symm (u - v)).property

/-- One generator-equivariant retraction of the global invisible kernel can kill
all finite causal modes simultaneously. -/
theorem deningerMeyerInvisible_exists_causalRetraction :
    ∃ r : DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerMeyerInvisible,
      (∀ u : DeningerMeyerInvisible, r u = u) ∧
      (∀ u, r (deningerMeyerCohomologyGenerator u) = deningerMeyerInvisibleGenerator (r u)) ∧
      (∀ u ∈ DeningerMeyerFiniteCausalModes, r u = 0) := by
  obtain ⟨r, hr⟩ := deningerMeyerInvisiblePolynomial_baer.extension_property
    invisibleModuloFinite invisibleModuloFinite_injective LinearMap.id
  let rpoly := r.comp finiteCausalPolynomialRange.mkQ
  let rC : DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerMeyerInvisible :=
    (Module.AEval'.of deningerMeyerInvisibleGenerator).symm.toLinearMap.comp
      ((rpoly.restrictScalars ℂ).comp
        (Module.AEval'.of deningerMeyerCohomologyGenerator).toLinearMap)
  refine ⟨rC, ?_, ?_, ?_⟩
  · intro u
    have h := LinearMap.congr_fun hr (Module.AEval'.of deningerMeyerInvisibleGenerator u)
    exact congrArg (Module.AEval'.of deningerMeyerInvisibleGenerator).symm h
  · intro u
    change (Module.AEval'.of deningerMeyerInvisibleGenerator).symm
      (rpoly (Module.AEval'.of deningerMeyerCohomologyGenerator
        (deningerMeyerCohomologyGenerator u))) = _
    rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]
    rfl
  · intro u hu
    have hq : finiteCausalPolynomialRange.mkQ
        (Module.AEval'.of deningerMeyerCohomologyGenerator u) = 0 :=
      Submodule.Quotient.mk_eq_zero.mpr ((mem_finiteCausalPolynomialRange _).mpr hu)
    change (Module.AEval'.of deningerMeyerInvisibleGenerator).symm
      (r (finiteCausalPolynomialRange.mkQ
        (Module.AEval'.of deningerMeyerCohomologyGenerator u))) = 0
    rw [hq, map_zero, map_zero]

/-- A fixed choice of the compatible invisible retraction. -/
def deningerMeyerInvisibleCausalRetraction :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerMeyerInvisible :=
  Classical.choose deningerMeyerInvisible_exists_causalRetraction

theorem deningerMeyerInvisibleCausalRetraction_invisible (u : DeningerMeyerInvisible) :
    deningerMeyerInvisibleCausalRetraction u = u :=
  (Classical.choose_spec deningerMeyerInvisible_exists_causalRetraction).1 u

theorem deningerMeyerInvisibleCausalRetraction_generator
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerInvisibleCausalRetraction (deningerMeyerCohomologyGenerator u) =
      deningerMeyerInvisibleGenerator (deningerMeyerInvisibleCausalRetraction u) :=
  (Classical.choose_spec deningerMeyerInvisible_exists_causalRetraction).2.1 u

theorem deningerMeyerInvisibleCausalRetraction_finite
    (u : DeningerMeyerStrongLogCohomology) (hu : u ∈ DeningerMeyerFiniteCausalModes) :
    deningerMeyerInvisibleCausalRetraction u = 0 :=
  (Classical.choose_spec deningerMeyerInvisible_exists_causalRetraction).2.2 u hu

/-- The global source projector; its kernel is precisely the invisible sector. -/
def deningerMeyerGlobalCausalProjector : Module.End ℂ DeningerMeyerStrongLogCohomology :=
  LinearMap.id - DeningerMeyerInvisible.subtype.comp deningerMeyerInvisibleCausalRetraction

theorem deningerMeyerGlobalCausalProjector_invisible (u : DeningerMeyerInvisible) :
    deningerMeyerGlobalCausalProjector u = 0 := by
  change (u : DeningerMeyerStrongLogCohomology) -
    (deningerMeyerInvisibleCausalRetraction u : DeningerMeyerStrongLogCohomology) = 0
  rw [deningerMeyerInvisibleCausalRetraction_invisible, sub_self]

theorem deningerMeyerGlobalCausalProjector_comparison
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCompactOpenXiComparison (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerCompactOpenXiComparison u := by
  change deningerMeyerCompactOpenXiComparison
    (u - (deningerMeyerInvisibleCausalRetraction u : DeningerMeyerStrongLogCohomology)) = _
  rw [map_sub, (deningerMeyerInvisibleCausalRetraction u).property, sub_zero]

theorem deningerMeyerGlobalCausalProjector_jets
    (u : DeningerMeyerStrongLogCohomology) (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerXiSupportJetEvaluationLM rho j u := by
  change deningerMeyerXiSupportJetEvaluationLM rho j
    (u - (deningerMeyerInvisibleCausalRetraction u : DeningerMeyerStrongLogCohomology)) = _
  rw [map_sub, (mem_deningerMeyerInvisible_iff _).mp
    (deningerMeyerInvisibleCausalRetraction u).property rho j, sub_zero]

/-- The global splitting preserves the actual logarithmic generator. -/
theorem deningerMeyerGlobalCausalProjector_generator
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalCausalProjector (deningerMeyerCohomologyGenerator u) =
      deningerMeyerCohomologyGenerator (deningerMeyerGlobalCausalProjector u) := by
  change deningerMeyerCohomologyGenerator u -
      (deningerMeyerInvisibleCausalRetraction (deningerMeyerCohomologyGenerator u) :
        DeningerMeyerStrongLogCohomology) =
    deningerMeyerCohomologyGenerator
      (u - (deningerMeyerInvisibleCausalRetraction u : DeningerMeyerStrongLogCohomology))
  rw [deningerMeyerInvisibleCausalRetraction_generator, map_sub]
  rfl

@[simp]
theorem deningerMeyerGlobalCausalProjector_idempotent
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalCausalProjector (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerGlobalCausalProjector u := by
  change deningerMeyerGlobalCausalProjector
    (u - (deningerMeyerInvisibleCausalRetraction u : DeningerMeyerStrongLogCohomology)) = _
  rw [map_sub, deningerMeyerGlobalCausalProjector_invisible, sub_zero]

/-- No invisible homogeneous mode survives in the projected actual source space. -/
theorem deningerMeyerGlobalCausalProjector_ker :
    LinearMap.ker deningerMeyerGlobalCausalProjector = DeningerMeyerInvisible := by
  ext u
  constructor
  · intro hu
    change deningerMeyerCompactOpenXiComparison u = 0
    rw [← deningerMeyerGlobalCausalProjector_comparison u, hu, map_zero]
  · intro hu
    exact deningerMeyerGlobalCausalProjector_invisible ⟨u, hu⟩

/-- Every finite Hedenmalm causal source packet keeps its original representative. -/
theorem deningerMeyerGlobalCausalProjector_synthesis
    (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerGlobalCausalProjector (deningerMeyerFiniteXiCausalSynthesis S c) =
      deningerMeyerFiniteXiCausalSynthesis S c := by
  change deningerMeyerFiniteXiCausalSynthesis S c -
    (deningerMeyerInvisibleCausalRetraction (deningerMeyerFiniteXiCausalSynthesis S c) :
      DeningerMeyerStrongLogCohomology) = _
  rw [deningerMeyerInvisibleCausalRetraction_finite _ ⟨S, c, rfl⟩]
  exact sub_zero _

theorem deningerMeyerGlobalCausalProjector_finite_left
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalCausalProjector (deningerMeyerFiniteXiCausalProjector S u) =
      deningerMeyerFiniteXiCausalProjector S u :=
  deningerMeyerGlobalCausalProjector_synthesis S _

theorem deningerMeyerGlobalCausalProjector_finite_right
    (S : Finset XiDivisorSupport) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerFiniteXiCausalProjector S u := by
  have hE : deningerMeyerFiniteXiJetPacketLM S (deningerMeyerGlobalCausalProjector u) =
      deningerMeyerFiniteXiJetPacketLM S u := by
    funext q
    exact deningerMeyerGlobalCausalProjector_jets u q.1.1 q.2
  exact congrArg (deningerMeyerFiniteXiCausalSection S) hE

end
end RHTower
