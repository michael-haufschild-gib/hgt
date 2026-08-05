import GaloisForLFunctions.HTGeometry.ShilovCorrelationPathJoin

/-!
# Transmutation: every module is a two-edge migration obstruction

A prescribed module `D` is realized simultaneously, on one two-edge tower, as the deficit of the
upper link, the escape of the lower link, the excess of the two-step composition over the direct
correlation, and the degree-one migration cohomology of the tower — even though the upper link and
the composite are both escape-free.

Main results:

* `transmutation_escapeFree_upper`, `transmutation_escapeFree_composite`: the upper link and the
  composite carry no escape;
* `transmutationDeficitEquiv`, `transmutationEscapeEquiv`: the upper deficit and the lower escape
  are both `D`;
* `transmutation_relationalComp_ne`, `transmutationCompositionExcessEquiv`: the two-step
  composition is strictly larger than the direct correlation, with excess `D`;
* `transmutationCohomologyEquiv`: the degree-one migration cohomology of the tower is `D`.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

section RelativeQuotientHelpers

variable {𝕜 : Type u} [Field 𝕜] {V : Type v} [AddCommGroup V] [Module 𝕜 V]

/-- A relative quotient with full numerator and trivial divisor is the ambient module. -/
noncomputable def relativeQuotientEquivOfTopOfBot (L M : Submodule 𝕜 V) (hM : M = ⊤)
    (hL : L = ⊥) : RelativeQuotient L M ≃ₗ[𝕜] V :=
  (Submodule.quotEquivOfEq (L.comap M.subtype) ⊥ (by
    rw [hL, Submodule.comap_bot, Submodule.ker_subtype])).trans
    ((Submodule.quotEquivOfEqBot (⊥ : Submodule 𝕜 M) rfl).trans
      ((LinearEquiv.ofEq M ⊤ hM).trans Submodule.topEquiv))

end RelativeQuotientHelpers

section Transmutation

variable (𝕜 : Type u) [Field 𝕜] (D : Type v) [AddCommGroup D] [Module 𝕜 D]

/-- Bonds of the two-edge transmutation tower: the identity on the bottom edge, zero above. -/
def transmutationBond : ℕ → (D →ₗ[𝕜] D)
  | 0 => LinearMap.id
  | _ + 1 => 0

/-- Boundary submodules of the two-edge transmutation tower. -/
def transmutationBoundary : ℕ → Submodule 𝕜 D
  | 0 => ⊥
  | 1 => ⊤
  | _ + 2 => ⊥

@[simp] theorem transmutationBond_zero : transmutationBond 𝕜 D 0 = LinearMap.id := rfl

@[simp] theorem transmutationBond_succ (n : ℕ) : transmutationBond 𝕜 D (n + 1) = 0 := rfl

@[simp] theorem transmutationBoundary_zero : transmutationBoundary 𝕜 D 0 = ⊥ := rfl

@[simp] theorem transmutationBoundary_one : transmutationBoundary 𝕜 D 1 = ⊤ := rfl

@[simp] theorem transmutationBoundary_add_two (n : ℕ) :
    transmutationBoundary 𝕜 D (n + 2) = ⊥ := rfl

/-- The upper link of the tower is escape-free. -/
theorem transmutation_escapeFree_upper :
    EscapeFree (transmutationBond 𝕜 D 1) (transmutationBoundary 𝕜 D 2)
      (transmutationBoundary 𝕜 D 1) := by
  show Submodule.map (0 : D →ₗ[𝕜] D) ⊥ ≤ ⊤
  exact le_top

/-- The composite of the two links is escape-free. -/
theorem transmutation_escapeFree_composite :
    EscapeFree (transmutationBond 𝕜 D 0 ∘ₗ transmutationBond 𝕜 D 1)
      (transmutationBoundary 𝕜 D 2) (transmutationBoundary 𝕜 D 0) := by
  show Submodule.map (LinearMap.id ∘ₗ (0 : D →ₗ[𝕜] D)) ⊥ ≤ ⊥
  rw [Submodule.map_bot]

/-- The deficit of the upper link is the prescribed module. -/
noncomputable def transmutationDeficitEquiv :
    DeficitDefect (transmutationBond 𝕜 D 1) (transmutationBoundary 𝕜 D 2)
      (transmutationBoundary 𝕜 D 1) ≃ₗ[𝕜] D :=
  relativeQuotientEquivOfTopOfBot _ _ rfl (by
    show Submodule.map (0 : D →ₗ[𝕜] D) ⊥ = ⊥
    rw [Submodule.map_bot])

/-- The escape of the lower link is the prescribed module. -/
noncomputable def transmutationEscapeEquiv :
    EscapeDefect (transmutationBond 𝕜 D 0) (transmutationBoundary 𝕜 D 1)
      (transmutationBoundary 𝕜 D 0) ≃ₗ[𝕜] D :=
  relativeQuotientEquivOfTopOfBot _ _ (by
    show Submodule.map (LinearMap.id : D →ₗ[𝕜] D) ⊤ = ⊤
    rw [Submodule.map_id]) rfl

theorem transmutation_edgeJoin_composite :
    edgeJoin (transmutationBond 𝕜 D 0 ∘ₗ transmutationBond 𝕜 D 1)
      (transmutationBoundary 𝕜 D 2) (transmutationBoundary 𝕜 D 0) = ⊥ :=
  (edgeJoin_eq_target_iff_escapeFree _ _ _).mpr (transmutation_escapeFree_composite 𝕜 D)

/-- The two-step composition is strictly larger than the direct correlation. -/
theorem transmutation_relationalComp_ne [Nontrivial D] :
    relationalComp
        (envelopeCorrelation (transmutationBond 𝕜 D 1) (transmutationBoundary 𝕜 D 2)
          (transmutationBoundary 𝕜 D 1))
        (envelopeCorrelation (transmutationBond 𝕜 D 0) (transmutationBoundary 𝕜 D 1)
          (transmutationBoundary 𝕜 D 0)) ≠
      envelopeCorrelation (transmutationBond 𝕜 D 0 ∘ₗ transmutationBond 𝕜 D 1)
        (transmutationBoundary 𝕜 D 2) (transmutationBoundary 𝕜 D 0) := by
  rw [Ne, relationalComp_eq_envelopeCorrelation_iff, transmutation_edgeJoin_composite]
  intro hle
  have htop : (⊤ : Submodule 𝕜 D) ≤ ⊥ := by
    have : Submodule.map (transmutationBond 𝕜 D 0) (transmutationBoundary 𝕜 D 1) = ⊤ := by
      show Submodule.map (LinearMap.id : D →ₗ[𝕜] D) ⊤ = ⊤
      rw [Submodule.map_id]
    rwa [this] at hle
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial D)
  exact hxy (by
    have hx : x = 0 := (Submodule.mem_bot 𝕜).mp (htop Submodule.mem_top)
    have hy : y = 0 := (Submodule.mem_bot 𝕜).mp (htop Submodule.mem_top)
    rw [hx, hy])

/-- The excess of the two-step composition over the direct correlation is the prescribed
module. -/
noncomputable def transmutationCompositionExcessEquiv :
    RelativeQuotient
      (edgeJoin (transmutationBond 𝕜 D 0 ∘ₗ transmutationBond 𝕜 D 1)
        (transmutationBoundary 𝕜 D 2) (transmutationBoundary 𝕜 D 0))
      (Submodule.map (transmutationBond 𝕜 D 0) (transmutationBoundary 𝕜 D 1)) ≃ₗ[𝕜] D :=
  relativeQuotientEquivOfTopOfBot _ _ (by
    show Submodule.map (LinearMap.id : D →ₗ[𝕜] D) ⊤ = ⊤
    rw [Submodule.map_id]) (transmutation_edgeJoin_composite 𝕜 D)

theorem transmutationEdge_zero :
    migrationEdge (fun _ => D) (transmutationBond 𝕜 D) (transmutationBoundary 𝕜 D) 0 = ⊤ := by
  show (⊥ : Submodule 𝕜 D) ⊔ Submodule.map (LinearMap.id : D →ₗ[𝕜] D) ⊤ = ⊤
  rw [Submodule.map_id, bot_sup_eq]

theorem transmutationEdge_one :
    migrationEdge (fun _ => D) (transmutationBond 𝕜 D) (transmutationBoundary 𝕜 D) 1 = ⊤ := by
  show (⊤ : Submodule 𝕜 D) ⊔ Submodule.map (0 : D →ₗ[𝕜] D) ⊥ = ⊤
  rw [top_sup_eq]

theorem transmutationEdge_add_two (n : ℕ) :
    migrationEdge (fun _ => D) (transmutationBond 𝕜 D) (transmutationBoundary 𝕜 D) (n + 2) =
      ⊥ := by
  show (⊥ : Submodule 𝕜 D) ⊔ Submodule.map (0 : D →ₗ[𝕜] D) ⊥ = ⊥
  rw [Submodule.map_bot, bot_sup_eq]

/-- Evaluation detecting the degree-one migration class of the transmutation tower. -/
noncomputable def transmutationEvaluation :
    (∀ n, migrationEdge (fun _ => D) (transmutationBond 𝕜 D) (transmutationBoundary 𝕜 D) n)
      →ₗ[𝕜] D :=
  (migrationEdge (fun _ => D) (transmutationBond 𝕜 D)
        (transmutationBoundary 𝕜 D) 0).subtype.comp (LinearMap.proj 0) +
    (migrationEdge (fun _ => D) (transmutationBond 𝕜 D)
        (transmutationBoundary 𝕜 D) 1).subtype.comp (LinearMap.proj 1)

theorem transmutationEvaluation_apply
    (c : ∀ n, migrationEdge (fun _ => D) (transmutationBond 𝕜 D)
      (transmutationBoundary 𝕜 D) n) :
    transmutationEvaluation 𝕜 D c = (c 0 : D) + (c 1 : D) :=
  rfl

theorem transmutationEvaluation_surjective :
    Function.Surjective (transmutationEvaluation 𝕜 D) := by
  intro x
  refine ⟨fun n =>
    match n with
    | 0 => ⟨x, by rw [transmutationEdge_zero]; exact Submodule.mem_top⟩
    | _ + 1 => 0, ?_⟩
  rw [transmutationEvaluation_apply]
  show x + (0 : D) = x
  rw [add_zero]

theorem ker_transmutationEvaluation :
    LinearMap.ker (transmutationEvaluation 𝕜 D) =
      LinearMap.range (migrationDifference (fun _ => D) (transmutationBond 𝕜 D)
        (transmutationBoundary 𝕜 D)) := by
  apply le_antisymm
  · intro c hc
    have hc' : (c 0 : D) + (c 1 : D) = 0 := hc
    refine ⟨fun n =>
      match n with
      | 0 => 0
      | 1 => ⟨(c 0 : D), by rw [transmutationBoundary_one]; exact Submodule.mem_top⟩
      | _ + 2 => 0, ?_⟩
    funext n
    apply Subtype.ext
    match n with
    | 0 =>
      show (LinearMap.id : D →ₗ[𝕜] D) (c 0 : D) - (0 : D) = (c 0 : D)
      rw [sub_zero]
      rfl
    | 1 =>
      show (0 : D →ₗ[𝕜] D) (0 : D) - (c 0 : D) = (c 1 : D)
      show (0 : D) - (c 0 : D) = (c 1 : D)
      rw [zero_sub]
      exact neg_eq_of_add_eq_zero_right hc'
    | m + 2 =>
      show (0 : D →ₗ[𝕜] D) (0 : D) - (0 : D) = (c (m + 2) : D)
      show (0 : D) - (0 : D) = (c (m + 2) : D)
      rw [sub_zero]
      exact (((migrationEdge (fun _ => D) (transmutationBond 𝕜 D)
        (transmutationBoundary 𝕜 D) (m + 2)).eq_bot_iff.mp
          (transmutationEdge_add_two 𝕜 D m)) _ (c (m + 2)).2).symm
  · rintro _ ⟨j, rfl⟩
    show ((migrationDifference (fun _ => D) (transmutationBond 𝕜 D)
      (transmutationBoundary 𝕜 D) j) 0 : D) +
      ((migrationDifference (fun _ => D) (transmutationBond 𝕜 D)
        (transmutationBoundary 𝕜 D) j) 1 : D) = 0
    have h0 : (j 0 : D) = 0 := (Submodule.mem_bot 𝕜).mp (j 0).2
    show ((LinearMap.id : D →ₗ[𝕜] D) (j 1 : D) - (j 0 : D)) +
      ((0 : D →ₗ[𝕜] D) (j 2 : D) - (j 1 : D)) = 0
    rw [h0]
    show ((j 1 : D) - 0) + (0 - (j 1 : D)) = 0
    abel

/-- The degree-one migration cohomology of the transmutation tower is the prescribed module. -/
noncomputable def transmutationCohomologyEquiv :
    MigrationCohomologyOne (fun _ => D) (transmutationBond 𝕜 D)
      (transmutationBoundary 𝕜 D) ≃ₗ[𝕜] D :=
  (Submodule.quotEquivOfEq _ _ (ker_transmutationEvaluation 𝕜 D).symm).trans
    ((transmutationEvaluation 𝕜 D).quotKerEquivOfSurjective
      (transmutationEvaluation_surjective 𝕜 D))

end Transmutation

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
