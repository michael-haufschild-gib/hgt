import GaloisForLFunctions.HTGeometry.FinitelyPresentedCentralKernel

/-!
# Basic stability of finite presentability

A presentation on any finite generating type is as good as one on `Fin n`, finite presentability
transfers along isomorphisms, and every finite group is finitely presented by its multiplication
table: in the quotient of the free group on the underlying set by the relators `a · b · (ab)⁻¹` the
generators multiply exactly as in the group, so that quotient is the group.

Finite groups being finitely presented is the input that lets a group action with **finite**
stabilizers feed a presentation criterion.

* `map_normalClosure_of_mulEquiv` : an isomorphism carries normal closures to normal closures.
* `isFinitelyPresented_of_free_presentation` : any finite generating type will do.
* `IsFinitelyPresented.of_mulEquiv` : transfer along an isomorphism.
* `isFinitelyPresented_of_finite` : **every finite group is finitely presented.**
-/

namespace GaloisForLFunctions.HTGeometry

open Subgroup

/-- An isomorphism carries a normal closure to the normal closure of the image. -/
theorem map_normalClosure_of_mulEquiv {G H : Type*} [Group G] [Group H] (f : G ≃* H) (S : Set G) :
    Subgroup.map (f : G →* H) (normalClosure S) = normalClosure ((f : G →* H) '' S) := by
  refine le_antisymm (map_normalClosure_le _ _) ?_
  have hback := map_normalClosure_le (f.symm : H →* G) ((f : G →* H) '' S)
  have hsymm : ∀ y : G, (f.symm : H →* G) ((f : G →* H) y) = y := by
    intro y
    simp
  have himg : (f.symm : H →* G) '' ((f : G →* H) '' S) = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [hsymm y]
      exact hy
    · intro hx
      exact ⟨(f : G →* H) x, ⟨x, hx, rfl⟩, hsymm x⟩
  rw [himg] at hback
  intro x hx
  exact ⟨(f.symm : H →* G) x, hback ⟨x, hx, rfl⟩, by simp⟩

/-- A presentation on **any** finite generating type gives finite presentability. -/
theorem isFinitelyPresented_of_free_presentation {X : Type*} [Finite X] {G : Type*} [Group G]
    (ψ : FreeGroup X →* G) (hψ : Function.Surjective ψ) {S : Set (FreeGroup X)} (hS : S.Finite)
    (hker : ψ.ker = normalClosure S) : IsFinitelyPresented G := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  refine ⟨m, ψ.comp ((FreeGroup.freeGroupCongr e).symm : FreeGroup (Fin m) →* FreeGroup X),
    hψ.comp (FreeGroup.freeGroupCongr e).symm.surjective,
    ((FreeGroup.freeGroupCongr e : FreeGroup X ≃* FreeGroup (Fin m)) :
      FreeGroup X →* FreeGroup (Fin m)) '' S, hS.image _, ?_⟩
  rw [← MonoidHom.comap_ker ψ, hker, Subgroup.comap_equiv_eq_map_symm, MulEquiv.symm_symm,
    map_normalClosure_of_mulEquiv]

/-- Finite presentability transfers along an isomorphism. -/
theorem IsFinitelyPresented.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨n, ψ, hψ, S, hS, hker⟩ := hG
  refine ⟨n, (e : G →* H).comp ψ, e.surjective.comp hψ, S, hS, ?_⟩
  rw [← hker]
  exact MonoidHom.ker_comp_of_injective ψ (e : G →* H) e.injective

/-- The multiplication-table relators of a group. -/
def multTableRelators (G : Type*) [Group G] : Set (FreeGroup G) :=
  Set.range (fun p : G × G => FreeGroup.of p.1 * FreeGroup.of p.2 * (FreeGroup.of (p.1 * p.2))⁻¹)

theorem multTableRelators_finite {G : Type*} [Group G] [Finite G] :
    (multTableRelators G).Finite := Set.finite_range _

theorem normalClosure_multTableRelators_le_ker {G : Type*} [Group G] :
    normalClosure (multTableRelators G) ≤ (FreeGroup.lift (id : G → G)).ker := by
  refine normalClosure_le_normal ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simp [SetLike.mem_coe, MonoidHom.mem_ker]

theorem quotient_multTable_mul {G : Type*} [Group G] (a b : G) :
    (QuotientGroup.mk' (normalClosure (multTableRelators G))) (FreeGroup.of (a * b))
      = (QuotientGroup.mk' (normalClosure (multTableRelators G))) (FreeGroup.of a)
        * (QuotientGroup.mk' (normalClosure (multTableRelators G))) (FreeGroup.of b) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hmem : (FreeGroup.of a * FreeGroup.of b * (FreeGroup.of (a * b))⁻¹)
      ∈ normalClosure (multTableRelators G) := subset_normalClosure ⟨(a, b), rfl⟩
  have hconj := (normalClosure_normal (s := multTableRelators G)).conj_mem _ hmem
    (FreeGroup.of (a * b))⁻¹
  have heq : (FreeGroup.of (a * b))⁻¹ * (FreeGroup.of a * FreeGroup.of b
        * (FreeGroup.of (a * b))⁻¹) * ((FreeGroup.of (a * b))⁻¹)⁻¹
      = (FreeGroup.of (a * b))⁻¹ * (FreeGroup.of a * FreeGroup.of b) := by group
  rwa [heq] at hconj

theorem ker_le_normalClosure_multTableRelators {G : Type*} [Group G] :
    (FreeGroup.lift (id : G → G)).ker ≤ normalClosure (multTableRelators G) := by
  have hcomp : (MonoidHom.mk' (fun a : G =>
        (QuotientGroup.mk' (normalClosure (multTableRelators G))) (FreeGroup.of a))
      quotient_multTable_mul).comp (FreeGroup.lift (id : G → G))
      = QuotientGroup.mk' (normalClosure (multTableRelators G)) :=
    FreeGroup.ext_hom _ _ fun a => by simp
  intro w hw
  have h1 := (congrArg
    (fun f : FreeGroup G →* FreeGroup G ⧸ normalClosure (multTableRelators G) => f w) hcomp).symm
  simp only [MonoidHom.coe_comp, Function.comp_apply] at h1
  rw [MonoidHom.mem_ker.1 hw, map_one] at h1
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

/-- **Every finite group is finitely presented**, by its multiplication table. -/
theorem isFinitelyPresented_of_finite {G : Type*} [Group G] [Finite G] :
    IsFinitelyPresented G :=
  isFinitelyPresented_of_free_presentation (FreeGroup.lift (id : G → G))
    (fun g => ⟨FreeGroup.of g, by simp⟩) multTableRelators_finite
    (le_antisymm ker_le_normalClosure_multTableRelators normalClosure_multTableRelators_le_ker)

end GaloisForLFunctions.HTGeometry
