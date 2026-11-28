import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible

/-! A fixed type spans all fixed vectors in an irreducible
representation if its translates return to the type modulo the
coinvariant relations. Compact averaging provides the disjointness. -/

noncomputable section

namespace Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem invariants_eq_range_of_orbit_mod_coinvariants
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (H : Subgroup G)
    (hcomp : Disjoint (invariants (ρ.comp H.subtype)) (Coinvariants.ker (ρ.comp H.subtype)))
    (j : W →ₗ[ℂ] V) (hj : j ≠ 0)
    (hjfix : LinearMap.range j ≤ invariants (ρ.comp H.subtype))
    (hgen : ∀ g w, ρ g (j w) ∈ LinearMap.range j ⊔ Coinvariants.ker (ρ.comp H.subtype)) :
    invariants (ρ.comp H.subtype) = LinearMap.range j := by
  let S := Submodule.span ℂ {v : V | ∃ g w, ρ g (j w) = v}
  have hs (g : G) (v : V) (hv : v ∈ S) : ρ g v ∈ S := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g', w, rfl⟩
      refine Submodule.subset_span ⟨g * g', w, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]
      exact S.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact S.smul_mem c hx
  let U : Subrepresentation ρ := ⟨S, fun g {v} hv => hs g v hv⟩
  have hjU (w : W) : j w ∈ U :=
    Submodule.subset_span ⟨1, w, by rw [map_one, Module.End.one_apply]⟩
  have hU : U = ⊤ := (eq_bot_or_eq_top U).resolve_left fun h => hj (by
    apply LinearMap.ext
    intro w
    have hw := hjU w
    rw [h] at hw
    exact hw)
  have hS : S = ⊤ := congrArg Subrepresentation.toSubmodule hU
  have hle : S ≤ LinearMap.range j ⊔ Coinvariants.ker (ρ.comp H.subtype) :=
    Submodule.span_le.mpr (by rintro v ⟨g, w, rfl⟩; exact hgen g w)
  refine le_antisymm ?_ hjfix
  intro v hv
  have hvS : v ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hvS)
  have hbf : b ∈ invariants (ρ.comp H.subtype) := by
    simpa using (invariants (ρ.comp H.subtype)).sub_mem hv (hjfix ha)
  have hb0 := Submodule.disjoint_def.mp hcomp b hbf hb
  rwa [hb0, add_zero]

end Representation

#print axioms Representation.invariants_eq_range_of_orbit_mod_coinvariants
