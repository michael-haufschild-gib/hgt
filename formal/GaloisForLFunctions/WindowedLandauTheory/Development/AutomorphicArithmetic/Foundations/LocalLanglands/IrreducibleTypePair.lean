import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! Two irreducible representations sharing a type are equivalent
when the fixed part of the generated product representation is the
diagonal type. A nonzero coordinate kernel would supply an extra
fixed vector. -/

noncomputable section

namespace Representation

variable {G V V' W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [Nontrivial W]

private theorem surjective_of_nonzero_to_irreducible {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {r : Representation ℂ G A} {s : Representation ℂ G B} [s.IsIrreducible]
    (f : r.IntertwiningMap s) (hf : ∃ x, f x ≠ 0) : Function.Surjective f := by
  have htop : f.range = ⊤ := (eq_bot_or_eq_top f.range).resolve_left fun he => by
    obtain ⟨x, hx⟩ := hf
    have hm : f x ∈ f.range := ⟨x, rfl⟩
    rw [he] at hm
    exact hx hm
  intro y
  have hm : y ∈ f.range := htop ▸ Submodule.mem_top
  exact hm

theorem nonempty_equiv_of_fixed_diagonal_type
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') [ρ.IsIrreducible] [ρ'.IsIrreducible]
    (H : Subgroup G) (j : W →ₗ[ℂ] V) (j' : W →ₗ[ℂ] V')
    (hj : Function.Injective j) (hj' : Function.Injective j')
    (hj'Fix : ∀ h ∈ H, ∀ w, ρ' h (j' w) = j' w)
    (U : Subrepresentation (ρ.prod ρ'))
    (hU : ∀ w, (j w, j' w) ∈ U)
    (hdiag : ∀ x ∈ U, (∀ h ∈ H, (ρ.prod ρ') h x = x) → ∃ w, (j w, j' w) = x) :
    Nonempty (ρ.Equiv ρ') := by
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hj₀ : j w₀ ≠ 0 := fun h => hw₀ (hj (by rw [h, map_zero]))
  have hj₀' : j' w₀ ≠ 0 := fun h => hw₀ (hj' (by rw [h, map_zero]))
  let right : Subrepresentation ρ' :=
    ⟨U.toSubmodule.comap (LinearMap.inr ℂ V V'), fun g {v} hv => by
      change ((0 : V), ρ' g v) ∈ U.toSubmodule
      simpa only [prod_apply_apply, LinearMap.inr_apply, map_zero] using U.apply_mem_toSubmodule g hv⟩
  have hright : right = ⊥ := (eq_bot_or_eq_top right).resolve_right fun htop => by
    have hvU : ((0 : V), j' w₀) ∈ U := by
      have hv : j' w₀ ∈ right := htop ▸ Submodule.mem_top
      exact hv
    obtain ⟨w, hw⟩ := hdiag _ hvU
      (fun g hg => by simp only [prod_apply_apply, map_zero, hj'Fix g hg])
    have hw0 : w = 0 := hj (by rw [map_zero]; exact congrArg Prod.fst hw)
    have h' : j' w = j' w₀ := congrArg Prod.snd hw
    rw [hw0, map_zero] at h'
    exact hj₀' h'.symm
  let incl : U.toRepresentation.IntertwiningMap (ρ.prod ρ') :=
    ⟨U.toSubmodule.subtype, fun _ => rfl⟩
  let F := (IntertwiningMap.fst ℂ ρ ρ').comp incl
  let F' := (IntertwiningMap.snd ℂ ρ ρ').comp incl
  let u₀ : U.toSubmodule := ⟨(j w₀, j' w₀), hU w₀⟩
  have hFsurj := surjective_of_nonzero_to_irreducible F ⟨u₀, hj₀⟩
  have hF'surj := surjective_of_nonzero_to_irreducible F' ⟨u₀, hj₀'⟩
  have hFinj : Function.Injective F := (injective_iff_map_eq_zero F.toLinearMap).mpr fun u hu => by
    have hfst : u.val.1 = 0 := hu
    have hsnd : u.val.2 ∈ right := by
      change ((0 : V), u.val.2) ∈ U
      rw [← hfst, Prod.mk.eta]
      exact u.2
    rw [hright] at hsnd
    exact Subtype.ext (Prod.ext hfst hsnd)
  let e := F.ofBijective ⟨hFinj, hFsurj⟩
  let f := F'.comp e.symm.toIntertwiningMap
  have hf : Function.Surjective f := hF'surj.comp e.symm.surjective
  have hf0 : f ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := hf (j' w₀)
    rw [h] at hu
    exact hj₀' hu.symm
  obtain h | h := IsIrreducible.bijective_or_eq_zero f
  · exact ⟨f.ofBijective h⟩
  · exact (hf0 h).elim

end Representation

#print axioms Representation.nonempty_equiv_of_fixed_diagonal_type
