import GaloisForLFunctions.RHTower.Artin.ArtinNilpotentGroupsAreMonomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RepresentationTheory.Irreducible

/-! Common eigenspaces and imprimitivity for nilpotent-group representations. -/

open GaloisForLFunctions Module

namespace GlobalTheory.CuspGL

private theorem exists_common_eigenvector_of_commute
    {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (f : ι → Module.End k V) (hf : ∀ i j, f i * f j = f j * f i) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : k, f i v = c • v := by
  suffices h : ∃ (v : V) (c : ι → k), v ≠ 0 ∧ ∀ i, f i v = c i • v by
    obtain ⟨v, c, hv, hc⟩ := h
    exact ⟨v, hv, fun i => ⟨c i, hc i⟩⟩
  have hcomm (i j : ι) : Commute (f i) (f j) := hf i j
  clear hf
  classical
  generalize hdim : Module.finrank k V = n
  induction n using Nat.strongRecOn generalizing V with
  | ind n ih =>
      by_cases hall : ∀ i, ∃ z : k, f i = z • (1 : Module.End k V)
      · choose χ hχ using hall
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        refine ⟨x, χ, hx, fun i => ?_⟩
        rw [hχ i]
        rfl
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨z, hz⟩ := (f i).exists_eigenvalue
        let E := (f i).eigenspace z
        have hEbot : E ≠ ⊥ := hz
        have hEtop : E ≠ ⊤ := by
          intro h
          apply hi z
          ext x
          change f i x = z • x
          apply Module.End.mem_eigenspace_iff.mp
          change x ∈ E
          rw [h]
          trivial
        have hmaps (j : ι) : Set.MapsTo (f j) E E := by
          intro x hx
          have hix := Module.End.mem_eigenspace_iff.mp hx
          apply Module.End.mem_eigenspace_iff.mpr
          calc
            f i (f j x) = f j (f i x) := LinearMap.congr_fun (hcomm i j).eq x
            _ = z • f j x := by rw [hix, map_smul]
        let g (j : ι) : Module.End k E := (f j).restrict (hmaps j)
        have hg (j k : ι) : Commute (g j) (g k) := by
          ext x
          exact LinearMap.congr_fun (hcomm j k).eq x
        letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEbot
        have hlt : Module.finrank k E < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hEtop
        obtain ⟨x, χ, hx, hχ⟩ := ih (Module.finrank k E) hlt g hg rfl
        refine ⟨(x : V), χ, fun h => hx (Subtype.ext h), fun j => ?_⟩
        exact congrArg Subtype.val (hχ j)

private theorem exists_normal_commuting_image
    {k G V : Type} [Field k] [Group G] [Group.IsNilpotent G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (hρ : ¬ ∀ a b, ρ a * ρ b = ρ b * ρ a) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, ρ a * ρ b = ρ b * ρ a) ∧
      ∃ a ∈ A, ∃ b, ρ a * ρ b ≠ ρ b * ρ a := by
  let u : G →* (Module.End k V)ˣ := ρ.toHomUnits
  let π := u.rangeRestrict
  haveI : Group.IsNilpotent u.range := Group.nilpotent_of_surjective π u.rangeRestrict_surjective
  have hnc : ¬ ∀ a b : u.range, a * b = b * a := by
    intro h
    exact hρ fun a b => congrArg (fun x : u.range => (x.1 : Module.End k V)) (h (π a) (π b))
  obtain ⟨B, hBn, hBc, hBz⟩ := exists_normal_comm_not_le_center hnc
  letI : B.Normal := hBn
  have hex : ∃ a ∈ B, a ∉ Subgroup.center u.range := by
    by_contra! h
    exact hBz h
  obtain ⟨a, ha, haz⟩ := hex
  have hex' : ∃ b : u.range, b * a ≠ a * b := by
    by_contra! h
    exact haz (Subgroup.mem_center_iff.mpr h)
  obtain ⟨b, hb⟩ := hex'
  obtain ⟨a', rfl⟩ := u.rangeRestrict_surjective a
  obtain ⟨b', rfl⟩ := u.rangeRestrict_surjective b
  refine ⟨B.comap π, inferInstance, ?_, a', ha, b', ?_⟩
  · intro x hx y hy
    exact congrArg (fun z : B => (z.1.1 : Module.End k V))
      ((isMulCommutative_iff.mp hBc) ⟨π x, hx⟩ ⟨π y, hy⟩)
  · intro h
    exact hb (Subtype.ext (Units.ext h.symm))


private theorem invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H

/-- An irreducible representation of a nilpotent group is one-dimensional or induced by
the stabilizer of a common eigenspace whose translates form a direct sum. -/
theorem finrank_eq_one_or_imprimitive (k : Type) [Field k] [IsAlgClosed k]
    (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (hirr : ρ.IsIrreducible) :
    Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧
      (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧
      ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by
  haveI : Nontrivial V := by
    have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun H => h1 (Subrepresentation.ext H)
    exact (Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩
  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · left
    obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun g : G => ρ g) hc
    have htop := invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨m, hm⟩ := hv g
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hm' : ρ g v = m • v := hm
      rw [hm']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      v (Submodule.mem_span_singleton_self v) hv0
    rw [← finrank_top, ← htop, finrank_span_singleton hv0]
  right
  obtain ⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩ := exists_normal_commuting_image ρ hc
  letI : B.Normal := hBn
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun b : B => ρ b)
    (fun a b => hBc a a.2 b b.2)
  choose μ hμ using hv
  let c : G →* MulAut B := MulAut.conjNormal
  have hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹ := fun g b => rfl
  let E : (B → k) → Submodule k V := fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)
  have hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w := by
    intro χ w
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hind : iSupIndep E :=
    (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ =>
        iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top
  have hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b)) := by
    intro g w hw
    rw [hE] at hw ⊢
    intro b
    rw [← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    congr 2
    group
  let T : Subgroup G :=
    { carrier := {g | ∀ b, μ (c g b) = μ b}
      one_mem' := fun b => by simp
      mul_mem' := fun {x y} hx hy b => by
        rw [map_mul, MulAut.mul_apply, hx, hy]
      inv_mem' := fun {x} hx b => by
        rw [← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
  have hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b := fun g => Iff.rfl
  have hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ := by
    intro t ht w hw
    have h1 := hmap t w hw
    have h2 : (fun b => μ (c t⁻¹ b)) = μ := funext ((hT _).1 (T.inv_mem ht))
    rwa [h2] at h1
  have hvE : v ∈ E μ := (hE _ _).2 hμ
  refine ⟨T, E μ, ?_, hstab, ?_, ?_⟩
  · intro hTop
    have htop := invariant_eq_top_of_irreducible ρ hirr (E μ)
      (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0
    have hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w := fun w =>
      (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
    apply hne
    ext w
    simp only [Module.End.mul_apply, hs, map_smul]
  · have hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b) := by
      intro q q' hq
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 ((hT _).2 fun b => ?_)
      have h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b)) := congrFun hq _
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    refine (hind.comp hinj).mono fun q => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmap _ w hw
  · have hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out) := by
      intro g w hw
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T g
      refine Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩
      rw [ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0
    intro g w hw
    have hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤
        (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g) := by
      refine iSup_le fun q => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact hmem _ u hu
    exact hle hw

end GlobalTheory.CuspGL
