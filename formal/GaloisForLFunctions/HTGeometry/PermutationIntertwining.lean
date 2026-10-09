import Mathlib.GroupTheory.Perm.Cycle.Basic

open Set
namespace GaloisForLFunctions.HTGeometry

/-- An explicit fiber intertwining is exactly the canonical permutation-group equivalence. -/
theorem permCongr_eq_of_intertwining {A B : Type*} (e : A ≃ B)
    (T : Equiv.Perm A) (S : Equiv.Perm B) (h : ∀ a, e (T a) = S (e a)) :
    e.permCongrHom T = S := by
  apply Equiv.ext
  intro b
  change e (T (e.symm b)) = S b
  rw [h, e.apply_symm_apply]

/-- Transport through any fiber equivalence preserves a transposition, without finiteness input. -/
theorem isSwap_of_intertwining {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A ≃ B)
    (T : Equiv.Perm A) (S : Equiv.Perm B) (h : ∀ a, e (T a) = S (e a))
    (hT : T.IsSwap) : S.IsSwap := by
  classical
  obtain ⟨x, y, hxy, hswap⟩ := hT
  refine ⟨e x, e y, fun h => hxy (e.injective h), ?_⟩
  apply Equiv.ext
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [← h a, hswap]
  by_cases hax : a = x
  · subst a
    simp
  by_cases hay : a = y
  · subst a
    simp
  have hex : e a ≠ e x := fun h => hax (e.injective h)
  have hey : e a ≠ e y := fun h => hay (e.injective h)
  simp [Equiv.swap_apply_def, hax, hay, hex, hey]

/-- Transport through any fiber equivalence preserves a full cycle, without finiteness input. -/
theorem isCycleOn_univ_of_intertwining {A B : Type*} (e : A ≃ B)
    (T : Equiv.Perm A) (S : Equiv.Perm B) (h : ∀ a, e (T a) = S (e a))
    (hT : T.IsCycleOn univ) : S.IsCycleOn univ := by
  have heq := permCongr_eq_of_intertwining e T S h
  refine ⟨⟨fun _ _ => mem_univ _, S.injective.injOn, ?_⟩, ?_⟩
  · intro b _
    exact ⟨S.symm b, mem_univ _, S.apply_symm_apply b⟩
  · intro b _ c _
    obtain ⟨k, hk⟩ := hT.2 (mem_univ (e.symm b)) (mem_univ (e.symm c))
    refine ⟨k, ?_⟩
    have hz : e.permCongrHom (T ^ k) = S ^ k := by rw [map_zpow, heq]
    have hp := congrArg (fun p : Equiv.Perm B => p b) hz
    change e ((T ^ k) (e.symm b)) = (S ^ k) b at hp
    rw [hk, e.apply_symm_apply] at hp
    exact hp.symm

end GaloisForLFunctions.HTGeometry
