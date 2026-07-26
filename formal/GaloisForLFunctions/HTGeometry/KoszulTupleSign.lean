import GaloisForLFunctions.HTGeometry.SimplicialCochainComplex
import GaloisForLFunctions.HTGeometry.GeneralKoszulComplex

/-!
# The iterated incidence sign of a tuple, and its alternation

The Hochster strand maps at Koszul degrees one, two and three are weighted by the iterated incidence
sign `faceSign σ (v 0) · faceSign (σ ∖ v 0) (v 1) · faceSign (σ ∖ {v 0, v 1}) (v 2) · ⋯`.  This file
defines that weight at **every** degree and proves the property everything else rests on: on tuples
with distinct entries in `σ` it is **alternating**.

`tupleSign` is defined by the obvious recursion (peel the head, erase it from `σ`).  The alternation
is proved in three steps, each avoiding dependent-type surgery on `Fin`:

* `tupleSign_swap_head` — swapping the first two entries flips the sign; this is exactly the incidence
  antisymmetry `faceSign_mul_faceSign_erase_antisymm` applied to the two peeled vertices, the deeper
  factors being unchanged because the two erasures commute;
* `tupleSign_swap_adjacent` — swapping the entries at positions `t` and `t+1` flips the sign, by
  induction on the degree: the case `t = 0` is the head swap, and a swap at positions `≥ 1` is a
  swap of the tail;
* `tupleSign_comp_perm` — the general transformation law `tupleSign σ (v ∘ π) = sign π • tupleSign σ v`,
  obtained from the adjacent case because adjacent transpositions generate the symmetric group
  (`Equiv.Perm.mclosure_swap_castSucc_succ`).

`tupleSign_swap` is the transposition form, which is the hypothesis shape of `IsAltTensor`.  This is
the degree-uniform replacement for the hand-made `faceSign3_antisym12/23` used at degree three, and
the reason the higher Hochster strand maps land in the alternating Koszul complex.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-- The iterated incidence sign of a tuple relative to a finite vertex set: peel the head, erase it,
and continue. -/
def tupleSign (F : Type*) [CommRing F] : {p : ℕ} → Finset α → (Fin p → α) → F
  | 0, _, _ => 1
  | (_ + 1), σ, v => faceSign F σ (v 0) * tupleSign F (σ.erase (v 0)) (Fin.tail v)

@[simp]
theorem tupleSign_zero (σ : Finset α) (v : Fin 0 → α) : tupleSign F σ v = 1 := rfl

theorem tupleSign_succ {p : ℕ} (σ : Finset α) (v : Fin (p + 1) → α) :
    tupleSign F σ v = faceSign F σ (v 0) * tupleSign F (σ.erase (v 0)) (Fin.tail v) := rfl

/-! ### Swapping the first two entries -/

/-- **Swapping the first two entries flips the iterated incidence sign.**  The two peeled factors are
exchanged, which is the incidence antisymmetry, and the remaining factors are unchanged because the
two erasures commute. -/
theorem tupleSign_swap_head {q : ℕ} (σ : Finset α) (v : Fin (q + 2) → α)
    (h0 : v 0 ∈ σ) (h1 : v 1 ∈ σ) (hne : v 0 ≠ v 1) :
    tupleSign F σ (v ∘ Equiv.swap 0 1) = - tupleSign F σ v := by
  have hsucc : (Fin.succ (0 : Fin (q + 1))) = (1 : Fin (q + 2)) := Fin.succ_zero_eq_one
  have hw0 : (v ∘ Equiv.swap (0 : Fin (q + 2)) 1) 0 = v 1 := by
    show v (Equiv.swap (0 : Fin (q + 2)) 1 0) = v 1
    rw [Equiv.swap_apply_left]
  have hw1 : Fin.tail (v ∘ Equiv.swap (0 : Fin (q + 2)) 1) 0 = v 0 := by
    show v (Equiv.swap (0 : Fin (q + 2)) 1 (Fin.succ 0)) = v 0
    rw [hsucc, Equiv.swap_apply_right]
  have hv1 : Fin.tail v 0 = v 1 := congrArg v hsucc
  have htt : Fin.tail (Fin.tail (v ∘ Equiv.swap (0 : Fin (q + 2)) 1))
      = Fin.tail (Fin.tail v) := by
    funext t
    show v (Equiv.swap (0 : Fin (q + 2)) 1 (Fin.succ (Fin.succ t))) = v (Fin.succ (Fin.succ t))
    have hfix : Equiv.swap (0 : Fin (q + 2)) 1 (Fin.succ (Fin.succ t)) = Fin.succ (Fin.succ t) := by
      refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
      intro hcon
      exact (Fin.succ_ne_zero t) (Fin.succ_inj.mp (hcon.trans hsucc.symm))
    rw [hfix]
  have hL : tupleSign F σ (v ∘ Equiv.swap 0 1)
      = faceSign F σ (v 1) * faceSign F (σ.erase (v 1)) (v 0)
        * tupleSign F ((σ.erase (v 1)).erase (v 0)) (Fin.tail (Fin.tail v)) := by
    rw [tupleSign_succ, hw0, tupleSign_succ, hw1, htt]
    ring
  have hR : tupleSign F σ v
      = faceSign F σ (v 0) * faceSign F (σ.erase (v 0)) (v 1)
        * tupleSign F ((σ.erase (v 0)).erase (v 1)) (Fin.tail (Fin.tail v)) := by
    rw [tupleSign_succ, tupleSign_succ, hv1]
    ring
  rw [hL, hR,
    show (σ.erase (v 1)).erase (v 0) = (σ.erase (v 0)).erase (v 1) from Finset.erase_right_comm]
  have hs := faceSign_mul_faceSign_erase_antisymm (F := F) h0 h1 hne
  linear_combination (tupleSign F ((σ.erase (v 0)).erase (v 1)) (Fin.tail (Fin.tail v))) * hs

/-! ### Swapping adjacent entries -/

omit [DecidableEq α] [LinearOrder α] in
/-- Swapping two entries at positions `≥ 1` is a swap of the tail. -/
theorem tail_comp_swap_succ {q : ℕ} (v : Fin (q + 2) → α) (a b : Fin (q + 1)) :
    Fin.tail (v ∘ Equiv.swap a.succ b.succ) = (Fin.tail v) ∘ Equiv.swap a b := by
  funext t
  show v (Equiv.swap a.succ b.succ (Fin.succ t)) = v (Fin.succ (Equiv.swap a b t))
  congr 1
  by_cases h1 : t = a
  · subst h1; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases h2 : t = b
    · subst h2; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.succ_inj.mp h))
        (fun h => h2 (Fin.succ_inj.mp h)), Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [DecidableEq α] [LinearOrder α] in
/-- A swap of two entries at positions `≥ 1` fixes the head. -/
theorem head_comp_swap_succ {q : ℕ} (v : Fin (q + 2) → α) (a b : Fin (q + 1)) :
    (v ∘ Equiv.swap a.succ b.succ) 0 = v 0 := by
  show v (Equiv.swap a.succ b.succ 0) = v 0
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.succ_ne_zero a)) (Ne.symm (Fin.succ_ne_zero b))]

/-- **Swapping adjacent entries flips the iterated incidence sign.** -/
theorem tupleSign_swap_adjacent : ∀ {p : ℕ} (σ : Finset α) (v : Fin (p + 1) → α),
    (∀ t, v t ∈ σ) → Function.Injective v → ∀ t : Fin p,
    tupleSign F σ (v ∘ Equiv.swap t.castSucc t.succ) = - tupleSign F σ v := by
  intro p
  induction p with
  | zero => intro _ _ _ _ t; exact t.elim0
  | succ q ih =>
    intro σ v hmem hinj t
    refine Fin.cases ?_ (fun s => ?_) t
    · rw [show (Fin.castSucc (0 : Fin (q + 1))) = (0 : Fin (q + 2)) from Fin.castSucc_zero,
        show (Fin.succ (0 : Fin (q + 1))) = (1 : Fin (q + 2)) from Fin.succ_zero_eq_one]
      exact tupleSign_swap_head σ v (hmem 0) (hmem 1) (fun h => Fin.zero_ne_one (hinj h))
    · rw [show (Fin.castSucc s.succ) = (Fin.succ s.castSucc) from (Fin.succ_castSucc s).symm]
      have hmem' : ∀ u, Fin.tail v u ∈ σ.erase (v 0) := by
        intro u
        exact Finset.mem_erase.mpr ⟨fun h => (Fin.succ_ne_zero u) (hinj h), hmem u.succ⟩
      have hinj' : Function.Injective (Fin.tail v) := fun x y h =>
        Fin.succ_inj.mp (hinj h)
      rw [tupleSign_succ, head_comp_swap_succ v s.castSucc s.succ,
        tail_comp_swap_succ v s.castSucc s.succ,
        ih (σ.erase (v 0)) (Fin.tail v) hmem' hinj' s, tupleSign_succ σ v]
      ring

/-! ### The general transformation law -/

/-- **The iterated incidence sign transforms by the sign of the permutation.**  Adjacent
transpositions generate the symmetric group, so the adjacent case propagates to every permutation. -/
theorem tupleSign_comp_perm : ∀ {p : ℕ} (σ : Finset α) (v : Fin p → α),
    (∀ t, v t ∈ σ) → Function.Injective v → ∀ π : Equiv.Perm (Fin p),
    tupleSign F σ (v ∘ π) = (Equiv.Perm.sign π : ℤ) • tupleSign F σ v := by
  intro p
  match p with
  | 0 =>
    intro σ v _ _ π
    rw [Subsingleton.elim π 1]
    simp
  | (q + 1) =>
    intro σ v hmem hinj π
    have hmain : ∀ ρ : Equiv.Perm (Fin (q + 1)),
        ρ ∈ Submonoid.closure (Set.range fun i : Fin q => Equiv.swap i.castSucc i.succ) →
        ∀ w : Fin (q + 1) → α, (∀ t, w t ∈ σ) → Function.Injective w →
        tupleSign F σ (w ∘ ρ) = (Equiv.Perm.sign ρ : ℤ) • tupleSign F σ w := by
      intro ρ hρ
      induction hρ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro w hw hwi
        rw [tupleSign_swap_adjacent σ w hw hwi i,
          Equiv.Perm.sign_swap Fin.castSucc_lt_succ.ne]
        simp
      | one => intro w _ _; simp
      | mul x y _ _ hx hy =>
        intro w hw hwi
        have hwx : ∀ t, (w ∘ x) t ∈ σ := fun t => hw (x t)
        have hwxi : Function.Injective (w ∘ x) := hwi.comp x.injective
        rw [show w ∘ ⇑(x * y) = (w ∘ ⇑x) ∘ ⇑y from by
            funext t; rfl,
          hy (w ∘ ⇑x) hwx hwxi, hx w hw hwi, map_mul, Units.val_mul, smul_smul]
        congr 1
        ring
    exact hmain π (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top π)
      v hmem hinj

/-- **The iterated incidence sign is alternating.**  Transposing any two entries of a tuple with
distinct entries in `σ` flips the sign — the hypothesis shape of `IsAltTensor`. -/
theorem tupleSign_swap {p : ℕ} (σ : Finset α) (v : Fin p → α)
    (hmem : ∀ t, v t ∈ σ) (hinj : Function.Injective v) (i j : Fin p) (hij : i ≠ j) :
    tupleSign F σ (v ∘ Equiv.swap i j) = - tupleSign F σ v := by
  rw [tupleSign_comp_perm σ v hmem hinj (Equiv.swap i j), Equiv.Perm.sign_swap hij]
  simp

end

end GaloisForLFunctions.HTGeometry
