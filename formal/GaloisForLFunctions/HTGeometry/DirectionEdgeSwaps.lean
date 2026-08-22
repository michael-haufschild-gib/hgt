import GaloisForLFunctions.HTGeometry.SingleDirectionTransverse
import GaloisForLFunctions.HTGeometry.SingleTransverseEdgeSwaps

/-!
# Every hypercube edge swap in one direction is realized

Transporting the direction-zero edge swaps through the coordinate relabelling gives, for a
transverse coupling in direction `i`, exactly the swaps of the hypercube edges in that direction, on
the original labelling of the cube.

## Main results

* `directionRoot` — the root family of the single-direction family, on the original cube.
* `swap_boolToggle_mem_realizedPermSubgroup` — every direction-`i` edge swap is realized.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ}

/-- The root family of a single-direction Hamiltonian, labelled by the original cube. -/
def directionRoot (s ρ : (Fin m → Bool) → L) (i : Fin (m + 1))
    (x : Fin (m + 1) → Bool) : L :=
  cubeQuadRoot s ρ (cubeRelabel (Equiv.swap 0 i) x)

theorem cubeRelabel_swap_apply (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    cubeRelabel (Equiv.swap (0 : Fin (m + 1)) i) x
      = Fin.cons (x i) (Fin.tail (x ∘ Equiv.swap (0 : Fin (m + 1)) i)) := by
  have h0 : (x ∘ Equiv.swap (0 : Fin (m + 1)) i) 0 = x i := by
    simp [Equiv.swap_apply_left]
  rw [cubeRelabel_apply, ← h0, Fin.cons_self_tail]

theorem cubeRelabel_swap_boolToggle (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    cubeRelabel (Equiv.swap (0 : Fin (m + 1)) i) (boolToggle x i)
      = Fin.cons (!x i) (Fin.tail (x ∘ Equiv.swap (0 : Fin (m + 1)) i)) := by
  classical
  rw [cubeRelabel_swap_apply]
  have hval : boolToggle x i i = !x i := by
    simp [boolToggle, Function.update_self]
  rw [hval]
  congr 1
  funext k
  show boolToggle x i (Equiv.swap (0 : Fin (m + 1)) i k.succ) = x (Equiv.swap (0 : Fin (m+1)) i k.succ)
  have hne : Equiv.swap (0 : Fin (m + 1)) i k.succ ≠ i := by
    intro h
    have : k.succ = (0 : Fin (m + 1)) := by
      have := congrArg (Equiv.swap (0 : Fin (m + 1)) i) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    exact (Fin.succ_ne_zero k) this
  simp [boolToggle, Function.update_of_ne hne]

/-- **Every hypercube edge swap in the transverse direction is realized.** -/
theorem swap_boolToggle_mem_realizedPermSubgroup
    (s ρ : (Fin m → Bool) → L) (h2 : (2 : L) ≠ 0)
    (hs : ∀ z, s z ∈ baseRange F L)
    (enum : (Fin m → Bool) ≃ Fin (Fintype.card (Fin m → Bool)))
    (hsq : ∀ z, ρ z * ρ z ∈ baseRange F L)
    (hindep : ∀ T : Finset (Fin m → Bool), T.Nonempty →
      ¬ IsSqIn (baseRange F L) (∏ z ∈ T, ρ z * ρ z))
    (htop : radicalStage (baseRange F L)
      (fun k => if h : k < Fintype.card (Fin m → Bool) then ρ (enum.symm ⟨k, h⟩) else 1)
      (Fintype.card (Fin m → Bool)) = ⊤)
    (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    Equiv.swap x (boolToggle x i)
      ∈ realizedPermSubgroup (F := F) (directionRoot s ρ i) := by
  classical
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 i with hτ
  set e : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) := cubeRelabel τ with he
  set z₀ : Fin m → Bool := Fin.tail (x ∘ τ) with hz₀
  obtain ⟨σ, hσ⟩ :=
    exists_algEquiv_swap_cubeQuadRoot (F := F) s ρ h2 hs enum hsq hindep htop z₀
  have hex : e x = Fin.cons (x i) z₀ := by
    rw [he, hz₀, hτ]
    exact cubeRelabel_swap_apply i x
  have hetog : e (boolToggle x i) = Fin.cons (!x i) z₀ := by
    rw [he, hz₀, hτ]
    exact cubeRelabel_swap_boolToggle i x
  refine ⟨σ, fun w => ?_⟩
  show σ (cubeQuadRoot s ρ (e w)) = cubeQuadRoot s ρ (e (Equiv.swap x (boolToggle x i) w))
  rw [hσ (e w)]
  congr 1
  have hkey := equiv_swap_map e.symm (Fin.cons true z₀) (Fin.cons false z₀) (e w)
  rw [Equiv.symm_apply_apply] at hkey
  have hswap : Equiv.swap (Fin.cons true z₀) (Fin.cons false z₀) (e w)
      = e (Equiv.swap (e.symm (Fin.cons true z₀)) (e.symm (Fin.cons false z₀)) w) := by
    rw [← hkey, Equiv.apply_symm_apply]
  rw [hswap]
  congr 2
  cases hxi : x i with
  | false =>
      have hetog' : e (boolToggle x i) = Fin.cons true z₀ := by
        rw [hetog, hxi]
        rfl
      have hex' : e x = Fin.cons false z₀ := by
        rw [hex, hxi]
      have h1 : e.symm (Fin.cons true z₀) = boolToggle x i := by
        rw [← hetog', Equiv.symm_apply_apply]
      have h2' : e.symm (Fin.cons false z₀) = x := by
        rw [← hex', Equiv.symm_apply_apply]
      rw [h1, h2', Equiv.swap_comm]
  | true =>
      have hetog' : e (boolToggle x i) = Fin.cons false z₀ := by
        rw [hetog, hxi]
        rfl
      have hex' : e x = Fin.cons true z₀ := by
        rw [hex, hxi]
      have h1 : e.symm (Fin.cons true z₀) = x := by
        rw [← hex', Equiv.symm_apply_apply]
      have h2' : e.symm (Fin.cons false z₀) = boolToggle x i := by
        rw [← hetog', Equiv.symm_apply_apply]
      rw [h1, h2']

end

end GaloisForLFunctions.HTGeometry
