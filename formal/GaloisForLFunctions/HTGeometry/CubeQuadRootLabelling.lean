import GaloisForLFunctions.HTGeometry.HypercubeSingleTransverseBlocks
import GaloisForLFunctions.HTGeometry.BlockFlipRealization

/-!
# Labelling the block roots by hypercube points

The characteristic polynomial of a Hamiltonian with a single transverse coupling factors into
`2^{n-1}` quadratics, one per hypercube edge in the transverse direction.  Indexing the two roots of
each quadratic by the two endpoints of its edge turns the block transposition into the hypercube
edge swap, which is the shape the generation theorem consumes.

## Main results

* `cubePairEquiv`, `cubeQuadRoot` — the hypercube labelling of the block roots.
* `prod_cubeQuadRoot` — the characteristic polynomial splits into those linear factors.
* `map_cubeQuadRoot_of_flip` — a block flip acts as the hypercube edge swap.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {L : Type*} [Field L] {m : ℕ}

/-- Relabelling a block-root index as a hypercube point. -/
def cubePairEquiv (m : ℕ) : ((Fin m → Bool) × Bool) ≃ (Fin (m + 1) → Bool) where
  toFun p := Fin.cons p.2 p.1
  invFun x := (Fin.tail x, x 0)
  left_inv := by
    rintro ⟨z, b⟩
    simp [Fin.tail_cons]
  right_inv := by
    intro x
    simp [Fin.cons_self_tail]

@[simp] theorem cubePairEquiv_apply (z : Fin m → Bool) (b : Bool) :
    cubePairEquiv m (z, b) = Fin.cons b z := rfl

/-- The root of the single-transverse characteristic polynomial attached to a hypercube point. -/
def cubeQuadRoot (s ρ : (Fin m → Bool) → L) (x : Fin (m + 1) → Bool) : L :=
  quadRoot s ρ ((cubePairEquiv m).symm x)

theorem equiv_swap_map {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) (a b x : α) :
    e (Equiv.swap a b x) = Equiv.swap (e a) (e b) (e x) := by
  by_cases hxa : x = a
  · subst hxa
    simp
  by_cases hxb : x = b
  · subst hxb
    simp
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
    Equiv.swap_apply_of_ne_of_ne (fun h => hxa (e.injective h)) (fun h => hxb (e.injective h))]

@[simp] theorem cubeQuadRoot_cons (s ρ : (Fin m → Bool) → L) (b : Bool) (z : Fin m → Bool) :
    cubeQuadRoot s ρ (Fin.cons b z) = quadRoot s ρ (z, b) := by
  have h : (cubePairEquiv m).symm (Fin.cons b z) = (z, b) :=
    (cubePairEquiv m).symm_apply_apply (z, b)
  rw [cubeQuadRoot, h]

/-- **The block quadratics split into the hypercube-labelled linear factors.** -/
theorem prod_cubeQuadRoot (h2 : (2 : L) ≠ 0) (s q ρ : (Fin m → Bool) → L)
    (hρ : ∀ z, ρ z * ρ z = s z * s z - 4 * q z) :
    (∏ z : Fin m → Bool, (X ^ 2 - C (s z) * X + C (q z)))
      = ∏ x : Fin (m + 1) → Bool, (X - C (cubeQuadRoot s ρ x)) := by
  classical
  rw [prod_quadratic_eq_prod_quadRoot h2 s q ρ hρ]
  refine Fintype.prod_equiv (cubePairEquiv m) _ _ fun p => ?_
  obtain ⟨z, b⟩ := p
  rw [cubePairEquiv_apply, cubeQuadRoot_cons]

/-- **A block flip acts as the hypercube edge swap.** -/
theorem map_cubeQuadRoot_of_flip (s ρ : (Fin m → Bool) → L) (z₀ : Fin m → Bool) (σ : L ≃+* L)
    (hs : ∀ z, σ (s z) = s z)
    (hfix : ∀ z, z ≠ z₀ → σ (ρ z) = ρ z) (hneg : σ (ρ z₀) = -ρ z₀)
    (x : Fin (m + 1) → Bool) :
    σ (cubeQuadRoot s ρ x)
      = cubeQuadRoot s ρ
          (Equiv.swap (Fin.cons true z₀) (Fin.cons false z₀) x) := by
  classical
  rw [cubeQuadRoot, map_quadRoot_of_flip s ρ z₀ σ hs hfix hneg, cubeQuadRoot]
  congr 1
  have h := equiv_swap_map (cubePairEquiv m).symm
    (Fin.cons true z₀) (Fin.cons false z₀) x
  rw [show (cubePairEquiv m).symm (Fin.cons true z₀) = (z₀, true) from
      (cubePairEquiv m).symm_apply_apply (z₀, true),
    show (cubePairEquiv m).symm (Fin.cons false z₀) = (z₀, false) from
      (cubePairEquiv m).symm_apply_apply (z₀, false)] at h
  exact h.symm

end

end GaloisForLFunctions.HTGeometry
