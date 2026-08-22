import GaloisForLFunctions.HTGeometry.CubeQuadRootLabelling
import GaloisForLFunctions.HTGeometry.RootFamilyGalois

/-!
# The single-transverse family realizes every edge swap in its own direction

Turning on one transverse coupling makes the Hamiltonian block-diagonal in the hypercube edges of
that direction.  With the block discriminants independent in the square-class group of the base,
each edge swap is realized by a base automorphism of the splitting field, in the labelling of the
roots by hypercube points.

## Main results

* `exists_algEquiv_swap_cubeQuadRoot` — the edge swap as a base automorphism.
* `swap_mem_realizedPermSubgroup` — the same, as membership in the realized-permutation subgroup.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ}

/-- **Every edge swap in the transverse direction is realized.** -/
theorem exists_algEquiv_swap_cubeQuadRoot
    (s ρ : (Fin m → Bool) → L) (h2 : (2 : L) ≠ 0)
    (hs : ∀ z, s z ∈ baseRange F L)
    (enum : (Fin m → Bool) ≃ Fin (Fintype.card (Fin m → Bool)))
    (hsq : ∀ z, ρ z * ρ z ∈ baseRange F L)
    (hindep : ∀ T : Finset (Fin m → Bool), T.Nonempty →
      ¬ IsSqIn (baseRange F L) (∏ z ∈ T, ρ z * ρ z))
    (htop : radicalStage (baseRange F L)
      (fun n => if h : n < Fintype.card (Fin m → Bool) then ρ (enum.symm ⟨n, h⟩) else 1)
      (Fintype.card (Fin m → Bool)) = ⊤)
    (z₀ : Fin m → Bool) :
    ∃ σ : L ≃ₐ[F] L, ∀ x : Fin (m + 1) → Bool,
      σ (cubeQuadRoot s ρ x)
        = cubeQuadRoot s ρ (Equiv.swap (Fin.cons true z₀) (Fin.cons false z₀) x) := by
  classical
  have hcard : 0 < Fintype.card (Fin m → Bool) := Fintype.card_pos
  obtain ⟨σ, hσ⟩ :=
    exists_algEquiv_swap_quadRoot (F := F) s ρ h2 hs enum hsq hindep htop hcard z₀
  refine ⟨σ, fun x => ?_⟩
  rw [cubeQuadRoot, hσ, cubeQuadRoot]
  congr 1
  have h := equiv_swap_map (cubePairEquiv m).symm
    (Fin.cons true z₀) (Fin.cons false z₀) x
  rw [show (cubePairEquiv m).symm (Fin.cons true z₀) = (z₀, true) from
      (cubePairEquiv m).symm_apply_apply (z₀, true),
    show (cubePairEquiv m).symm (Fin.cons false z₀) = (z₀, false) from
      (cubePairEquiv m).symm_apply_apply (z₀, false)] at h
  exact h.symm

/-- The edge swap, as membership in the realized-permutation subgroup of the labelled roots. -/
theorem swap_mem_realizedPermSubgroup
    (s ρ : (Fin m → Bool) → L) (h2 : (2 : L) ≠ 0)
    (hs : ∀ z, s z ∈ baseRange F L)
    (enum : (Fin m → Bool) ≃ Fin (Fintype.card (Fin m → Bool)))
    (hsq : ∀ z, ρ z * ρ z ∈ baseRange F L)
    (hindep : ∀ T : Finset (Fin m → Bool), T.Nonempty →
      ¬ IsSqIn (baseRange F L) (∏ z ∈ T, ρ z * ρ z))
    (htop : radicalStage (baseRange F L)
      (fun n => if h : n < Fintype.card (Fin m → Bool) then ρ (enum.symm ⟨n, h⟩) else 1)
      (Fintype.card (Fin m → Bool)) = ⊤)
    (z₀ : Fin m → Bool) :
    Equiv.swap (Fin.cons true z₀) (Fin.cons false z₀)
      ∈ realizedPermSubgroup (F := F) (cubeQuadRoot s ρ) :=
  exists_algEquiv_swap_cubeQuadRoot s ρ h2 hs enum hsq hindep htop z₀

end

end GaloisForLFunctions.HTGeometry
