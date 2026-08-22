import GaloisForLFunctions.HTGeometry.DirectionEdgeSwaps

/-!
# From block flips to hypercube edge swaps in one direction

A base automorphism negating one block radical and fixing the others acts on the labelled roots as
the transposition of that block's two endpoints.  Transporting through the coordinate relabelling
that moves the transverse direction turns those transpositions into the hypercube edge swaps of the
chosen direction, on the original labelling of the cube.

## Main results

* `exists_algEquiv_swap_directionRoot` — every edge swap in the chosen direction is realized.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ}

/-- **Every hypercube edge swap in the transverse direction is realized**, given the block flips. -/
theorem exists_algEquiv_swap_directionRoot
    (s ρ : (Fin m → Bool) → L) (hs : ∀ z, s z ∈ baseRange F L)
    (hflip : ∀ z₀ : Fin m → Bool, ∃ σ : L ≃ₐ[F] L,
      (∀ z, z ≠ z₀ → σ (ρ z) = ρ z) ∧ σ (ρ z₀) = -ρ z₀)
    (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    ∃ σ : L ≃ₐ[F] L, ∀ y : Fin (m + 1) → Bool,
      σ (directionRoot s ρ i y)
        = directionRoot s ρ i (Equiv.swap x (boolToggle x i) y) := by
  classical
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 i with hτ
  set e : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) := cubeRelabel τ with he
  set z₀ : Fin m → Bool := Fin.tail (x ∘ τ) with hz₀
  obtain ⟨σ, hfix, hneg⟩ := hflip z₀
  have hsfix : ∀ z, σ (s z) = s z := by
    intro z
    obtain ⟨y, hy⟩ := (RingHom.mem_fieldRange).mp (hs z)
    rw [← hy]
    exact σ.commutes y
  have hσ : ∀ w : Fin (m + 1) → Bool, σ (cubeQuadRoot s ρ w)
      = cubeQuadRoot s ρ (Equiv.swap (Fin.cons true z₀) (Fin.cons false z₀) w) := by
    intro w
    exact map_cubeQuadRoot_of_flip s ρ z₀ (σ : L ≃+* L) hsfix hfix hneg w
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
