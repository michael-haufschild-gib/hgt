import GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms

/-!
# Enlarging a packet by complement translates

The finite-vanishing form of the damping obligation asks for a lower-automorphic form with
prescribed jets at a packet `{w i}` and vanishing jets at the translated points
`{w i + comp z}` for finitely many nonzero complement indices `z`.  Those translated points have
to form a legitimate packet for the *lower* lattice `ΓH`: distinct points of `ℂ^d/ΓH`.

They do, and for a reason with no analysis in it.  Two translates of the same base point differ by
`comp` of a nonzero index, which meets `ΓH` only at `0` because `comp` embeds a complement of `ΓH`
in `Γ`.  Two translates of different base points differ by an element of `Γ` plus `w i − w j`, and
the base points are already distinct modulo the *full* lattice `Γ`.  So distinctness modulo `ΓH` of
the enlarged packet is exactly distinctness modulo `Γ` of the original one.

* `enlargedPacketPoints`;
* `pairwiseDistinctModulo_enlargedPacketPoints`;
* `PairwiseDistinctModulo.comp` — restriction along an injection.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Restricting a packet along an injection keeps its points distinct. -/
theorem PairwiseDistinctModulo.comp {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {I J : Type*} {w : I → Fin d → ℂ} (hw : PairwiseDistinctModulo Γ w)
    {e : J → I} (he : Function.Injective e) :
    PairwiseDistinctModulo Γ (w ∘ e) :=
  fun _ _ hij => hw fun h => hij (he h)

/-- The packet `{w i}` enlarged by the complement translates indexed by `t`. -/
def enlargedPacketPoints {d c : ℕ} {I T : Type*} (w : I → Fin d → ℂ)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (t : T → (Fin c → ℤ)) :
    I × T → Fin d → ℂ :=
  fun p => w p.1 + comp (t p.2)

@[simp] theorem enlargedPacketPoints_apply {d c : ℕ} {I T : Type*} (w : I → Fin d → ℂ)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (t : T → (Fin c → ℤ)) (p : I × T) :
    enlargedPacketPoints w comp t p = w p.1 + comp (t p.2) := rfl

/-- **The enlarged packet is a packet for the lower lattice.** -/
theorem pairwiseDistinctModulo_enlargedPacketPoints {d c : ℕ}
    {ΓH Γ : AddSubgroup (Fin d → ℂ)} (le : ΓH ≤ Γ)
    {I T : Type*} {w : I → Fin d → ℂ} {comp : (Fin c → ℤ) →+ (Fin d → ℂ)}
    (comp_mem : ∀ z, comp z ∈ Γ) (hcompH : ∀ z, comp z ∈ ΓH → z = 0)
    {t : T → (Fin c → ℤ)} (ht : Function.Injective t)
    (hw : PairwiseDistinctModulo Γ w) :
    PairwiseDistinctModulo ΓH (enlargedPacketPoints w comp t) := by
  rintro ⟨i, s⟩ ⟨j, s'⟩ hne hmem
  simp only [enlargedPacketPoints_apply] at hmem
  by_cases hij : i = j
  · subst hij
    have hs : s ≠ s' := by
      intro h
      exact hne (by rw [h])
    have hdiff : w i + comp (t s) - (w i + comp (t s')) = comp (t s - t s') := by
      rw [map_sub]
      abel
    rw [hdiff] at hmem
    exact hs (ht (sub_eq_zero.mp (hcompH _ hmem)))
  · refine hw hij ?_
    have hdiff : w i - w j
        = (w i + comp (t s) - (w j + comp (t s'))) - comp (t s - t s') := by
      rw [map_sub]
      abel
    rw [hdiff]
    exact Γ.sub_mem (le hmem) (comp_mem _)

end GaloisForLFunctions.HTGeometry
