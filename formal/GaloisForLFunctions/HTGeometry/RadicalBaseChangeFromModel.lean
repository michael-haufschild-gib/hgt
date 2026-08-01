import GaloisForLFunctions.HTGeometry.RadicalBaseChangeFromRoots
import GaloisForLFunctions.HTGeometry.RootEnumerationTransport

/-!
# Base change with all root data taken from a model

The roots of the first factor may be enumerated in any splitting field of it; the isomorphism with
the root field inside the ambient carries the enumeration, the surjectivity of the action, and the
Vandermonde product across.

So the statement is proved entirely from data computed in whatever model is convenient, which is
where the Galois group of the first factor is known.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **Base change along an even radical extension, from a model of the first factor.** -/
noncomputable def radicalBaseChangeEvenFromModel {p : Polynomial F} {c : F} {m : ℕ}
    (hp : p ≠ 0) (hm : 0 < m)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ (2 * m) - Polynomial.C c))]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    {L₀ : Type*} [Field L₀] [Algebra F L₀] [Polynomial.IsSplittingField F L₀ p]
    (ψ : (L₀ ≃ₐ[F] L₀) ≃* Equiv.Perm γ)
    (hζ : (primitiveRoots (2 * m) F).Nonempty)
    {dd : ℕ} (hdd : 2 ≤ dd) (w : Fin dd → L₀)
    (hwinj : Function.Injective w)
    (hwrange : ∀ x : L₀, x ∈ p.rootSet L₀ ↔ ∃ i, w i = x)
    (hwsurj : ∀ e : Equiv.Perm (Fin dd), ∃ σ : L₀ ≃ₐ[F] L₀, ∀ i, σ (w i) = w (e i))
    (hdeg : ∀ α : L, α ^ (2 * m) = algebraMap F L c → 2 * m ≤ Module.finrank F F⟮α⟯)
    (hclass : ∀ e : F, algebraMap F L₀ e = vandermondeProd w * vandermondeProd w →
      ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[rootField F (L := L) (Polynomial.X ^ (2 * m) - Polynomial.C c)] L) ≃* Equiv.Perm γ := by
  have hq : (Polynomial.X ^ (2 * m) - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  have hsplitAll := Polynomial.IsSplittingField.splits' (K := F) (L := L)
    (f := p * (Polynomial.X ^ (2 * m) - Polynomial.C c))
  have hsplitp := splits_of_splits_mul_left (L := L) hp hq hsplitAll
  haveI := isSplittingField_rootField (F := F) (p := p) (L := L) hsplitp
  let φ : rootField F (L := L) p ≃ₐ[F] L₀ :=
    (Polynomial.IsSplittingField.algEquiv (rootField F (L := L) p) p).trans
      (Polynomial.IsSplittingField.algEquiv L₀ p).symm
  have htrans := rootEnumeration_algEquiv φ hp w hwinj hwrange
  refine radicalBaseChangeEvenFromEnumeration hp hm ψ hζ hdd (fun i => φ.symm (w i))
    htrans.1 htrans.2 (rootAction_surjective_algEquiv φ w hwsurj) hdeg ?_
  intro e he
  refine hclass e ?_
  have hV : vandermondeProd (fun i => φ.symm (w i)) = φ.symm (vandermondeProd w) :=
    (map_vandermondeProd_ringHom (φ.symm : rootField F (L := L) p ≃ₐ[F] L₀ → _ |>.toRingHom) w).symm
  rw [hV, ← map_mul] at he
  have h := congrArg φ he
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.commutes φ e] at h
  exact h.symm ▸ rfl

end GaloisForLFunctions.HTGeometry
