import Mathlib.Order.KonigLemma

/-!
# Locally finite constitutive realization towers

Every coherent inverse tower of nonempty finite realization types has a compatible global section.
Thus a finite-local/global law gap cannot be caused by absence of a set-theoretic end in a coherent
locally finite total tower; noncoherence, nonproperness, or an extra admission doctrine is required.

No computation tactic, project postulate, or unproved premise is used.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Locally finite constitutive realization Kőnig law.** Finitely many roots and finite one-step
extension fibres force a compatible global realization. -/
theorem constitutiveLocallyFiniteRealizationTower_hasGlobalSection
    {α : ℕ → Type*} [Finite (α 0)] [∀ i, Nonempty (α i)]
    (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a,
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hfiniteFiber : ∀ i a,
      {b : α (i + 1) | π (Nat.le_add_right i 1) b = a}.Finite) :
    ∃ f : (i : ℕ) → α i, ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by
  exact exists_seq_forall_proj_of_forall_finite π π_refl π_trans
    hfiniteFiber

/-- Finite realization types automatically satisfy the local-finiteness hypothesis. -/
theorem constitutiveFiniteRealizationTower_hasGlobalSection
    {α : ℕ → Type*} [∀ i, Finite (α i)] [∀ i, Nonempty (α i)]
    (π : {i j : ℕ} → (hij : i ≤ j) → α j → α i)
    (π_refl : ∀ ⦃i⦄ (a : α i), π rfl.le a = a)
    (π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) a,
      π hij (π hjk a) = π (hij.trans hjk) a) :
    ∃ f : (i : ℕ) → α i, ∀ ⦃i j⦄ (hij : i ≤ j), π hij (f j) = f i := by
  exact constitutiveLocallyFiniteRealizationTower_hasGlobalSection π π_refl π_trans
    (fun _ _ => Set.toFinite _)

end GaloisForLFunctions.HTGeometry
