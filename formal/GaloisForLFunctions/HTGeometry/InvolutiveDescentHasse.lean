import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.InvolutiveDescentExactSequenceLaw

/-!
# Hasse quotient for involutive descent

For any involution, invariant complex observables embed in all observables and the universal descent
defect maps onto the odd sector.  The resulting sequence is exact, so observables modulo invariant
ones are precisely odd descent obstructions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex observables invariant under a given self-map. -/
def involutiveInvariantSubmodule {Q : Type*} (tau : Q → Q) :
    Submodule ℂ (Q → ℂ) where
  carrier := {f | ∀ q, f (tau q) = f q}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg q
    change f (tau q) + g (tau q) = f q + g q
    rw [hf q, hg q]
  smul_mem' := by
    intro c f hf q
    change c * f (tau q) = c * f q
    rw [hf q]

/-- Complex observables anti-invariant under a given self-map. -/
def involutiveOddSubmodule {Q : Type*} (tau : Q → Q) :
    Submodule ℂ (Q → ℂ) where
  carrier := {f | ∀ q, f (tau q) = -f q}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg q
    change f (tau q) + g (tau q) = -(f q + g q)
    rw [hf q, hg q]
    ring
  smul_mem' := by
    intro c f hf q
    change c * f (tau q) = -(c * f q)
    rw [hf q]
    ring

/-- The universal involutive descent defect as a complex-linear map. -/
def involutiveDescentDefectLinearMap {Q : Type*} (tau : Q → Q) :
    (Q → ℂ) →ₗ[ℂ] (Q → ℂ) where
  toFun f := involutiveDescentDefect tau f
  map_add' f g := by
    funext q
    simp only [involutiveDescentDefect, Pi.add_apply]
    ring
  map_smul' c f := by
    funext q
    change c * f q - c * f (tau q) = c * (f q - f (tau q))
    ring

/-- The descent defect with codomain restricted to the odd sector. -/
def involutiveOddDescentMap {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) :
    (Q → ℂ) →ₗ[ℂ] involutiveOddSubmodule tau :=
  (involutiveDescentDefectLinearMap tau).codRestrict
    (involutiveOddSubmodule tau) (fun f q =>
      involutiveDescentDefect_apply_involution htau f q)

/-- Invariant observables are exactly the kernel of the odd descent map. -/
theorem involutiveInvariant_oddDescent_exact
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) :
    Function.Exact (involutiveInvariantSubmodule tau).subtype
      (involutiveOddDescentMap tau htau) := by
  intro f
  constructor
  · intro hf
    have hzero : ∀ q, involutiveDescentDefect tau f q = 0 := by
      intro q
      have hval := congrArg Subtype.val hf
      exact congrFun hval q
    have hinv := (invariantUnder_iff_involutiveDescentDefect_eq_zero tau f).2 hzero
    exact ⟨⟨f, hinv⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    apply Subtype.ext
    funext q
    change involutiveDescentDefect tau f.1 q = 0
    rw [involutiveDescentDefect, f.2 q, sub_self]

/-- Every odd observable is an involutive descent defect. -/
theorem involutiveOddDescentMap_surjective
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) :
    Function.Surjective (involutiveOddDescentMap tau htau) := by
  intro h
  refine ⟨fun q => h.1 q / 2, ?_⟩
  apply Subtype.ext
  funext q
  change h.1 q / 2 - h.1 (tau q) / 2 = h.1 q
  rw [h.2 q]
  ring

/-- Observables modulo invariant ones are exactly odd descent obstructions. -/
noncomputable def involutiveDescentHasseQuotientEquiv
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) :
    ((Q → ℂ) ⧸ LinearMap.range (involutiveInvariantSubmodule tau).subtype) ≃ₗ[ℂ]
      involutiveOddSubmodule tau :=
  linearHasseQuotientEquiv
    (involutiveInvariantSubmodule tau).subtype
    (involutiveOddDescentMap tau htau)
    (involutiveInvariant_oddDescent_exact tau htau)
    (involutiveOddDescentMap_surjective tau htau)

/-- The involutive Hasse quotient is induced by the descent defect. -/
@[simp] theorem involutiveDescentHasseQuotientEquiv_mk
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) (f : Q → ℂ) :
    involutiveDescentHasseQuotientEquiv tau htau (Submodule.Quotient.mk f) =
      involutiveOddDescentMap tau htau f := by
  simp [involutiveDescentHasseQuotientEquiv]

/-- Two observables have the same descent defect exactly when they differ by an invariant
observable. -/
theorem involutiveDescent_congr_hasse_iff
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau) (f g : Q → ℂ) :
    f - g ∈ LinearMap.range (involutiveInvariantSubmodule tau).subtype ↔
      involutiveOddDescentMap tau htau f = involutiveOddDescentMap tau htau g :=
  linearHasse_congr_iff
    (involutiveInvariantSubmodule tau).subtype
    (involutiveOddDescentMap tau htau)
    (involutiveInvariant_oddDescent_exact tau htau) f g

/-- Every odd obstruction has a representative, unique modulo invariant observables. -/
theorem involutiveOdd_exists_unique_mod_invariant
    {Q : Type*} (tau : Q → Q) (htau : Function.Involutive tau)
    (h : involutiveOddSubmodule tau) :
    ∃ f : Q → ℂ, involutiveOddDescentMap tau htau f = h ∧
      ∀ g : Q → ℂ, involutiveOddDescentMap tau htau g = h ↔
        g - f ∈ LinearMap.range (involutiveInvariantSubmodule tau).subtype :=
  linearHasse_exists_unique_mod_global
    (involutiveInvariantSubmodule tau).subtype
    (involutiveOddDescentMap tau htau)
    (involutiveInvariant_oddDescent_exact tau htau)
    (involutiveOddDescentMap_surjective tau htau) h

end
end GaloisForLFunctions.HTGeometry
