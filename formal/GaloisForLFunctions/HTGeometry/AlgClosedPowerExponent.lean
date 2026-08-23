import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Exponents are determined on the units of an algebraically closed field

The unit group of an algebraically closed field is infinite, while the `d`-th roots of unity form
a finite group for `d ≥ 1`.  Hence two exponents that agree as maps on the units are equal.
-/

namespace HTGeometry

variable {κ : Type*} [Field κ]

/-- The unit group of an infinite field is infinite. -/
theorem infinite_units_of_infinite [Infinite κ] : Infinite κˣ := by
  have hset : ({0} : Set κ)ᶜ.Infinite := (Set.finite_singleton (0 : κ)).infinite_compl
  haveI : Infinite ↥(({0} : Set κ)ᶜ) := hset.to_subtype
  refine Infinite.of_injective (fun a : ↥(({0} : Set κ)ᶜ) => Units.mk0 (a : κ) ?_) ?_
  · exact a.2
  · intro a b hab
    refine Subtype.ext ?_
    have := congrArg (fun u : κˣ => (u : κ)) hab
    simpa using this

/-- **Two exponents that agree on the units of an algebraically closed field are equal.** -/
theorem pow_eq_pow_exponent_eq [IsAlgClosed κ] {m k : ℕ} (h : ∀ y : κˣ, y ^ m = y ^ k) :
    m = k := by
  haveI : Infinite κˣ := infinite_units_of_infinite
  by_contra hne
  rcases Nat.lt_or_ge m k with hlt | hge
  · have hd : 0 < k - m := by omega
    haveI : NeZero (k - m) := ⟨by omega⟩
    have hall : ∀ y : κˣ, y ∈ rootsOfUnity (k - m) κ := by
      intro y
      rw [mem_rootsOfUnity]
      have hy := (h y).symm
      have : y ^ (m + (k - m)) = y ^ m := by
        rw [show m + (k - m) = k from by omega]
        exact hy
      rw [pow_add] at this
      exact mul_left_cancel (a := y ^ m) (by rw [mul_one]; exact this)
    haveI : Finite ↥(rootsOfUnity (k - m) κ) := inferInstance
    haveI : Finite κˣ := Finite.of_injective
      (fun y : κˣ => (⟨y, hall y⟩ : ↥(rootsOfUnity (k - m) κ)))
      (fun a b hab => congrArg Subtype.val hab)
    exact not_finite κˣ
  · have hlt' : k < m := by omega
    have hd : 0 < m - k := by omega
    haveI : NeZero (m - k) := ⟨by omega⟩
    have hall : ∀ y : κˣ, y ∈ rootsOfUnity (m - k) κ := by
      intro y
      rw [mem_rootsOfUnity]
      have hy := h y
      have : y ^ (k + (m - k)) = y ^ k := by
        rw [show k + (m - k) = m from by omega]
        exact hy
      rw [pow_add] at this
      exact mul_left_cancel (a := y ^ k) (by rw [mul_one]; exact this)
    haveI : Finite κˣ := Finite.of_injective
      (fun y : κˣ => (⟨y, hall y⟩ : ↥(rootsOfUnity (m - k) κ)))
      (fun a b hab => congrArg Subtype.val hab)
    exact not_finite κˣ

end HTGeometry
