import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The degree of inseparability and the subring `ℤ̲κ/κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §1, the paragraph
preceding Proposition 1.3.

For an algebraic extension `E / F` of exponential characteristic `q`, the *degree of
inseparability* of `x ∈ E` is `d_x = q ^ n_x`, where `n_x` is the least `n` with `x ^ q ^ n`
separable over `F`.  The source needs `d_{x y} ∣ d_x d_y`, which is what makes

`ℤ̲κ/κ₀ = { ∑_r n_r (r) | d_r divides n_r }`

a subring of `ℤ̲κ`; that subring is `deningerInsepSubring`.

Existence of an admissible exponent is `separableClosure.isPurelyInseparable` together with
`IsPurelyInseparable.pow_mem`; the multiplicativity is the observation that the admissible
exponents form an upward-closed set and that `separableClosure F E` is a subfield, so the maximum
of two admissible exponents is admissible for the product.
-/

namespace RHTower

open IntermediateField

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]

/-- The set of exponents `n` for which `x ^ q ^ n` is separable over `F`. -/
def deningerInsepExpSet (x : E) : Set ℕ := {n : ℕ | IsSeparable F (x ^ q ^ n)}

/-- **Deninger, §1.**  The inseparability exponent of `x` over `F`: the least `n` with
`x ^ q ^ n` separable over `F`. -/
noncomputable def deningerInsepExp (x : E) : ℕ := sInf (deningerInsepExpSet F E q x)

/-- **Deninger, §1.**  The degree of inseparability `d_x = q ^ n_x`. -/
noncomputable def deningerInsepDegree (x : E) : ℕ := q ^ deningerInsepExp F E q x

variable {F E q}

omit [ExpChar F q] in
omit [ExpChar F q] in
theorem deningerMem_insepExpSet_iff {x : E} {n : ℕ} :
    n ∈ deningerInsepExpSet F E q x ↔ x ^ q ^ n ∈ separableClosure F E := Iff.rfl

omit [ExpChar F q] in
/-- The set of admissible exponents is upward closed. -/
theorem deningerInsepExpSet_upward {x : E} {n m : ℕ} (h : n ∈ deningerInsepExpSet F E q x)
    (hnm : n ≤ m) : m ∈ deningerInsepExpSet F E q x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [deningerMem_insepExpSet_iff] at h ⊢
  have hpow : x ^ q ^ (n + k) = (x ^ q ^ n) ^ q ^ k := by
    rw [← pow_mul, ← pow_add]
  rw [hpow]
  exact pow_mem h _

variable (F E q)

/-- For an algebraic extension the set of admissible exponents is nonempty. -/
theorem deningerInsepExpSet_nonempty [Algebra.IsAlgebraic F E] (x : E) :
    (deningerInsepExpSet F E q x).Nonempty := by
  haveI : ExpChar (separableClosure F E) q := expChar_of_injective_ringHom
    (algebraMap F (separableClosure F E)).injective q
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) q x
  refine ⟨n, ?_⟩
  rw [deningerMem_insepExpSet_iff]
  obtain ⟨y, hy⟩ := hn
  rw [← hy]
  exact y.2

variable {F E q}

theorem deningerInsepExp_mem [Algebra.IsAlgebraic F E] (x : E) :
    deningerInsepExp F E q x ∈ deningerInsepExpSet F E q x :=
  Nat.sInf_mem (deningerInsepExpSet_nonempty F E q x)

omit [ExpChar F q] in
omit [ExpChar F q] in
theorem deningerInsepExp_le {x : E} {n : ℕ} (h : n ∈ deningerInsepExpSet F E q x) :
    deningerInsepExp F E q x ≤ n :=
  Nat.sInf_le h

omit [ExpChar F q] in
@[simp] theorem deningerInsepExp_one : deningerInsepExp F E q 1 = 0 := by
  refine Nat.le_antisymm (deningerInsepExp_le ?_) (Nat.zero_le _)
  rw [deningerMem_insepExpSet_iff]
  simp

omit [ExpChar F q] in
@[simp] theorem deningerInsepDegree_one : deningerInsepDegree F E q 1 = 1 := by
  rw [deningerInsepDegree, deningerInsepExp_one, pow_zero]

/-- **Deninger, §1.**  `d_{x y}` divides `d_x d_y`; this is what makes `ℤ̲κ/κ₀` a subring. -/
theorem deningerInsepExp_mul_le [Algebra.IsAlgebraic F E] (x y : E) :
    deningerInsepExp F E q (x * y)
      ≤ max (deningerInsepExp F E q x) (deningerInsepExp F E q y) := by
  refine deningerInsepExp_le ?_
  rw [deningerMem_insepExpSet_iff, mul_pow]
  exact mul_mem
    (deningerInsepExpSet_upward (deningerInsepExp_mem x) (le_max_left _ _))
    (deningerInsepExpSet_upward (deningerInsepExp_mem y) (le_max_right _ _))

theorem deningerInsepDegree_mul_dvd [Algebra.IsAlgebraic F E] (x y : E) :
    deningerInsepDegree F E q (x * y)
      ∣ deningerInsepDegree F E q x * deningerInsepDegree F E q y := by
  rw [deningerInsepDegree, deningerInsepDegree, deningerInsepDegree, ← pow_add]
  refine pow_dvd_pow q ?_
  calc deningerInsepExp F E q (x * y)
      ≤ max (deningerInsepExp F E q x) (deningerInsepExp F E q y) :=
        deningerInsepExp_mul_le x y
    _ ≤ deningerInsepExp F E q x + deningerInsepExp F E q y := max_le_add_of_nonneg
        (Nat.zero_le _) (Nat.zero_le _)

/-! ## The subring `ℤ̲κ/κ₀` -/

variable (F E q)

/-- **Deninger, §1.**  The subring `ℤ̲κ/κ₀ ⊆ ℤ̲κ` of those integral combinations of Teichmüller
atoms `(r)` whose coefficient at `r` is divisible by the degree of inseparability `d_r`. -/
noncomputable def deningerInsepSubring [Algebra.IsAlgebraic F E] :
    Subring (MonoidAlgebra ℤ Eˣ) where
  carrier := {ξ | ∀ r : Eˣ, (deningerInsepDegree F E q (r : E) : ℤ) ∣ ξ.coeff r}
  zero_mem' := by intro r; simp
  one_mem' := by
    intro r
    classical
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single]
    by_cases hr : (1 : Eˣ) = r
    · subst hr
      simp
    · simp [hr]
  add_mem' hx hy := by
    intro r
    rw [MonoidAlgebra.coeff_add]
    exact dvd_add (hx r) (hy r)
  neg_mem' hx := by
    intro r
    rw [MonoidAlgebra.coeff_neg]
    exact (hx r).neg_right
  mul_mem' {x y} hx hy := by
    intro r
    classical
    rw [MonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Finset.dvd_sum ?_
    intro m₁ _
    rw [Finsupp.sum]
    refine Finset.dvd_sum ?_
    intro m₂ _
    by_cases hm : m₁ * m₂ = r
    · rw [if_pos hm]
      have hdvd : (deningerInsepDegree F E q (r : E) : ℤ)
          ∣ (deningerInsepDegree F E q (m₁ : E) : ℤ)
            * (deningerInsepDegree F E q (m₂ : E) : ℤ) := by
        have h := deningerInsepDegree_mul_dvd (F := F) (q := q) ((m₁ : E)) ((m₂ : E))
        rw [← hm]
        simp only [Units.val_mul]
        exact_mod_cast h
      exact hdvd.trans (mul_dvd_mul (hx m₁) (hy m₂))
    · rw [if_neg hm]
      exact dvd_zero _

end RHTower
