import GaloisForLFunctions.HTGeometry.ClockCharacterSigmaMobius
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Charged clock family: the exact `ρ_λ q = λ^k q` interface

The charged phase of the clock-character classification supplies the constraint's action on the
generator through the whole cocharacter `ρ_λ q = λ^k q` (`λ ∈ C^*`, `k > 0`), not just a single
scaling.  Over an algebraically closed field the `k`-th powers avoid the exceptional values
`{0, 1, -1}` for some `λ`, so this family form collapses to the single-scaling hypothesis of
`differentialAlgEquiv_generator_multiplicative`, yielding the multiplicative rigidity `σ y = e y`.

This is exactly the `PGL₂`-cocharacter output interface (step §3) feeding the charged no-go (§4).
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- Over an algebraically closed field, for `k > 0` some nonzero element has its `k`-th power
outside `{1, -1}`: the `k`-th power map is not confined to the two exceptional roots of unity. -/
theorem exists_pow_ne_one_ne_neg_one {C : Type*} [Field C] [IsAlgClosed C]
    {k : ℕ} (hk : 0 < k) :
    ∃ lam : C, lam ≠ 0 ∧ lam ^ k ≠ 1 ∧ lam ^ k ≠ -1 := by
  have hroot : ∀ a : C, {x : C | x ^ k = a}.Finite := by
    intro a
    have h : {x : C | x ^ k = a}
        ⊆ (Polynomial.X ^ k - Polynomial.C a).rootSet C := by
      intro x hx
      rw [Polynomial.mem_rootSet]
      exact ⟨Polynomial.X_pow_sub_C_ne_zero hk a,
        by simpa [sub_eq_zero] using hx⟩
    exact ((Polynomial.X ^ k - Polynomial.C a).rootSet_finite C).subset h
  have hfin : ({x : C | x ^ k = 1} ∪ {x : C | x ^ k = -1} ∪ {0} : Set C).Finite :=
    ((hroot 1).union (hroot (-1))).union (Set.finite_singleton 0)
  obtain ⟨lam, hlam⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_singleton_iff] at hlam
  push Not at hlam
  exact ⟨lam, hlam.2, hlam.1.1, hlam.1.2⟩

/-- **Charged clock family rigidity.**  With the clock acting on the generator by the full charged
cocharacter `ρ_λ y = λ^k y` (`k > 0`) and each `ρ_λ` commuting with the constraint `σ`, the
constraint is multiplication by a single constant: `σ y = e y`. -/
theorem clock_charge_family_multiplicative
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) (ρ : C → (E →ₐ[C] E)) {y : E} {k : ℕ} (hk : 0 < k)
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    (hρ : ∀ lam : C, (ρ lam) y = algebraMap C E (lam ^ k) * y)
    (hcomm : ∀ lam : C, σ.toAlgHom ((ρ lam) y) = (ρ lam) (σ.toAlgHom y)) :
    ∃ e : C, σ y = algebraMap C E e * y := by
  obtain ⟨lam, hlam0, hlam1, hlamm1⟩ := exists_pow_ne_one_ne_neg_one (C := C) hk
  exact differentialAlgEquiv_generator_multiplicative σ (ρ lam) hy hytop hderiv
    (pow_ne_zero k hlam0) hlam1 hlamm1 (hρ lam) (hcomm lam)

end GaloisForLFunctions.HTGeometry
