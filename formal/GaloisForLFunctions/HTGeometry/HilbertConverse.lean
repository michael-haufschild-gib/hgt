import GaloisForLFunctions.HTGeometry.HilbertRegularityCriterion

/-!
# Rank-nullity in Hilbert-function form, and the converse criterion

```text
finrank_quotient_range_add_of_injective  an injective map has the predicted cokernel dimension
le_finrank_quotient_range_add            and any map has at least that much
hilbert_of_forall_mem                    ** a nonzerodivisor makes the dimensions add up in every
                                            degree **
```

The last is the converse of `forall_mem_of_hilbert`, and it is what a degeneration argument reads
off the special fibre: there the linear forms *are* a regular sequence, so the Hilbert-function
equation holds there, and the degeneration transports it.

Together with the inequality `le_finrank_quotient_range_add`, which holds for any map at all, the
two directions close the loop: an inequality in one direction from semicontinuity plus the
always-true inequality in the other forces the equation, hence regularity.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **Rank-nullity in the form the Hilbert-function criterion uses.**  For an injective map the
quotient by the image has exactly the predicted dimension. -/
theorem finrank_quotient_range_add_of_injective [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f) :
    finrank K (W ⧸ LinearMap.range f) + finrank K V = finrank K W := by
  have h1 : finrank K (W ⧸ LinearMap.range f) + finrank K (LinearMap.range f) = finrank K W :=
    Submodule.finrank_quotient_add_finrank _
  have h2 : finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank K (LinearMap.ker f) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hf]
    simp
  omega

/-- And for any map the quotient is at least that big. -/
theorem le_finrank_quotient_range_add [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) :
    finrank K W ≤ finrank K (W ⧸ LinearMap.range f) + finrank K V := by
  have h1 : finrank K (W ⧸ LinearMap.range f) + finrank K (LinearMap.range f) = finrank K W :=
    Submodule.finrank_quotient_add_finrank _
  have h2 : finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker f
  omega

section Graded

open MvPolynomial

universe u
variable {σ : Type*} {K' : Type u} [Field K']

/-- **The converse of the Hilbert criterion.**  A nonzerodivisor makes the dimensions add up in
every degree. -/
theorem hilbert_of_forall_mem {a : Ideal (MvPolynomial σ K')} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K'} {d : ℕ} (hl : l.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K' (homogeneousSubmodule σ K' e)]
    (hreg : ∀ f : MvPolynomial σ K', l * f ∈ a → f ∈ a) (e : ℕ) :
    finrank K' (quotDegreePart ((a ⊔ Ideal.span {l}).restrictScalars K') (d + e))
      + finrank K' (quotDegreePart (a.restrictScalars K') e)
    = finrank K' (quotDegreePart (a.restrictScalars K') (d + e)) := by
  have hinj : Function.Injective (mulQuotHom (a := a) hl e) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have hy : Submodule.Quotient.mk (mulDegreeHom hl e y) = 0 := hx
      rw [Submodule.Quotient.mk_eq_zero] at hy
      have hmem : l * (y : MvPolynomial σ K') ∈ a := hy
      rw [Submodule.Quotient.mk_eq_zero]
      exact hreg _ hmem
  rw [← (cokerMulQuotEquiv ha hl e).finrank_eq]
  exact finrank_quotient_range_add_of_injective _ hinj

end Graded

end GaloisForLFunctions.HTGeometry
