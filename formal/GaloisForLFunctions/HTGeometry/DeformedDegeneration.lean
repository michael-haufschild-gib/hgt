import GaloisForLFunctions.HTGeometry.DegenerationTransport

/-!
# The degeneration transports regularity to a deformed form

```text
forall_mem_of_degeneration'   ** the element regular on the initial ideal and the element proved
                                 regular on the original one need only share a degree **
```

This is the form the flat family actually delivers.  Rescaling the variables carries the fibre of the
family over a nonzero point back to the original ideal but *moves the form*: the fibre at `lam` is
`R/(I + φ_lam⁻¹(l))`, not `R/(I + l)`.  Since a degeneration argument is free to choose which form it
proves regular — any linear form will do for building a regular sequence — the useful statement
compares `R/(I + l')` with `R/(J + l)` for two forms of the same degree.

The proof is unchanged: equal Hilbert functions, the equation for `J` from `l` being regular there,
the fibre bound in one direction, and the free inequality in the other.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **The degeneration transports regularity even when the form is deformed.**  The element regular
on the initial ideal and the element proved regular on the original ideal need only have the same
degree; the fibre hypothesis compares the two quotients actually formed. -/
theorem forall_mem_of_degeneration' {I J : Ideal (MvPolynomial σ K)}
    {S : Submodule K (MvPolynomial σ K)}
    (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J) (hS : IsGradedSubmodule S)
    (hIS : IsCompl (I.restrictScalars K) S) (hJS : IsCompl (J.restrictScalars K) S)
    {l l' : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (hl' : l'.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K (homogeneousSubmodule σ K e)]
    (hreg : ∀ f : MvPolynomial σ K, l * f ∈ J → f ∈ J)
    (hsemi : ∀ e : ℕ,
      finrank K (quotDegreePart ((I ⊔ Ideal.span {l'}).restrictScalars K) (d + e))
        ≤ finrank K (quotDegreePart ((J ⊔ Ideal.span {l}).restrictScalars K) (d + e))) :
    ∀ f : MvPolynomial σ K, l' * f ∈ I → f ∈ I := by
  have hIJ : ∀ e : ℕ, finrank K (quotDegreePart (I.restrictScalars K) e)
      = finrank K (quotDegreePart (J.restrictScalars K) e) := fun e =>
    finrank_quotDegreePart_eq_of_finrank_degreePart_eq e
      (finrank_degreePart_eq (isGradedSubmodule_of_isHomogIdeal hI)
        (isGradedSubmodule_of_isHomogIdeal hJ) hS hIS hJS e)
  refine forall_mem_of_hilbert hI hl' fun e => ?_
  have hJeq := hilbert_of_forall_mem hJ hl hreg e
  have hge : finrank K (quotDegreePart (I.restrictScalars K) (d + e))
      ≤ finrank K (quotDegreePart ((I ⊔ Ideal.span {l'}).restrictScalars K) (d + e))
        + finrank K (quotDegreePart (I.restrictScalars K) e) := by
    have hle := le_finrank_quotient_range_add (mulQuotHom (a := I) hl' e)
    rwa [(cokerMulQuotEquiv hI hl' e).finrank_eq] at hle
  have h1 := hsemi e
  have h2 := hIJ e
  have h3 := hIJ (d + e)
  omega

end GaloisForLFunctions.HTGeometry
