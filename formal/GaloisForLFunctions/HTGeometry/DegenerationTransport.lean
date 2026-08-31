import GaloisForLFunctions.HTGeometry.HilbertConverse

/-!
# A Gröbner degeneration transports regularity

```text
isGradedSubmodule_of_isHomogIdeal                    a homogeneous ideal is a graded subspace
finrank_quotDegreePart_eq_of_finrank_degreePart_eq   equal graded pieces give equal quotient pieces
forall_mem_of_degeneration                           ** if two homogeneous ideals have the same
                                                        graded complement, an element regular on one
                                                        of them and with no jump in the fibre
                                                        dimensions is regular on the other **
```

The proof is the closed loop.  Equal complements give equal Hilbert functions in every degree; the
regular element gives the Hilbert-function equation for the second ideal
(`hilbert_of_forall_mem`); the fibre-dimension bound transports it to the first as an inequality;
`le_finrank_quotient_range_add` supplies the reverse inequality for free; and
`forall_mem_of_hilbert` converts the resulting equation back into regularity.

This is the statement a Gröbner degeneration needs, with no homological algebra: the initial ideal is
the second ideal, the standard monomials are the common complement, and the fibre bound is the
semicontinuity of the flat family.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem isGradedSubmodule_of_isHomogIdeal {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a) :
    IsGradedSubmodule (a.restrictScalars K) := fun e x hx => ha e x hx

theorem finrank_quotDegreePart_eq_of_finrank_degreePart_eq
    {A B : Submodule K (MvPolynomial σ K)} (e : ℕ)
    [FiniteDimensional K (homogeneousSubmodule σ K e)]
    (h : finrank K (degreePart A e) = finrank K (degreePart B e)) :
    finrank K (quotDegreePart A e) = finrank K (quotDegreePart B e) := by
  have h1 : finrank K (quotDegreePart A e) + finrank K (degreePart A e)
      = finrank K (homogeneousSubmodule σ K e) := Submodule.finrank_quotient_add_finrank _
  have h2 : finrank K (quotDegreePart B e) + finrank K (degreePart B e)
      = finrank K (homogeneousSubmodule σ K e) := Submodule.finrank_quotient_add_finrank _
  omega

/-- **A Gröbner degeneration transports regularity of a linear form.**  If two homogeneous ideals
have the same graded complement, a homogeneous element regular on one of them, and the fibre
dimensions do not go up, then it is regular on the other. -/
theorem forall_mem_of_degeneration {I J : Ideal (MvPolynomial σ K)}
    {S : Submodule K (MvPolynomial σ K)}
    (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J) (hS : IsGradedSubmodule S)
    (hIS : IsCompl (I.restrictScalars K) S) (hJS : IsCompl (J.restrictScalars K) S)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K (homogeneousSubmodule σ K e)]
    (hreg : ∀ f : MvPolynomial σ K, l * f ∈ J → f ∈ J)
    (hsemi : ∀ e : ℕ,
      finrank K (quotDegreePart ((I ⊔ Ideal.span {l}).restrictScalars K) (d + e))
        ≤ finrank K (quotDegreePart ((J ⊔ Ideal.span {l}).restrictScalars K) (d + e))) :
    ∀ f : MvPolynomial σ K, l * f ∈ I → f ∈ I := by
  have hIJ : ∀ e : ℕ, finrank K (quotDegreePart (I.restrictScalars K) e)
      = finrank K (quotDegreePart (J.restrictScalars K) e) := fun e =>
    finrank_quotDegreePart_eq_of_finrank_degreePart_eq e
      (finrank_degreePart_eq (isGradedSubmodule_of_isHomogIdeal hI)
        (isGradedSubmodule_of_isHomogIdeal hJ) hS hIS hJS e)
  refine forall_mem_of_hilbert hI hl fun e => ?_
  have hJeq := hilbert_of_forall_mem hJ hl hreg e
  have hge : finrank K (quotDegreePart (I.restrictScalars K) (d + e))
      ≤ finrank K (quotDegreePart ((I ⊔ Ideal.span {l}).restrictScalars K) (d + e))
        + finrank K (quotDegreePart (I.restrictScalars K) e) := by
    have hle := le_finrank_quotient_range_add (mulQuotHom (a := I) hl e)
    rwa [(cokerMulQuotEquiv hI hl e).finrank_eq] at hle
  have h1 := hsemi e
  have h2 := hIJ e
  have h3 := hIJ (d + e)
  omega

end GaloisForLFunctions.HTGeometry
