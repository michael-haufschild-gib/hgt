import GaloisForLFunctions.HTGeometry.DeformedDegeneration

/-!
# The degeneration step, and the invariant that lets it iterate

```text
forall_mem_of_hilbert_le   ** the step, with equal Hilbert functions as a hypothesis **
hilbert_eq_of_forall_mem   ** and the invariant: if both forms are regular, the quotients again have
                              equal Hilbert functions **
```

The invariant carried along a regular sequence is *equal Hilbert functions*, not a common
complement: after quotienting by a regular element on each side, the two Hilbert functions drop by
the same rule, so they stay equal, and the step applies again.

That is what turns a single transported regular element into a transported regular *sequence* — and
it is why the common complement is needed only at the start, where the corpus's standard-monomial
basis supplies it.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **The degeneration step, with equal Hilbert functions as a hypothesis.**  This is the form the
iteration uses: the invariant carried along a regular sequence is that the two quotients have the
same Hilbert function, not that they have a common complement. -/
theorem forall_mem_of_hilbert_le {I J : Ideal (MvPolynomial σ K)}
    (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J)
    (hHilb : ∀ e : ℕ, finrank K (quotDegreePart (I.restrictScalars K) e)
      = finrank K (quotDegreePart (J.restrictScalars K) e))
    {l l' : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (hl' : l'.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K (homogeneousSubmodule σ K e)]
    (hreg : ∀ f : MvPolynomial σ K, l * f ∈ J → f ∈ J)
    (hsemi : ∀ e : ℕ,
      finrank K (quotDegreePart ((I ⊔ Ideal.span {l'}).restrictScalars K) (d + e))
        ≤ finrank K (quotDegreePart ((J ⊔ Ideal.span {l}).restrictScalars K) (d + e))) :
    ∀ f : MvPolynomial σ K, l' * f ∈ I → f ∈ I := by
  refine forall_mem_of_hilbert hI hl' fun e => ?_
  have hJeq := hilbert_of_forall_mem hJ hl hreg e
  have hge : finrank K (quotDegreePart (I.restrictScalars K) (d + e))
      ≤ finrank K (quotDegreePart ((I ⊔ Ideal.span {l'}).restrictScalars K) (d + e))
        + finrank K (quotDegreePart (I.restrictScalars K) e) := by
    have hle := le_finrank_quotient_range_add (mulQuotHom (a := I) hl' e)
    rwa [(cokerMulQuotEquiv hI hl' e).finrank_eq] at hle
  have h1 := hsemi e
  have h2 := hHilb e
  have h3 := hHilb (d + e)
  omega

/-- **And the invariant is preserved.**  If both forms are regular, the two quotients again have the
same Hilbert function. -/
theorem hilbert_eq_of_forall_mem {I J : Ideal (MvPolynomial σ K)}
    (hI : IsHomogIdeal I) (hJ : IsHomogIdeal J)
    (hHilb : ∀ e : ℕ, finrank K (quotDegreePart (I.restrictScalars K) e)
      = finrank K (quotDegreePart (J.restrictScalars K) e))
    {l l' : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (hl' : l'.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K (homogeneousSubmodule σ K e)]
    (hregJ : ∀ f : MvPolynomial σ K, l * f ∈ J → f ∈ J)
    (hregI : ∀ f : MvPolynomial σ K, l' * f ∈ I → f ∈ I) (e : ℕ) :
    finrank K (quotDegreePart ((I ⊔ Ideal.span {l'}).restrictScalars K) (d + e))
      = finrank K (quotDegreePart ((J ⊔ Ideal.span {l}).restrictScalars K) (d + e)) := by
  have hIeq := hilbert_of_forall_mem hI hl' hregI e
  have hJeq := hilbert_of_forall_mem hJ hl hregJ e
  have h2 := hHilb e
  have h3 := hHilb (d + e)
  omega

end GaloisForLFunctions.HTGeometry
