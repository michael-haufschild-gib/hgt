import GaloisForLFunctions.HTGeometry.ProdFibreSplit
import GaloisForLFunctions.HTGeometry.QuotientRegularSequence
import GaloisForLFunctions.HTGeometry.CyclicFibreDimension

/-!
# Fibre dimensions: transport, additivity, and the cyclic value

```text
finrank_quot_congr   the fibre dimension is an isomorphism invariant
finrank_quot_prod    it is additive on products
finrank_quot_pi      and on finite products
finrank_quot_cyclic  ** and on a cyclic module it is one exactly where the annihilator vanishes **
```

These are the four steps of a fibre computation along the decomposition of a finitely generated
module over a principal ideal domain.  The cyclic value is `finrank_quotient_span_pair` moved from
the ideal presentation `K[X] ⧸ (span q ⊔ span (X - lam))` to the module presentation
`(K[X] ⧸ span q) ⧸ (span (X - lam) • ⊤)` by `quotSMulTopIdealEquiv`.

Together with `finrank_quotient_finsupp` — the free part contributes its rank at every point — they
compute the fibre of any finitely generated module over the base line: the rank plus the number of
torsion summands whose annihilator vanishes at that point.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]

theorem finrank_quot_congr {M N : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
    (I : Ideal A) (e : M ≃ₗ[A] N) :
    finrank K (M ⧸ (I • (⊤ : Submodule A M))) = finrank K (N ⧸ (I • (⊤ : Submodule A N))) :=
  ((quotSmulEquivOfEquiv I e).restrictScalars K).finrank_eq

theorem finrank_quot_prod {M N : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
    (I : Ideal A) [FiniteDimensional K (M ⧸ (I • (⊤ : Submodule A M)))]
    [FiniteDimensional K (N ⧸ (I • (⊤ : Submodule A N)))] :
    finrank K ((M × N) ⧸ (I • (⊤ : Submodule A (M × N))))
      = finrank K (M ⧸ (I • (⊤ : Submodule A M)))
        + finrank K (N ⧸ (I • (⊤ : Submodule A N))) := by
  rw [((prodQuotSmulEquiv I).restrictScalars K).finrank_eq, finrank_prod]

theorem finrank_quot_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, Module K (M i)]
    [∀ i, IsScalarTower K A (M i)] (I : Ideal A)
    [∀ i, FiniteDimensional K (M i ⧸ (I • (⊤ : Submodule A (M i))))] :
    finrank K ((∀ i, M i) ⧸ (I • (⊤ : Submodule A (∀ i, M i))))
      = ∑ i, finrank K (M i ⧸ (I • (⊤ : Submodule A (M i)))) := by
  rw [((piQuotSmulEquiv (ι := ι) (M := M) I).restrictScalars K).finrank_eq,
    Module.finrank_pi_fintype K]

open scoped Classical in
/-- **The fibre of a cyclic module, in module presentation.** -/
theorem finrank_quot_cyclic (q : K[X]) (lam : K) :
    finrank K ((K[X] ⧸ Ideal.span {q}) ⧸
        (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (K[X] ⧸ Ideal.span {q}))))
      = if (X - C lam : K[X]) ∣ q then 1 else 0 := by
  rw [((quotSMulTopIdealEquiv (Ideal.span {q})
    (Ideal.span {(X - C lam : K[X])})).restrictScalars K).finrank_eq]
  exact finrank_quotient_span_pair q lam

end GaloisForLFunctions.HTGeometry
