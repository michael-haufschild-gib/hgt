import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterCoefficientField

/-!
# Exact independence criteria after excluding primes

The filter criterion specializes to three useful coefficient fields: finite prime activity,
activity confined to a prescribed exceptional set, and activity confined there up to finitely
many additional primes. These are exact criteria, including finite and empty retained prime sets.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- The cofinite filter recovers the existing finite-prime coefficient field. -/
theorem primeFilterCoefficientField_cofinite :
    (primeFilterCoefficientField cofinite).toSubfield = finitePrimeCoefficientField := by
  ext x
  change (∀ᶠ p in cofinite, primeFractionDerivation p x = 0) ↔
    (finitePrimeActivity x).Finite
  rw [eventually_cofinite]
  rfl

/-- Keeping all primes in `P` makes coefficients precisely the fractions invisible on `P`. -/
theorem mem_principal_primeFilterCoefficientField_iff
    (P : Set Nat.Primes) (x : arithmeticFunctionFractionField) :
    x ∈ primeFilterCoefficientField (principal P) ↔
      ∀ p ∈ P, primeFractionDerivation p x = 0 :=
  eventually_principal

/-- Allowing finitely many additional exceptions means only finitely many active primes remain
inside the retained set. -/
theorem mem_relative_cofinite_primeFilterCoefficientField_iff
    (P : Set Nat.Primes) (x : arithmeticFunctionFractionField) :
    x ∈ primeFilterCoefficientField (cofinite ⊓ principal P) ↔
      {p ∈ P | primeFractionDerivation p x ≠ 0}.Finite := by
  rw [mem_primeFilterCoefficientField_iff, eventually_inf_principal, eventually_cofinite]
  simp only [not_imp]

/-- For a fixed retained prime set, ordinary coefficient-vector independence is already the exact
criterion over the field of fractions with no activity there. -/
theorem algebraicIndependent_primeColumns_over_principalField_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Set Nat.Primes) (a : I → Nat.Primes → ℂ) :
    AlgebraicIndependent (primeFilterCoefficientField (principal P))
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) ↔
      LinearIndependent ℂ (fun i (p : P) => a i p.1) := by
  rw [algebraicIndependent_primeColumns_over_filterField_iff,
    Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i
    have hzero := h c (by
      rw [eventually_principal]
      intro p hp
      have heval := congrFun hc (⟨p, hp⟩ : P)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval)
    exact congrFun hzero i
  · intro h c hc
    funext i
    apply h c _ i
    funext p
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      (eventually_principal.mp hc p.1 p.2)

/-- Exact relative-tail criterion: every nonzero combination must remain nonzero at infinitely
many retained primes. Coefficients may use every excluded prime and finitely many retained ones. -/
theorem algebraicIndependent_primeColumns_over_relativeTailField_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Set Nat.Primes) (a : I → Nat.Primes → ℂ) :
    AlgebraicIndependent (primeFilterCoefficientField (cofinite ⊓ principal P))
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) ↔
      ∀ c : I → ℂ, {p ∈ P | ∑ i, c i * a i p ≠ 0}.Finite → c = 0 := by
  rw [algebraicIndependent_primeColumns_over_filterField_iff]
  simp only [FilterCoefficientIndependent, eventually_inf_principal, eventually_cofinite, not_imp]

/-- The cofinite specialization agrees exactly with tail coefficient independence. -/
theorem filterCoefficientIndependent_cofinite_iff
    {I : Type*} [Fintype I] (a : I → Nat.Primes → ℂ) :
    FilterCoefficientIndependent cofinite a ↔ TailCoefficientIndependent a := by
  simp only [FilterCoefficientIndependent, TailCoefficientIndependent, eventually_cofinite]

#print axioms algebraicIndependent_primeColumns_over_principalField_iff
#print axioms algebraicIndependent_primeColumns_over_relativeTailField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
