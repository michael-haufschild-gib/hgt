import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFiniteColors

/-!
# Finite color bases and exact prime independence

Restricting a full basis of functions on a finite color space preserves independence exactly
when no color is removed. Applied to prime columns, this identifies the exact exceptional-prime
criterion for every finite character table or product basis: every color fiber must survive.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter Module
open scoped Classical

noncomputable section

/-- A full basis of scalar functions remains independent on a subset exactly when the subset is
all of the domain. A missing point supplies a nonzero indicator in the restriction kernel. -/
theorem linearIndependent_restrict_functionBasis_iff
    {I C : Type*} [Fintype I] (B : Basis I ℂ (C → ℂ)) (S : Set C) :
    LinearIndependent ℂ (fun i (c : S) => B i c.1) ↔ S = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_iff_forall.mpr
    intro c
    by_contra hc
    let v : C → ℂ := fun d => if d = c then 1 else 0
    have hsum : ∑ i, (B.repr v) i • (fun d : S => B i d.1) = 0 := by
      funext d
      have hd : d.1 ≠ c := by
        intro hdc
        exact hc (hdc ▸ d.2)
      have heval := congrFun (B.sum_repr v) d.1
      simpa [v, hd, Finset.sum_apply, Pi.smul_apply] using heval
    have hcoeff := (Fintype.linearIndependent_iff.mp h) (B.repr v) hsum
    have hv : v = 0 := by
      rw [← B.sum_repr v]
      simp only [hcoeff, zero_smul, Finset.sum_const_zero]
    have heval := congrFun hv c
    simpa [v] using heval
  · rintro rfl
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    apply (Fintype.linearIndependent_iff.mp B.linearIndependent) c _ i
    funext d
    have heval := congrFun hc (⟨d, Set.mem_univ d⟩ : (Set.univ : Set C))
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using heval

/-- For any finite function basis, algebraic independence of its prime columns is equivalent to
survival of every color fiber. This includes all finite character and anchored product bases. -/
theorem algebraicIndependent_finiteColorBasis_iff
    {I C : Type*} [Fintype I] [DecidableEq I] [Finite C]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (B : Basis I ℂ (C → ℂ)) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (fun p => B i (color p)))) ↔
      ∀ c, ∃ᶠ p in F, color p = c := by
  simpa only [Set.eq_univ_iff_forall, frequentPrimeColors, Set.mem_setOf_eq] using
    (algebraicIndependent_finiteColorPrimeColumns_iff F color (fun i c => B i c)).trans
      (linearIndependent_restrict_functionBasis_iff B (frequentPrimeColors F color))

/-- The exact density-zero exception criterion for every finite function basis. -/
theorem algebraicIndependent_finiteColorBasis_over_densityField_iff
    {I C : Type*} [Fintype I] [DecidableEq I] [Finite C]
    (W : ℕ → Finset Nat.Primes) (color : Nat.Primes → C) (B : Basis I ℂ (C → ℂ)) :
    AlgebraicIndependent (primeDensityCoefficientField W)
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (fun p => B i (color p)))) ↔
      ∀ c, ¬ PrimeWindowDensityZero W {p | color p = c} := by
  rw [algebraicIndependent_finiteColorBasis_iff (primeWindowDensityFilter W) color B]
  constructor
  · intro h c
    exact (mem_frequentPrimeColors_density_iff W color c).mp (h c)
  · intro h c
    exact (mem_frequentPrimeColors_density_iff W color c).mpr (h c)

#print axioms linearIndependent_restrict_functionBasis_iff
#print axioms algebraicIndependent_finiteColorBasis_over_densityField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
