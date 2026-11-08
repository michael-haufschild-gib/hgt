import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodHardy
import Mathlib.Algebra.Group.Nat.Hom

/-!
# Identifiability of finite prime likelihood packets

Dedekind independence of distinct geometric sequences proves that finite
Hardy packets have unique coefficients. The spectral Gram isometry transfers
this uniqueness to actual likelihood vectors in semicircle `L²`.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Distinct reciprocal-prime geometric sequences are independent by Dedekind’s character theorem. -/
theorem primeHardyKernel_linearIndependent : LinearIndependent ℝ primeHardyKernel := by
  let A : PrimeHardy →ₗ[ℝ] (Multiplicative ℕ → ℝ) :=
    { toFun := fun x n => x n.toAdd
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp A
  change LinearIndependent ℝ (fun p : Nat.Primes =>
    (powersHom ℝ (primeReciprocal p) : Multiplicative ℕ → ℝ))
  apply ((linearIndependent_monoidHom (Multiplicative ℕ) ℝ).comp
    (powersHom ℝ) (powersHom ℝ).injective).comp
  intro p q hpq
  apply Subtype.ext
  have h : (p : ℝ) = (q : ℝ) := inv_injective hpq
  exact_mod_cast h

/-- Finite Hardy packets determine every prime coefficient uniquely. -/
theorem primeHardyKernelMap_injective : Function.Injective primeHardyKernelMap := by
  have he (c : Nat.Primes →₀ ℝ) :
      primeHardyKernelMap c = Finsupp.linearCombination ℝ primeHardyKernel c := by
    induction c using Finsupp.induction with
    | zero => simp
    | single_add p a c hp ha ih =>
        simp only [map_add, primeHardyKernelMap_single, Finsupp.linearCombination_single, ih]
  intro c d h
  apply primeHardyKernel_linearIndependent.finsuppLinearCombination_injective
  simpa only [← he] using h

/-- Equality of actual likelihood packets forces equality of their prime coefficients. -/
theorem kestenLikelihoodMap_injective : Function.Injective kestenLikelihoodMap := by
  apply LinearMap.ker_eq_bot.mp
  rw [HilbertMetric.NomologicalCrossGram.ker_eq_of_inner_eq
    kestenLikelihoodMap primeHardyKernelMap inner_kestenLikelihoodMap]
  exact LinearMap.ker_eq_bot.mpr primeHardyKernelMap_injective

/-- All prime likelihood vectors form a linearly independent family in semicircle `L²`. -/
theorem kestenLikelihoodVector_linearIndependent : LinearIndependent ℝ kestenLikelihoodVector :=
  linearIndependent_iff_injective_finsuppLinearCombination.mpr kestenLikelihoodMap_injective

end
end GaloisForLFunctions.SelbergClass.Primon

