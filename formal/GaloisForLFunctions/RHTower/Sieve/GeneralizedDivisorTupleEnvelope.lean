import GaloisForLFunctions.HTGeometry.ArithmeticFunctionDeterminantCoefficient
import GaloisForLFunctions.RHTower.Sieve.GeneralizedDivisorShortInterval

/-!
# Finite tuple families and generalized-divisor coefficients

Any injectively labelled family of ordered positive `(r+1)`-factorizations of `n` has cardinality
at most the coefficient of `ζ^(r+1)` at `n`.  This is the exact combinatorial envelope needed for
families of disjoint Harman cells and recursive block chains.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

open GaloisForLFunctions

/-- Canonical factor data attached to a valid positive vector; invalid vectors are totalized at
the fixed factorization `(n,1,...,1)`. -/
def generalizedDivisorFactorDataOfVector
    (r n : ℕ) (hn : 0 < n) (v : Fin (r + 1) → ℕ) :
    GaloisForLFunctions.DirichletFactorData (r + 1) n := by
  let fallback : Fin (r + 1) → ℕ := Fin.cases n (fun _ => 1)
  have hfallbackPos : ∀ i, 0 < fallback i := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [fallback] using hn
    | succ i => simp [fallback]
  have hfallbackProd : (∏ i, fallback i) = n := by
    rw [Fin.prod_univ_succ]
    simp [fallback]
  by_cases hv : (∀ i, 0 < v i) ∧ (∏ i, v i) = n
  · exact Classical.choose
      (GaloisForLFunctions.exists_dirichletFactorData_factors_eq v hv.1 hv.2)
  · exact Classical.choose
      (GaloisForLFunctions.exists_dirichletFactorData_factors_eq
        fallback hfallbackPos hfallbackProd)

theorem generalizedDivisorFactorDataOfVector_factors
    (r n : ℕ) (hn : 0 < n) (v : Fin (r + 1) → ℕ)
    (hpos : ∀ i, 0 < v i) (hprod : (∏ i, v i) = n) :
    (generalizedDivisorFactorDataOfVector r n hn v).factors = v := by
  rw [generalizedDivisorFactorDataOfVector]
  split
  · exact Classical.choose_spec
      (GaloisForLFunctions.exists_dirichletFactorData_factors_eq v hpos hprod)
  · rename_i hnot
    exact False.elim (hnot ⟨hpos, hprod⟩)

private theorem zeta_int_apply_eq_cast (n : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℤ) n =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) n : ℤ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [ArithmeticFunction.zeta_apply, hn]

private theorem zeta_int_pow_apply_eq_cast (q n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ q) n =
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ q) n : ℕ) : ℤ) := by
  induction q generalizing n with
  | zero =>
      by_cases hn : n = 1
      · subst n
        simp
      · simp [hn]
  | succ q ih =>
      rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply,
        ArithmeticFunction.mul_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro de hde
      rw [ih, zeta_int_apply_eq_cast]

/-- Factor-data cardinality is exactly the generalized-divisor coefficient. -/
theorem card_dirichletFactorData_eq_zeta_pow
    (q n : ℕ) (hn : 0 < n) :
    Fintype.card (GaloisForLFunctions.DirichletFactorData q n) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ q) n := by
  have hcoef := GaloisForLFunctions.arithmeticFunction_fin_prod_apply
    q n (fun _ : Fin q => (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
  have hzeta : ∀ d : GaloisForLFunctions.DirichletFactorData q n, ∀ i,
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ) (d.factors i) = 1 := by
    intro d i
    rw [zeta_int_apply_eq_cast]
    norm_cast
    exact ArithmeticFunction.zeta_apply_ne (d.factor_pos hn i).ne'
  simp_rw [hzeta] at hcoef
  have hcoef' :
      ((Fintype.card (GaloisForLFunctions.DirichletFactorData q n) : ℕ) : ℤ) =
        ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ q) n := by
    simpa using hcoef.symm
  rw [zeta_int_pow_apply_eq_cast] at hcoef'
  exact_mod_cast hcoef'

/-- Injective positive product vectors are counted by one zeta-convolution coefficient. -/
theorem card_le_zeta_pow_of_injective_factorVectors
    {α : Type*} [DecidableEq α]
    (r n : ℕ) (hn : 0 < n) (S : Finset α) (v : α → Fin (r + 1) → ℕ)
    (hvinj : Set.InjOn v S)
    (hpos : ∀ a ∈ S, ∀ i, 0 < v a i)
    (hprod : ∀ a ∈ S, (∏ i, v a i) = n) :
    S.card ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 1)) n := by
  let f : α → GaloisForLFunctions.DirichletFactorData (r + 1) n :=
    fun a => generalizedDivisorFactorDataOfVector r n hn (v a)
  calc
    S.card ≤ Fintype.card (GaloisForLFunctions.DirichletFactorData (r + 1) n) := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card_of_injOn f
      · intro a ha
        exact Finset.mem_univ _
      · intro a ha b hb hab
        apply hvinj ha hb
        rw [← generalizedDivisorFactorDataOfVector_factors
          r n hn (v a) (hpos a ha) (hprod a ha)]
        rw [← generalizedDivisorFactorDataOfVector_factors
          r n hn (v b) (hpos b hb) (hprod b hb)]
        exact congrArg GaloisForLFunctions.DirichletFactorData.factors hab
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 1)) n :=
      card_dirichletFactorData_eq_zeta_pow (r + 1) n hn

end

end RHTower.Sieve
