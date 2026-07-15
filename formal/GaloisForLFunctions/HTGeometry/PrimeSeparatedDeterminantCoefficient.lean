import GaloisForLFunctions.HTGeometry.ArithmeticFunctionDeterminantCoefficient
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Determinants with separated prime rows

If row `i` of a matrix of arithmetic functions is supported on powers of a distinct prime `q i`,
unique factorization separates the rows inside every Dirichlet-convolution determinant.  The
coefficient at `prod_i q_i ^ e_i` is therefore the determinant of the scalar matrix obtained by
reading row `i` at `q_i ^ e_i`.

Unlike the point-mass coefficient law, the entries may have arbitrary infinite tails along their
own prime-power ray.  This is the determinant mechanism needed for all-valuation Euler
completions.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-- Equality of products in distinct prime coordinates determines an arbitrary exponent vector. -/
theorem primePacket_powProduct_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q) :
    Function.Injective (fun e : I → ℕ => ∏ i, (q i : ℕ) ^ e i) := by
  classical
  intro e f hef
  funext j
  have hfac := congrArg Nat.factorization hef
  have happly := congrArg (fun g : ℕ →₀ ℕ => g (q j : ℕ)) hfac
  simp_rw [Nat.factorization_prod_apply
    (fun i hi => pow_ne_zero _ (q i).2.ne_zero)] at happly
  have hfactor (x y : I) :
      (q x : ℕ).factorization (q y : ℕ) = if x = y then 1 else 0 := by
    rw [Nat.Prime.factorization (q x).2]
    by_cases hxy : x = y
    · subst y
      rw [Finsupp.single_eq_same, if_pos rfl]
    · have hqne : (q x : ℕ) ≠ (q y : ℕ) := by
        intro h
        apply hxy
        apply hq
        exact Subtype.ext h
      rw [Finsupp.single_eq_of_ne hqne.symm, if_neg hxy]
  have hfactorPow (x y : I) (k : ℕ) :
      ((q x : ℕ) ^ k).factorization (q y : ℕ) =
        if x = y then k else 0 := by
    rw [Nat.factorization_pow]
    change k * (q x : ℕ).factorization (q y : ℕ) = _
    rw [hfactor]
    by_cases hxy : x = y <;> simp [hxy]
  simp_rw [hfactorPow] at happly
  simpa using happly

/-- An arithmetic function is supported on the nonnegative powers of one prime. -/
def SupportedOnPrimeRay (q : Nat.Primes) (f : ArithmeticFunction ℂ) : Prop :=
  ∀ ⦃n : ℕ⦄, f n ≠ 0 → ∃ k : ℕ, n = (q : ℕ) ^ k

/-- A Dirichlet-convolution product of functions on pairwise distinct prime rays has a unique
factorization at the corresponding product coefficient. -/
theorem arithmeticFunction_fin_prod_apply_primeRays
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (f : I → ArithmeticFunction ℂ)
    (hsupport : ∀ i, SupportedOnPrimeRay (q i) (f i)) :
    (∏ i, f i) (∏ i, (q i : ℕ) ^ e i) =
      ∏ i, f i ((q i : ℕ) ^ e i) := by
  classical
  let v : I → ℕ := fun i => (q i : ℕ) ^ e i
  let n : ℕ := ∏ i, v i
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hvpos : ∀ i, 0 < v i := fun i => pow_pos (q i).2.pos _
  obtain ⟨d₀, hd₀⟩ :=
    GaloisForLFunctions.exists_dirichletFactorData_factors_eq
      (q := Fintype.card I)
      (fun i : Fin (Fintype.card I) => v (E.symm i))
      (fun i => hvpos (E.symm i)) rfl
  let f' : Fin (Fintype.card I) → ArithmeticFunction ℂ := fun i => f (E.symm i)
  have hprod_reindex :
      (∏ i : Fin (Fintype.card I), f' i) = ∏ i : I, f i := by
    exact E.symm.prod_comp f
  have hn_reindex :
      (∏ i : Fin (Fintype.card I), v (E.symm i)) = n := by
    exact E.symm.prod_comp v
  change (∏ i : I, f i) n = ∏ i : I, f i (v i)
  rw [← hprod_reindex]
  rw [← hn_reindex]
  rw [GaloisForLFunctions.arithmeticFunction_fin_prod_apply]
  rw [Fintype.sum_eq_single d₀]
  · rw [hd₀]
    exact E.symm.prod_comp (fun i => f i (v i))
  · intro d hne
    by_contra hnonzero
    have hpoint : ∀ i : Fin (Fintype.card I),
        f' i (d.factors i) ≠ 0 := by
      intro i
      exact Finset.prod_ne_zero_iff.mp hnonzero i (Finset.mem_univ i)
    choose m hm using fun i => hsupport (E.symm i) (hpoint i)
    have hpowprod :
        (∏ i : I, (q i : ℕ) ^ (m (E i))) = ∏ i : I, (q i : ℕ) ^ e i := by
      calc
        (∏ i : I, (q i : ℕ) ^ (m (E i))) =
            ∏ j : Fin (Fintype.card I), (q (E.symm j) : ℕ) ^ m j := by
              simpa using E.prod_comp (fun j => (q (E.symm j) : ℕ) ^ m j)
        _ = ∏ j : Fin (Fintype.card I), d.factors j := by
              apply Finset.prod_congr rfl
              intro j hj
              rw [hm j]
        _ = ∏ j : Fin (Fintype.card I), v (E.symm j) := by
              rw [d.prod_factors, hn_reindex]
        _ = ∏ i : I, (q i : ℕ) ^ e i := by
              exact E.symm.prod_comp v
    have hmexp : (fun i : I => m (E i)) = e :=
      primePacket_powProduct_injective q hq hpowprod
    have hfac : d.factors = d₀.factors := by
      funext j
      rw [hm j, hd₀]
      have := congrFun hmexp (E.symm j)
      have hme : m j = e (E.symm j) := by simpa using this
      change (q (E.symm j) : ℕ) ^ m j =
        (q (E.symm j) : ℕ) ^ e (E.symm j)
      rw [hme]
    apply hne
    exact GaloisForLFunctions.DirichletFactorData.factors_injective
      (Finset.prod_pos fun i hi => hvpos (E.symm i)) hfac

/-- **Separated-prime determinant coefficient law.**  If row `i` is supported on the powers of
the distinct prime `q i`, then the coefficient of the arithmetic determinant at
`prod_i q_i ^ e_i` is the determinant of the rowwise scalar coefficient matrix. -/
theorem primeRayMatrix_det_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (M : Matrix I I (ArithmeticFunction ℂ))
    (hsupport : ∀ i j, SupportedOnPrimeRay (q i) (M i j)) :
    M.det (∏ i, (q i : ℕ) ^ e i) =
      Matrix.det (fun i j => M i j ((q i : ℕ) ^ e i)) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f (∏ i, (q i : ℕ) ^ e i)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ σ, Equiv.Perm.sign σ • ∏ i, M (σ i) i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  calc
    ev (Equiv.Perm.sign σ • ∏ i, M (σ i) i) =
        Equiv.Perm.sign σ • ev (∏ i, M (σ i) i) :=
      ev.map_zsmul (Equiv.Perm.sign σ) (∏ i, M (σ i) i)
    _ = Equiv.Perm.sign σ •
        ∏ i, M (σ i) i ((q (σ i) : ℕ) ^ e (σ i)) := by
      change Equiv.Perm.sign σ •
          ((∏ i, M (σ i) i) (∏ i, (q i : ℕ) ^ e i)) = _
      have hqσ : Function.Injective (q ∘ σ) := hq.comp σ.injective
      have hsupportσ : ∀ i,
          SupportedOnPrimeRay ((q ∘ σ) i) (M (σ i) i) := by
        intro i
        exact hsupport (σ i) i
      have hprod :
          (∏ i, (q i : ℕ) ^ e i) =
            ∏ i, ((q ∘ σ) i : ℕ) ^ (e ∘ σ) i := by
        symm
        exact Equiv.prod_comp σ (fun i => (q i : ℕ) ^ e i)
      rw [hprod, arithmeticFunction_fin_prod_apply_primeRays
        (q ∘ σ) hqσ (e ∘ σ) (fun i => M (σ i) i) hsupportσ]
      simp only [Function.comp_apply]
    _ = Equiv.Perm.sign σ •
        ∏ i, M (σ i) i ((q (σ i) : ℕ) ^ e (σ i)) := rfl

/-- A nonzero separated-prime scalar coefficient determinant certifies a nonzero determinant in
the arithmetic-function ring. -/
theorem primeRayMatrix_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (M : Matrix I I (ArithmeticFunction ℂ))
    (hsupport : ∀ i j, SupportedOnPrimeRay (q i) (M i j))
    (hdet : Matrix.det (fun i j => M i j ((q i : ℕ) ^ e i)) ≠ 0) :
    M.det ≠ 0 := by
  intro hzero
  have happly : M.det (∏ i, (q i : ℕ) ^ e i) = 0 := by
    simpa using congrArg
      (fun f : ArithmeticFunction ℂ => f (∏ i, (q i : ℕ) ^ e i)) hzero
  rw [primeRayMatrix_det_apply q hq e M hsupport] at happly
  exact hdet happly

end

end GaloisForLFunctions.HTGeometry
