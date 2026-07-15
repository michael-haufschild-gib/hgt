import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The prime-power block coefficient of an arithmetic Jacobian

The basic derivative of a column supported at `p^(e+1)` is a point mass at `q^e`.  For globally
distinct row primes, the coefficient of `prod_i q_i^(e_i)` in the convolution determinant keeps
exactly the permutations preserving the exponent layers.  It is therefore the determinant of the
ordinary coefficient matrix with all cross-layer entries set to zero.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

/-- The arithmetic point mass with value `z` at a positive integer `n`.  At `n = 0` it is defined
to be zero, as required by the arithmetic-function convention. -/
def arithmeticPointMass (n : ℕ) (z : ℂ) : ArithmeticFunction ℂ :=
  if hn : n = 0 then 0 else
    { toFun := fun m => if m = n then z else 0
      map_zero' := by rw [if_neg (Ne.symm hn)] }

theorem arithmeticPointMass_apply_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) (z : ℂ) (m : ℕ) :
    arithmeticPointMass n z m = if m = n then z else 0 := by
  simp [arithmeticPointMass, hn]

@[simp]
theorem arithmeticPointMass_apply_self
    {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    arithmeticPointMass n z n = z := by
  simp [arithmeticPointMass_apply_of_ne_zero hn]

theorem arithmeticPointMass_apply_of_ne
    {m n : ℕ} (hn : n ≠ 0) (hmn : m ≠ n) (z : ℂ) :
    arithmeticPointMass n z m = 0 := by
  simp [arithmeticPointMass_apply_of_ne_zero hn, hmn]

/-- Dirichlet convolution multiplies positive point masses by multiplying both locations and
values. -/
theorem arithmeticPointMass_mul
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (a b : ℂ) :
    arithmeticPointMass m a * arithmeticPointMass n b =
      arithmeticPointMass (m * n) (a * b) := by
  ext k
  rw [ArithmeticFunction.mul_apply]
  by_cases hk : k = m * n
  · subst k
    rw [Finset.sum_eq_single (m, n)]
    · rw [arithmeticPointMass_apply_self hm,
        arithmeticPointMass_apply_self hn,
        arithmeticPointMass_apply_self (mul_ne_zero hm hn)]
    · intro de hde hdene
      rcases de with ⟨d, e⟩
      by_cases hdm : d = m
      · subst d
        have hen : e ≠ n := by
          intro hen
          exact hdene (Prod.ext rfl hen)
        rw [arithmeticPointMass_apply_self hm,
          arithmeticPointMass_apply_of_ne hn hen]
        simp
      · rw [arithmeticPointMass_apply_of_ne hm hdm]
        simp
    · intro hnot
      exfalso
      apply hnot
      exact Nat.mem_divisorsAntidiagonal.mpr
        ⟨rfl, Nat.mul_ne_zero hm hn⟩
  · rw [arithmeticPointMass_apply_of_ne (mul_ne_zero hm hn) hk]
    apply Finset.sum_eq_zero
    intro de hde
    rcases de with ⟨d, e⟩
    by_cases hdm : d = m
    · subst d
      by_cases hen : e = n
      · exfalso
        have hprod : m * n = k := by
          simpa [hen] using (Nat.mem_divisorsAntidiagonal.mp hde).1
        exact hk hprod.symm
      · rw [arithmeticPointMass_apply_of_ne hn hen]
        simp
    · rw [arithmeticPointMass_apply_of_ne hm hdm]
      simp

theorem arithmeticPointMass_finprod
    {I : Type*} [Fintype I]
    (n : I → ℕ) (z : I → ℂ) (hn : ∀ i, n i ≠ 0) :
    ∏ i, arithmeticPointMass (n i) (z i) =
      arithmeticPointMass (∏ i, n i) (∏ i, z i) := by
  classical
  let s : Finset I := Finset.univ
  change (∏ i ∈ s, arithmeticPointMass (n i) (z i)) = _
  have hprod : ∀ t : Finset I,
      (∏ i ∈ t, arithmeticPointMass (n i) (z i)) =
        arithmeticPointMass (∏ i ∈ t, n i) (∏ i ∈ t, z i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        ext k
        by_cases hk : k = 1
        · subst k
          simp [arithmeticPointMass_apply_self one_ne_zero]
        · simp [arithmeticPointMass_apply_of_ne one_ne_zero hk,
            hk]
    | @insert i t hit ih =>
        rw [Finset.prod_insert hit, Finset.prod_insert hit,
          Finset.prod_insert hit, ih,
          arithmeticPointMass_mul (hn i)]
        exact Finset.prod_ne_zero_iff.mpr fun j hj => hn j
  simpa [s] using hprod s

/-- Equality of two products in distinct prime coordinates is equality of every exponent. -/
theorem primePacket_powProduct_eq_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (σ : Equiv.Perm I) :
    (∏ j, (q (σ j) : ℕ) ^ e j) = (∏ j, (q j : ℕ) ^ e j) ↔
      ∀ j, e j = e (σ j) := by
  classical
  constructor
  · intro hprod j
    have hfac := congrArg Nat.factorization hprod
    have happly := congrArg
      (fun f : ℕ →₀ ℕ => f (q (σ j) : ℕ)) hfac
    simp_rw [Nat.factorization_prod_apply
      (fun i hi => pow_ne_zero _ (q (σ i)).2.ne_zero)] at happly
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
    simpa [σ.injective.eq_iff] using happly
  · intro hpres
    calc
      (∏ j, (q (σ j) : ℕ) ^ e j) =
          ∏ j, (q (σ j) : ℕ) ^ e (σ j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hpres j]
      _ = ∏ j, (q j : ℕ) ^ e j :=
        Equiv.prod_comp σ (fun j => (q j : ℕ) ^ e j)

/-- The Jacobian matrix whose row `i`, column `j` is a point mass at the row prime raised to the
column exponent. -/
def primePowerPointMassMatrix
    {I : Type*} (q : I → Nat.Primes) (e : I → ℕ) (B : Matrix I I ℂ) :
    Matrix I I (ArithmeticFunction ℂ) :=
  fun i j => arithmeticPointMass ((q i : ℕ) ^ e j) (B i j)

/-- The scalar coefficient matrix obtained by deleting every cross-exponent entry. -/
def primePowerBlockMatrix
    {I : Type*} [DecidableEq ℕ]
    (e : I → ℕ) (B : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if e i = e j then B i j else 0

/-- **Prime-power block coefficient law.**  The distinguished coefficient of the convolution
Jacobian determinant is exactly the determinant of the exponent-block scalar matrix. -/
theorem primePowerPointMassMatrix_det_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (B : Matrix I I ℂ) :
    (primePowerPointMassMatrix q e B).det
        (∏ i, (q i : ℕ) ^ e i) =
      (primePowerBlockMatrix e B).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f (∏ i, (q i : ℕ) ^ e i)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ σ, Equiv.Perm.sign σ •
      ∏ i, primePowerPointMassMatrix q e B (σ i) i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  calc
    ev (Equiv.Perm.sign σ •
        ∏ i, primePowerPointMassMatrix q e B (σ i) i) =
        Equiv.Perm.sign σ • ev
          (∏ i, primePowerPointMassMatrix q e B (σ i) i) :=
      ev.map_zsmul (Equiv.Perm.sign σ)
        (∏ i, primePowerPointMassMatrix q e B (σ i) i)
    _ = _ := by
      change Equiv.Perm.sign σ •
          ((∏ i, primePowerPointMassMatrix q e B (σ i) i)
            (∏ i, (q i : ℕ) ^ e i)) = _
      simp only [primePowerPointMassMatrix]
      rw [arithmeticPointMass_finprod]
      · rw [arithmeticPointMass_apply_of_ne_zero
          (Finset.prod_ne_zero_iff.mpr fun i hi =>
            pow_ne_zero _ (q (σ i)).2.ne_zero)]
        by_cases hpres : ∀ j, e j = e (σ j)
        · have hloc := (primePacket_powProduct_eq_iff q hq e σ).mpr hpres
          rw [if_pos hloc.symm]
          simp only [primePowerBlockMatrix]
          have hentry : ∀ j,
              (if e (σ j) = e j then B (σ j) j else 0) = B (σ j) j := by
            intro j
            rw [if_pos (hpres j).symm]
          simp_rw [hentry]
        · have hloc := (primePacket_powProduct_eq_iff q hq e σ).not.mpr hpres
          rw [if_neg (Ne.symm hloc)]
          simp only [smul_zero]
          have hzero : ∏ j, primePowerBlockMatrix e B (σ j) j = 0 := by
            rw [Finset.prod_eq_zero_iff]
            obtain ⟨j, hj⟩ := not_forall.mp hpres
            refine ⟨j, Finset.mem_univ j, ?_⟩
            simp [primePowerBlockMatrix, Ne.symm hj]
          rw [hzero, smul_zero]
      · intro i
        exact pow_ne_zero _ (q (σ i)).2.ne_zero

/-- A nonzero exponent-block scalar determinant forces a nonzero arithmetic-function Jacobian. -/
theorem primePowerPointMassMatrix_det_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → Nat.Primes) (hq : Function.Injective q)
    (e : I → ℕ) (B : Matrix I I ℂ)
    (hB : (primePowerBlockMatrix e B).det ≠ 0) :
    (primePowerPointMassMatrix q e B).det ≠ 0 := by
  intro hzero
  have happly : (primePowerPointMassMatrix q e B).det
      (∏ i, (q i : ℕ) ^ e i) = 0 := by
    simpa using congrArg
      (fun f : ArithmeticFunction ℂ => f (∏ i, (q i : ℕ) ^ e i)) hzero
  rw [primePowerPointMassMatrix_det_apply q hq e B] at happly
  exact hB happly

end

end GaloisForLFunctions.HTGeometry
