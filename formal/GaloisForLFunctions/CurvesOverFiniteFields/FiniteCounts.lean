import GaloisForLFunctions.CurvesOverFiniteFields.PrincipalDivisors
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finiteness over a finite field of constants

Let `F` be finite with `q` elements.

* Frobenius: if `P` is a finite place of degree `d` and `d ∣ N`, then `a^{q^N} ≡ a mod P` on the
  finite chart (`pow_card_pow_sub_mem`), since `A/P` is a field with `q^d` elements.
* Every finite place of degree `≤ n` therefore contains `x^{q^{n!}} − x ≠ 0`, so there are
  finitely many (`finite_finPlace_deg_le`).
* An effective divisor of degree `n` has coefficients at most `n`, supported on places of degree
  at most `n`, so there are finitely many (`finite_effective`).
-/

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)] {K : Type*} [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
/-- In an effective divisor, a coefficient times the degree of its place is at most the degree. -/
theorem coeff_fin_mul_le_deg {D : Divisor F K} (hD : 0 ≤ D) (P : FinPlace F K) :
    D.1 P * finDeg F K P ≤ D.deg := by
  have h1 : ∀ Q, 0 ≤ D.1 Q := fun Q => Finsupp.le_def.mp (Prod.le_def.mp hD).1 Q
  have h2 : ∀ Q, 0 ≤ D.2 Q := fun Q => Finsupp.le_def.mp (Prod.le_def.mp hD).2 Q
  have hs1 : D.1 P * finDeg F K P ≤ D.1.sum fun P n => n * (finDeg F K P : ℤ) := by
    by_cases hP : D.1 P = 0
    · rw [hP, zero_mul]
      exact Finset.sum_nonneg fun Q _ => mul_nonneg (h1 Q) (Nat.cast_nonneg _)
    · exact Finset.single_le_sum (f := fun P => D.1 P * (finDeg F K P : ℤ))
        (fun Q _ => mul_nonneg (h1 Q) (Nat.cast_nonneg _)) (Finsupp.mem_support_iff.mpr hP)
  have hs2 : 0 ≤ D.2.sum fun Q n => n * (infDeg F K Q : ℤ) :=
    Finset.sum_nonneg fun Q _ => mul_nonneg (h2 Q) (Nat.cast_nonneg _)
  unfold Divisor.deg
  linarith

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
/-- In an effective divisor, a coefficient times the degree of its place is at most the degree. -/
theorem coeff_inf_mul_le_deg {D : Divisor F K} (hD : 0 ≤ D) (Q : InfPlace F K) :
    D.2 Q * infDeg F K Q ≤ D.deg := by
  have h1 : ∀ P, 0 ≤ D.1 P := fun P => Finsupp.le_def.mp (Prod.le_def.mp hD).1 P
  have h2 : ∀ P, 0 ≤ D.2 P := fun P => Finsupp.le_def.mp (Prod.le_def.mp hD).2 P
  have hs2 : D.2 Q * infDeg F K Q ≤ D.2.sum fun Q n => n * (infDeg F K Q : ℤ) := by
    by_cases hQ : D.2 Q = 0
    · rw [hQ, zero_mul]
      exact Finset.sum_nonneg fun P _ => mul_nonneg (h2 P) (Nat.cast_nonneg _)
    · exact Finset.single_le_sum (f := fun Q => D.2 Q * (infDeg F K Q : ℤ))
        (fun P _ => mul_nonneg (h2 P) (Nat.cast_nonneg _)) (Finsupp.mem_support_iff.mpr hQ)
  have hs1 : 0 ≤ D.1.sum fun P n => n * (finDeg F K P : ℤ) :=
    Finset.sum_nonneg fun P _ => mul_nonneg (h1 P) (Nat.cast_nonneg _)
  unfold Divisor.deg
  linarith

variable [Fintype F]

omit [DecidableEq (RatFunc F)] [IsScalarTower F (RatFunc F) K] in
/-- **Frobenius on a residue field**: on the finite chart, `a^{q^N} ≡ a mod P` whenever the degree
of `P` divides `N`. -/
theorem pow_card_pow_sub_mem (P : FinPlace F K) (a : finChart F K) {N : ℕ}
    (hN : finDeg F K P ∣ N) : a ^ (Fintype.card F ^ N) - a ∈ P.asIdeal := by
  classical
  haveI := P.isMaximal
  letI : Field (finChart F K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  haveI : Finite (finChart F K ⧸ P.asIdeal) := Module.finite_of_finite F
  letI : Fintype (finChart F K ⧸ P.asIdeal) := Fintype.ofFinite _
  obtain ⟨m, rfl⟩ := hN
  have hcard : Fintype.card (finChart F K ⧸ P.asIdeal) = Fintype.card F ^ finDeg F K P :=
    Module.card_eq_pow_finrank
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, pow_mul, ← hcard,
    FiniteField.pow_card_pow, sub_self]

omit [DecidableEq (RatFunc F)] [IsScalarTower F (RatFunc F) K] in
/-- There are finitely many finite places of degree at most `n`. -/
theorem finite_finPlace_deg_le (n : ℕ) : {P : FinPlace F K | finDeg F K P ≤ n}.Finite := by
  classical
  have hz : (algebraMap F[X] (finChart F K) X) ^ (Fintype.card F ^ n.factorial) -
      algebraMap F[X] (finChart F K) X ≠ 0 := by
    have h := FiniteField.X_pow_card_pow_sub_X_ne_zero F (Nat.factorial_ne_zero n)
      (Fintype.one_lt_card (α := F))
    intro h0
    apply h
    apply FunctionField.ringOfIntegers.algebraMap_injective F K
    rw [map_sub, map_pow, map_zero]
    exact h0
  refine (Ideal.finite_factors (I := Ideal.span {(algebraMap F[X] (finChart F K) X) ^
    (Fintype.card F ^ n.factorial) - algebraMap F[X] (finChart F K) X}) ?_).subset fun P hP => ?_
  · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · show P.asIdeal ∣ _
    rw [Ideal.dvd_span_singleton]
    exact pow_card_pow_sub_mem P _ (Nat.dvd_factorial (finrank_pos_quotient_place (F := F) P) hP)

/-- **Finitely many effective divisors of each degree.** -/
theorem finite_effective (n : ℤ) : {D : Divisor F K | 0 ≤ D ∧ D.deg = n}.Finite := by
  classical
  refine ((Set.finite_Icc (0 : FinPlace F K →₀ ℤ)
      (Finsupp.indicator (finite_finPlace_deg_le (F := F) (K := K) n.toNat).toFinset
        fun _ _ => n)).prod
    (Set.finite_Icc (0 : InfPlace F K →₀ ℤ) (Finsupp.equivFunOnFinite.symm fun _ => n))).subset ?_
  rintro D ⟨hD0, hDn⟩
  have hD1 := (Prod.le_def.mp hD0).1
  have hD2 := (Prod.le_def.mp hD0).2
  refine Set.mem_prod.mpr ⟨⟨hD1, Finsupp.le_def.mpr fun P => ?_⟩,
    ⟨hD2, Finsupp.le_def.mpr fun Q => ?_⟩⟩
  · have hle := coeff_fin_mul_le_deg hD0 P
    have hd : (1 : ℤ) ≤ finDeg F K P := by
      exact_mod_cast finrank_pos_quotient_place (F := F) P
    have h0 : 0 ≤ D.1 P := Finsupp.le_def.mp hD1 P
    have hmul := mul_le_mul_of_nonneg_left hd h0
    rw [Finsupp.indicator_apply]
    split_ifs with hP
    · linarith
    · by_contra hlt
      apply hP
      rw [Set.Finite.mem_toFinset]
      have h1 : (1 : ℤ) ≤ D.1 P := by omega
      have h2 : (finDeg F K P : ℤ) ≤ n := by nlinarith
      show finDeg F K P ≤ n.toNat
      omega
  · have hle := coeff_inf_mul_le_deg hD0 Q
    have hd : (1 : ℤ) ≤ infDeg F K Q := by
      exact_mod_cast finrank_pos_quotient_place (F := F) Q
    have h0 : 0 ≤ D.2 Q := Finsupp.le_def.mp hD2 Q
    have hmul := mul_le_mul_of_nonneg_left hd h0
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    linarith

end GaloisForLFunctions.CurvesOverFiniteFields
