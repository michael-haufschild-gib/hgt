import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

/-!
# A simple branch point forces Kummer irreducibility

The simple zero at the origin of `c X (1-X^b)^R` makes every positive-degree
radical polynomial Eisenstein at `X`. This works over every coefficient
field, including arbitrary field extensions, and over its rational function field.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial

variable {K : Type*} [Field K]

/-- A polynomial with a simple zero at the origin gives an Eisenstein radical. -/
theorem simpleZero_isEisenstein {f : K[X]} (hzero : f.coeff 0 = 0)
    (hsimple : f.coeff 1 ≠ 0) (n : ℕ) :
    (X ^ (n + 1) - C f : K[X][X]).IsEisensteinAt (Ideal.span {(X : K[X])}) where
  leading := by
    rw [(monic_X_pow_sub_C f (Nat.succ_ne_zero n)).leadingCoeff]
    intro h
    have hd := Ideal.mem_span_singleton.mp h
    have he := X_dvd_iff.mp hd
    simp at he
  mem := by
    intro j hj
    rw [natDegree_X_pow_sub_C] at hj
    rw [coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C]
    by_cases hj0 : j = 0
    · rw [if_pos hj0, zero_sub]
      exact Ideal.mem_span_singleton.mpr (dvd_neg.mpr (X_dvd_iff.mpr hzero))
    · rw [if_neg hj0, sub_zero]
      exact Ideal.zero_mem _
  notMem := by
    rw [coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C, if_pos rfl, zero_sub]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨g, hg⟩
    have he := congrArg (fun P : K[X] => P.coeff 1) hg
    simp only [coeff_neg, coeff_X_pow_mul', show ¬ (2 : ℕ) ≤ 1 by omega, if_false] at he
    exact hsimple (neg_eq_zero.mp he)

/-- Eisenstein at the simple branch point proves irreducibility in two variables. -/
theorem simpleZero_radical_irreducible {f : K[X]} (hzero : f.coeff 0 = 0)
    (hsimple : f.coeff 1 ≠ 0) (n : ℕ) :
    Irreducible (X ^ (n + 1) - C f : K[X][X]) := by
  exact (simpleZero_isEisenstein hzero hsimple n).irreducible
    ((Ideal.span_singleton_prime (X_ne_zero : (X : K[X]) ≠ 0)).mpr prime_X)
    (monic_X_pow_sub_C f (Nat.succ_ne_zero n)).isPrimitive
    (by rw [natDegree_X_pow_sub_C]; omega)

/-- The Kummer branch polynomial with a nonzero scalar and positive branch exponent. -/
def kummerBranch (c : Kˣ) (b R : ℕ) : K[X] :=
  C (c : K) * X * (1 - X ^ (b + 1)) ^ R

@[simp] theorem kummerBranch_coeff_zero (c : Kˣ) (b R : ℕ) :
    (kummerBranch c b R).coeff 0 = 0 := by
  simp [kummerBranch, coeff_zero_eq_eval_zero]

/-- The coefficient of `X` is exactly the chosen nonzero scalar. -/
theorem kummerBranch_coeff_one (c : Kˣ) (b R : ℕ) :
    (kummerBranch c b R).coeff 1 = (c : K) := by
  rw [kummerBranch, mul_assoc, coeff_C_mul, coeff_X_mul]
  simp [coeff_zero_eq_eval_zero]

/-- Every positive-degree Kummer equation in this family is irreducible,
uniformly over all coefficient fields. -/
theorem kummerBranch_irreducible (c : Kˣ) (b R n : ℕ) :
    Irreducible (X ^ (n + 1) - C (kummerBranch c b R) : K[X][X]) := by
  apply simpleZero_radical_irreducible (kummerBranch_coeff_zero c b R)
  rw [kummerBranch_coeff_one]
  exact Units.ne_zero c

/-- Irreducibility persists over the rational function field. -/
theorem kummerBranch_fraction_irreducible (c : Kˣ) (b R n : ℕ) :
    Irreducible (X ^ (n + 1) -
      C (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)) :
        (FractionRing K[X])[X]) := by
  have hm := monic_X_pow_sub_C (kummerBranch c b R) (Nat.succ_ne_zero n)
  have hi := (hm.isPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing K[X])).mp (kummerBranch_irreducible c b R n)
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C] using hi

/-- The radical polynomial over the rational function field. -/
def kummerBranchFieldPolynomial (c : Kˣ) (b R n : ℕ) : (FractionRing K[X])[X] :=
  X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))

instance kummerBranchFieldPolynomial_irreducible (c : Kˣ) (b R n : ℕ) :
    Fact (Irreducible (kummerBranchFieldPolynomial c b R n)) :=
  ⟨kummerBranch_fraction_irreducible c b R n⟩

/-- The function field obtained by adjoining the Kummer radical. Its field
structure is supplied by the proved Eisenstein irreducibility. -/
abbrev KummerBranchField (c : Kˣ) (b R n : ℕ) :=
  AdjoinRoot (kummerBranchFieldPolynomial c b R n)

/-- The radical has precisely the degree specified by its equation. -/
theorem kummerBranchField_finrank (c : Kˣ) (b R n : ℕ) :
    Module.finrank (FractionRing K[X]) (KummerBranchField c b R n) = n + 1 := by
  have hi := (kummerBranchFieldPolynomial_irreducible c b R n).out
  calc
    _ = (AdjoinRoot.powerBasis hi.ne_zero).dim := (AdjoinRoot.powerBasis hi.ne_zero).finrank
    _ = n + 1 := by
      rw [AdjoinRoot.powerBasis_dim, kummerBranchFieldPolynomial, natDegree_X_pow_sub_C]

/-- The canonical generator satisfies the branch equation in the constructed field. -/
theorem kummerBranchField_root_pow (c : Kˣ) (b R n : ℕ) :
    (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) ^ (n + 1) =
      algebraMap (FractionRing K[X]) (KummerBranchField c b R n)
        (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R)) := by
  have h := AdjoinRoot.eval₂_root (kummerBranchFieldPolynomial c b R n)
  change (X ^ (n + 1) - C (algebraMap K[X] (FractionRing K[X]) (kummerBranch c b R))).eval₂
    (AdjoinRoot.of (kummerBranchFieldPolynomial c b R n))
    (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
