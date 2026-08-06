import GaloisForLFunctions.HTGeometry.InverseJetNumeratorMap
import GaloisForLFunctions.HTGeometry.OneDeepFibreBound
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The fibre's system as a universal polynomial system

The square system of an observation is written over a polynomial ring in the unknown jet
coefficients: the completed jet becomes a tuple of variables shifted by the observed tail, the
inverse numerators are formed over that ring, and the observed reciprocal tail supplies the
constants.  Specialising at a point of affine space recovers the system over the ground field.

This is what makes the count an ordinary question about the common zeros of finitely many
polynomials in finitely many variables.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The `i`-th coefficient of the completed jet, as a polynomial in the unknown coefficients. -/
noncomputable def jetVar (U : K[X]) (m : ℕ) (i : ℕ) : MvPolynomial (Fin m) K :=
  if h : i < m then MvPolynomial.X ⟨i, h⟩ + MvPolynomial.C (U.coeff i)
  else MvPolynomial.C (U.coeff i)

/-- **Specialising a jet variable at a candidate jet.** -/
theorem eval_jetVar {U A : K[X]} {m : ℕ} (hA : A.degree < (m : ℕ)) (i : ℕ) :
    MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (jetVar U m i) = (A + U).coeff i := by
  rw [jetVar]
  split_ifs with h
  · simp
  · have hzero : A.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hA (by exact_mod_cast (by omega : m ≤ i)))
    simp [hzero]

/-- The `k`-th equation of the observation's system, as a polynomial in the unknown jet
coefficients. -/
noncomputable def fibreSysPoly (U V : K[X]) (m k : ℕ) : MvPolynomial (Fin m) K :=
  jetVar U m 0 ^ (k + 1) * MvPolynomial.C (V.coeff k)
    - (invNumerator (jetVar U m) k).eval (jetVar U m 0)

/-- **Specialising the system at a candidate jet.** -/
theorem eval_fibreSysPoly {U V A : K[X]} {m : ℕ} (hA : A.degree < (m : ℕ)) (k : ℕ) :
    MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (fibreSysPoly U V m k)
      = (A + U).coeff 0 ^ (k + 1) * V.coeff k
        - (invNumerator (fun i => (A + U).coeff i) k).eval ((A + U).coeff 0) := by
  have hfun : (fun i => MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (jetVar U m i))
      = fun i => (A + U).coeff i := funext fun i => eval_jetVar hA i
  have hpt : MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (jetVar U m 0)
      = (A + U).coeff 0 := eval_jetVar hA 0
  rw [fibreSysPoly, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
    eval_invNumerator_map (MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)))
      (jetVar U m) k (jetVar U m 0), hfun, hpt]


/-! ## The solutions are the common zeros -/

section ZeroLocus

variable {K : Type*} [Field K] {m n : ℕ}

/-- **An equation of the system vanishes exactly when the observation's equation holds.** -/
theorem eval_fibreSysPoly_eq_zero_iff {U V A : K[X]} (hA : A.degree < (m : ℕ)) (k : ℕ) :
    MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (fibreSysPoly U V m k) = 0
      ↔ (A + U).coeff 0 ^ (k + 1) * V.coeff k
        = (invNumerator (fun i => (A + U).coeff i) k).eval ((A + U).coeff 0) := by
  rw [eval_fibreSysPoly hA, sub_eq_zero]

/-- **The solutions of an observation's system are the common zeros of finitely many polynomials,
away from the vanishing of the jet's constant term.** -/
theorem mem_criticalSystemSolutions_iff {U V A : K[X]} (hA : A.degree < (m : ℕ)) :
    ((A + U).coeff 0 ≠ 0 ∧ ∀ k : ℕ, n ≤ k → k < m + n →
        (A + U).coeff 0 ^ (k + 1) * V.coeff k
          = (invNumerator (fun i => (A + U).coeff i) k).eval ((A + U).coeff 0))
      ↔ (MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (jetVar U m 0) ≠ 0 ∧
        ∀ k : ℕ, n ≤ k → k < m + n →
          MvPolynomial.eval (fun j : Fin m => A.coeff (j : ℕ)) (fibreSysPoly U V m k) = 0) := by
  constructor
  · rintro ⟨ha, hsys⟩
    refine ⟨?_, fun k hk1 hk2 => (eval_fibreSysPoly_eq_zero_iff hA k).2 (hsys k hk1 hk2)⟩
    rwa [eval_jetVar hA]
  · rintro ⟨ha, hsys⟩
    refine ⟨?_, fun k hk1 hk2 => (eval_fibreSysPoly_eq_zero_iff hA k).1 (hsys k hk1 hk2)⟩
    rwa [eval_jetVar hA] at ha

end ZeroLocus


/-! ## Degrees in the universal system -/

section Degrees

variable {K : Type*} [Field K] {m : ℕ}

theorem totalDegree_jetVar_le (U : K[X]) (m i : ℕ) : (jetVar U m i).totalDegree ≤ 1 := by
  rw [jetVar]
  split_ifs with h
  · refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  · simp [MvPolynomial.totalDegree_C]

/-- **The evaluated numerator has total degree at most its index.**  Each term of the recursion
carries one tail coefficient, a power of the jet's constant term, and a numerator of smaller
index. -/
theorem totalDegree_eval_invNumerator_jetVar_le (U : K[X]) (m : ℕ) :
    ∀ k : ℕ, ((invNumerator (jetVar U m) k).eval (jetVar U m 0)).totalDegree ≤ k
  | 0 => by
      rw [invNumerator_zero, Polynomial.eval_one]
      simp
  | (k + 1) => by
      rw [invNumerator_succ, Polynomial.eval_neg, Polynomial.eval_finsetSum]
      refine le_trans (le_of_eq (MvPolynomial.totalDegree_neg _)) ?_
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
      refine Finset.sup_le fun i hi => ?_
      have hik : k - i ≤ k := Nat.sub_le _ _
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : ((jetVar U m (i + 1)) * (jetVar U m 0) ^ i).totalDegree ≤ 1 + i := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have h2 : ((jetVar U m 0) ^ i).totalDegree ≤ i := by
          refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
          calc i * (jetVar U m 0).totalDegree ≤ i * 1 :=
                Nat.mul_le_mul_left i (totalDegree_jetVar_le U m 0)
            _ = i := mul_one i
        exact Nat.add_le_add (totalDegree_jetVar_le U m (i + 1)) h2
      have h3 := totalDegree_eval_invNumerator_jetVar_le U m (k - i)
      have hile : i ≤ k := by
        have := Finset.mem_range.1 hi
        omega
      calc ((jetVar U m (i + 1)) * (jetVar U m 0) ^ i).totalDegree
            + ((invNumerator (jetVar U m) (k - i)).eval (jetVar U m 0)).totalDegree
          ≤ (1 + i) + (k - i) := Nat.add_le_add h1 h3
        _ ≤ k + 1 := by omega

/-- **The equations of the universal system have total degree at most one more than their
index.** -/
theorem totalDegree_fibreSysPoly_le (U V : K[X]) (m k : ℕ) :
    (fibreSysPoly U V m k).totalDegree ≤ k + 1 := by
  rw [fibreSysPoly, sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h2 : ((jetVar U m 0) ^ (k + 1)).totalDegree ≤ k + 1 := by
      refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
      calc (k + 1) * (jetVar U m 0).totalDegree ≤ (k + 1) * 1 :=
            Nat.mul_le_mul_left _ (totalDegree_jetVar_le U m 0)
        _ = k + 1 := mul_one _
    simpa [MvPolynomial.totalDegree_C] using h2
  · refine le_trans (le_of_eq (MvPolynomial.totalDegree_neg _)) ?_
    exact le_trans (totalDegree_eval_invNumerator_jetVar_le U m k) (Nat.le_succ k)

end Degrees

end GaloisForLFunctions.HTGeometry
