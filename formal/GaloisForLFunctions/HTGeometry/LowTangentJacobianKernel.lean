import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Low tangents are kernel vectors of the critical Jacobian

For an inverse pair `A Y ≡ 1` to the horizon, multiplying the tangent relation
`X^(m+n) ∣ U Y + A V` by `Y` and substituting the inverse identity gives

```text
V ≡ - Y² U      (mod X^(m+n)) ,
```

so the reciprocal component of a low tangent is determined by its raw component.  Since `V` has
degree below `n`, the coefficients of `-Y² U` in degrees `n, …, n+m-1` all vanish — and those are
exactly the rows of `criticalReciprocalJacobian Y n m`.  Hence the coefficient vector of `U` is a
kernel vector of that matrix, and conversely corank one makes the raw component unique up to
scale:

```text
dvd_reciprocal_of_low_tangent               V ≡ -Y² U
jacobian_mulVec_eq_zero_of_low_tangent      ** a low tangent is a kernel vector **
coeff_vec_ne_zero
low_tangent_unique_of_finrank_ker_eq_one
    ** corank one  ⟹  any two low tangents have proportional raw components **
```

The last statement is exactly the uniqueness hypothesis that
`CriticalSchurTangentConstantTerm.isCoprime_of_low_tangent_unique` consumes, so this closes the gap
between generic corank one and coprimality of the tangent pair.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

variable {F : Type*} [Field F]

/-- **A low tangent determines its reciprocal component.** -/
theorem dvd_reciprocal_of_low_tangent {m n : ℕ} {A Y U V : F[X]}
    (hInv : (X : F[X]) ^ (m + n) ∣ A * Y - 1)
    (htan : (X : F[X]) ^ (m + n) ∣ U * Y + A * V) :
    (X : F[X]) ^ (m + n) ∣ V + Y * Y * U := by
  obtain ⟨q, hq⟩ := hInv
  obtain ⟨s, hs⟩ := htan
  refine ⟨Y * s - q * V, ?_⟩
  have hAY : A * Y = 1 + X ^ (m + n) * q := by
    rw [← hq]; ring
  have hmul : Y * (U * Y + A * V) = Y * (X ^ (m + n) * s) := by rw [hs]
  have hexp : Y * (U * Y + A * V) = Y * Y * U + (A * Y) * V := by ring
  rw [hexp, hAY] at hmul
  linear_combination hmul

/-- **A low tangent is a kernel vector of the critical Jacobian.** -/
theorem jacobian_mulVec_eq_zero_of_low_tangent {m n : ℕ} {A Y U V : F[X]}
    (hInv : (X : F[X]) ^ (m + n) ∣ A * Y - 1)
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (htan : (X : F[X]) ^ (m + n) ∣ U * Y + A * V) :
    (criticalReciprocalJacobian Y n m).mulVec (fun i : Fin m => U.coeff i) = 0 := by
  classical
  obtain ⟨s, hs⟩ := dvd_reciprocal_of_low_tangent hInv htan
  funext r
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) r.isLt
  have hUdeg : U.natDegree < m := by
    rcases eq_or_ne U 0 with rfl | hU0
    · simpa using hmpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hU0).mpr hU
  have hsum : U = ∑ i ∈ Finset.range m, C (U.coeff i) * X ^ i :=
    Polynomial.as_sum_range_C_mul_X_pow' U hUdeg
  have hzero : (Y * Y * U).coeff (n + r) = 0 := by
    have hval : Y * Y * U = X ^ (m + n) * s - V := by linear_combination hs
    rw [hval, Polynomial.coeff_sub]
    have h1 : V.coeff (n + r) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hV (by exact_mod_cast Nat.le_add_right n (r : ℕ)))
    have h2 : ((X : F[X]) ^ (m + n) * s).coeff (n + r) = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      simp only [ite_eq_right_iff]
      intro hle
      omega
    rw [h1, h2, sub_zero]
  have hexpand : (Y * Y * U).coeff (n + r)
      = ∑ i ∈ Finset.range m, (Y * Y * X ^ i).coeff (n + r) * U.coeff i := by
    conv_lhs => rw [hsum]
    rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Y * Y * (C (U.coeff i) * X ^ i) = C (U.coeff i) * (Y * Y * X ^ i) by ring,
      Polynomial.coeff_C_mul, mul_comm]
  have hJ : ∀ i : Fin m, criticalReciprocalJacobian Y n m r i
      = -((Y * Y * X ^ (i : ℕ)).coeff (n + r)) := by
    intro i
    simp [criticalReciprocalJacobian, criticalReciprocalInfinitesimal]
  have hfin : ∑ i : Fin m, (Y * Y * X ^ (i : ℕ)).coeff (n + r) * U.coeff i
      = (Y * Y * U).coeff (n + r) := by
    rw [hexpand]
    exact Fin.sum_univ_eq_sum_range (fun i => (Y * Y * X ^ i).coeff (n + r) * U.coeff i) m
  have hmain : ∑ i : Fin m, criticalReciprocalJacobian Y n m r i * U.coeff i = 0 := by
    have hrw : ∀ i : Fin m, criticalReciprocalJacobian Y n m r i * U.coeff i
        = -((Y * Y * X ^ (i : ℕ)).coeff (n + r) * U.coeff i) := by
      intro i
      rw [hJ i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hrw i), Finset.sum_neg_distrib, hfin, hzero, neg_zero]
  simpa [Matrix.mulVec, dotProduct] using hmain

/-- The coefficient vector of a nonzero low polynomial is nonzero. -/
theorem coeff_vec_ne_zero {m : ℕ} {U : F[X]} (hU : U ≠ 0) (hdeg : U.degree < (m : ℕ)) :
    (fun i : Fin m => U.coeff i) ≠ 0 := by
  intro hzero
  refine hU (Polynomial.ext fun i => ?_)
  rcases lt_or_ge i m with hi | hi
  · have := congrFun hzero ⟨i, hi⟩
    simpa using this
  · have : U.degree < (i : ℕ) := lt_of_lt_of_le hdeg (by exact_mod_cast hi)
    simpa using Polynomial.coeff_eq_zero_of_degree_lt this

/-- **Corank one makes the low tangent unique up to scale.**  Two low tangent pairs for the same
inverse pair have proportional raw components as soon as the critical Jacobian has a
one-dimensional kernel. -/
theorem low_tangent_unique_of_finrank_ker_eq_one {m n : ℕ} {A Y U V U' V' : F[X]}
    (hInv : (X : F[X]) ^ (m + n) ∣ A * Y - 1)
    (hker : Module.finrank F (LinearMap.ker (criticalReciprocalJacobian Y n m).mulVecLin) = 1)
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (htan : (X : F[X]) ^ (m + n) ∣ U * Y + A * V) (hUne : U ≠ 0)
    (hU' : U'.degree < (m : ℕ)) (hV' : V'.degree < (n : ℕ))
    (htan' : (X : F[X]) ^ (m + n) ∣ U' * Y + A * V') :
    ∃ c : F, U' = C c * U := by
  classical
  set J := criticalReciprocalJacobian Y n m with hJdef
  have hmem : (fun i : Fin m => U.coeff i) ∈ LinearMap.ker J.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using
      jacobian_mulVec_eq_zero_of_low_tangent hInv hU hV htan
  have hmem' : (fun i : Fin m => U'.coeff i) ∈ LinearMap.ker J.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using
      jacobian_mulVec_eq_zero_of_low_tangent hInv hU' hV' htan'
  have hne : (⟨fun i : Fin m => U.coeff i, hmem⟩ :
      LinearMap.ker J.mulVecLin) ≠ 0 := by
    intro h
    exact coeff_vec_ne_zero hUne hU (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hker
    (⟨fun i : Fin m => U'.coeff i, hmem'⟩ : LinearMap.ker J.mulVecLin)
  refine ⟨c, Polynomial.ext fun i => ?_⟩
  rcases lt_or_ge i m with hi | hi
  · have hcv := congrArg Subtype.val hc
    have := congrFun hcv ⟨i, hi⟩
    simpa [Polynomial.coeff_C_mul] using this.symm
  · have h1 : U'.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hU' (by exact_mod_cast hi))
    have h2 : U.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hU (by exact_mod_cast hi))
    rw [h1, Polynomial.coeff_C_mul, h2, mul_zero]

end GaloisForLFunctions.HTGeometry
