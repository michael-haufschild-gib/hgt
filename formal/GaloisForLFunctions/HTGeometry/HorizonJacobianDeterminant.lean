import GaloisForLFunctions.HTGeometry.HorizonConormalJacobianKernel
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# Determinant and kernel of the horizon observation Jacobian

The horizon observation Jacobian is block triangular with an identity block, so its determinant is
the determinant of the transposed reciprocal Jacobian — the caustic determinant.  A nonzero low
tangent has a nonzero conormal vector, so a collision forces that determinant to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial Matrix

set_option maxHeartbeats 4000000

variable {F : Type*} [CommRing F]

/-- The critical reciprocal Jacobian is functorial in the coefficient ring. -/
theorem criticalReciprocalJacobian_map {G : Type*} [CommRing G] (f : F →+* G)
    (Y : F[X]) (n m : ℕ) :
    (criticalReciprocalJacobian Y n m).map f = criticalReciprocalJacobian (Y.map f) n m := by
  classical
  refine Matrix.ext fun r i => ?_
  rw [Matrix.map_apply, criticalReciprocalJacobian_apply, criticalReciprocalJacobian_apply,
    rectangularSchurToeplitz, rectangularSchurToeplitz]
  by_cases hle : (i : ℕ) ≤ n + (r : ℕ)
  · rw [if_pos hle, if_pos hle, map_neg, ← Polynomial.map_mul, Polynomial.coeff_map]
  · rw [if_neg hle, if_neg hle, map_neg, map_zero]

theorem horizonObservationJacobian_apply_inl (Y : F[X]) (n m : ℕ)
    (t : Fin m ⊕ Fin n) (s' : Fin m) :
    horizonObservationJacobian Y n m t (Sum.inl s')
      = if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s' : ℕ) then
          -((Y * Y).coeff (n + (s' : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ))) else 0 := rfl

theorem horizonObservationJacobian_apply_inr (Y : F[X]) (n m : ℕ)
    (t : Fin m ⊕ Fin n) (s' : Fin n) :
    horizonObservationJacobian Y n m t (Sum.inr s') = if t = Sum.inr s' then 1 else 0 := rfl

/-- The horizon observation Jacobian in block form. -/
theorem horizonObservationJacobian_eq_fromBlocks (Y : F[X]) (n m : ℕ) :
    horizonObservationJacobian Y n m
      = Matrix.fromBlocks (criticalReciprocalJacobian Y n m).transpose 0
          (Matrix.of fun (r : Fin n) (s : Fin m) =>
            horizonObservationJacobian Y n m (Sum.inr r) (Sum.inl s))
          1 := by
  classical
  refine Matrix.ext fun t s => ?_
  rcases t with t' | t' <;> rcases s with s' | s'
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply, criticalReciprocalJacobian_apply,
      rectangularSchurToeplitz, horizonObservationJacobian_apply_inl,
      show ((finSumFinEquiv (Sum.inl t' : Fin m ⊕ Fin n) : Fin (m + n)) : ℕ) = (t' : ℕ) by simp]
    by_cases hle : (t' : ℕ) ≤ n + (s' : ℕ)
    · rw [if_pos hle, if_pos hle]
    · rw [if_neg hle, if_neg hle, neg_zero]
  · rw [Matrix.fromBlocks_apply₁₂, horizonObservationJacobian_apply_inr,
      if_neg (by simp), Matrix.zero_apply]
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
  · rw [Matrix.fromBlocks_apply₂₂, horizonObservationJacobian_apply_inr, Matrix.one_apply]
    by_cases h : t' = s'
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]

/-- **The horizon observation Jacobian has the reciprocal Jacobian determinant.** -/
theorem det_horizonObservationJacobian (Y : F[X]) (n m : ℕ) :
    (horizonObservationJacobian Y n m).det = (criticalReciprocalJacobian Y n m).det := by
  classical
  rw [horizonObservationJacobian_eq_fromBlocks, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one, Matrix.det_transpose]

/-- A nonzero low tangent has a nonzero conormal vector. -/
theorem horizonConormalVector_ne_zero {E : Type*} [Field E] {m n : ℕ} {U V : E[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ)) (hne : U ≠ 0 ∨ V ≠ 0) :
    horizonConormalVector U V m n ≠ 0 := by
  intro hzero
  rcases hne with hne | hne
  · obtain ⟨i, hi⟩ : ∃ i, U.coeff i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Polynomial.ext fun i => by simpa using hcon i)
    have him : i < m := by
      by_contra hcon
      exact hi (Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hU (by exact_mod_cast (by omega : m ≤ i))))
    have := congrFun hzero (Sum.inl (⟨m - 1 - i, by omega⟩ : Fin m))
    rw [horizonConormalVector] at this
    simp only [Pi.zero_apply] at this
    rw [show m - 1 - (m - 1 - i) = i by omega] at this
    exact hi this
  · obtain ⟨i, hi⟩ : ∃ i, V.coeff i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Polynomial.ext fun i => by simpa using hcon i)
    have him : i < n := by
      by_contra hcon
      exact hi (Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hV (by exact_mod_cast (by omega : n ≤ i))))
    have := congrFun hzero (Sum.inr (⟨n - 1 - i, by omega⟩ : Fin n))
    rw [horizonConormalVector] at this
    simp only [Pi.zero_apply] at this
    rw [show n - 1 - (n - 1 - i) = i by omega] at this
    exact hi (neg_eq_zero.mp this)

end

end GaloisForLFunctions.HTGeometry
