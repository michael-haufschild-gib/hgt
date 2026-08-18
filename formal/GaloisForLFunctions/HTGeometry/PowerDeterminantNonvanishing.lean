import GaloisForLFunctions.HTGeometry.PowerMatrixCramer
import GaloisForLFunctions.HTGeometry.SeparatingPowerIndependence
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Nonvanishing of the power determinant at a parameter

If `n` algebra maps of a finite free algebra to a field, all lying over the same map of the base,
separate an element `θ`, then the determinant of the coordinate matrix of the powers of `θ` does not
vanish under that map.  This is the last input to the chart data of `AlgebraSpectrumCovering`: at a
parameter whose fibre is split with `n` points, a separating `θ` exists
(`SplitAlgebraSeparation`) and the open set `U` on which `θ` generates contains that parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

/-- **Nonvanishing of the power determinant at a parameter.**  If `n` algebra maps of a finite free
`A`-algebra to a field `K`, all lying over the same map `φ : A →+* K`, separate `θ`, then the
determinant of the coordinate matrix of the powers of `θ` does not vanish under `φ`. -/
theorem det_powerMatrix_map_ne_zero {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Field K] {n : ℕ} (e : Module.Basis (Fin n) A B) (θ : B) (φ : A →+* K)
    (χ : Fin n → B →+* K) (hcomm : ∀ i, ∀ a : A, χ i (algebraMap A B a) = φ a)
    (hsep : Function.Injective fun i => χ i θ) :
    φ ((powerMatrix e θ).det) ≠ 0 := by
  classical
  intro hdet
  have hdet' : ((powerMatrix e θ).map φ).det = 0 := by
    rw [RingHom.map_det] at hdet
    exact hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet'
  have hVdm : (Matrix.vandermonde fun i => χ i θ).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hsep
  have hkey : (Matrix.vandermonde fun i => χ i θ).mulVec v = 0 := by
    funext k
    have hexp : ∀ j : Fin n, χ k (θ ^ (j : ℕ)) =
        ∑ i : Fin n, φ (e.repr (θ ^ (j : ℕ)) i) * χ k (e i) := by
      intro j
      conv_lhs => rw [← e.sum_repr (θ ^ (j : ℕ))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hcomm k]
    have hzero : ∀ i : Fin n, ∑ j : Fin n, φ (e.repr (θ ^ (j : ℕ)) i) * v j = 0 := by
      intro i
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, powerMatrix, Matrix.map_apply] using this
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    calc ∑ j : Fin n, (χ k θ) ^ (j : ℕ) * v j
        = ∑ j : Fin n, χ k (θ ^ (j : ℕ)) * v j := by
          exact Finset.sum_congr rfl fun j _ => by rw [map_pow]
      _ = ∑ i : Fin n, (∑ j : Fin n, φ (e.repr (θ ^ (j : ℕ)) i) * v j) * χ k (e i) := by
          simp only [hexp, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by simp [hzero]
  exact hv0 (Matrix.eq_zero_of_mulVec_eq_zero hVdm hkey)

end GaloisForLFunctions.HTGeometry
