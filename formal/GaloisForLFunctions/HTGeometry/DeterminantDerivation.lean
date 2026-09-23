import Mathlib

/-!
# Jacobi's formula for a derivation

The derivative of a determinant is the sum of the determinants obtained by differentiating one
column at a time.  For a matrix satisfying a linear system `δ M = M A` this collapses to
`δ (det M) = det M · tr A`, so a normalized Wronskian forces the system matrix to be traceless.
Neither statement is in mathlib.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [Differential R]

/-- **Leibniz rule for a finite product.** -/
theorem deriv_finsetProd_determinantDerivation {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, f i)′ = ∑ i ∈ s, (f i)′ * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hself : (insert a s).erase a = s := Finset.erase_insert ha
      have hother : ∀ i ∈ s, (f i)′ * ∏ j ∈ (insert a s).erase i, f j
          = f a * ((f i)′ * ∏ j ∈ s.erase i, f j) := by
        intro i hi
        have hia : a ≠ i := fun h => ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hia,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.prod_insert ha, Derivation.leibniz, Finset.sum_insert ha, hself,
        Finset.sum_congr rfl hother, ← Finset.mul_sum, ← ih]
      simp only [smul_eq_mul]
      ring

/-- **Jacobi's formula.**  The derivative of a determinant is the sum over columns of the
determinants obtained by differentiating that column. -/
theorem deriv_det_determinantDerivation {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    (M.det)′ = ∑ j, (M.updateCol j (fun r => (M r j)′)).det := by
  classical
  have hleft : (M.det)′
      = ∑ σ : Equiv.Perm (Fin N), ∑ j : Fin N,
          (Equiv.Perm.sign σ : ℤ) • ((M (σ j) j)′ * ∏ i ∈ Finset.univ.erase j, M (σ i) i) := by
    rw [Matrix.det_apply, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, deriv_finsetProd_determinantDerivation, Finset.smul_sum]
  have hright : ∀ j : Fin N, (M.updateCol j (fun r => (M r j)′)).det
      = ∑ σ : Equiv.Perm (Fin N),
          (Equiv.Perm.sign σ : ℤ) • ((M (σ j) j)′ * ∏ i ∈ Finset.univ.erase j, M (σ i) i) := by
    intro j
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [hij]
  rw [hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (hright j).symm

/-- **The logarithmic derivative of a Wronskian is the trace of the system matrix.** -/
theorem deriv_det_of_system {N : ℕ} (M A : Matrix (Fin N) (Fin N) R)
    (h : ∀ i j, (M i j)′ = (M * A) i j) :
    (M.det)′ = M.det * A.trace := by
  classical
  rw [deriv_det_determinantDerivation]
  have hcol : ∀ j : Fin N, (M.updateCol j (fun r => (M r j)′)).det = A j j * M.det := by
    intro j
    have hfun : (fun r => (M r j)′) = fun r => ∑ i, (A i j) • M r i := by
      funext r
      rw [h r j]
      simp only [Matrix.mul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hfun, Matrix.det_updateCol_sum, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => hcol j, ← Finset.sum_mul, Matrix.trace]
  simp [Matrix.diag, mul_comm]

/-- **A normalized Wronskian forces a traceless system matrix.** -/
theorem trace_eq_zero_of_det_eq_one {N : ℕ} (M A : Matrix (Fin N) (Fin N) R)
    (h : ∀ i j, (M i j)′ = (M * A) i j) (hdet : M.det = 1) : A.trace = 0 := by
  have := deriv_det_of_system M A h
  rw [hdet, one_mul, Derivation.map_one_eq_zero] at this
  exact this.symm

end GaloisForLFunctions.HTGeometry
