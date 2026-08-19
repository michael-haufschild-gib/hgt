import GaloisForLFunctions.HTGeometry.SiegelSwapMinors

/-!
# Comparison of projected norms

If one form dominates a multiple of another, so do their projected norms, and hence their Jacobi
diagonals and the determinants of their leading minors.

The proof is a two-sided use of the intrinsic characterisation: the optimal competitor for the
larger form is *a* competitor for the smaller one.

This is what turns a uniform ellipticity bound `A[v] ≥ λ‖v‖²` into a lower bound for every leading
minor of `A` in terms of the corresponding minor of the standard Gram matrix.

* `projNorm_mono` : **comparison of projected norms.**
* `d_mono` : comparison of the Jacobi diagonals.
* `det_leadingBlock_mono` : **comparison of the leading minors.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **Comparison of projected norms.** -/
theorem projNorm_mono {J K : JacobiData n} {lam : ℝ} (hlam : 0 ≤ lam)
    (hdom : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    (i : Fin n) (v : Fin n → ℝ) :
    lam * K.projNorm i v ≤ J.projNorm i v := by
  obtain ⟨w, hw, hwval⟩ := J.projNorm_eq_form_sub i v
  calc lam * K.projNorm i v
      ≤ lam * ((v - w) ⬝ᵥ (K.form *ᵥ (v - w))) :=
        mul_le_mul_of_nonneg_left (K.projNorm_le_form_sub i v hw) hlam
    _ ≤ (v - w) ⬝ᵥ (J.form *ᵥ (v - w)) := hdom (v - w)
    _ = J.projNorm i v := hwval.symm

/-- Comparison of the Jacobi diagonals. -/
theorem d_mono {J K : JacobiData n} {lam : ℝ} (hlam : 0 ≤ lam)
    (hdom : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    (i : Fin n) : lam * K.d i ≤ J.d i := by
  have := projNorm_mono hlam hdom i (Pi.single i (1 : ℝ))
  rwa [J.projNorm_self i, K.projNorm_self i] at this

/-- **Comparison of the leading minors.** -/
theorem det_leadingBlock_mono {J K : JacobiData n} {lam : ℝ} (hlam : 0 ≤ lam)
    (hdom : ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    {k : ℕ} (hk : k ≤ n) :
    lam ^ k * (leadingBlock hk K.form).det ≤ (leadingBlock hk J.form).det := by
  classical
  rw [det_leadingBlock_form hk J, det_leadingBlock_form hk K]
  have hstep : ∀ m : Fin k, lam * K.d (Fin.castLE hk m) ≤ J.d (Fin.castLE hk m) :=
    fun m => d_mono hlam hdom _
  have hprod : (∏ m : Fin k, (lam * K.d (Fin.castLE hk m)))
      ≤ ∏ m : Fin k, J.d (Fin.castLE hk m) := by
    refine Finset.prod_le_prod (fun m _ => ?_) (fun m _ => hstep m)
    exact mul_nonneg hlam (K.pos _).le
  calc lam ^ k * ∏ m : Fin k, K.d (Fin.castLE hk m)
      = ∏ m : Fin k, (lam * K.d (Fin.castLE hk m)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ m : Fin k, J.d (Fin.castLE hk m) := hprod

end GaloisForLFunctions.HTGeometry
