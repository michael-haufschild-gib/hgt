import GaloisForLFunctions.HTGeometry.PaperDiagonalCluster

/-! # Complete quotient norms for recurrent diagonal models

If every multiplier value recurs along escaping coordinates, the whole operator
norm survives every compact correction. Pointwise-null diagonal errors preserve
this model in the compact quotient.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

def PaperDiagonalRecurrent (v : ℕ → ℂ) : Prop :=
  ∀ n, ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, v (j k) = v n

theorem paperBoundedDiagonal_norm_le_of_bound (v : ℕ → ℂ) {C M : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hM : 0 ≤ M) (hbound : ∀ n, ‖v n‖ ≤ M) :
    ‖lpDiagonalCLM v hC hv‖ ≤ M := by
  have heq : lpDiagonalCLM v hC hv = lpDiagonalCLM v hM hbound := by
    ext f n
    rfl
  rw [heq]
  exact norm_lpDiagonalCLM_le _ _ _

theorem paperBoundedDiagonal_norm_sub_le (v w : ℕ → ℂ) {C D M : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hD : 0 ≤ D) (hw : ∀ n, ‖w n‖ ≤ D)
    (hM : 0 ≤ M) (hbound : ∀ n, ‖v n - w n‖ ≤ M) :
    ‖lpDiagonalCLM v hC hv - lpDiagonalCLM w hD hw‖ ≤ M := by
  have heq : lpDiagonalCLM v hC hv - lpDiagonalCLM w hD hw =
      lpDiagonalCLM (fun n => v n - w n) hM hbound := by
    ext f n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, lpDiagonalCLM_apply, sub_mul]
  rw [heq]
  exact norm_lpDiagonalCLM_le _ _ _

theorem paperBoundedDiagonal_sub_compact (v w : ℕ → ℂ) {C D : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hD : 0 ≤ D) (hw : ∀ n, ‖w n‖ ≤ D)
    (hlim : Tendsto (fun n => ‖v n - w n‖) atTop (𝓝 0)) :
    IsCompactOperator (lpDiagonalCLM v hC hv - lpDiagonalCLM w hD hw) := by
  have hb : ∀ n, ‖v n - w n‖ ≤ C + D := fun n =>
    (norm_sub_le _ _).trans (add_le_add (hv n) (hw n))
  have heq : lpDiagonalCLM v hC hv - lpDiagonalCLM w hD hw =
      lpDiagonalCLM (fun n => v n - w n) (add_nonneg hC hD) hb := by
    ext f n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, lpDiagonalCLM_apply, sub_mul]
  rw [heq]
  exact isCompactOperator_lpDiagonalCLM _ _ _ hlim

theorem paperBoundedDiagonal_unitary (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hunit : ∀ n, ‖v n‖ = 1) :
    lpDiagonalCLM v hC hv ∈ unitary (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
  have hc : ∀ n, ‖(starRingEnd ℂ) (v n)‖ ≤ C := by
    intro n
    simpa only [Complex.norm_conj] using hv n
  let B := lpDiagonalCLM (fun n => (starRingEnd ℂ) (v n)) hC hc
  have hadj : lpDiagonalCLM v hC hv = B.adjoint :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).2 (lpDiagonalCLM_inner v hC hv hC hc)
  have hstar : star (lpDiagonalCLM v hC hv) = B := by
    have h := congrArg star hadj
    simpa only [← ContinuousLinearMap.star_eq_adjoint, star_star] using h
  rw [Unitary.mem_iff, hstar]
  constructor
  · ext f n
    change (starRingEnd ℂ) (v n) * (v n * f n) = f n
    rw [← mul_assoc, Complex.conj_mul']
    simp [hunit n]
  · ext f n
    change v n * ((starRingEnd ℂ) (v n) * f n) = f n
    rw [mul_left_comm, ← mul_assoc, Complex.conj_mul']
    simp [hunit n]

/-- Every recurrent value supplies the lower bound needed for the full model norm. -/
theorem paperRecurrentDiagonal_norm_le_sub_compact (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hrec : PaperDiagonalRecurrent v)
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    ‖lpDiagonalCLM v hC hv‖ ≤ ‖lpDiagonalCLM v hC hv - K.val‖ := by
  apply paperBoundedDiagonal_norm_le_of_bound _ hC hv (norm_nonneg _)
  intro n
  obtain ⟨j, hj, heq⟩ := hrec n
  apply paperDiagonalCluster_le_norm_sub_compact v hC hv j hj
    (L := v n) (K := K)
  simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => v n) atTop (𝓝 (v n)))

theorem paperRecurrentDiagonal_compactIdealDistance (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hrec : PaperDiagonalRecurrent v) :
    compactIdealDistance (lpDiagonalCLM v hC hv) = ‖lpDiagonalCLM v hC hv‖ := by
  apply le_antisymm
  · simpa using compactIdealDistance_le (lpDiagonalCLM v hC hv) 0 isCompactOperator_zero
  · apply le_compactIdealDistance
    intro K hK
    exact paperRecurrentDiagonal_norm_le_sub_compact v hC hv hrec ⟨K, hK⟩

theorem paperRecurrentDiagonal_compact_iff_eq_zero (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hrec : PaperDiagonalRecurrent v) :
    IsCompactOperator (lpDiagonalCLM v hC hv) ↔ lpDiagonalCLM v hC hv = 0 := by
  constructor
  · intro h
    have hnorm := paperRecurrentDiagonal_norm_le_sub_compact v hC hv hrec
      ⟨lpDiagonalCLM v hC hv, h⟩
    simpa using hnorm
  · intro h
    rw [h]
    exact isCompactOperator_zero

end GaloisForLFunctions.HTGeometry
