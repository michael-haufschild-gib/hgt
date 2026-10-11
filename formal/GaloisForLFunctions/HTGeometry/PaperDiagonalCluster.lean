import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal

/-!
# Escaping arithmetic channels survive compact perturbations

A bounded diagonal need not converge. Every limit along an escaping sequence of coordinates
still supplies a lower bound against all compact operators, including nondiagonal corrections.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter
open scoped Topology

/-- Every escaping diagonal character survives arbitrary compact correction. -/
theorem paperDiagonalCluster_le_norm_sub_compact (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ n, ‖v n‖ ≤ C) (j : ℕ → ℕ)
    (hj : Tendsto j atTop atTop) {L : ℂ}
    (hv : Tendsto (fun n => v (j n)) atTop (𝓝 L))
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    ‖L‖ ≤ ‖lpDiagonalCLM v hC hb - K.1‖ := by
  have hK := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n => lp.single 2 (j n) (1 : ℂ))
    (fun n => by rw [lp.norm_single (by norm_num), norm_one])
    (fun z => (tendsto_inner_lp_single z).comp hj)
  have hlim := hv.norm.sub hK.norm
  simp only [norm_zero, sub_zero] at hlim
  apply le_of_tendsto' hlim
  intro n
  have h := norm_sub_norm_le (lpDiagonalCLM v hC hb (lp.single 2 (j n) (1 : ℂ)))
    (K.1 (lp.single 2 (j n) (1 : ℂ)))
  have hbound := (lpDiagonalCLM v hC hb - K.1).le_opNorm
    (lp.single 2 (j n) (1 : ℂ))
  rw [lp.norm_single (by norm_num), norm_one, mul_one, sub_apply] at hbound
  rw [lpDiagonalCLM_single, lp.norm_single (by norm_num)] at h
  rw [lpDiagonalCLM_single] at hbound
  exact h.trans hbound

/-- The same lower bound in the compact quotient. -/
theorem paperDiagonalCluster_le_compactIdealDistance (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ n, ‖v n‖ ≤ C) (j : ℕ → ℕ)
    (hj : Tendsto j atTop atTop) {L : ℂ}
    (hv : Tendsto (fun n => v (j n)) atTop (𝓝 L)) :
    ‖L‖ ≤ compactIdealDistance (lpDiagonalCLM v hC hb) :=
  le_compactIdealDistance _ _ fun K hK =>
    paperDiagonalCluster_le_norm_sub_compact v hC hb j hj hv ⟨K, hK⟩

/-- Adding a compact operator preserves the exact quotient distance. -/
theorem paperCompactIdealDistance_add_compact
    (T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (S : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    compactIdealDistance (T + S.1) = compactIdealDistance T := by
  apply le_antisymm
  · apply le_compactIdealDistance
    intro K hK
    have h := compactIdealDistance_le (T + S.1) (K + S.1) (hK.add S.2)
    simpa only [add_sub_add_right_eq_sub] using h
  · apply le_compactIdealDistance
    intro K hK
    have h := compactIdealDistance_le T (K - S.1) (hK.sub S.2)
    convert h using 1
    congr 1
    abel

/-- Subtracting a compact operator preserves the exact quotient distance. -/
theorem paperCompactIdealDistance_sub_compact
    (T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (S : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    compactIdealDistance (T - S.1) = compactIdealDistance T := by
  simpa only [sub_eq_add_neg] using paperCompactIdealDistance_add_compact T ⟨-S.1, S.2.neg⟩

end
end GaloisForLFunctions.HTGeometry
