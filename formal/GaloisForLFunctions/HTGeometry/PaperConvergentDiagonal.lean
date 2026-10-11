import GaloisForLFunctions.HTGeometry.LaplaceFormationCompletionTopology
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin

/-!
# Exact compact quotient of a convergent depth history

A convergent scalar history acts diagonally on the existing `ℓ²(ℕ)` model. Its deviation from
its limiting scalar identity is compact. Escaping coordinate vectors prove the matching lower
bound against every compact operator, including operators mixing different depth coordinates.
The proven TraceCone compact-ideal weight therefore detects exactly the limiting character.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Classical
open scoped ENNReal Topology

/-- The bounded diagonal of a convergent history; boundedness is derived from convergence. -/
def paperConvergentDiagonal (v : ℕ → ℂ) {L : ℂ} (hv : Tendsto v atTop (𝓝 L)) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpDiagonalCLM v (le_max_left 0 (sSup (Set.range fun n => ‖v n‖)))
    (fun n => (le_csSup hv.norm.bddAbove_range (Set.mem_range_self n)).trans
      (le_max_right 0 _))

@[simp] theorem paperConvergentDiagonal_apply (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    paperConvergentDiagonal v hv f n = v n * f n := rfl

@[simp] theorem paperConvergentDiagonal_single (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (n : ℕ) :
    paperConvergentDiagonal v hv (lp.single 2 n (1 : ℂ)) = lp.single 2 n (v n) :=
  lpDiagonalCLM_single _ _ _ _

/-- Differences of history operators retain the complete pointwise difference. -/
theorem paperConvergentDiagonal_sub (v w : ℕ → ℂ) {L M : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (hw : Tendsto w atTop (𝓝 M)) :
    paperConvergentDiagonal v hv - paperConvergentDiagonal w hw =
      paperConvergentDiagonal (fun n => v n - w n) (hv.sub hw) := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, paperConvergentDiagonal_apply]
  ring

theorem paperConvergentDiagonal_const (L : ℂ) :
    paperConvergentDiagonal (fun _ => L) tendsto_const_nhds =
      L • (1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  simp [paperConvergentDiagonal_apply]

/-- The history's entire deviation from its limiting scalar is compact. -/
theorem paperConvergentDiagonal_sub_limit_compact (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) :
    IsCompactOperator (paperConvergentDiagonal v hv - L • 1 :
      lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
  rw [← paperConvergentDiagonal_const, paperConvergentDiagonal_sub]
  apply isCompactOperator_lpDiagonalCLM
  simpa only [sub_self, norm_zero] using (hv.sub (tendsto_const_nhds (x := L))).norm

/-- Every compact correction leaves at least the limiting character's norm. -/
theorem paperConvergentDiagonal_limit_le_norm_sub_compact (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L))
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    ‖L‖ ≤ ‖paperConvergentDiagonal v hv - K.1‖ := by
  let D := paperConvergentDiagonal v hv
  have hK := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n => lp.single 2 n (1 : ℂ))
    (fun n => by rw [lp.norm_single (by norm_num), norm_one]) tendsto_inner_lp_single
  have hlim := hv.norm.sub hK.norm
  simp only [norm_zero, sub_zero] at hlim
  apply le_of_tendsto' hlim
  intro n
  have h := norm_sub_norm_le (D (lp.single 2 n (1 : ℂ)))
    (K.1 (lp.single 2 n (1 : ℂ)))
  have hb := (D - K.1).le_opNorm (lp.single 2 n (1 : ℂ))
  rw [lp.norm_single (by norm_num), norm_one, mul_one, sub_apply] at hb
  have hd : ‖D (lp.single 2 n (1 : ℂ))‖ = ‖v n‖ := by
    dsimp only [D]
    rw [paperConvergentDiagonal_single, lp.norm_single (by norm_num)]
  rw [hd] at h
  exact h.trans hb

/-- The exact essential norm is the norm of the limiting character. -/
theorem paperConvergentDiagonal_compactIdealDistance (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) :
    compactIdealDistance (paperConvergentDiagonal v hv) = ‖L‖ := by
  apply le_antisymm
  · have h := compactIdealDistance_le (paperConvergentDiagonal v hv)
      (paperConvergentDiagonal v hv - L • 1)
      (paperConvergentDiagonal_sub_limit_compact v hv)
    have hs : ‖(L • 1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)‖ ≤ ‖L‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
      intro f
      exact (norm_smul L f).le
    have hle : compactIdealDistance (paperConvergentDiagonal v hv) ≤
        ‖(L • 1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)‖ := by
      simpa only [sub_sub_cancel] using h
    exact hle.trans hs
  · exact le_compactIdealDistance _ _ fun K hK =>
      paperConvergentDiagonal_limit_le_norm_sub_compact v hv ⟨K, hK⟩

/-- Compactness of the full history is exactly vanishing of its cofinal character. -/
theorem paperConvergentDiagonal_compact_iff (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) :
    IsCompactOperator (paperConvergentDiagonal v hv) ↔ L = 0 := by
  constructor
  · intro h
    have hn := paperConvergentDiagonal_limit_le_norm_sub_compact v hv
      ⟨paperConvergentDiagonal v hv, h⟩
    rw [sub_self, norm_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · intro h
    have hc := paperConvergentDiagonal_sub_limit_compact v hv
    simpa only [h, zero_smul, sub_zero] using hc

/-- Compact equivalence of two histories is equality of their limiting characters. -/
theorem paperConvergentDiagonal_compact_sub_iff (v w : ℕ → ℂ) {L M : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (hw : Tendsto w atTop (𝓝 M)) :
    IsCompactOperator (paperConvergentDiagonal v hv - paperConvergentDiagonal w hw) ↔ L = M := by
  rw [paperConvergentDiagonal_sub, paperConvergentDiagonal_compact_iff, sub_eq_zero]

/-- The quotient preserves exactly the distance between limiting characters. -/
theorem paperConvergentDiagonal_compactIdealDistance_sub (v w : ℕ → ℂ) {L M : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (hw : Tendsto w atTop (𝓝 M)) :
    compactIdealDistance (paperConvergentDiagonal v hv - paperConvergentDiagonal w hw) =
      ‖L - M‖ := by
  rw [paperConvergentDiagonal_sub, paperConvergentDiagonal_compactIdealDistance]

/-- The paper compact-ideal trace detects exactly the nonzero limiting character. -/
theorem paperConvergentDiagonal_traceCost (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2) (paperConvergentDiagonal v hv) =
      if L = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperConvergentDiagonal_compact_iff]

/-- Mixing finitely or compactly many depths does not change the ideal classification. -/
theorem paperConvergentDiagonal_traceCost_add_compact (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L))
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperConvergentDiagonal v hv + K.1) = if L = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperConvergentDiagonal_traceCost]

end
end GaloisForLFunctions.HTGeometry
