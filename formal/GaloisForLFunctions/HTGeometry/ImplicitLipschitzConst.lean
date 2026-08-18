import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

/-!
# The implicit Lipschitz constant depends only on the dominance datum

The Lipschitz constant of the explicit branch produced by the implicit function theorem in Lipschitz
form is built from the reference functional, the deviation bound and the order alone — the relation
itself does not enter.  Naming it makes the branch uniform over a family of relations sharing one
dominance datum, which is what a differential equation with varying coefficients needs: at every
time the same constant governs the branch.
-/

namespace GaloisForLFunctions

variable {n : ℕ}

/-- The Lipschitz constant of the implicit branch attached to a dominance datum. -/
noncomputable def implicitLipschitzConst (n : ℕ)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) (C : ℝ) : NNReal :=
  2 * Real.toNNReal ((C + ∑ k ∈ Finset.univ.erase (Fin.last n), ‖partialCoeff L k‖) * n
    / (‖partialCoeff L (Fin.last n)‖ - C))

/-- **The implicit branch, with its Lipschitz constant named.** -/
theorem exists_lipschitz_implicit_const {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hP : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) :
    ∃ Φ : (Fin n → ℂ) → ℂ, LipschitzWith (implicitLipschitzConst n L C) Φ ∧
      ∀ y ∈ S, P y = 0 → y (Fin.last n) = Φ (fun k : Fin n => y k.castSucc) := by
  classical
  set c : ℝ := ‖partialCoeff L (Fin.last n)‖ with hc
  set B : ℝ := ∑ k ∈ Finset.univ.erase (Fin.last n), ‖partialCoeff L k‖ with hB
  have hBnonneg : 0 ≤ B := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hcC : 0 < c - C := by linarith
  set M : ℝ := (C + B) * n / (c - C) with hM
  have hMnonneg : 0 ≤ M := by
    rw [hM]
    positivity
  have hgraph : ∀ y ∈ S, P y = 0 → ∀ z ∈ S, P z = 0 →
      dist (y (Fin.last n)) (z (Fin.last n))
        ≤ (Real.toNNReal M : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) := by
    intro y hyS hyP z hzS hzP
    have hest := implicit_lipschitz_estimate hS hP hC hbound (Fin.last n) hyS hzS hyP hzP
    have hsum := sum_erase_last_le (y := y) (z := z)
    have hCB : 0 ≤ C + B := by linarith
    have hchain : (c - C) * ‖y (Fin.last n) - z (Fin.last n)‖
        ≤ (C + B) * ((n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc)) := by
      refine le_trans hest ?_
      exact mul_le_mul_of_nonneg_left hsum hCB
    rw [Real.coe_toNNReal M hMnonneg, hM, dist_eq_norm]
    rw [div_mul_eq_mul_div, le_div_iff₀ hcC]
    calc ‖y (Fin.last n) - z (Fin.last n)‖ * (c - C)
        = (c - C) * ‖y (Fin.last n) - z (Fin.last n)‖ := by ring
      _ ≤ (C + B) * ((n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc)) := hchain
      _ = (C + B) * (n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) := by ring
  obtain ⟨Φ, hΦlip, hΦval⟩ := exists_lipschitz_of_graph hgraph
  exact ⟨Φ, hΦlip, hΦval⟩

end GaloisForLFunctions
