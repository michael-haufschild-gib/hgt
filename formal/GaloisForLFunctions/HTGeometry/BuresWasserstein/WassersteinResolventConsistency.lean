import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinTrapping

/-!
# Consistency of arbitrary resolvent steps

Any solution `Y` of the normalized resolvent equation `hΦ(Y) + G(Y,X) = 0` satisfies
`Y - X = -hΦ(Y) - R(Y,X)`, so `‖Y - X‖ ≤ hB + C‖Y - X‖²`.  On the branch where
`C‖Y - X‖ ≤ ½` this forces `‖Y - X‖ ≤ 2Bh`, and feeding that back gives

`‖Y - (X - hΦ(X))‖ ≤ (2BL + 4CB²) h²`.

So every resolvent step — not only the one produced by the contraction — is a second-order
perturbation of the explicit Euler step.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

lemma wassGConst_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < wassGConst α β := by
  have h := gmFieldLipConst_nonneg hα hβ
  have hαi : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  unfold wassGConst
  have h2 : (0 : ℝ) ≤ (β * β * α⁻¹) * (gmFieldLipConst α β * gmFieldLipConst α β) := by
    positivity
  linarith

/-- **Proposition 4.14 (Kim–Mer–Pálfia), resolvent steps.**  Every solution of the normalized
resolvent equation that is not far from the base point is the explicit Euler step up to `O(h²)`. -/
theorem exists_resolvent_consistency {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ B C Cc : ℝ, 0 ≤ B ∧ 0 < C ∧ 0 ≤ Cc ∧
      ∀ X Y : A, IsStrictlyPositive X → IsStrictlyPositive Y →
        α • (1 : A) ≤ X → X ≤ β • (1 : A) → α • (1 : A) ≤ Y → Y ≤ β • (1 : A) →
        ∀ h : ℝ, 0 < h → h • wassField s w Av Y + wassG Y X = 0 →
          C * ‖Y - X‖ ≤ 1 / 2 →
          ‖Y - X‖ ≤ 2 * B * h ∧ ‖Y - (X - h • wassField s w Av X)‖ ≤ Cc * (h * h) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨B, L, hB0, hL0, hBnd, hLip⟩ :=
    exists_bound_lipschitz_wassField (A := A) (s := s) (w := w) (Av := Av)
      hα hαβ hw hwsum hA hAα hAβ
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = wassGConst α β := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hCdef]; exact wassGConst_pos hα hβ
  refine ⟨B, C, 2 * B * L + 4 * C * B * B, hB0, hC0, by positivity, ?_⟩
  intro X Y hX hY hXα hXβ hYα hYβ h hh heq hsmall
  -- the increment identity
  have hΔ : Y - X = -(h • wassField s w Av Y) - (wassG Y X - (Y - X)) := by
    have h2 : -(h • wassField s w Av Y) - (wassG Y X - (Y - X))
        = (Y - X) - (h • wassField s w Av Y + wassG Y X) := by abel_nf
    rw [h2, heq, sub_zero]
  have hRq : ‖wassG Y X - (Y - X)‖ ≤ C * (‖Y - X‖ * ‖Y - X‖) := by
    have hq := norm_wassG_sub_le hX hY hα hαβ hXα hXβ hYα hYβ
    rw [← hCdef] at hq
    exact hq
  have hΦY : ‖wassField s w Av Y‖ ≤ B := hBnd Y hY hYα hYβ
  have hfirst : ‖Y - X‖ ≤ h * B + C * (‖Y - X‖ * ‖Y - X‖) := by
    have hb1 : ‖-(h • wassField s w Av Y)‖ ≤ h * B := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left hΦY hh.le
    have hrw : ‖Y - X‖ = ‖-(h • wassField s w Av Y) - (wassG Y X - (Y - X))‖ := by
      rw [← hΔ]
    have hstep : ‖Y - X‖ ≤ ‖-(h • wassField s w Av Y)‖ + ‖wassG Y X - (Y - X)‖ := by
      rw [hrw]
      exact norm_sub_le _ _
    linarith [hb1, hRq, hstep]
  have hbound : ‖Y - X‖ ≤ 2 * B * h := by
    have hhalf : C * (‖Y - X‖ * ‖Y - X‖) ≤ (1/2) * ‖Y - X‖ := by
      have h1 : C * (‖Y - X‖ * ‖Y - X‖) = (C * ‖Y - X‖) * ‖Y - X‖ := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
    linarith [hfirst, hhalf]
  refine ⟨hbound, ?_⟩
  have hid : Y - (X - h • wassField s w Av X)
      = -(h • (wassField s w Av Y - wassField s w Av X)) - (wassG Y X - (Y - X)) := by
    have h2 : -(h • (wassField s w Av Y - wassField s w Av X)) - (wassG Y X - (Y - X))
        = (Y - (X - h • wassField s w Av X)) - (h • wassField s w Av Y + wassG Y X) := by
      rw [smul_sub]; abel_nf
    rw [h2, heq, sub_zero]
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  have hb1 : ‖-(h • (wassField s w Av Y - wassField s w Av X))‖ ≤ h * (L * (2 * B * h)) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    refine mul_le_mul_of_nonneg_left ?_ hh.le
    refine (hLip Y X hY hX hYα hYβ hXα hXβ).trans ?_
    exact mul_le_mul_of_nonneg_left hbound hL0
  have hb2 : ‖wassG Y X - (Y - X)‖ ≤ C * ((2 * B * h) * (2 * B * h)) := by
    refine hRq.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC0.le
    exact mul_le_mul hbound hbound (norm_nonneg _) (by positivity)
  nlinarith [hb1, hb2]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
