/-
# Subpower closure with Bourgain's explicit scale constant

The quantitative Taylor estimate forces the bootstrap scale to be
`A * R^(2/3)` rather than literally `R^(2/3)`.  This module proves that
the fixed dilation is harmless.  Conjugating the scale map by
`R = A^3 * S` turns

`A * R^(2/3)`

exactly into

`A^3 * S^(2/3)`.

Thus the already formalized two-thirds bootstrap applies without hiding
the large absolute constant forced by the Taylor remainder.
-/
import GaloisForLFunctions.RHTower.BourgainPowerScaleSubpower

namespace RHTower

noncomputable section

/-- A fixed dilation in Bourgain's two-thirds recurrence does not change
the subpower conclusion. -/
theorem bourgain_subpower_of_dilated_twoThirds_recurrence
    (b : ℝ → ℝ) {A B γ : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hγ : 0 ≤ γ)
    (hcoarse :
      ∀ x : ℝ, 1 ≤ x →
        b x ≤ B * x ^ γ)
    (hrec :
      ∀ δ : ℝ, 0 < δ →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 1 ≤ x →
            b x ≤ C * x ^ δ *
              b (A * x ^ (2 / 3 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧
        ∀ x : ℝ, 1 ≤ x →
          b x ≤ D * x ^ ε := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let T : ℝ := A ^ (3 : ℕ)
  have hT : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ hA
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let g : ℝ → ℝ := fun y => b (T * y)
  have hscale (y : ℝ) (hy : 0 ≤ y) :
      A * (T * y) ^ (2 / 3 : ℝ) =
        T * y ^ (2 / 3 : ℝ) := by
    have hArpow :
        (A ^ (3 : ℕ)) ^ (2 / 3 : ℝ) =
          A ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast A 3, ← Real.rpow_natCast A 2]
      rw [← Real.rpow_mul hA0.le]
      norm_num
    rw [Real.mul_rpow hT0.le hy]
    dsimp [T] at hArpow ⊢
    rw [hArpow]
    ring
  have hgCoarse :
      ∀ y : ℝ, 1 ≤ y →
        g y ≤ (B * T ^ γ) * y ^ γ := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by norm_num) hy
    have hTy : 1 ≤ T * y := by nlinarith
    calc
      g y = b (T * y) := rfl
      _ ≤ B * (T * y) ^ γ := hcoarse (T * y) hTy
      _ = (B * T ^ γ) * y ^ γ := by
        rw [Real.mul_rpow hT0.le hy0]
        ring
  have hgRec :
      ∀ δ : ℝ, 0 < δ →
        ∃ C : ℝ, 0 < C ∧
          ∀ y : ℝ, 1 ≤ y →
            g y ≤ C * y ^ δ *
              g (y ^ (2 / 3 : ℝ)) := by
    intro δ hδ
    obtain ⟨C, hC, hstep⟩ := hrec δ hδ
    refine ⟨C * T ^ δ, mul_pos hC (Real.rpow_pos_of_pos hT0 _), ?_⟩
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by norm_num) hy
    have hTy : 1 ≤ T * y := by nlinarith
    calc
      g y = b (T * y) := rfl
      _ ≤ C * (T * y) ^ δ *
          b (A * (T * y) ^ (2 / 3 : ℝ)) :=
        hstep (T * y) hTy
      _ = (C * T ^ δ) * y ^ δ *
          g (y ^ (2 / 3 : ℝ)) := by
        rw [Real.mul_rpow hT0.le hy0, hscale y hy0]
        dsimp only [g]
        ring
  have hBT : 0 < B * T ^ γ :=
    mul_pos hB (Real.rpow_pos_of_pos hT0 _)
  intro ε hε
  obtain ⟨E, hE, hg⟩ :=
    bourgain_subpower_of_twoThirds_recurrence
      g hBT hγ hgCoarse hgRec ε hε
  let D : ℝ := E + B * T ^ γ
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxpow : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  by_cases hlarge : T ≤ x
  · let y : ℝ := x / T
    have hy : 1 ≤ y := by
      dsimp [y]
      exact (le_div_iff₀ hT0).2 (by simpa [mul_comm] using hlarge)
    have hy0 : 0 ≤ y := le_trans (by norm_num) hy
    have hyx : y ≤ x := by
      dsimp [y]
      exact div_le_self hx0.le hT
    have hxy : T * y = x := by
      dsimp [y]
      field_simp
    calc
      b x = g y := by
        dsimp [g]
        rw [hxy]
      _ ≤ E * y ^ ε := hg y hy
      _ ≤ E * x ^ ε := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hy0 hyx hε.le) hE.le
      _ ≤ D * x ^ ε := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp [D]; linarith [show 0 ≤ B * T ^ γ by positivity])
          (Real.rpow_nonneg hx0.le _)
  · have hxT : x < T := lt_of_not_ge hlarge
    have hcoarse' := hcoarse x hx
    have hxγ :
        x ^ γ ≤ T ^ γ :=
      Real.rpow_le_rpow hx0.le hxT.le hγ
    calc
      b x ≤ B * x ^ γ := hcoarse'
      _ ≤ B * T ^ γ :=
        mul_le_mul_of_nonneg_left hxγ hB.le
      _ ≤ D := by
        dsimp [D]
        linarith
      _ ≤ D * x ^ ε := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hxpow hD.le

end

end RHTower
