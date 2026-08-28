import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointEvenGlobal
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointFarTail

open Set

namespace RHTower

noncomputable section

/-- Radial antitonicity forces the center-mixed first jet to be nonpositive away from the
reflection center. -/
theorem thetaCuspCenterMixedDensityFirstJet_nonpos_of_pos
    {a t : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (ht : 0 < t) :
    thetaCuspCenterMixedDensityFirstJet a t ≤ 0 := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let g : ℝ → ℝ := fun s => f (max 0 s)
  have hfanti : AntitoneOn f (Ici 0) := by
    simpa only [f] using antitoneOn_thetaCuspCenterMixedDensity ha0 ha
  have hganti : Antitone g := by
    intro x y hxy
    exact hfanti (by simp) (by simp) (max_le_max_left 0 hxy)
  have hgf : g =ᶠ[nhds t] f := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change f (max 0 s) = f s
    rw [max_eq_right hs.le]
  have hfderiv : HasDerivAt f (thetaCuspCenterMixedDensityFirstJet a t) t := by
    simpa only [f] using hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t
  exact (hfderiv.congr_of_eventuallyEq hgf).nonpos_of_antitone hganti

/-- Negativity of the odd determinant forces the middle equal-step drop to exceed the first
drop.  This is the first nonlinear shape constraint on any rank-four counterexample. -/
theorem thetaCuspCenterMixedOddParityWall_neg_forces_middleDrop_gt_firstDrop
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t)
    (hneg : thetaCuspCenterMixedOddParityWall a t < 0) :
    thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t <
      thetaCuspCenterMixedDensity a t - thetaCuspCenterMixedDensity a (2 * t) := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let A : ℝ := f 0 - f t
  let B : ℝ := f t - f (2 * t)
  let T : ℝ := f 0 - f (3 * t)
  have hA : 0 < A := by
    dsimp [A, f]
    exact sub_pos.mpr (thetaCuspCenterMixedDensity_lt_zero ha0 ha ht)
  have hB : 0 ≤ B := by
    dsimp [B, f]
    have hmono := antitoneOn_thetaCuspCenterMixedDensity ha0.le ha
    exact sub_nonneg.mpr <| hmono
      (show t ∈ Ici (0 : ℝ) from ht.le)
      (show 2 * t ∈ Ici (0 : ℝ) from
        mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ht.le)
      (by linarith)
  have hT : A ≤ T := by
    dsimp [A, T, f]
    have hmono := antitoneOn_thetaCuspCenterMixedDensity ha0.le ha
    have h13 := hmono
      (show t ∈ Ici (0 : ℝ) from ht.le)
      (show 3 * t ∈ Ici (0 : ℝ) from
        mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) ht.le)
      (by linarith : t ≤ 3 * t)
    linarith
  have hwall : B ^ 2 > A * T := by
    dsimp [A, B, T, f]
    unfold thetaCuspCenterMixedOddParityWall toeplitzFourOddParityWall at hneg
    nlinarith
  by_contra hnot
  have hBA : B ≤ A := le_of_not_gt hnot
  have hsq : B ^ 2 ≤ A ^ 2 := (sq_le_sq₀ hB hA.le).2 hBA
  have hprod : A ^ 2 ≤ A * T := by nlinarith
  exact (not_lt_of_ge hsq) (lt_of_le_of_lt hprod hwall)

/-- Once the even sector is globally eliminated, every failed rank-four packet produces one
interior stationary odd obstruction with a dominant middle drop and a nonnegative dyadic decay
jet defect. -/
theorem exists_thetaCuspCenterMixedOddStationary_obstruction_of_not_posSemidef
    {a t₀ : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht₀ : 0 < t₀)
    (hfail : ¬ Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t₀)) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspCenterMixedOddParityWall a t < 0 ∧
      thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t <
        thetaCuspCenterMixedDensity a t - thetaCuspCenterMixedDensity a (2 * t) ∧
      0 ≤ thetaCuspCenterMixedDensityFirstJet a t -
        2 * thetaCuspCenterMixedDensityFirstJet a (2 * t) ∧
      -3 * thetaCuspCenterMixedDensityFirstJet a (3 * t) *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t) -
        thetaCuspCenterMixedDensityFirstJet a t *
          (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a (3 * t)) -
        2 * (thetaCuspCenterMixedDensity a t -
          thetaCuspCenterMixedDensity a (2 * t)) *
          (thetaCuspCenterMixedDensityFirstJet a t -
            2 * thetaCuspCenterMixedDensityFirstJet a (2 * t)) = 0 := by
  have hodd0 : thetaCuspCenterMixedOddParityWall a t₀ < 0 := by
    have hnot : ¬ 0 ≤ thetaCuspCenterMixedOddParityWall a t₀ := by
      intro hodd
      exact hfail <|
        (thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall
          ha0 ha ht₀).2 hodd
    exact lt_of_not_ge hnot
  obtain ⟨t, ht, hneg, hstat⟩ :=
    exists_thetaCuspCenterMixedOddParityWall_stationary_neg_of_neg ha0 ha ht₀ hodd0
  have hdrop :=
    thetaCuspCenterMixedOddParityWall_neg_forces_middleDrop_gt_firstDrop ha0 ha ht hneg
  have hp1 := thetaCuspCenterMixedDensityFirstJet_nonpos_of_pos ha0.le ha ht
  have hp3 := thetaCuspCenterMixedDensityFirstJet_nonpos_of_pos ha0.le ha
    (by positivity : 0 < 3 * t)
  have hA : 0 < thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t :=
    sub_pos.mpr (thetaCuspCenterMixedDensity_lt_zero ha0 ha ht)
  have hT : 0 < thetaCuspCenterMixedDensity a 0 -
      thetaCuspCenterMixedDensity a (3 * t) :=
    sub_pos.mpr <| thetaCuspCenterMixedDensity_lt_zero ha0 ha (by positivity)
  have hB : 0 < thetaCuspCenterMixedDensity a t -
      thetaCuspCenterMixedDensity a (2 * t) := hA.trans hdrop
  have hj : 0 ≤ thetaCuspCenterMixedDensityFirstJet a t -
      2 * thetaCuspCenterMixedDensityFirstJet a (2 * t) := by
    nlinarith
  exact ⟨t, ht, hneg, hdrop, hj, hstat⟩

end

end RHTower
