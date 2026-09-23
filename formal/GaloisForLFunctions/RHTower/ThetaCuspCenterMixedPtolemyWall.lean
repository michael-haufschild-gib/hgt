import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointEvenGlobal

open Set

namespace RHTower

noncomputable section

/-- Intrinsic chord from the reflection center for the center-mixed theta correlation. -/
def thetaCuspCenterMixedChord (a t : ℝ) : ℝ :=
  Real.sqrt
    (thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t)

/-- The reflection-odd rank-four wall is exactly the equispaced Ptolemy inequality for the
intrinsic center-mixed chord. -/
theorem thetaCuspCenterMixedOddParityWall_nonneg_iff_ptolemy
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 ≤ t) :
    0 ≤ thetaCuspCenterMixedOddParityWall a t ↔
      thetaCuspCenterMixedChord a (2 * t) ^ (2 : ℕ) ≤
        thetaCuspCenterMixedChord a t ^ (2 : ℕ) +
          thetaCuspCenterMixedChord a t * thetaCuspCenterMixedChord a (3 * t) := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  let A : ℝ := f 0 - f t
  let B : ℝ := f t - f (2 * t)
  let T : ℝ := f 0 - f (3 * t)
  have hmono := antitoneOn_thetaCuspCenterMixedDensity ha0.le ha
  have hA : 0 ≤ A := by
    dsimp only [A, f]
    exact sub_nonneg.mpr <| hmono (by simp) ht ht
  have hB : 0 ≤ B := by
    dsimp only [B, f]
    exact sub_nonneg.mpr <| hmono ht
      (mul_nonneg (by norm_num) ht) (by linarith)
  have hT : 0 ≤ T := by
    dsimp only [T, f]
    exact sub_nonneg.mpr <| hmono (by simp)
      (mul_nonneg (by norm_num) ht) (by linarith)
  let P : ℝ := Real.sqrt A * Real.sqrt T
  have hP : 0 ≤ P := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hPsq : P ^ (2 : ℕ) = A * T := by
    dsimp only [P]
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hT]
  have hchord1 : thetaCuspCenterMixedChord a t ^ (2 : ℕ) = A := by
    dsimp only [thetaCuspCenterMixedChord, A, f]
    exact Real.sq_sqrt hA
  have hchord2 : thetaCuspCenterMixedChord a (2 * t) ^ (2 : ℕ) = A + B := by
    unfold thetaCuspCenterMixedChord
    rw [Real.sq_sqrt]
    · dsimp only [A, B, f]
      ring
    · have h02 := hmono
        (show 0 ∈ Ici (0 : ℝ) by simp)
        (show 2 * t ∈ Ici (0 : ℝ) from mul_nonneg (by norm_num) ht)
        (by linarith : 0 ≤ 2 * t)
      exact sub_nonneg.mpr h02
  have hchordProd :
      thetaCuspCenterMixedChord a t * thetaCuspCenterMixedChord a (3 * t) = P := by
    rfl
  have hwall :
      thetaCuspCenterMixedOddParityWall a t = A * T - B ^ (2 : ℕ) := by
    unfold thetaCuspCenterMixedOddParityWall toeplitzFourOddParityWall
    dsimp only [A, B, T, f]
    ring
  rw [hwall, hchord1, hchord2, hchordProd]
  constructor
  · intro h
    have hsq : B ^ (2 : ℕ) ≤ P ^ (2 : ℕ) := by rw [hPsq]; linarith
    have hBP : B ≤ P := (sq_le_sq₀ hB hP).mp hsq
    linarith
  · intro h
    have hBP : B ≤ P := by linarith
    have hsq : B ^ (2 : ℕ) ≤ P ^ (2 : ℕ) := (sq_le_sq₀ hB hP).2 hBP
    rw [hPsq] at hsq
    linarith

/-- Global rank-four theta positivity is precisely Ptolemy geometry of the intrinsic chord on
the equispaced packet. -/
theorem thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_ptolemy
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) ↔
      thetaCuspCenterMixedChord a (2 * t) ^ (2 : ℕ) ≤
        thetaCuspCenterMixedChord a t ^ (2 : ℕ) +
          thetaCuspCenterMixedChord a t * thetaCuspCenterMixedChord a (3 * t) := by
  rw [thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall ha0 ha ht]
  exact thetaCuspCenterMixedOddParityWall_nonneg_iff_ptolemy ha0 ha ht.le

end

end RHTower
