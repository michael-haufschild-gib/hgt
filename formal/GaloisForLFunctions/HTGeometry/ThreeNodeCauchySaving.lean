import GaloisForLFunctions.HTGeometry.RealAdjugateHeatPhase

/-!
# An explicit saving from three-node interpolation columns

The difference between a separated trace product and the column envelope is
the sum of all three Cauchy--Schwarz square defects. Two columns alone give
a quantitative lower bound independent of the zeroth root weight.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

def threeCauchyDefect (u r : Fin 3 → ℝ) : ℝ :=
  (u 0 * r 1 - u 1 * r 0) ^ 2 + (u 0 * r 2 - u 2 * r 0) ^ 2 +
    (u 1 * r 2 - u 2 * r 1) ^ 2

theorem threeCauchyDefect_nonneg (u r : Fin 3 → ℝ) : 0 ≤ threeCauchyDefect u r := by
  unfold threeCauchyDefect
  positivity

theorem threeCauchyDefect_identity (u r : Fin 3 → ℝ) :
    (∑ j, u j * r j) ^ 2 + threeCauchyDefect u r =
      (∑ j, u j ^ 2) * ∑ j, r j ^ 2 := by
  simp only [Fin.sum_univ_three, threeCauchyDefect]
  ring

def realThreeAdjugateHeatDefect (M : Matrix (Fin 3) (Fin 3) ℝ)
    (rate r : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ∑ i, threeCauchyDefect (fun j => |M.adjugate j i|) r * Real.exp (t * rate i)

theorem realThreeAdjugateHeatDefect_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ)
    (rate r : Fin 3 → ℝ) (t : ℝ) : 0 ≤ realThreeAdjugateHeatDefect M rate r t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (threeCauchyDefect_nonneg _ _) (Real.exp_pos _).le

/-- Every cross term in the Cauchy saving is retained in an exact square identity. -/
theorem realThreeAdjugateHeatDefect_identity (M : Matrix (Fin 3) (Fin 3) ℝ)
    (rate r : Fin 3 → ℝ) (t : ℝ) :
    realAdjugateHeatPhaseEnvelope M rate r t + realThreeAdjugateHeatDefect M rate r t =
      (∑ j, r j ^ 2) * ∑ j, ∑ i, M.adjugate j i ^ 2 * Real.exp (t * rate i) := by
  have h (i : Fin 3) := threeCauchyDefect_identity (fun j => |M.adjugate j i|) r
  simp only [sq_abs] at h
  unfold realAdjugateHeatPhaseEnvelope realThreeAdjugateHeatDefect
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i, ((∑ j, M.adjugate j i ^ 2) * ∑ j, r j ^ 2) * Real.exp (t * rate i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← add_mul, h i]
    _ = (∑ j, r j ^ 2) * ∑ i, (∑ j, M.adjugate j i ^ 2) * Real.exp (t * rate i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]

/-- Two actual interpolation columns yield a positive saving away from coincident nodes. -/
theorem realThreeVandermondeHeatDefect_lower (x r : Fin 3 → ℝ) (t : ℝ) :
    (min ((x 1 - x 2) ^ 2 * Real.exp (t * x 0))
      ((x 0 - x 2) ^ 2 * Real.exp (t * x 1)) / 2) *
        ((|x 1 * x 2| - |x 0 * x 2|) * r 2) ^ 2 ≤
          realThreeAdjugateHeatDefect (Matrix.vandermonde x) x r t := by
  let M := Matrix.vandermonde x
  let w₀ := (x 1 - x 2) ^ 2 * Real.exp (t * x 0)
  let w₁ := (x 0 - x 2) ^ 2 * Real.exp (t * x 1)
  let m := min w₀ w₁
  let z₀ := |x 1 * x 2| * r 2 - r 0
  let z₁ := |x 0 * x 2| * r 2 - r 0
  have hm : 0 ≤ m := le_min (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hcol (i : Fin 3) :
      (|M.adjugate 0 i| * r 2 - |M.adjugate 2 i| * r 0) ^ 2 * Real.exp (t * x i) ≤
        threeCauchyDefect (fun j => |M.adjugate j i|) r * Real.exp (t * x i) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    unfold threeCauchyDefect
    linarith only [sq_nonneg (|M.adjugate 0 i| * r 1 - |M.adjugate 1 i| * r 0),
      sq_nonneg (|M.adjugate 1 i| * r 2 - |M.adjugate 2 i| * r 1)]
  have h00 : M.adjugate 0 0 = x 1 * x 2 * (x 2 - x 1) := by
    simp [M, Matrix.adjugate_fin_three, Matrix.vandermonde_apply]
    ring
  have h20 : M.adjugate 2 0 = x 2 - x 1 := by
    simp [M, Matrix.adjugate_fin_three, Matrix.vandermonde_apply]
  have h01 : M.adjugate 0 1 = x 0 * x 2 * (x 0 - x 2) := by
    simp [M, Matrix.adjugate_fin_three, Matrix.vandermonde_apply]
    ring
  have h21 : M.adjugate 2 1 = x 0 - x 2 := by
    simp [M, Matrix.adjugate_fin_three, Matrix.vandermonde_apply]
    ring
  have h0 : w₀ * z₀ ^ 2 ≤ threeCauchyDefect (fun j => |M.adjugate j 0|) r *
      Real.exp (t * x 0) := by
    have h := hcol 0
    rw [h00, h20, abs_mul] at h
    have he : (|x 1 * x 2| * |x 2 - x 1| * r 2 - |x 2 - x 1| * r 0) ^ 2 *
        Real.exp (t * x 0) = w₀ * z₀ ^ 2 := by
      rw [show |x 1 * x 2| * |x 2 - x 1| * r 2 - |x 2 - x 1| * r 0 =
        |x 2 - x 1| * z₀ by dsimp only [z₀]; ring, mul_pow, sq_abs]
      dsimp only [w₀]
      ring
    rwa [he] at h
  have h1 : w₁ * z₁ ^ 2 ≤ threeCauchyDefect (fun j => |M.adjugate j 1|) r *
      Real.exp (t * x 1) := by
    have h := hcol 1
    rw [h01, h21, abs_mul] at h
    have he : (|x 0 * x 2| * |x 0 - x 2| * r 2 - |x 0 - x 2| * r 0) ^ 2 *
        Real.exp (t * x 1) = w₁ * z₁ ^ 2 := by
      rw [show |x 0 * x 2| * |x 0 - x 2| * r 2 - |x 0 - x 2| * r 0 =
        |x 0 - x 2| * z₁ by dsimp only [z₁]; ring, mul_pow, sq_abs]
      dsimp only [w₁]
      ring
    rwa [he] at h
  have hpair : w₀ * z₀ ^ 2 + w₁ * z₁ ^ 2 ≤ realThreeAdjugateHeatDefect M x r t := by
    unfold realThreeAdjugateHeatDefect
    rw [Fin.sum_univ_three]
    have h2 := mul_nonneg (threeCauchyDefect_nonneg (fun j => |M.adjugate j 2|) r)
      (Real.exp_pos (t * x 2)).le
    linarith only [h0, h1, h2]
  have hmin0 := mul_le_mul_of_nonneg_right (min_le_left w₀ w₁) (sq_nonneg z₀)
  have hmin1 := mul_le_mul_of_nonneg_right (min_le_right w₀ w₁) (sq_nonneg z₁)
  have hsq : (z₀ - z₁) ^ 2 ≤ 2 * (z₀ ^ 2 + z₁ ^ 2) := by
    nlinarith only [sq_nonneg (z₀ + z₁)]
  have h := mul_le_mul_of_nonneg_left hsq hm
  have hid : (|x 1 * x 2| - |x 0 * x 2|) * r 2 = z₀ - z₁ := by
    dsimp only [z₀, z₁]
    ring
  rw [hid]
  change (m / 2) * (z₀ - z₁) ^ 2 ≤ _
  nlinarith only [hpair, hmin0, hmin1, h]

end
end GaloisForLFunctions.HTGeometry
