import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip

/-!
# Full Gaussian envelope in a complex theta strip

The complete holomorphic theta source retains its full Gaussian rate
`π cos(2δ)` on every closed strip of aperture `δ < π/4`. The finite constant
is the sum of the existing Gaussian atom majorant. Reflection supplies both
cusps. These estimates retain the rate needed by the power-weighted source
spaces and their analytic translation orbits.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The complete Gaussian profile, with the strip aperture's exact decay rate. -/
def thetaStripGaussianEnvelope (δ x : ℝ) : ℝ :=
  Real.exp (9 * |x| / 2) *
    Real.exp (-(Real.pi * Real.cos (2 * δ)) * Real.exp (2 * |x|))

/-- A finite constant obtained by summing the literal Gaussian atom majorant. -/
def thetaStripGaussianConstant (δ : ℝ) : ℝ :=
  (2 * Real.pi * (2 * Real.pi + 3) * Real.exp (Real.pi * Real.cos (2 * δ))) *
    ∑' n : ℕ, ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) *
      Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2)

theorem thetaStripGaussianConstant_nonneg (δ : ℝ) :
    0 ≤ thetaStripGaussianConstant δ := by
  unfold thetaStripGaussianConstant
  apply mul_nonneg (by positivity)
  exact tsum_nonneg fun n => by positivity

private theorem norm_thetaCuspComplexTerm_le_gaussian
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (z : ℂ) (him : |z.im| ≤ δ) (hre : 0 ≤ z.re) (n : ℕ) :
    ‖thetaCuspComplexTerm z n‖ ≤
      (2 * Real.pi * (2 * Real.pi + 3) * Real.exp (Real.pi * Real.cos (2 * δ))) *
      (Real.exp (9 * z.re / 2) *
        Real.exp (-(Real.pi * Real.cos (2 * δ)) * Real.exp (2 * z.re))) *
      (((n : ℝ) ^ 4 + (n : ℝ) ^ 2) *
        Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2)) := by
  let c := Real.pi * Real.cos (2 * δ)
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  have hc : 0 < c := mul_pos Real.pi_pos hcos
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [thetaCuspComplexTerm_zero, norm_zero, Nat.cast_zero, zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), zero_add, zero_mul, mul_zero, le_refl]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have he1 : (1 : ℝ) ≤ Real.exp (2 * z.re) := Real.one_le_exp (by linarith)
  have hproduct : 0 ≤ c * (((n : ℝ) ^ 2 - 1) * (Real.exp (2 * z.re) - 1)) :=
    mul_nonneg hc.le (mul_nonneg (by linarith) (by linarith))
  have hgauss : Real.exp (-c * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) ≤
      Real.exp (-c * Real.exp (2 * z.re)) * Real.exp c *
        Real.exp (-c * (n : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hproduct]
  have hpoly : 2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
      3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re) ≤
      (2 * Real.pi + 3) * ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) * Real.exp (4 * z.re) := by
    calc
      _ ≤ (2 * Real.pi + 3) * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
          (2 * Real.pi + 3) * (n : ℝ) ^ 2 * Real.exp (4 * z.re) := by
        gcongr <;> linarith [Real.pi_pos]
      _ = _ := by ring
  have hpre := mul_le_mul_of_nonneg_left hpoly
    (by positivity : 0 ≤ Real.exp (z.re / 2) * (2 * Real.pi))
  have hexp : Real.exp (9 * z.re / 2) = Real.exp (z.re / 2) * Real.exp (4 * z.re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ _ := norm_thetaCuspComplexTerm_le_pointwise hδ4.le him n
    _ ≤ (Real.exp (z.re / 2) * (2 * Real.pi) *
          ((2 * Real.pi + 3) * ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) * Real.exp (4 * z.re))) *
        (Real.exp (-c * Real.exp (2 * z.re)) * Real.exp c *
          Real.exp (-c * (n : ℝ) ^ 2)) :=
      mul_le_mul hpre hgauss (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [hexp]
      dsimp [c]
      ring

private theorem norm_thetaCuspStripSource_le_gaussian_of_nonneg
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (z : ℂ) (him : |z.im| ≤ δ) (hre : 0 ≤ z.re) :
    ‖thetaCuspStripSource z‖ ≤ thetaStripGaussianConstant δ *
      thetaStripGaussianEnvelope δ z.re := by
  let c := Real.pi * Real.cos (2 * δ)
  let K := 2 * Real.pi * (2 * Real.pi + 3) * Real.exp c
  let G := Real.exp (9 * z.re / 2) * Real.exp (-c * Real.exp (2 * z.re))
  let m : ℕ → ℝ := fun n => ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) * Real.exp (-c * (n : ℝ) ^ 2)
  have hc : 0 < c := mul_pos Real.pi_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩)
  have hm : Summable m := summable_thetaCuspMajorant hc
  have hz : z ∈ thetaCuspStrip := by
    dsimp only [thetaCuspStrip, mem_setOf_eq]
    linarith
  have hnorm := (summable_thetaCuspComplexTerm hz).norm
  calc
    ‖thetaCuspStripSource z‖ ≤ ∑' n : ℕ, ‖thetaCuspComplexTerm z n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (K * G) * m n :=
      hnorm.tsum_le_tsum
        (norm_thetaCuspComplexTerm_le_gaussian δ hδ0 hδ4 z him hre) (hm.mul_left (K * G))
    _ = (K * ∑' n : ℕ, m n) * G := by
      rw [hm.tsum_mul_left]
      ring
    _ = _ := by
      simp only [thetaStripGaussianConstant, thetaStripGaussianEnvelope, abs_of_nonneg hre]
      rfl

/-- The complete complex source keeps the exact Gaussian strip rate at both cusps. -/
theorem norm_thetaCuspStripSource_le_gaussian_envelope
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (z : ℂ) (him : |z.im| ≤ δ) :
    ‖thetaCuspStripSource z‖ ≤ thetaStripGaussianConstant δ *
      thetaStripGaussianEnvelope δ z.re := by
  by_cases hre : 0 ≤ z.re
  · exact norm_thetaCuspStripSource_le_gaussian_of_nonneg δ hδ0 hδ4 z him hre
  · have hz : z ∈ thetaCuspStrip := by
      dsimp only [thetaCuspStrip, mem_setOf_eq]
      linarith
    have hn := norm_thetaCuspStripSource_le_gaussian_of_nonneg δ hδ0 hδ4 (-z)
      (by simpa only [Complex.neg_im, abs_neg] using him)
      (by simp only [Complex.neg_re]; linarith)
    rw [thetaCuspStripSource_neg hz] at hn
    simpa only [thetaStripGaussianEnvelope, Complex.neg_re, abs_neg] using hn

end

end RHTower
