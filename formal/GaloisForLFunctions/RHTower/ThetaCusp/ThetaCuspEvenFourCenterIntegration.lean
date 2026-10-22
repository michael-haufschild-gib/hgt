import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourCompensation

/-!
# Exact center integration of the corrected even rank-four block

Only the twelfth entry receives a derivative of the proved zero-boundary center flux.
All entries retain their literal mixed moments. The canonical complete source is
strict near the seam and on a cofinal ray, simultaneously for every positive aperture.
-/
open MeasureTheory Set Matrix
namespace RHTower
noncomputable section

/-- Corrected weighted source matrix whose entries integrate to the actual even mixed block. -/
def thetaCuspCenterCorrectedEvenFour (a C r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val) *
    (r*Real.sinh (a*r)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) (r/2)) +
    if i.val = 3 ∧ j.val = 3 then C*deriv (thetaCuspCenterCompensationFlux a) r else 0

/-- Every corrected entry is absolutely integrable at every critical aperture. -/
theorem integrableOn_thetaCuspCenterCorrectedEvenFour
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (C : ℝ) (i j : Fin 4) :
    IntegrableOn (fun r => thetaCuspCenterCorrectedEvenFour a C r i j) (Ioi 0) := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  unfold thetaCuspCenterCorrectedEvenFour
  split_ifs
  · exact hi.add ((integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul C)
  · simpa only [add_zero, IntegrableOn] using hi

/-- Exact entrywise preservation, including the literal twelfth mixed derivative. -/
theorem integral_thetaCuspCenterCorrectedEvenFour
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (C : ℝ) (i j : Fin 4) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterCorrectedEvenFour a C r i j) =
      (-1 : ℝ)^(i.val+j.val)*iteratedDeriv (2*(i.val+j.val)) (thetaCuspCenterMixedDensity a) 0 := by
  have hi := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha
    (2*(i.val+j.val))).const_mul ((-1 : ℝ)^(i.val+j.val))
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  unfold thetaCuspCenterCorrectedEvenFour
  split_ifs
  · rw [integral_add hi ((integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul C),
      integral_const_mul, integral_const_mul, integral_deriv_thetaCuspCenterCompensationFlux habs,
      mul_zero, add_zero]
    rw [iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]
  · simp only [add_zero]
    rw [integral_const_mul, iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]

/-- The exact aperture-dependent correction dominates the source correction in matrix order. -/
theorem thetaCuspCenterCorrectedEvenFour_posDef_of_source
    {a C r : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hr : 0 < r)
    (hs : (thetaCuspNativeEvenFourCompensated C (r/2)).PosDef) :
    (thetaCuspCenterCorrectedEvenFour a C r).PosDef := by
  let w := r*Real.sinh (a*r)
  have hw : 0 < w := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hF : w*thetaCuspCenterCompensationSource (r/2) ≤
      deriv (thetaCuspCenterCompensationFlux a) r := by
    convert deriv_thetaCuspCenterCompensationFlux_lower ha.le hr.le using 1
    unfold w thetaCuspCenterCompensationSource
    ring
  let d : Fin 4 → ℝ := fun i => if i.val = 3 then
    C*(deriv (thetaCuspCenterCompensationFlux a) r-w*thetaCuspCenterCompensationSource (r/2)) else 0
  have hD : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp only [d]
    split_ifs
    · exact mul_nonneg hC (sub_nonneg.mpr hF)
    · exact le_rfl
  have heq : thetaCuspCenterCorrectedEvenFour a C r =
      w • thetaCuspNativeEvenFourCompensated C (r/2) + Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaCuspCenterCorrectedEvenFour, thetaCuspNativeEvenFourCompensated,
        Matrix.diagonal, d, w] <;> ring
  rw [heq]
  exact (hs.smul hw).add_posSemidef hD

/-- One compact center gap remains for the exact corrected integrand at every positive aperture. -/
theorem exists_thetaCuspCenterCorrectedEvenFour_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ, 0 < a → 0 < r → (r < δ ∨ R ≤ r) →
      (thetaCuspCenterCorrectedEvenFour a thetaCuspNativeEvenCompensationCoefficient r).PosDef := by
  obtain ⟨δ, R, hδ, hR, hsource⟩ := exists_thetaCuspNativeEvenFourCompensated_compact_gap
  refine ⟨2*δ, 2*R, by positivity, by linarith, fun a r ha hr h => ?_⟩
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha
    thetaCuspNativeEvenCompensationCoefficient_pos.le hr
  apply hsource (r/2) (by positivity)
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end
end RHTower
