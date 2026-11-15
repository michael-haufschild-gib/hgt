import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFrameFourier

/-!
# An inverse-scale Fourier bound for the smooth moment covering

The ordered weights sum to the smooth neighborhood cutoff. Their uniform
Fourier integral norms therefore give a bound proportional to the number
of centers. The dimension-dependent grid has inverse-scale cardinality,
so the full cutoff has Fourier integral norm at most `C / |ε|` for
`0 < |ε| ≤ 1`, uniformly over every shear direction.
-/

open scoped BigOperators FourierTransform
open MeasureTheory

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The smooth covering cutoff in Euclidean ambient coordinates. -/
def smoothCoveringEuclideanSchwartz (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) :
    SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : AffineAxisIndex r k => ℝ))
      (smoothCoveringSchwartz r k q ε hε δ)

/-- The pointwise ordered partition is also an identity in Schwartz space. -/
theorem sum_coveringWeightEuclideanSchwartz (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) :
    (∑ i ∈ dimensionCoveringGrid r q ε, coveringWeightEuclideanSchwartz r k q ε hε δ i) =
      smoothCoveringEuclideanSchwartz r k q ε hε δ := by
  ext x : 1
  rw [sum_apply]
  change (∑ i ∈ dimensionCoveringGrid r q ε,
    (coveringWeight r k q ε δ i (WithLp.ofLp x) : ℂ)) =
      (smoothCovering r k q ε δ (WithLp.ofLp x) : ℂ)
  rw [← Complex.ofReal_sum, sum_coveringWeight]

/-- The integral norm of the full inverse kernel is bounded by the sum of the piece norms. -/
theorem smoothCovering_fourierL1_le_sum (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) :
    (∫ x, ‖(𝓕⁻ (smoothCoveringEuclideanSchwartz r k q ε hε δ) :
      SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) x‖) ≤
        ∑ i ∈ dimensionCoveringGrid r q ε,
          ∫ x, ‖(𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
            SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) x‖ := by
  have he : (𝓕⁻ (smoothCoveringEuclideanSchwartz r k q ε hε δ) :
      SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) =
      ∑ i ∈ dimensionCoveringGrid r q ε,
        (𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
          SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) := by
    rw [← sum_coveringWeightEuclideanSchwartz, FourierTransform.fourierInv_sum]
  have hi (i : ℤ) : Integrable (fun x =>
      ‖(𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) x‖) :=
    (𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
      SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ).integrable.norm
  calc
    _ ≤ ∫ x, ∑ i ∈ dimensionCoveringGrid r q ε,
        ‖(𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
          SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) x‖ := by
      apply integral_mono
        (𝓕⁻ (smoothCoveringEuclideanSchwartz r k q ε hε δ) :
          SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ).integrable.norm
        (integrable_finsetSum (dimensionCoveringGrid r q ε) (fun i _ => hi i))
      intro x
      rw [he, sum_apply]
      exact norm_sum_le _ _
    _ = _ := integral_finsetSum (dimensionCoveringGrid r q ε) (fun i _ => hi i)

/-- A single constant bounds the full inverse kernel by the grid cardinality. -/
theorem exists_smoothCovering_fourierL1_card_bound (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (δ : Fin (r + 1) → ℝ),
      (∫ x, ‖(𝓕⁻ (smoothCoveringEuclideanSchwartz r (k + 1) q ε hε δ) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r (k + 1))) ℂ) x‖) ≤
          ((dimensionCoveringGrid r q ε).card : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_coveringWeight_fourierL1 r k q
  refine ⟨C, hC, ?_⟩
  intro ε hε δ
  apply (smoothCovering_fourierL1_le_sum r (k + 1) q ε hε δ).trans
  calc
    _ ≤ ∑ _i ∈ dimensionCoveringGrid r q ε, C :=
      Finset.sum_le_sum (fun i hi => hbound ε hε δ i hi)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The rounded grid gives an explicit inverse-scale expression at every nonzero scale. -/
theorem exists_smoothCovering_fourierL1_grid_bound (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (δ : Fin (r + 1) → ℝ),
      (∫ x, ‖(𝓕⁻ (smoothCoveringEuclideanSchwartz r (k + 1) q ε hε δ) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r (k + 1))) ℂ) x‖) ≤
          C * (2 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 3) := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothCovering_fourierL1_card_bound r k q
  refine ⟨C, hC, ?_⟩
  intro ε hε δ
  exact (hbound ε hε δ).trans ((mul_le_mul_of_nonneg_right
    (card_dimensionCoveringGrid_le r q ε) hC.le).trans_eq (mul_comm _ _))

/-- The repaired smooth neighborhood cutoff has a uniform inverse-scale Fourier integral norm. -/
theorem exists_smoothCovering_fourierL1_inverseScale_bound (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0), |ε| ≤ 1 →
      ∀ (δ : Fin (r + 1) → ℝ),
      (∫ x, ‖(𝓕⁻ (smoothCoveringEuclideanSchwartz r (k + 1) q ε hε δ) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r (k + 1))) ℂ) x‖) ≤ C / |ε| := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothCovering_fourierL1_grid_bound r k q
  refine ⟨C * (2 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) + 3), by positivity, ?_⟩
  intro ε hε hsmall δ
  have ha : 0 < |ε| := abs_pos.mpr hε
  have hthree : (3 : ℝ) ≤ 3 / |ε| := (le_div_iff₀ ha).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 3))
  apply (hbound ε hε δ).trans
  calc
    _ ≤ C * (2 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 3 / |ε|) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hthree _) hC.le
    _ = _ := by ring

#print axioms smoothCoveringEuclideanSchwartz
#print axioms sum_coveringWeightEuclideanSchwartz
#print axioms smoothCovering_fourierL1_le_sum
#print axioms exists_smoothCovering_fourierL1_card_bound
#print axioms exists_smoothCovering_fourierL1_grid_bound
#print axioms exists_smoothCovering_fourierL1_inverseScale_bound

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
