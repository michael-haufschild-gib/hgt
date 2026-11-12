import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactAbelMean
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelMeans
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicPowerNormalization

/-!
# Abel averaging commutes with the discrete contact normalization

The co-Poisson floor estimate makes the normalization error bounded and
vanishing. Its Abel mean is zero, so the exact integer-normalized contacts
have the same mean as their continuously normalized Laplace staircase.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity SelbergClass.DegreeOne

private theorem normalizedPowerContacts_eq_power_profile (a : ℝ) :
    normalizedPowerContacts a = fun N => (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N := by
  funext N
  change (N : ℝ) ^ (2 * a - 1) * powerContactPrefix a N = _
  rw [show -(1 - 2 * a) = 2 * a - 1 by ring]

/-- The normalized contacts are subpolynomial throughout the closed width range. -/
theorem strictGrowth_normalizedPowerContacts_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    _root_.HTGeometry.StrictNaturalPowerGrowth (normalizedPowerContacts a) 0 := by
  have hg := (strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw).rpow_mul (-(1 - 2 * a))
  rw [add_neg_cancel] at hg
  rw [normalizedPowerContacts_eq_power_profile]
  exact hg

/-- The literal normalized contact samples have their forced Abel mean
even when their ordinary limit does not exist. -/
theorem tendsto_logarithmicAbelMean_normalizedPowerContacts
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    Tendsto (logarithmicAbelMean (normalizedPowerContacts a)) (𝓝[>] 0)
      (𝓝 ((-deriv riemannZeta (1 - (a : ℂ)) / riemannZeta (1 - (a : ℂ)) -
        riemannZeta (1 - (a : ℂ))) / ((1 - 2 * a : ℝ) : ℂ))) := by
  let θ := 1 - 2 * a
  let f := powerContactPrefix a
  let g : ℕ → ℝ := fun N => (N : ℝ) ^ (-θ) * f N
  let E := logarithmicPowerNormalizationError f θ
  have hθ : 0 ≤ θ := by dsimp only [θ]; linarith only [ha2]
  have hθ1 : θ ≤ 1 := by dsimp only [θ]; linarith only [ha]
  have hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ :=
    strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw
  have hmeas : AEStronglyMeasurable E (volume.restrict (Ioi 0)) :=
    ((measurable_stepLaplaceIntegrand g 0).sub
      (measurable_stepLaplaceIntegrand f (θ : ℂ))).aestronglyMeasurable
  obtain ⟨C, _, hC⟩ := exists_bound_logarithmicPowerNormalizationError hθ hθ1 hf
  have hElim := tendsto_abelMean_of_bounded_tendsto hmeas hC
    (tendsto_logarithmicPowerNormalizationError_zero hθ hθ1 hf)
  have hlim := hElim.add (tendsto_powerContactAbelMean_of_add_width_le_half ha ha2 haw)
  rw [zero_add] at hlim
  rw [normalizedPowerContacts_eq_power_profile]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hprod : (fun u => stepLaplaceIntegrand f (θ : ℂ) u * abelKernel 0 (ε : ℂ) u) =
      stepLaplaceIntegrand f ((θ + ε : ℝ) : ℂ) := by
    funext u
    simp only [stepLaplaceIntegrand, abelKernel, ofReal_zero, mul_zero, neg_zero,
      Complex.cpow_zero, one_mul]
    rw [mul_right_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hEc : IntegrableOn (fun u => E u * abelKernel 0 (ε : ℂ) u) (Ioi 0) :=
    integrableOn_mul_abelKernel hmeas hC 0 hε0
  have hfc : IntegrableOn (fun u => stepLaplaceIntegrand f (θ : ℂ) u * abelKernel 0 (ε : ℂ) u)
      (Ioi 0) := by
    rw [hprod]
    exact (integrable_powerContactAbelIntegrand ha ha2 haw hε0).integrableOn
  have hsum : abelIntegral (stepLaplaceIntegrand g 0) 0 (ε : ℂ) =
      abelIntegral E 0 (ε : ℂ) + abelIntegral (stepLaplaceIntegrand f (θ : ℂ)) 0 (ε : ℂ) := by
    rw [abelIntegral, abelIntegral, abelIntegral, ← integral_add hEc hfc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp only [E, logarithmicPowerNormalizationError]
      ring
  have hwhole : abelIntegral (stepLaplaceIntegrand f (θ : ℂ)) 0 (ε : ℂ) =
      ∫ u : ℝ, stepLaplaceIntegrand f ((θ + ε : ℝ) : ℂ) u := by
    rw [abelIntegral, hprod, ← integral_Ici_eq_integral_Ioi]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    exact stepLaplaceIntegrand_of_neg (by simp [f, powerContactPrefix]) _ (not_le.mp hu)
  change (ε : ℂ) * abelIntegral E 0 (ε : ℂ) + powerContactAbelMean a ε =
    (ε : ℂ) * abelIntegral (stepLaplaceIntegrand g 0) 0 (ε : ℂ)
  rw [hsum, mul_add, hwhole, powerContactAbelMean]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
