import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.SpectralBand
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FiniteCeiling
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm

/-! # Interlacing of positive conserving squared propagators

Isometric compression bounds every singular value from above. Finite rank
of the squared error bounds it from below by a shifted occupation weight.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap _root_.RHTower

/-- The positive conserving square is an isometric compression of critical squared heat. -/
theorem conserving_square_compression (G : Propagator) :
    ∃ U : Gas →ₗᵢ[ℂ] Gas, G.val^2 = star U.toContinuousLinearMap*(squareHeat.val*U.toContinuousLinearMap) := by
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property.2
  refine ⟨U,?_⟩
  rw [show G.val^2 = star G.val*G.val by rw [G.property.1.isSelfAdjoint.star_eq,pow_two],hu,
    star_mul,critical_isPositive.isSelfAdjoint.star_eq]
  change _ = star U.toContinuousLinearMap*(criticalOperator^2*U.toContinuousLinearMap)
  rw [pow_two,mul_assoc,mul_assoc]

theorem conserving_square_hs (G : Propagator) : (G.val^2).IsHilbertSchmidt := by
  obtain ⟨U,hU⟩ := conserving_square_compression G
  rw [hU]
  exact (squareHeat.property.2.comp_right _).comp_left _

theorem conserving_spectrum_le (G : Propagator) (n : ℕ) :
    approxNumber (G.val^2) n ≤ occupationWeight n := by
  obtain ⟨U,hU⟩ := conserving_square_compression G
  let V := U.toContinuousLinearMap
  have hV : ‖V‖ ≤ 1 := U.norm_toContinuousLinearMap_le
  have hV' : ‖star V‖ ≤ 1 := (norm_star V).le.trans hV
  have h₁ := rectApproxNumber_comp_le_left (star V) (squareHeat.val*V) n
  have h₂ := rectApproxNumber_comp_le_right squareHeat.val V n
  rw [hU,← squareHeat_approxNumber]
  change rectApproxNumber (star V ∘L (squareHeat.val*V)) n ≤ rectApproxNumber squareHeat.val n
  exact (h₁.trans (mul_le_of_le_one_left (rectApproxNumber_nonneg _ _) hV')).trans
    (h₂.trans (mul_le_of_le_one_right (rectApproxNumber_nonneg _ _) hV))

/-- Spectral sequence of an admissible projection in the compact interlacing band. -/
def physicalSpectrum (P : Projection) {r : ℕ} (hd : MissingDimension P r) (hc : Conserving (projected P)) :
    SpectralBand r := fun n => ⟨approxNumber ((projected P)^2) n,by
      have h := approxNumber_add_finiteRank_shift_le (A := (projected P)^2) (squareError_rank P hd) n
      rw [show (projected P)^2+(squareHeat.val-(projected P)^2) = squareHeat.val by abel,squareHeat_approxNumber] at h
      exact h,conserving_spectrum_le ⟨projected P,projected_positive _,hc⟩ n⟩

/-- The set of relative readings for all positive conserving propagators of fixed missing dimension. -/
def responseAtRank (f : SpectralResponse) (r : ℕ) : Set ℝ :=
  {y | ∃ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)),
    relativeReading f (physicalSpectrum P hd hc) = y}

#print axioms conserving_spectrum_le
#print axioms physicalSpectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
