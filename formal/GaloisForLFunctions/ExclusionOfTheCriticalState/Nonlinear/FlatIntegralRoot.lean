import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralEnergy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatRootContraction
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity

/-!
# The flat integral energy as a squared nonlinear L² norm

The pointwise square-root contraction represents twice the integral
energy exactly as an L² norm squared. Consequently its scalar square
root is globally 1-Lipschitz. Zero energy is precisely the negative cone,
including on infinite measure spaces.
-/

open MeasureTheory Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The square-root potential applied to an arbitrary L² profile. -/
def rootLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  rootPotential_contraction.compLp rootPotential_zero f

/-- Pointwise square-root contraction induces a contraction on the full L² space. -/
theorem rootLp_contraction : LipschitzWith 1 (rootLp : Lp ℝ 2 μ → Lp ℝ 2 μ) :=
  rootPotential_contraction.lipschitzWith_compLp rootPotential_zero

/-- The nonlinear Hilbert norm represents the integral energy exactly. -/
theorem rootLp_norm_sq (f : Lp ℝ 2 μ) : ‖rootLp f‖ ^ 2 = 2 * integralEnergy f := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ x, inner ℝ (rootLp f x) (rootLp f x) ∂μ) =
        ∫ x, 2 * potential (f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [rootPotential_contraction.coeFn_compLp rootPotential_zero f] with x hx
      change inner ℝ ((rootPotential_contraction.compLp rootPotential_zero f) x)
        ((rootPotential_contraction.compLp rootPotential_zero f) x) = _
      rw [hx]
      change rootPotential (f x) * rootPotential (f x) = _
      simpa only [sq] using rootPotential_sq (f x)
    _ = _ := integral_const_mul 2 _

/-- The square root of twice the energy is the norm of the contracted profile. -/
theorem rootLp_norm (f : Lp ℝ 2 μ) : ‖rootLp f‖ = Real.sqrt (2 * integralEnergy f) := by
  rw [← rootLp_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Energy square roots have a global unit Lipschitz bound, independent of the measure. -/
theorem integralEnergy_root_contraction :
    LipschitzWith 1 (fun f : Lp ℝ 2 μ => Real.sqrt (2 * integralEnergy f)) := by
  have he : (fun f : Lp ℝ 2 μ => Real.sqrt (2 * integralEnergy f)) =
      fun f => ‖rootLp f‖ := funext fun f => (rootLp_norm f).symm
  rw [he]
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_sub_le_iff.mpr
  have hb : ‖rootLp f - rootLp g‖ ≤ ‖f - g‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using rootLp_contraction.dist_le_mul f g
  constructor
  · exact (norm_sub_norm_le _ _).trans hb
  · have hs := norm_sub_norm_le (rootLp g) (rootLp f)
    rw [norm_sub_rev] at hs
    exact hs.trans hb

/-- No positive-amplitude profile can have zero integral energy. -/
theorem integralEnergy_zero_iff (f : Lp ℝ 2 μ) :
    integralEnergy f = 0 ↔ ∀ᵐ x ∂μ, f x ≤ 0 := by
  rw [integralEnergy, integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (potential_bounds (f x)).1) (integrable_potential f)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (potential_zero_iff (f x)).mp hx
  · intro h
    filter_upwards [h] with x hx
    exact (potential_zero_iff (f x)).mpr hx

/-- The complete set of integral-energy minimizers is the almost-everywhere negative cone. -/
theorem integralEnergy_minimizer_iff (f : Lp ℝ 2 μ) :
    (∀ g : Lp ℝ 2 μ, integralEnergy f ≤ integralEnergy g) ↔ ∀ᵐ x ∂μ, f x ≤ 0 := by
  constructor
  · intro h
    apply (integralEnergy_zero_iff f).mp
    have hz : integralEnergy (0 : Lp ℝ 2 μ) = 0 := by
      apply (integralEnergy_zero_iff _).mpr
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simpa only [hx, Pi.zero_apply] using (le_refl (0 : ℝ))
    exact le_antisymm (hz ▸ h 0) (integral_energy_bounds f).1
  · intro h g
    rw [(integralEnergy_zero_iff f).mpr h]
    exact (integral_energy_bounds g).1

#print axioms rootLp_norm_sq
#print axioms integralEnergy_root_contraction
#print axioms integralEnergy_zero_iff
#print axioms integralEnergy_minimizer_iff
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
