import GaloisForLFunctions.HTGeometry.FokasLenellsRawDivided
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The first Taylor coefficient of the actual scattering endpoints

Factor the true endpoint equation by k, use an integrable majorant uniform
near zero, and pass to the limit by dominated convergence. The resulting
coefficient is an integral of the explicitly divided original Lax kernel.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawOrientedDividedDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawDividedDerivative q k v (-x) else rawDividedDerivative q k v x

theorem rawOrientedDividedDerivative_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedDividedDerivative q k v left) := by
  cases left
  · exact rawDividedDerivative_integrable q k v
  · exact (rawDividedDerivative_integrable q k v).comp_neg.neg

theorem rawOrientedDerivative_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) :
    rawOrientedDerivative q k v left x = (k : ℂ) • rawOrientedDividedDerivative q k v left x := by
  cases left <;> simp only [rawOrientedDerivative,rawOrientedDividedDerivative,↓reduceIte,
    Bool.false_eq_true,rawInteractionDerivative_factor,smul_neg]

def rawFirstSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  ∫ x in Set.Ioi (0 : ℝ), rawOrientedDividedDerivative q k v left x

/-- An exact factorization of the actual endpoint displacement. -/
theorem rawAsymptoticVector_first_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawAsymptoticVector q k v left = v+(k : ℂ) • rawFirstSlope q k v left := by
  unfold rawAsymptoticVector rawFirstSlope
  simp_rw [rawOrientedDerivative_factor,integral_smul]

private theorem rawOrientedDividedDerivative_near_bound (q : SchwartzMap ℝ ℂ) (k : ℝ)
    (v : SpectralVector) (left : Bool) (x : ℝ) (hk : |k| ≤ 1) :
    ‖rawOrientedDividedDerivative q k v left x‖ ≤
      (‖v‖*Real.exp (rawInteractionMass q))*rawInteractionDensity q (if left then -x else x) := by
  have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (rawInteractionMass_nonneg q)
  have hb := (rawDividedDerivative_bound q k v (if left then -x else x)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v))
      (rawInteractionDensity_nonneg q _))
  cases left <;> simpa only [rawOrientedDividedDerivative,↓reduceIte,Bool.false_eq_true,norm_neg] using hb

/-- Dominated convergence applies to the genuine endpoint slope on both half-lines. -/
theorem rawFirstSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawFirstSlope q k v left) (𝓝 0) (𝓝 (rawFirstSlope q 0 v left)) := by
  have hb : Integrable (fun x : ℝ => (‖v‖*Real.exp (rawInteractionMass q))*
      rawInteractionDensity q (if left then -x else x)) := by
    cases left
    · exact (rawInteractionDensity_integrable q).const_mul _
    · exact (rawInteractionDensity_integrable q).comp_neg.const_mul _
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (‖v‖*Real.exp (rawInteractionMass q))*rawInteractionDensity q (if left then -x else x))
    (Eventually.of_forall fun k => (rawOrientedDividedDerivative_integrable q k v left).aestronglyMeasurable.restrict)
    ?_ hb.integrableOn ?_
  · filter_upwards [hk] with k hk
    exact Eventually.of_forall fun x => rawOrientedDividedDerivative_near_bound q k v left x hk.le
  · apply Eventually.of_forall
    intro x
    cases left
    · simpa only [rawOrientedDividedDerivative,Bool.false_eq_true,↓reduceIte,
        rawDividedDerivative,rawInteractionSolution_zero_frequency] using rawDividedDerivative_tendsto_zero q v x
    · simpa only [rawOrientedDividedDerivative,↓reduceIte,rawDividedDerivative,
        rawInteractionSolution_zero_frequency] using (rawDividedDerivative_tendsto_zero q v (-x)).neg

/-- The actual asymptotic vector is differentiable in the original spectral variable at zero. -/
theorem rawAsymptoticVector_hasDerivAt_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    HasDerivAt (fun k : ℝ => rawAsymptoticVector q k v left) (rawFirstSlope q 0 v left) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hh : Tendsto (fun k => rawFirstSlope q k v left) (𝓝[≠] (0 : ℝ)) (𝓝 (rawFirstSlope q 0 v left)) :=
    (rawFirstSlope_tendsto_zero q v left).mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := hk
  simp only [zero_add,rawAsymptoticVector_zero_frequency]
  rw [rawAsymptoticVector_first_factor,add_sub_cancel_left]
  change rawFirstSlope q k v left = k⁻¹ • (k • rawFirstSlope q k v left)
  rw [smul_smul,inv_mul_cancel₀ hk0,one_smul]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
