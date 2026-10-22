import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.FiniteSpectralPhaseActionLaw

/-!
# Radial phase normalization for Hardy boundary scaling

`phaseNormalize 1 a` is the radial projection `a / ‖a‖` of a complex number onto the unit circle
(with value `1` at `a = 0`), and its distance from `a` is exactly `|‖a‖ - 1|`. Hence, when inner
disk multipliers `F i` take values of modulus tending to `1` at points `q i` of the unit disk, the
radial phase of `F i (q i)` is an admissible unimodular constant: the residual core
`(M_{F i} - c i) P_i`, with `c i` that phase and `P_i` the projection onto the model space of the
Blaschke product with the single zero `q i` repeated `m + 1` times, tends to zero in operator norm.

## Main results

- `norm_sub_phaseNormalize_one_eq_abs_norm_sub_one`: `‖a - phaseNormalize 1 a‖ = |‖a‖ - 1|`.
- `tendsto_norm_sub_phaseNormalize_one_zero`: if `‖z i‖ → 1` then
  `‖z i - phaseNormalize 1 (z i)‖ → 0`.
- `tendsto_norm_finiteModelResidualCore_repeatSingle_zero_of_norm_value_one`: if every `F i` is a
  Hardy multiplier isometry and `‖F i (q i)‖ → 1`, the finite-model residual core with radial-phase
  constant tends to zero in operator norm, for every fixed multiplicity `m + 1`.

## Hypotheses

The two phase identities are unconditional. The residual-core limit assumes that each `F i` is a
Hardy multiplier isometry (`HardyMultiplierIsometry`: multiplication by `F i` preserves the Hardy
norm), that `‖q i‖ < 1`, and that `‖F i (q i)‖ → 1` along the filter.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The distance from `a` to its radial phase `a / ‖a‖` is `|‖a‖ - 1|` (also at `a = 0`, where the
phase is `1`). -/
theorem norm_sub_phaseNormalize_one_eq_abs_norm_sub_one (a : ℂ) :
    ‖a - phaseNormalize 1 a‖ = |‖a‖ - 1| := by
  by_cases ha : a = 0
  · simp [ha, phaseNormalize]
  · rw [phaseNormalize, if_neg ha]
    have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hfac : a - a / ‖a‖ = ((1 - 1 / ‖a‖ : ℝ) : ℂ) * a := by
      push_cast
      field_simp
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (1 - 1 / ‖a‖ : ℝ) = (‖a‖ - 1) / ‖a‖ by field_simp]
    rw [abs_div, abs_of_pos hnorm]
    field_simp

/-- If `‖z i‖ → 1` along a filter, then `z i` approaches its radial phase:
`‖z i - phaseNormalize 1 (z i)‖ → 0`. -/
theorem tendsto_norm_sub_phaseNormalize_one_zero
    {ι : Type*} {l : Filter ι} (z : ι → ℂ)
    (hz : Tendsto (fun i => ‖z i‖) l (𝓝 1)) :
    Tendsto (fun i => ‖z i - phaseNormalize 1 (z i)‖) l (𝓝 0) := by
  have hsub : Tendsto (fun i => ‖z i‖ - 1) l (𝓝 0) := by
    convert hz.sub_const 1 using 1 <;> norm_num
  have habs := hsub.abs
  have habs' : Tendsto (fun i => |‖z i‖ - 1|) l (𝓝 0) := by simpa using habs
  exact habs'.congr' (Eventually.of_forall fun i =>
    (norm_sub_phaseNormalize_one_eq_abs_norm_sub_one (z i)).symm)

/-- Assuming each `F i` is a Hardy multiplier isometry, `‖q i‖ < 1`, and `‖F i (q i)‖ → 1`, the
residual core of `F i` with constant the radial phase of `F i (q i)`, compressed to the model space
of the Blaschke product with zero `q i` of multiplicity `m + 1`, tends to `0` in operator norm. -/
theorem tendsto_norm_finiteModelResidualCore_repeatSingle_zero_of_norm_value_one
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) (m : ℕ)
    (hvalue : Tendsto (fun i => ‖(F i).fn (q i)‖) l (𝓝 1)) :
    Tendsto (fun i =>
      ‖finiteModelResidualCore (F i) (FiniteBlaschke.repeatSingle (hq i) m)
        (phaseNormalize 1 ((F i).fn (q i)))‖) l (𝓝 0) := by
  apply tendsto_norm_finiteModelResidualCore_repeatSingle_zero
    F hF q hq (fun i => phaseNormalize 1 ((F i).fn (q i)))
  · intro i
    exact norm_phaseNormalize_finiteSpectralPhaseActionLaw (by norm_num)
  · exact tendsto_norm_sub_phaseNormalize_one_zero
      (fun i => (F i).fn (q i)) hvalue

end

end GaloisForLFunctions.HTGeometry
