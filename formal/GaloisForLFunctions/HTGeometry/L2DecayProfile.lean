import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The one-dimensional square-integrable decay profile

On the real line the profile `t ↦ (1 + |t|)⁻¹` is square integrable, because its square is the
Japanese bracket of exponent `2`, which exceeds the dimension.  Any measurable function dominated
by a multiple of that profile is therefore in `L²`.  This is the standard route from a pointwise
`O(1/|t|)` decay estimate to membership in the Hilbert space.
-/

open MeasureTheory Real

noncomputable section

namespace HTGeometry

/-- The decay profile `(1 + |t|)⁻¹` is square integrable on the line. -/
theorem memLp_two_decayProfile : MemLp (fun t : ℝ => (1 + |t|)⁻¹) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (1 + |t|)⁻¹) volume := by fun_prop
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) volume := by
    apply integrable_one_add_norm
    simp
  refine hint.congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have hnorm : ‖(1 + |t|)⁻¹‖ = (1 + |t|)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 + |t|)⁻¹)]
  have hrpow : (1 + |t|) ^ (-(2 : ℝ)) = ((1 + |t|) ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hpos.le, ← Real.rpow_natCast (1 + |t|) 2]
    norm_num
  rw [Real.norm_eq_abs t, hrpow, hnorm, inv_pow]

/-- **From pointwise decay to `L²`.**  A measurable function dominated by a multiple of the decay
profile is square integrable. -/
theorem memLp_two_of_decayProfile {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hbound : ∀ t : ℝ, ‖f t‖ ≤ C * (1 + |t|)⁻¹) :
    MemLp f 2 volume := by
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg (f 0)) (hbound 0)
    simpa using h
  refine MemLp.mono (memLp_two_decayProfile.const_mul C) hf
    (Filter.Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (1 + |t|)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * (1 + |t|)⁻¹)]
  exact hbound t

end HTGeometry
