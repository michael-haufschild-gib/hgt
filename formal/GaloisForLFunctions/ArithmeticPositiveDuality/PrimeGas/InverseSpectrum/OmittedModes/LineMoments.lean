import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineClosure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.StrictDeficit
import GaloisForLFunctions.RHTower.MobiusDoubledParityContractionSaturationRigidity

/-! # Trace loss for one genuinely missing direction

The squared heat contracts every wave outside its range strictly.
The first two energy moments then bound the fourth-trace cost of a line.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

abbrev MissingWave := {v : Gas // v ∉ LinearMap.range criticalOperator.toLinearMap}

theorem missingWave_ne_zero (v : MissingWave) : v.val ≠ 0 :=
  fun h => v.property (h ▸ (LinearMap.range criticalOperator.toLinearMap).zero_mem)

theorem nonzero_line_conserves_iff (v : Gas) :
    v ≠ 0 ∧ Conserving (projected (omitLine v)) ↔ v ∉ LinearMap.range criticalOperator.toLinearMap := by
  rw [line_conserves_iff]
  constructor
  · rintro ⟨hne,h⟩ hmem
    exact hne (h hmem)
  · intro h
    exact ⟨missingWave_ne_zero ⟨v,h⟩,fun hm => (h hm).elim⟩

/-- The actual positive conserving propagator associated to one missed line. -/
def linePropagator (v : MissingWave) : Propagator :=
  ⟨projected (omitLine v.val),projected_positive _,((nonzero_line_conserves_iff _).mpr v.property).2⟩

private theorem heat_contraction (v : Gas) : ‖criticalOperator v‖ ≤ ‖v‖ :=
  (criticalOperator.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) critical_norm_le_one)

private theorem heat_fixed_of_saturation {v : Gas} (h : ‖criticalOperator v‖ = ‖v‖) :
    criticalOperator (criticalOperator v) = v := by
  have he := _root_.RHTower.adjoint_apply_apply_eq_of_contraction_saturates criticalOperator critical_norm_le_one v h
  rwa [show adjoint criticalOperator = criticalOperator from critical_isPositive.isSelfAdjoint.star_eq] at he

def firstMoment (v : Gas) := ‖criticalOperator v‖^2/‖v‖^2
def secondMoment (v : Gas) := ‖squareHeat.val v‖^2/‖v‖^2

/-- The first and second normalized energy moments of a missing wave are strictly ordered. -/
theorem missing_moments (v : MissingWave) :
    0 < firstMoment v.val ∧ firstMoment v.val < 1 ∧ secondMoment v.val < firstMoment v.val := by
  let f := v.val
  have hden : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (missingWave_ne_zero v))
  have hn : criticalOperator f ≠ 0 := fun h => missingWave_ne_zero v (critical_injective (h.trans (map_zero _).symm))
  have hfix : criticalOperator (criticalOperator f) ≠ f := fun h => v.property ⟨criticalOperator f,h⟩
  have h₁ := lt_of_le_of_ne (heat_contraction f) (fun h => hfix (heat_fixed_of_saturation h))
  have h₂ := lt_of_le_of_ne (heat_contraction (criticalOperator f))
    (fun h => hfix (critical_injective (heat_fixed_of_saturation h)))
  exact ⟨div_pos (sq_pos_of_pos (norm_pos_iff.mpr hn)) hden,
    (div_lt_one hden).mpr ((sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₁),
    div_lt_div_of_pos_right ((sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₂) hden⟩

theorem lineLoss_eq_moments (v : Gas) : lineLoss v = 2*secondMoment v-(firstMoment v)^2 := by
  unfold lineLoss secondMoment firstMoment
  ring

/-- Every genuine conserved line omission loses strictly between zero and one unit of fourth trace. -/
theorem line_loss_bounds (v : MissingWave) : 0 < lineLoss v.val ∧ lineLoss v.val < 1 := by
  have hne : (linePropagator v).val ≠ criticalOperator := by
    intro eqn
    have he := (projected_eq_critical_iff (omitLine v.val)).mp eqn
    have hk := omitLine_kills v.val
    rw [he] at hk
    exact missingWave_ne_zero v hk
  have h := (strict_trace_stability_iff (linePropagator v)).mpr hne
  change _ < traceLoss (projected (omitLine v.val)) at h
  rw [traceLoss_omitLine] at h
  refine ⟨lt_of_le_of_lt (by positivity) h,?_⟩
  obtain ⟨_,_,h₂⟩ := missing_moments v
  rw [lineLoss_eq_moments]
  nlinarith only [h₂,sq_nonneg (1-firstMoment v.val)]

#print axioms nonzero_line_conserves_iff
#print axioms missing_moments
#print axioms line_loss_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
