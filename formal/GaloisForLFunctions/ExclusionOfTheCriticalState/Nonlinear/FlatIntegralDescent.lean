import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDifferential
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatDescent
import GaloisForLFunctions.RHTower.CHMDJumpGraphContractions

/-!
# Strong convergence of the flat L² gradient iteration

The unit gradient iteration converges strongly to the negative part of
every initial profile, on every measure space. Pointwise monotonicity
provides a square-integrable error bound, so scalar convergence upgrades
to convergence in the actual L² quotient. Infinite flatness does not
prevent convergence to the canonical energy minimizer.
-/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem negativePart_lipschitz : LipschitzWith 1 (fun t : ℝ => min t 0) :=
  LipschitzWith.id.min_const 0

/-- The pointwise negative-part projection in the actual L² space. -/
def negativePartLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  negativePart_lipschitz.compLp (min_self 0) f

theorem negativePartLp_ae (f : Lp ℝ 2 μ) :
    negativePartLp f =ᵐ[μ] fun x => min (f x) 0 :=
  negativePart_lipschitz.coeFn_compLp (min_self 0) f

/-- One unit gradient step. -/
def descentLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ := f - gradientLp f

theorem descentLp_ae (f : Lp ℝ 2 μ) :
    descentLp f =ᵐ[μ] fun x => descent (f x) := by
  filter_upwards [Lp.coeFn_sub f (gradientLp f),
    gradient_contraction.coeFn_compLp gradient_zero f] with x hx hg
  change (f - gradientLp f) x = _
  rw [hx]
  change f x - (gradient_contraction.compLp gradient_zero f) x = _
  rw [hg]
  rfl

/-- The nonlinear quotient iteration agrees almost everywhere with scalar descent. -/
theorem descentLp_iterate_ae (f : Lp ℝ 2 μ) (n : ℕ) :
    descentLp^[n] f =ᵐ[μ] fun x => descent^[n] (f x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    filter_upwards [descentLp_ae (descentLp^[n] f), ih] with x hx hi
    rw [hx, hi, Function.iterate_succ_apply']

private theorem scalar_error_bound (t : ℝ) (n : ℕ) :
    (descent^[n] t - min t 0) ^ 2 ≤ t ^ 2 := by
  have hb := descent_iterate_bounds t n
  by_cases ht : t ≤ 0
  · rw [min_eq_left ht] at hb ⊢
    rw [le_antisymm hb.2 hb.1, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact sq_nonneg t
  · rw [min_eq_right (le_of_not_ge ht)] at hb ⊢
    rw [sub_zero]
    nlinarith only [mul_nonneg hb.1 (sub_nonneg.mpr hb.2),
      mul_nonneg (le_of_not_ge ht) (sub_nonneg.mpr hb.2)]

/-- Every starting profile converges in L² norm to its negative part. -/
theorem descentLp_tendsto_negativePart (f : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => descentLp^[n] f) atTop (𝓝 (negativePartLp f)) := by
  have h := RHTower.CHMDClosedJump.toLp_tendsto_of_sq_dom
    (fun n => Lp.memLp (descentLp^[n] f)) (Lp.memLp (negativePartLp f))
    (Lp.memLp f).integrable_sq ?_ ?_
  · simpa only [Lp.toLp_coeFn] using h
  · intro n
    filter_upwards [descentLp_iterate_ae f n, negativePartLp_ae f] with x hn hp
    rw [hn, hp]
    exact scalar_error_bound (f x) n
  · filter_upwards [ae_all_iff.mpr (fun n => descentLp_iterate_ae f n),
      negativePartLp_ae f] with x hx hp
    simpa only [hx, hp] using descent_tendsto_negative_part (f x)

/-- The limit is a fixed point of the actual Hilbert-space gradient iteration. -/
theorem negativePartLp_fixed (f : Lp ℝ 2 μ) :
    descentLp (negativePartLp f) = negativePartLp f := by
  apply Lp.ext
  filter_upwards [descentLp_ae (negativePartLp f), negativePartLp_ae f] with x hx hp
  rw [hx, hp]
  exact (descent_fixed_iff _).mpr (min_le_right _ _)

/-- The strong limit minimizes the integral energy. -/
theorem negativePartLp_minimizes (f g : Lp ℝ 2 μ) :
    integralEnergy (negativePartLp f) ≤ integralEnergy g := by
  have hz : integralEnergy (negativePartLp f) = 0 := by
    unfold integralEnergy
    calc
      (∫ x, potential (negativePartLp f x) ∂μ) = ∫ _, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [negativePartLp_ae f] with x hx
        rw [hx]
        exact (potential_zero_iff _).mpr (min_le_right _ _)
      _ = 0 := integral_zero _ _
  rw [hz]
  exact (integral_energy_bounds g).1

#print axioms descentLp_iterate_ae
#print axioms descentLp_tendsto_negativePart
#print axioms negativePartLp_fixed
#print axioms negativePartLp_minimizes
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
