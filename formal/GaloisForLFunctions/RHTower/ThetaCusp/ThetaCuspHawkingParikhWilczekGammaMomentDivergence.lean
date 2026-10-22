import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusMomentDetector
import Mathlib.Analysis.SpecificLimits.Normed

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open Filter Topology
noncomputable section

private theorem pwGammaMoment_inverse_factorial_tendsto (w : ℂ) :
    Tendsto (fun k : ℕ => (1/w)^k / ((k+1).factorial:ℂ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => ‖1/w‖^k / (k.factorial:ℝ)) atTop (𝓝 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop ‖1/w‖
  have hb : Tendsto (fun k : ℕ => ‖1/w‖^k / ((k+1).factorial:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity) _ ht
    intro k
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (Nat.factorial_le (by omega : k≤k+1))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_div, norm_pow, Complex.norm_natCast] using hb

/-- The exact signed moments cannot be Taylor coefficients of a convergent series at zero. -/
theorem pwGammaMobiusReciprocalMoment_power_terms_not_tendsto (z : ℂ) {w : ℂ}
    (hw : w≠0) :
    ¬ Tendsto (fun k : ℕ => pwGammaMobiusReciprocalMoment z k*w^k) atTop (𝓝 0) := by
  intro ht
  have hp : Tendsto (fun k : ℕ => (pwGammaMobiusReciprocalMoment z k*w^k)*
      ((1/w)^k/((k+1).factorial:ℂ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.mul (pwGammaMoment_inverse_factorial_tendsto w)
  have he : ∀ k : ℕ, (pwGammaMobiusReciprocalMoment z k*w^k)*
      ((1/w)^k/((k+1).factorial:ℂ)) = pwGammaMobiusReciprocalNormalizedMoment z k := by
    intro k
    rw [pwGammaMobiusReciprocalNormalizedMoment_eq, div_pow, one_pow]
    field_simp
  have hz : Tendsto (pwGammaMobiusReciprocalNormalizedMoment z) atTop (𝓝 0) := hp.congr he
  exact pwGammaMobiusReciprocalCoefficient_zero_ne z
    (tendsto_nhds_unique (pwGammaMobiusReciprocalNormalizedMoment_tendsto z) hz)

theorem pwGammaMobiusReciprocalMoment_power_not_summable (z : ℂ) {w : ℂ}
    (hw : w≠0) :
    ¬ Summable (fun k : ℕ => pwGammaMobiusReciprocalMoment z k*w^k) := by
  intro hs
  exact pwGammaMobiusReciprocalMoment_power_terms_not_tendsto z hw hs.tendsto_atTop_zero

end
end RHTower
