import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseOperators
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The actual cutoff generator and its exact powers

The bounded reciprocal frequency is a self-adjoint operator; multiplying
by minus i recovers the existing cutoff time generator. C-star norm
identities then determine every power exactly, not merely an upper bound.
-/

open MeasureTheory Complex
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual bounded real frequency as an operator on the existing L2 carrier. -/
def cutoffFrequencyOperator (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := volume)
    (Complex.measurable_ofReal.comp (measurable_cutoffPhaseFrequency a))
    (cutoffPhaseBudget_pos a).le (fun z => by
      simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using abs_cutoffPhaseFrequency_le a z)

/-- The self-adjoint frequency operator uses the actual cutoff reciprocal frequency almost everywhere. -/
theorem cutoffFrequencyOperator_ae (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (cutoffFrequencyOperator a u : ℝ → ℂ) =ᵐ[volume] fun z => (cutoffPhaseFrequency a z : ℂ) * u z :=
  lpBoundedMulCLM_coeFn _ _ _ u

/-- The concrete cutoff frequency operator is self-adjoint. -/
theorem cutoffFrequencyOperator_isSelfAdjoint (a : ℝ) : IsSelfAdjoint (cutoffFrequencyOperator a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',eq_comm,ContinuousLinearMap.eq_adjoint_iff]
  exact lpBoundedMulCLM_inner_general _ _ _ (fun z => by simp)

/-- The existing zero-time generator is precisely minus i times this self-adjoint frequency operator. -/
theorem cutoffEvolutionTimeOperator_zero_eq_frequency (a : ℝ) :
    cutoffEvolutionTimeOperator a 0 = (-I) • cutoffFrequencyOperator a := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffEvolutionTimeOperator_ae a 0 u,
    cutoffFrequencyOperator_ae a u,Lp.coeFn_smul (-I) (cutoffFrequencyOperator a u)] with z h0 h1 h2
  change (cutoffEvolutionTimeOperator a 0 u) z = ((-I) • cutoffFrequencyOperator a u) z
  rw [h0,h2,Pi.smul_apply,h1]
  simp only [cutoffPhaseTimeSymbol,cutoffPhase,zero_mul,Complex.ofReal_zero,neg_zero,
    zero_mul,Complex.exp_zero,mul_one,smul_eq_mul]
  ring

/-- The actual bounded time generator is skew-adjoint. -/
theorem star_cutoffEvolutionTimeOperator_zero (a : ℝ) :
    star (cutoffEvolutionTimeOperator a 0) = -cutoffEvolutionTimeOperator a 0 := by
  rw [cutoffEvolutionTimeOperator_zero_eq_frequency,star_smul,
    (cutoffFrequencyOperator_isSelfAdjoint a).star_eq]
  simp

/-- The self-adjoint frequency has exactly the cutoff budget as norm. -/
theorem norm_cutoffFrequencyOperator (a : ℝ) :
    ‖cutoffFrequencyOperator a‖ = cutoffPhaseBudget a := by
  have h := norm_cutoffEvolutionTimeOperator a 0
  rw [cutoffEvolutionTimeOperator_zero_eq_frequency,norm_smul,norm_neg,norm_I,one_mul] at h
  exact h

private theorem selfAdjoint_norm_pow {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormOneClass A] (x : A) (hx : IsSelfAdjoint x) (n : ℕ) : ‖x^n‖ = ‖x‖^n := by
  by_cases hx0 : ‖x‖ = 0
  · have he : x = 0 := norm_eq_zero.mp hx0
    subst x
    cases n <;> simp
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
  have hle : n ≤ 2^n := Nat.lt_two_pow_self.le
  have hpow : ‖x^n‖ * ‖x‖^(2^n-n) ≥ ‖x‖^(2^n) := by
    calc
      _ ≥ ‖x^n‖ * ‖x^(2^n-n)‖ := mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _)
      _ ≥ ‖x^n * x^(2^n-n)‖ := norm_mul_le _ _
      _ = ‖x^(2^n)‖ := by rw [← pow_add,Nat.add_sub_of_le hle]
      _ = _ := hx.norm_pow_two_pow n
  apply le_antisymm (norm_pow_le _ _)
  apply le_of_mul_le_mul_right (a := ‖x‖^(2^n-n)) ?_ (pow_pos hxpos _)
  rwa [← pow_add,Nat.add_sub_of_le hle]

/-- Every natural power of the actual self-adjoint frequency has its exact expected norm. -/
theorem norm_cutoffFrequencyOperator_pow (a : ℝ) (n : ℕ) :
    ‖cutoffFrequencyOperator a ^ n‖ = cutoffPhaseBudget a ^ n := by
  rw [selfAdjoint_norm_pow _ (cutoffFrequencyOperator_isSelfAdjoint a),norm_cutoffFrequencyOperator]

/-- Every power of the actual skew-adjoint time generator has the sharp cutoff norm. -/
theorem norm_cutoffEvolutionTimeOperator_zero_pow (a : ℝ) (n : ℕ) :
    ‖cutoffEvolutionTimeOperator a 0 ^ n‖ = cutoffPhaseBudget a ^ n := by
  rw [cutoffEvolutionTimeOperator_zero_eq_frequency,smul_pow,norm_smul,
    norm_pow,norm_neg,norm_I,one_pow,one_mul,norm_cutoffFrequencyOperator_pow]

/-- At every time, the actual derivative factors through the same bounded zero-time generator. -/
theorem cutoffEvolutionTimeOperator_eq_generator_comp (a t : ℝ) :
    cutoffEvolutionTimeOperator a t = (cutoffEvolutionTimeOperator a 0).comp (cutoffEvolution a t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [cutoffEvolutionTimeOperator_ae a t u,
    cutoffEvolutionTimeOperator_ae a 0 (cutoffEvolution a t u),cutoffEvolution_ae a t u] with z h0 h1 h2
  change (cutoffEvolutionTimeOperator a t u) z = (cutoffEvolutionTimeOperator a 0 (cutoffEvolution a t u)) z
  rw [h0,h1,h2]
  simp only [cutoffPhaseTimeSymbol,cutoffPhase,zero_mul,Complex.ofReal_zero,neg_zero,
    zero_mul,Complex.exp_zero,mul_one]
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
