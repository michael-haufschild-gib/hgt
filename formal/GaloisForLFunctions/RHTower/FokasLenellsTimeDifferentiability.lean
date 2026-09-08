import GaloisForLFunctions.HTGeometry.FokasLenellsInverseFrequency
import GaloisForLFunctions.HTGeometry.L2DominatedDerivative
import GaloisForLFunctions.RHTower.FokasLenellsParameterContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Strong time differentiation of the actual scattering jump

The linear zero-frequency cancellation puts both genuine scattering symbols
in the singular time-generator domain. Their pointwise time derivatives have
one square-integrable envelope independent of time and position. The corpus's
dominated L² derivative theorem turns the formal phase differentiation into an
actual Hilbert-space derivative, continuously depending on both physical
parameters. Thus the two direct-scattering jump channels are genuinely C¹ in
time, with all smallness and origin cancellation proved internally.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual time derivative multiplies the two inverse-frequency channels by opposite half-imaginary factors. -/
def directTimeSymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (if reverse then -I/2 else I/2)*regularInverseFrequencyJump q t x reverse z

private theorem phase_channel_hasDerivAt (r t x z : ℝ) (c : ℂ) :
    HasDerivAt (fun s : ℝ => FDNLS.staggerPhase r (z*x-s/(4*z))*c)
      ((I*(r:ℂ)/4)*(FDNLS.staggerPhase r (z*x-t/(4*z))*c/(z:ℂ))) t := by
  have ha : HasDerivAt (fun s : ℝ => z*x-s/(4*z)) (-(1/(4*z))) t := by
    simpa only [id_eq,zero_sub] using (hasDerivAt_const t (z*x)).fun_sub ((hasDerivAt_id t).div_const (4*z))
  have hd := (((ha.ofReal_comp).const_mul (-(I*(r:ℂ)))).cexp).mul_const c
  convert! hd using 1
  unfold FDNLS.staggerPhase
  push_cast
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- Differentiation of the actual time phase is valid at every real frequency, including zero. -/
theorem directSymbol_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    HasDerivAt (fun s => directSymbol q s x reverse z) (directTimeSymbol q t x reverse z) t := by
  cases reverse
  · change HasDerivAt (fun s => FDNLS.staggerPhase 2 (z*x-s/(4*z))*
      regularReflectionCoefficient (globalSmallScatteringPotential q) z)
      ((I/2)*(FDNLS.staggerPhase 2 (z*x-t/(4*z))*
        regularReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ))) t
    convert! phase_channel_hasDerivAt 2 t x z (regularReflectionCoefficient (globalSmallScatteringPotential q) z) using 1
    push_cast
    ring
  · change HasDerivAt (fun s => FDNLS.staggerPhase (-2) (z*x-s/(4*z))*
      regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z)
      ((-I/2)*(FDNLS.staggerPhase (-2) (z*x-t/(4*z))*
        regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ))) t
    convert! phase_channel_hasDerivAt (-2) t x z (regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z) using 1
    push_cast
    ring

/-- The exact derivative norm is independent of time and position. -/
theorem directTimeSymbol_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directTimeSymbol q t x reverse z‖ = (1/2 : ℝ)*‖regularInverseFrequencyReflection q reverse z‖ := by
  cases reverse <;> norm_num [directTimeSymbol,norm_mul,norm_div,regularInverseFrequencyJump_norm]

theorem directSymbol_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (directSymbol q t x reverse) 2 volume := by
  cases reverse
  · exact (globalSmall_regularJump_memLp q t x).1
  · exact (globalSmall_regularJump_memLp q t x).2

/-- The actual time derivative belongs to L² for every physical parameter. -/
theorem directTimeSymbol_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (directTimeSymbol q t x reverse) 2 volume :=
  (regularInverseFrequencyJump_memLp q t x reverse).const_mul (if reverse then -I/2 else I/2)

/-- The actual reflection channel on the corpus's L² carrier. -/
def directSymbolL2 (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 :=
  (directSymbol_memLp q t x reverse).toLp (directSymbol q t x reverse)

/-- The genuine L² derivative of the time-dependent direct-scattering channel. -/
def directTimeSymbolL2 (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 :=
  (directTimeSymbol_memLp q t x reverse).toLp (directTimeSymbol q t x reverse)

/-- Dominated Hilbert-space differentiation validates the singular time generator on actual scattering data. -/
theorem directSymbolL2_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun s => directSymbolL2 q s x reverse) (directTimeSymbolL2 q t x reverse) t := by
  exact hasDerivAt_toLp_two_of_dominated volume (fun s => directSymbol q s x reverse)
    (fun s => directTimeSymbol q s x reverse)
    (fun s => directSymbol_memLp q s x reverse) (fun s => directTimeSymbol_memLp q s x reverse)
    (fun z => (1/2 : ℝ)*‖regularInverseFrequencyReflection q reverse z‖)
    ((regularInverseFrequencyReflection_memLp q reverse).norm.const_mul (1/2:ℝ))
    (Eventually.of_forall fun z s => directSymbol_time_hasDerivAt q s x reverse z)
    (Eventually.of_forall fun z s => (directTimeSymbol_norm q s x reverse z).le) t

/-- At each spectral point the derivative itself is jointly continuous in both physical parameters. -/
theorem continuous_directTimeSymbol_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ => directTimeSymbol q p.1 p.2 reverse z) := by
  change Continuous (fun p : ℝ × ℝ => (if reverse then -I/2 else I/2)*(directSymbol q p.1 p.2 reverse z/(z:ℂ)))
  exact continuous_const.mul ((continuous_directSymbol_parameters q reverse z).div_const (z:ℂ))

/-- The derivative is jointly continuous in time and position in the actual L² norm. -/
theorem continuous_directTimeSymbolL2_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : ℝ × ℝ => directTimeSymbolL2 q p.1 p.2 reverse) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => directTimeSymbol q p.1 p.2 reverse)
    (fun p => directTimeSymbol_memLp q p.1 p.2 reverse)
    (fun z => (1/2 : ℝ)*‖regularInverseFrequencyReflection q reverse z‖)
    ((regularInverseFrequencyReflection_memLp q reverse).norm.const_mul (1/2:ℝ))
  · intro p
    exact Eventually.of_forall fun z => (directTimeSymbol_norm q p.1 p.2 reverse z).le
  · exact Eventually.of_forall (continuous_directTimeSymbol_parameters q reverse)

/-- The actual direct-scattering jump channels are C¹ in time, not merely pointwise differentiable. -/
theorem directSymbolL2_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) :
    ContDiff ℝ 1 (fun t => directSymbolL2 q t x reverse) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directSymbolL2_time_hasDerivAt q t x reverse).differentiableAt,?_⟩
  have he : deriv (fun t => directSymbolL2 q t x reverse) = fun t => directTimeSymbolL2 q t x reverse :=
    funext fun t => (directSymbolL2_time_hasDerivAt q t x reverse).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directTimeSymbolL2_parameters q reverse).comp hc
  exact hh

/-- The same cancellation also bounds the time-derivative multiplier uniformly in space and time. -/
theorem directTimeSymbol_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directTimeSymbol q t x reverse z‖ ≤ (1/2 : ℝ)*regularReflectionFrequencyBudget q := by
  rw [directTimeSymbol_norm]
  exact mul_le_mul_of_nonneg_left (regularInverseFrequencyReflection_bound q reverse z) (by positivity)


/-- The time generator bound gives a uniform Lipschitz estimate for every actual jump symbol. -/
theorem directSymbol_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSymbol q t x reverse z-directSymbol q s x reverse z‖ ≤
      ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directSymbol_time_hasDerivAt q r x reverse z).hasDerivWithinAt)
    (fun r _ => directTimeSymbol_bound q r x reverse z)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- The actual bounded multiplier is Lipschitz in time on every L² vector. -/
theorem directMultiplier_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) (u : SoninL2) :
    ‖directMultiplier q t x reverse u-directMultiplier q s x reverse u‖ ≤
      (((1/2 : ℝ)*regularReflectionFrequencyBudget q)*|t-s|)*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := u)
  filter_upwards [Lp.coeFn_sub (directMultiplier q t x reverse u) (directMultiplier q s x reverse u),
    directMultiplier_ae q t x reverse u,directMultiplier_ae q s x reverse u] with z he ht hs
  rw [he,Pi.sub_apply,ht,hs,← sub_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right (directSymbol_time_bound q t s x reverse z) (norm_nonneg _)

/-- Zero-frequency cancellation upgrades time continuity of the actual multiplier to operator-norm Lipschitz continuity. -/
theorem norm_directMultiplier_time_sub_le (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (reverse : Bool) :
    ‖directMultiplier q t x reverse-directMultiplier q s x reverse‖ ≤
      ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*|t-s| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (abs_nonneg (t-s))
  · exact directMultiplier_time_bound q t s x reverse

end
end RHTower.FokasLenells
