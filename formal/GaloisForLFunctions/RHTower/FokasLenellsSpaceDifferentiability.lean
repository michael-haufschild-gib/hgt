import GaloisForLFunctions.HTGeometry.FokasLenellsWeightedData
import GaloisForLFunctions.RHTower.FokasLenellsTimeDifferentiability

/-!
# Strong spatial differentiation of actual reflection data

The proved second spectral-power decay places the actual reflection data
in the spatial generator domain. Dominated L² differentiation validates
both oscillatory channel derivatives. Their derivative norms are unchanged
by either physical parameter, and the derivative multiplier is uniformly
bounded by the first spectral-power estimate.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def directSpaceSymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (if reverse then 2*I else -2*I)*regularSpectralJump q t x reverse z

private theorem phase_spatial_channel_hasDerivAt (r t x z : ℝ) (c : ℂ) :
    HasDerivAt (fun y : ℝ => FDNLS.staggerPhase r (z*y-t/(4*z))*c)
      ((-I*(r : ℂ))*((z : ℂ)*(FDNLS.staggerPhase r (z*x-t/(4*z))*c))) x := by
  have ha : HasDerivAt (fun y : ℝ => z*y-t/(4*z)) z x := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul z).sub_const (t/(4*z))
  have hd := (((ha.ofReal_comp).const_mul (-(I*(r : ℂ)))).cexp).mul_const c
  convert! hd using 1
  unfold FDNLS.staggerPhase
  push_cast
  ring

/-- The spatial derivative of either actual jump channel exists at every spectral point, including zero. -/
theorem directSymbol_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    HasDerivAt (fun y => directSymbol q t y reverse z) (directSpaceSymbol q t x reverse z) x := by
  cases reverse
  · change HasDerivAt (fun y => FDNLS.staggerPhase 2 (z*y-t/(4*z))*regularReflectionCoefficient (globalSmallScatteringPotential q) z)
      ((-2*I)*((z : ℂ)*(FDNLS.staggerPhase 2 (z*x-t/(4*z))*regularReflectionCoefficient (globalSmallScatteringPotential q) z))) x
    convert! phase_spatial_channel_hasDerivAt 2 t x z (regularReflectionCoefficient (globalSmallScatteringPotential q) z) using 1
    push_cast
    ring
  · change HasDerivAt (fun y => FDNLS.staggerPhase (-2) (z*y-t/(4*z))*regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z)
      ((2*I)*((z : ℂ)*(FDNLS.staggerPhase (-2) (z*x-t/(4*z))*regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z))) x
    convert! phase_spatial_channel_hasDerivAt (-2) t x z (regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z) using 1
    push_cast
    ring

/-- The exact spatial derivative norm is independent of both physical parameters. -/
theorem directSpaceSymbol_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSpaceSymbol q t x reverse z‖ = 2*‖regularSpectralReflection q reverse z‖ := by
  cases reverse <;> norm_num [directSpaceSymbol,norm_mul,regularSpectralJump_norm]

theorem directSpaceSymbol_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (directSpaceSymbol q t x reverse) :=
  measurable_const.mul (regularSpectralJump_measurable q t x reverse)

theorem directSpaceSymbol_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (directSpaceSymbol q t x reverse) 2 volume :=
  (regularSpectralJump_memLp q t x reverse).const_mul (if reverse then 2*I else -2*I)

def directSpaceSymbolL2 (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 :=
  (directSpaceSymbol_memLp q t x reverse).toLp (directSpaceSymbol q t x reverse)

/-- The formal spatial generator is the genuine strong derivative on actual L² scattering data. -/
theorem directSymbolL2_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun y => directSymbolL2 q t y reverse) (directSpaceSymbolL2 q t x reverse) x := by
  exact hasDerivAt_toLp_two_of_dominated volume (fun y => directSymbol q t y reverse)
    (fun y => directSpaceSymbol q t y reverse)
    (fun y => directSymbol_memLp q t y reverse) (fun y => directSpaceSymbol_memLp q t y reverse)
    (fun z => 2*‖regularSpectralReflection q reverse z‖) ((regularSpectralReflection_memLp q reverse).norm.const_mul 2)
    (Eventually.of_forall fun z y => directSymbol_space_hasDerivAt q t y reverse z)
    (Eventually.of_forall fun z y => (directSpaceSymbol_norm q t y reverse z).le) x

theorem continuous_directSpaceSymbol_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ => directSpaceSymbol q p.1 p.2 reverse z) := by
  change Continuous (fun p : ℝ × ℝ => (if reverse then 2*I else -2*I)*((z : ℂ)*directSymbol q p.1 p.2 reverse z))
  exact continuous_const.mul (continuous_const.mul (continuous_directSymbol_parameters q reverse z))

/-- The actual L² spatial derivative varies jointly continuously in time and position. -/
theorem continuous_directSpaceSymbolL2_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : ℝ × ℝ => directSpaceSymbolL2 q p.1 p.2 reverse) := by
  apply continuous_toLp_two_of_dominated volume (fun p : ℝ × ℝ => directSpaceSymbol q p.1 p.2 reverse)
    (fun p => directSpaceSymbol_memLp q p.1 p.2 reverse)
    (fun z => 2*‖regularSpectralReflection q reverse z‖) ((regularSpectralReflection_memLp q reverse).norm.const_mul 2)
  · intro p
    exact Eventually.of_forall fun z => (directSpaceSymbol_norm q p.1 p.2 reverse z).le
  · exact Eventually.of_forall (continuous_directSpaceSymbol_parameters q reverse)

/-- Actual jump channels are C¹ in the spatial variable in L². -/
theorem directSymbolL2_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (reverse : Bool) :
    ContDiff ℝ 1 (fun x => directSymbolL2 q t x reverse) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directSymbolL2_space_hasDerivAt q t x reverse).differentiableAt,?_⟩
  have he : deriv (fun x => directSymbolL2 q t x reverse) = fun x => directSpaceSymbolL2 q t x reverse :=
    funext fun x => (directSymbolL2_space_hasDerivAt q t x reverse).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directSpaceSymbolL2_parameters q reverse).comp hc
  exact hh

/-- The spatial generator multiplier is uniformly bounded on all L² vectors. -/
theorem directSpaceSymbol_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSpaceSymbol q t x reverse z‖ ≤ 2*regularReflectionDecay q reverse := by
  rw [directSpaceSymbol_norm]
  exact mul_le_mul_of_nonneg_left (regularSpectralReflection_bound q reverse z) (by positivity)

/-- One nonnegative constant controls both spatial derivative channels. -/
def directSpaceOperatorBudget (q : SchwartzMap ℝ ℂ) : ℝ :=
  2*(regularReflectionDecay q false+regularReflectionDecay q true)

theorem directSpaceOperatorBudget_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ directSpaceOperatorBudget q := by
  unfold directSpaceOperatorBudget
  positivity [regularReflectionDecay_nonneg q false,regularReflectionDecay_nonneg q true]

theorem directSpaceSymbol_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSpaceSymbol q t x reverse z‖ ≤ directSpaceOperatorBudget q := by
  have hb := directSpaceSymbol_bound q t x reverse z
  unfold directSpaceOperatorBudget
  cases reverse <;> linarith [regularReflectionDecay_nonneg q false,regularReflectionDecay_nonneg q true]

/-- Actual jump symbols vary Lipschitz continuously in position, uniformly over real spectrum. -/
theorem directSymbol_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSymbol q t x reverse z-directSymbol q t y reverse z‖ ≤ directSpaceOperatorBudget q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directSymbol_space_hasDerivAt q t r reverse z).hasDerivWithinAt)
    (fun r _ => directSpaceSymbol_uniform_bound q t r reverse z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

end
end RHTower.FokasLenells
