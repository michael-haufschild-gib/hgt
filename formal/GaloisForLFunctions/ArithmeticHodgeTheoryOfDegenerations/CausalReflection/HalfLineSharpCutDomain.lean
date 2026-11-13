import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaContractions
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineTerminalTruncation
import GaloisForLFunctions.RHTower.CHMDSharpSpatialCut

/-!
# Sharp cuts in the actual half-line domain

The stationary Gamma crossing operator preserves sharp half-line cuts on
the full jump domain. The two-way Gamma/jump bridge transfers this to the
actual weighted domain. Interval restrictions and terminal collars follow
without a boundedness or boundary-regularity premise.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CHMDDoobGraph

/-- The iterated finite Gamma jump energy is also integrable on the product jump space. -/
theorem CriticalHalfLineEnergyDomain.integrable_stationaryJump {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (stationaryJump F) archBase := by
  have hm : Measurable (stationaryJump F) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
      ((measurable_difference hF.meas).pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => by
      have hd := hF.memLp_real.sub
        (hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h))
      have hs := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
      simp only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, sq_abs] at hs
      exact hs.const_mul (archLevyDensity h)
  · apply hF.integrableOn_levyIntegrand.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    change (archLevyDensity h * ∫ u, (F u - F (u + h)) ^ 2) =
      ∫ u, ‖stationaryJump F (h, u)‖
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun u =>
      (Real.norm_of_nonneg
        (mul_nonneg (archLevyDensity_pos hh).le (sq_nonneg (F u - F (u + h))))).symm

/-- Every sharp lower half-line cut preserves the full actual energy domain. -/
theorem CriticalHalfLineEnergyDomain.indicator_Iio {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (c : ℝ) :
    CriticalHalfLineEnergyDomain ((Iio c).indicator F) := by
  have hi := hF.integrable.indicator measurableSet_Iio
  have h2 := hF.memLp_real.indicator measurableSet_Iio
  have hj := integrable_stationary_outer
    (integrable_stationaryJump_indicator_Iio c hF.meas hF.memLp_real
      hF.integrable_stationaryJump)
  refine ⟨hF.meas.indicator measurableSet_Iio, hi, ?_, ?_, ?_,
    integrable_gammaBracket_of_levyIntegrand hi h2 hj⟩
  · apply (hF.sq.indicator measurableSet_Iio).congr
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Iio c
      · simp only [indicator_of_mem hu]
      · simp only [indicator_of_notMem hu, zero_pow two_ne_zero]
  · apply (hF.exponential.indicator measurableSet_Iio).congr
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Iio c
      · simp only [indicator_of_mem hu]
      · simp only [indicator_of_notMem hu, zero_pow two_ne_zero, zero_mul]
  · intro u hu
    by_cases hc : u ∈ Iio c
    · rw [indicator_of_mem hc, hF.support u hu]
    · rw [indicator_of_notMem hc]

/-- Two sharp half-line cuts give every bounded interval restriction. -/
theorem CriticalHalfLineEnergyDomain.indicator_Ico {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (lo hi : ℝ) :
    CriticalHalfLineEnergyDomain ((Ico lo hi).indicator F) := by
  have hd := (hF.add_const_mul (hF.indicator_Iio lo) (-1)).indicator_Iio hi
  have he : (Iio hi).indicator (fun u => F u + -1 * (Iio lo).indicator F u) =
      (Ico lo hi).indicator F := by
    funext u
    by_cases hlo : u < lo <;> by_cases hhi : u < hi
    · rw [indicator_of_mem hhi, indicator_of_mem hlo, neg_one_mul, add_neg_cancel,
        indicator_of_notMem (show u ∉ Ico lo hi from fun hu => (not_le.mpr hlo) hu.1)]
    · rw [indicator_of_notMem hhi,
        indicator_of_notMem (show u ∉ Ico lo hi from fun hu => hhi hu.2)]
    · rw [indicator_of_mem hhi, indicator_of_notMem hlo,
        indicator_of_mem (show u ∈ Ico lo hi from ⟨le_of_not_gt hlo, hhi⟩),
        mul_zero, add_zero]
    · rw [indicator_of_notMem hhi,
        indicator_of_notMem (show u ∉ Ico lo hi from fun hu => hhi hu.2)]
  rwa [he] at hd

/-- Terminal collars are legitimate tests in the actual weak equation. -/
theorem CriticalHalfLineEnergyDomain.terminalCut {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (h : ℝ) :
    CriticalHalfLineEnergyDomain (halfLineTerminalCut h F) := by
  have he : halfLineTerminalCut h F = (Ico (-h) 0).indicator F := by
    funext u
    by_cases hu : u = 0
    · subst u
      simp only [halfLineTerminalCut, hF.support 0 le_rfl, indicator_apply,
        ite_self]
    · have hm : u ∈ Icc (-h) 0 ↔ u ∈ Ico (-h) 0 :=
        ⟨fun hx => ⟨hx.1, lt_of_le_of_ne hx.2 hu⟩, fun hx => ⟨hx.1, hx.2.le⟩⟩
      simp only [halfLineTerminalCut, indicator_apply, hm]
  rw [he]
  exact hF.indicator_Ico (-h) 0

#print axioms CriticalHalfLineEnergyDomain.integrable_stationaryJump
#print axioms CriticalHalfLineEnergyDomain.indicator_Iio
#print axioms CriticalHalfLineEnergyDomain.indicator_Ico
#print axioms CriticalHalfLineEnergyDomain.terminalCut
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
