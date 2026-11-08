import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetAverage

/-!
# Entire large-height Mellin tail

Exponential decay of the actual averaged heat source makes its large-height Mellin tail entire.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The large-height part of the actual averaged scalar heat source. -/
def narainMeanTailSource (Y Z : Height) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (narainScalarHeatAverage Y Z)

/-- The large-height Mellin tail of the actual source. -/
def narainMeanMellinTail (Y Z : Height) : ℂ → ℂ :=
  mellin (narainMeanTailSource Y Z)

private theorem tailSource_clamped (Y Z : Height) :
    narainMeanTailSource Y Z = (Ioi (1 : ℝ)).indicator
      (fun y => narainScalarHeatAverage Y Z (max 1 y)) := by
  funext y
  by_cases hy : 1 < y
  · simp [narainMeanTailSource, hy, max_eq_right hy.le]
  · simp [narainMeanTailSource, hy]

private theorem continuous_clamped_average (Y Z : Height) :
    Continuous (fun y : ℝ => narainScalarHeatAverage Y Z (max 1 y)) :=
  (continuousOn_narainScalarHeatAverage Y Z).comp_continuous
    (continuous_const.max continuous_id)
    (fun y => zero_lt_one.trans_le (le_max_left 1 y))

/-- Cutting off the positive-height source leaves local integrability everywhere needed by Mellin inversion. -/
theorem locallyIntegrableOn_narainMeanTailSource (Y Z : Height) :
    LocallyIntegrableOn (narainMeanTailSource Y Z) (Ioi 0) := by
  rw [tailSource_clamped]
  exact ((continuous_clamped_average Y Z).locallyIntegrable.indicator
    measurableSet_Ioi).locallyIntegrableOn _

private theorem tailSource_top (Y Z : Height) :
    ∃ c : ℝ, 0 < c ∧ narainMeanTailSource Y Z =O[atTop]
      (fun y : ℝ => Real.exp (-c * y)) := by
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainScalarHeatAverage_exp Y Z
  obtain ⟨C, hC⟩ := htop.bound
  refine ⟨c, hc, IsBigO.of_bound C ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with y hCy hy
  simpa [narainMeanTailSource, hy] using hCy

private theorem tailSource_bot (Y Z : Height) (b : ℝ) :
    narainMeanTailSource Y Z =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with y hy
  simp [narainMeanTailSource, not_lt.mpr hy.le]

/-- Exponential decay makes the actual tail Mellin integral absolutely convergent at every parameter. -/
theorem mellinConvergent_narainMeanTailSource (Y Z : Height) (s : ℂ) :
    MellinConvergent (narainMeanTailSource Y Z) s := by
  obtain ⟨c, hc, htop⟩ := tailSource_top Y Z
  exact mellinConvergent_of_isBigO_rpow_exp hc (locallyIntegrableOn_narainMeanTailSource Y Z)
    htop (tailSource_bot Y Z (s.re - 1)) (by linarith)

/-- The actual large-height tail is entire and therefore cannot cancel arithmetic poles. -/
theorem differentiable_narainMeanMellinTail (Y Z : Height) :
    Differentiable ℂ (narainMeanMellinTail Y Z) := by
  intro s
  obtain ⟨c, hc, htop⟩ := tailSource_top Y Z
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc (locallyIntegrableOn_narainMeanTailSource Y Z)
    htop (tailSource_bot Y Z (s.re - 1)) (by linarith)

#print axioms mellinConvergent_narainMeanTailSource
#print axioms differentiable_narainMeanMellinTail
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
