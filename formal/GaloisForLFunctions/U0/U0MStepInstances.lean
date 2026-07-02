/-
# First sub-threshold independence instances

`U0PhiMStepFar.u0_mstep_independence` is unconditional over the whole viable region.  Here it is
instantiated at six concrete parameters of modulus strictly below the sharp threshold
`2 + √2 ≈ 3.414` — the FIRST `u₀`–Böttcher independence theorems below the direction-independent
window bound:

* `b = 3`               (`‖b‖ = 3`,  `unitDisk_avoids_filledJulia_three`);
* five critical-curve slice points at `arg b ≈ 105°, 125°, 140°, 150°, 155°`, each of modulus
  `≈ 3.00` (the square-tree viability certificates `slice_viable_105 … 155`).

Each instance is a single application of the unconditional theorem to the parameter's viability
certificate — no per-parameter analytic work.
-/
import GaloisForLFunctions.U0.U0PhiMStepFar
import GaloisForLFunctions.U0.U0DichotomyWitness
import GaloisForLFunctions.U0.U0CriticalCurveSlice

open Complex Bottcher
open U0PhiMStepFar U0DichotomyWitness U0DichotomySlice

namespace U0MStepInstances

/-- **m-step independence at `b = 3`** — modulus `3 < 2 + √2`, the escape parameter of the
dichotomy witness.  `u₀` and `ψ = bottcherCoord ∘ f_3^[N]` are algebraically independent over
`ℂ(z)`. -/
theorem u0_mstep_independence_three : MStepIndependence (3 : ℂ) :=
  u0_mstep_independence (fun _ hz => unitDisk_avoids_filledJulia_three hz)

/-- **m-step independence at the `105°` slice point** `b = ⟨−7/9, 29/10⟩` (`‖b‖ ≈ 3.00`). -/
theorem u0_mstep_independence_slice_105 : MStepIndependence (⟨-7/9, 29/10⟩ : ℂ) :=
  u0_mstep_independence slice_viable_105

/-- **m-step independence at the `125°` slice point** `b = ⟨−12/7, 22/9⟩` (`‖b‖ ≈ 2.99`). -/
theorem u0_mstep_independence_slice_125 : MStepIndependence (⟨-12/7, 22/9⟩ : ℂ) :=
  u0_mstep_independence slice_viable_125

/-- **m-step independence at the `140°` slice point** `b = ⟨−23/10, 27/14⟩` (`‖b‖ ≈ 3.00`). -/
theorem u0_mstep_independence_slice_140 : MStepIndependence (⟨-23/10, 27/14⟩ : ℂ) :=
  u0_mstep_independence slice_viable_140

/-- **m-step independence at the `150°` slice point** `b = ⟨−13/5, 3/2⟩` (`‖b‖ ≈ 3.00`). -/
theorem u0_mstep_independence_slice_150 : MStepIndependence (⟨-13/5, 3/2⟩ : ℂ) :=
  u0_mstep_independence slice_viable_150

/-- **m-step independence at the `155°` slice point** `b = ⟨−273/100, 156/125⟩` (`‖b‖ ≈ 3.00`). -/
theorem u0_mstep_independence_slice_155 : MStepIndependence (⟨-273/100, 156/125⟩ : ℂ) :=
  u0_mstep_independence slice_viable_155

/-- **The six sub-threshold instances, bundled.**  Independence holds at `b = 3` and at the five
certified critical-curve slice points, all of modulus strictly below `2 + √2`. -/
theorem u0_mstep_independence_subthreshold :
    MStepIndependence (3 : ℂ) ∧
    MStepIndependence (⟨-7/9, 29/10⟩ : ℂ) ∧
    MStepIndependence (⟨-12/7, 22/9⟩ : ℂ) ∧
    MStepIndependence (⟨-23/10, 27/14⟩ : ℂ) ∧
    MStepIndependence (⟨-13/5, 3/2⟩ : ℂ) ∧
    MStepIndependence (⟨-273/100, 156/125⟩ : ℂ) :=
  ⟨u0_mstep_independence_three, u0_mstep_independence_slice_105, u0_mstep_independence_slice_125,
    u0_mstep_independence_slice_140, u0_mstep_independence_slice_150,
    u0_mstep_independence_slice_155⟩

end U0MStepInstances
