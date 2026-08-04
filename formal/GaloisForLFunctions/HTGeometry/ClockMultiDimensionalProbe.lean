import GaloisForLFunctions.HTGeometry.ClockTubeRealProbeData
import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalProbe

/-!
# Clock probes for potentials coupling several transverse coordinates

The construction closes here in full generality. On Minkowski space of dimension `k + n + 2`, a
potential which depends on the two null coordinates continuously differentiably and on `k` transverse
coordinates analytically — a genuinely coupled dependence in all of them, not a slab, not a separable
product, and not a single transverse direction — admits a clock probe on an open neighbourhood of the
event, normalised to `1` there and nonvanishing on that neighbourhood.

The field is the real part of the solution of the characteristic equation, and the characteristic
equation is exactly the null form of `□ f + V f = 0` with the full transverse Laplacian.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- **The characteristic identity in real form**, with the full transverse Laplacian. -/
theorem probeMulti_characteristic {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} {T : ℝ}
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0)
    {s t : ℝ} {y : Fin k → ℝ} (hs : |s| < T) (ht : |t| < T) :
    probeMultiAb V T s t y + probeMultiAb V T s t y
      = ((∑ i : Fin k, probeMultiCc V T i i s t y)
        + (V s t (realTube y)).re * probeMultiU V T s t y) / 2 := by
  have hstep : clampedTubeStep V T (realTube y) s t
      = ((∑ i : Fin k, cpartial i (cpartial i (tubeSolution V s t)) (realTube y))
        + V s t (realTube y) * tubeSolution V s t (realTube y)) / 4 := by
    rw [clampedTubeStep_eq (le_of_lt hs) (le_of_lt ht)]
    rfl
  have hcc : ∀ i : Fin k, probeMultiCc V T i i s t y
      = (cpartial i (cpartial i (tubeSolution V s t)) (realTube y)).re := by
    intro i
    rw [probeMultiCc, clampedTubeSolution, boxClamp_eq_self (le_of_lt hs),
      boxClamp_eq_self (le_of_lt ht)]
  have hu : probeMultiU V T s t y = (tubeSolution V s t (realTube y)).re := by
    rw [probeMultiU, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  have hmul : (V s t (realTube y) * tubeSolution V s t (realTube y)).re
      = (V s t (realTube y)).re * (tubeSolution V s t (realTube y)).re := by
    rw [Complex.mul_re, hVreal s t y]
    ring
  have hsum : (∑ i : Fin k, cpartial i (cpartial i (tubeSolution V s t)) (realTube y)).re
      = ∑ i : Fin k, probeMultiCc V T i i s t y := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => (hcc i).symm
  have hAb : probeMultiAb V T s t y
      = ((∑ i : Fin k, probeMultiCc V T i i s t y)
        + (V s t (realTube y)).re * probeMultiU V T s t y) / 4 := by
    rw [probeMultiAb, hstep, div_four_re, Complex.add_re, hmul, hsum, ← hu]
  rw [hAb]
  ring

namespace TubeDatum

variable {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- The field of the probe, as a function on Minkowski space of dimension `k + n + 2`. -/
theorem continuous_probeMultiField (n : ℕ) : Continuous (nullMultiLift (probeMultiU V T) n) := by
  rw [nullMultiLift_eq_comp]
  exact hD.continuous_probeMultiU.comp (nullMultiCLM k n).continuous

/-- **Clock probes for potentials coupling several transverse coordinates, in every dimension at
least `k + 2`.** The potential depends on the two null coordinates continuously differentiably and on
the `k` transverse coordinates analytically. -/
theorem exists_clockProbe_nullMulti
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0) (hT : 0 < T) (n : ℕ)
    {x : Fin (k + n + 2) → ℝ} (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    ∃ W : Set (Fin (k + n + 2) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (k + n + 2) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          (nullMultiLift (fun s t y => (V s t (realTube y)).re) n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  have hUcont := hD.continuous_probeMultiField n
  have hnull : nullMultiCLM k n x
      = (((0 : ℝ), (0 : ℝ)), fun i : Fin k => x (transIdx k n i)) := by
    rw [nullMultiCLM_apply, hx0, hx1]
    norm_num
  have hxbox : x ∈ nullMultiBox (clockMultiBox k T) n := by
    rw [mem_nullMultiBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : nullMultiLift (probeMultiU V T) n x = 1 := by
    show probeMultiU V T (x 0 + x 1) (x 0 - x 1) (fun i : Fin k => x (transIdx k n i)) = 1
    rw [hx0, hx1, probeMultiU]
    norm_num
    rw [boxClamp_eq_self (le_of_lt (by simpa using hT) : |(0 : ℝ)| ≤ T)]
    rw [tubeSolution_zero_zero hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
      hD.sideNonneg hD.small (hD.absIm fun i : Fin k => x (transIdx k n i))]
    norm_num
  have hxne : nullMultiLift (probeMultiU V T) n x ≠ 0 := by
    rw [hone]
    exact one_ne_zero
  refine ⟨nullMultiBox (clockMultiBox k T) n ∩ {y | nullMultiLift (probeMultiU V T) n y ≠ 0},
    (isOpen_nullMultiBox (isOpen_clockMultiBox k T) n).inter (isOpen_ne.preimage hUcont),
    ⟨hxbox, hxne⟩, nullMultiLift (probeMultiU V T) n, ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_nullMultiLift hD.isC1OnMulti_probeMultiU
    hD.isC1OnMulti_probeMultiA hD.isC1OnMulti_probeMultiB
    (fun i => hD.isC1OnMulti_probeMultiC i) (fun y hy => hy.1) fun y hy => ?_
  have hybox : nullMultiCLM k n y ∈ clockMultiBox k T := hy.1
  exact probeMulti_characteristic hVreal hybox.1 hybox.2

end TubeDatum

end GaloisForLFunctions.HTGeometry
