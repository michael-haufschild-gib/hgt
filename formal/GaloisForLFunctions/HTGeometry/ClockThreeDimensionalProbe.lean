import GaloisForLFunctions.HTGeometry.ClockRealProbeData

/-!
# Clock probes for potentials with coupled transverse dependence

The construction closes here. On Minkowski space of dimension `n + 3`, a potential which depends on
the two null coordinates continuously differentiably and on one transverse coordinate analytically —
a genuinely coupled dependence, not a slab and not a separable product — admits a clock probe on an
open neighbourhood of the event, normalised to `1` there and nonvanishing on that neighbourhood.

The field is the real part of the solution of the characteristic equation, and the characteristic
equation is exactly the null form of `□ f + V f = 0`. Only the potential has to be real on the real
transverse axis; the solution is not required to be, because taking the real part is a continuous
linear map and `re(V·u) = (re V)·(re u)` as soon as `V` is real.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The real part of a quarter is a quarter of the real part. -/
theorem div_four_re (z : ℂ) : (z / 4).re = z.re / 4 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq_apply]
  ring

/-- **The characteristic identity in real form.** -/
theorem probe_characteristic {V : ℝ → ℝ → ℂ → ℂ} {T : ℝ}
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0)
    {s t w : ℝ} (hs : |s| < T) (ht : |t| < T) :
    probeAb V T s t w + probeAb V T s t w
      = (probeCc V T s t w + (V s t ((w : ℝ) : ℂ)).re * probeU V T s t w) / 2 := by
  have hstep : clampedStep V T ((w : ℝ) : ℂ) s t
      = (deriv (deriv (clockSolution V s t)) ((w : ℝ) : ℂ)
        + V s t ((w : ℝ) : ℂ) * clockSolution V s t ((w : ℝ) : ℂ)) / 4 := by
    rw [clampedStep_eq (le_of_lt hs) (le_of_lt ht)]
    rfl
  have hcc : probeCc V T s t w = (deriv (deriv (clockSolution V s t)) ((w : ℝ) : ℂ)).re := by
    rw [probeCc, clampedSolution, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  have hu : probeU V T s t w = (clockSolution V s t ((w : ℝ) : ℂ)).re := by
    rw [probeU, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  have hmul : (V s t ((w : ℝ) : ℂ) * clockSolution V s t ((w : ℝ) : ℂ)).re
      = (V s t ((w : ℝ) : ℂ)).re * (clockSolution V s t ((w : ℝ) : ℂ)).re := by
    rw [Complex.mul_re, hVreal s t w]
    ring
  have hAb : probeAb V T s t w
      = (probeCc V T s t w + (V s t ((w : ℝ) : ℂ)).re * probeU V T s t w) / 4 := by
    rw [probeAb, hstep, div_four_re, Complex.add_re, hmul, ← hcc, ← hu]
  rw [hAb]
  ring

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- The field of the probe, as a function on Minkowski space of dimension `n + 3`. -/
theorem continuous_probeField (n : ℕ) : Continuous (nullTransLift (probeU V T) n) := by
  rw [nullTransLift_eq_comp]
  exact hD.continuous_probeU.comp (nullTransCLM n).continuous

/-- **Clock probes for potentials with coupled transverse dependence, in every dimension at least
three.** The potential depends on the two null coordinates continuously differentiably and on one
transverse coordinate analytically. -/
theorem exists_clockProbe_nullTransverse
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0) (hT : 0 < T) (n : ℕ)
    {x : Fin (n + 3) → ℝ} (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    ∃ W : Set (Fin (n + 3) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 3) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          (nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  have hUcont := hD.continuous_probeField n
  have hnull : nullTransCLM n x = (((0 : ℝ), (0 : ℝ)), x 2) := by
    rw [nullTransCLM_apply, hx0, hx1]
    norm_num
  have hxbox : x ∈ nullTransBox (clockBox T) n := by
    rw [mem_nullTransBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : nullTransLift (probeU V T) n x = 1 := by
    show probeU V T (x 0 + x 1) (x 0 - x 1) (x 2) = 1
    rw [hx0, hx1, probeU]
    norm_num
    rw [boxClamp_eq_self (le_of_lt (by simpa using hT) : |(0 : ℝ)| ≤ T)]
    rw [clockSolution_zero_zero hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
      hD.sideNonneg hD.small (hD.absIm (x 2))]
    norm_num
  have hxne : nullTransLift (probeU V T) n x ≠ 0 := by
    rw [hone]
    exact one_ne_zero
  refine ⟨nullTransBox (clockBox T) n ∩ {y | nullTransLift (probeU V T) n y ≠ 0},
    (isOpen_nullTransBox (isOpen_clockBox T) n).inter (isOpen_ne.preimage hUcont),
    ⟨hxbox, hxne⟩, nullTransLift (probeU V T) n, ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_nullTransLift hD.isC1On3_probeU hD.isC1On3_probeA
    hD.isC1On3_probeB hD.isC1On3_probeC (fun y hy => hy.1) fun y hy => ?_
  have hybox : nullTransCLM n y ∈ clockBox T := hy.1
  exact probe_characteristic hVreal hybox.1 hybox.2

end ClockDatum

end GaloisForLFunctions.HTGeometry
