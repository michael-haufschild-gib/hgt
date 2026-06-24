/-
# Böttcher tower — Tier 2b: logarithmic capacity, equilibrium measure, Green's function

Vocabulary for the capacity-separation core (`q62-bottcher-independence-natural-boundary.md`
Step 1). Built on the Tier-2a energy primitives.

  * `IsProbOn μ K`        — `μ` is a probability measure carried by `K`
  * `robinConstant K`     — `V(K) = inf { I(μ) : μ prob. on K }`  (minimal logarithmic energy)
  * `logCapacity K`       — `cap(K) = exp(-V(K))`
  * `IsEquilibrium μ K`   — `μ` is a probability measure on `K` attaining the inf
  * `greenFunction μ V`   — `g = V - Uᵘ`  (Green's function of the exterior, pole at ∞)

Definitions only (Tier 2b); the strict-gain inequality and the separation theorem
build on these next.
-/
import GaloisForLFunctions.Bottcher.LogPotential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

namespace Bottcher

/-- `μ` is a probability measure carried by the compact set `K` (mass `0` off `K`). -/
def IsProbOn (μ : Measure ℂ) (K : Set ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Kᶜ = 0

/-- The Robin constant `V(K) = inf { I(μ) : μ a probability measure on K }`,
the minimal logarithmic energy. -/
noncomputable def robinConstant (K : Set ℂ) : ℝ :=
  sInf { e : ℝ | ∃ μ : Measure ℂ, IsProbOn μ K ∧ logEnergy μ = e }

/-- The logarithmic capacity `cap(K) = exp(-V(K))`. -/
noncomputable def logCapacity (K : Set ℂ) : ℝ := Real.exp (- robinConstant K)

/-- `μ` is an equilibrium measure of `K`: a probability measure on `K` whose energy
attains the Robin constant. -/
def IsEquilibrium (μ : Measure ℂ) (K : Set ℂ) : Prop :=
  IsProbOn μ K ∧ logEnergy μ = robinConstant K

/-- The Green's function of the exterior of `K` with pole at `∞`, written through an
equilibrium measure `μ` and Robin constant `V`: `g(z) = V - Uᵘ(z)`. On `K` one has
`Uᵘ = V` so `g = 0`; off `K`, `g > 0`. -/
noncomputable def greenFunction (μ : Measure ℂ) (V : ℝ) (z : ℂ) : ℝ :=
  V - logPotential μ z

/-- Capacity is monotone-compatible with the Robin constant: smaller Robin constant
means larger capacity. (Immediate from `exp` monotonicity; recorded for use in the
separation argument.) -/
theorem logCapacity_lt_of_robinConstant_lt {K L : Set ℂ}
    (h : robinConstant L < robinConstant K) : logCapacity K < logCapacity L := by
  unfold logCapacity
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The Robin constant is a lower bound for the energy of any probability measure on
`K` (given the energy set is bounded below — automatic for nonpolar `K`). This is the
inequality the strict-gain step contradicts in the separation argument. -/
theorem robinConstant_le {K : Set ℂ} {μ : Measure ℂ} (hμ : IsProbOn μ K)
    (hbdd : BddBelow { e : ℝ | ∃ ρ : Measure ℂ, IsProbOn ρ K ∧ logEnergy ρ = e }) :
    robinConstant K ≤ logEnergy μ :=
  csInf_le hbdd ⟨μ, hμ, rfl⟩

/-- Equality of capacity is equality of Robin constants (`exp` is injective). -/
theorem robinConstant_eq_of_logCapacity_eq {K L : Set ℂ}
    (h : logCapacity K = logCapacity L) : robinConstant K = robinConstant L := by
  have := Real.exp_injective (by simpa [logCapacity] using h)
  linarith

end Bottcher
