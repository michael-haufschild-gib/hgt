/-
The one-parameter family of covering functionals, and the length at which van der Corput stops.

An exponent pair `(κ, λ)` gives `|S| ≤ (T/M)^κ M^λ = M^(λ-κ) T^κ`, so in the covering picture it is
the source of shape `α = λ - κ`, `β = κ`.  Its demand for reaching the length `M = T^(x₀)` against
the target `M^(1/2) T^θ` is

    demand(κ, λ, x₀) = κ + (λ - κ - 1/2)·x₀ = G_(x₀)(κ, λ) - x₀/2 ,
    G_(x₀)(κ, λ) := (1 - x₀)·κ + x₀·λ .

So minimising the demand at a prescribed length is minimising the **linear functional `G_(x₀)`** over
the exponent-pair region, and `x₀` selects which functional is relevant.  Two endpoints:

    x₀ = 0    :  G = κ ,
    x₀ = 1/2  :  G = (κ + λ)/2 ,

the second being the pointwise subconvexity exponent.  The van der Corput process
`A(κ, λ) = (κ/(2κ+2), (κ+λ+1)/(2κ+2))` decreases `G_(x₀)` at `(κ, λ)` exactly when

    G_(x₀)(κ, λ) · (2κ + 1) > x₀ · (κ + 1) ,

which at `x₀ = 1/2` is the criterion `(κ+λ)(2κ+1) > κ+1` that fails at every record pair.  For
`x₀ < 1/2` it can hold, and at Bourgain's pair `(13/84, 55/84)` it holds precisely for

    x₀ < 715/1764 .

That threshold is `1/1764` above the decoupling threshold `17/42 = 714/1764` and `1/22932` below
Huxley's reach `332/819`: it lies strictly inside the junction at which the published proof hands off
from Huxley's bound to the decoupling bound.
-/
import GaloisForLFunctions.HTGeometry.SectionFourCoveringFloor
import GaloisForLFunctions.HTGeometry.ExponentPairSelfDuality

namespace HTGeometry

/-! ### The family of covering functionals -/

/-- The linear functional on exponent pairs whose minimum is the demand at length `T^(x₀)`. -/
def covFunctional (x₀ κ lam : ℚ) : ℚ := (1 - x₀) * κ + x₀ * lam

/-- The demand of an exponent pair for reaching length `T^(x₀)`. -/
def covDemandOfPair (x₀ κ lam : ℚ) : ℚ := covFunctional x₀ κ lam - x₀ / 2

/-- **The exponent pair's covering data is the general reach/demand of its shape.** -/
theorem covDemandOfPair_eq_coveringDemand (x₀ κ lam : ℚ) :
    covDemandOfPair x₀ κ lam = coveringDemand (lam - κ) κ x₀ := by
  unfold covDemandOfPair covFunctional coveringDemand; ring

/-- At the critical length the functional is half the subconvexity sum. -/
theorem covFunctional_at_half (κ lam : ℚ) :
    covFunctional (1 / 2) κ lam = (κ + lam) / 2 := by
  unfold covFunctional; ring

/-- At length zero the functional is `κ`. -/
@[simp] theorem covFunctional_at_zero (κ lam : ℚ) : covFunctional 0 κ lam = κ := by
  unfold covFunctional; ring

/-- The demand at the critical length is the pointwise subconvexity exponent. -/
theorem covDemand_at_half_eq_epMu (κ lam : ℚ) :
    covDemandOfPair (1 / 2) κ lam = epMu κ lam := by
  unfold covDemandOfPair covFunctional epMu; ring

/-! ### When `A` improves the functional -/

/-- **Exact criterion for the van der Corput process to decrease `G_(x₀)`.** -/
theorem covA_decreases_iff {x₀ κ lam : ℚ} (hκ : 0 ≤ κ) :
    covFunctional x₀ (procA_fst κ) (procA_snd κ lam) < covFunctional x₀ κ lam
      ↔ x₀ * (κ + 1) < covFunctional x₀ κ lam * (2 * κ + 1) := by
  have hpos : 0 < 2 * κ + 2 := by linarith
  unfold covFunctional procA_fst procA_snd
  rw [show (1 - x₀) * (κ / (2 * κ + 2)) + x₀ * ((κ + lam + 1) / (2 * κ + 2))
        = ((1 - x₀) * κ + x₀ * (κ + lam + 1)) / (2 * κ + 2) by field_simp,
    div_lt_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

/-- **At the critical length the criterion is the campaign's stationarity criterion.** -/
theorem covA_criterion_at_half (κ lam : ℚ) :
    ((1 : ℚ) / 2) * (κ + 1) < covFunctional (1 / 2) κ lam * (2 * κ + 1)
      ↔ κ + 1 < (κ + lam) * (2 * κ + 1) := by
  rw [covFunctional_at_half]
  constructor <;> intro h <;> linarith

/-! ### Bourgain's pair -/

/-- Bourgain's exponent-pair first coordinate. -/
def bourgainKappa : ℚ := 13 / 84

/-- Bourgain's exponent-pair second coordinate. -/
def bourgainLambda : ℚ := 55 / 84

/-- Bourgain's pair lies on the line of symmetry, where the subconvexity exponent equals `κ`. -/
theorem bourgain_pair_on_line : bourgainLambda = bourgainKappa + 1 / 2 := by
  unfold bourgainKappa bourgainLambda; norm_num

theorem bourgain_pair_mu : epMu bourgainKappa bourgainLambda = bourgainTheta := by
  unfold epMu bourgainKappa bourgainLambda bourgainTheta; norm_num

/-- **The `A`-image of Bourgain's pair.** -/
theorem procA_bourgain :
    procA_fst bourgainKappa = 13 / 194 ∧
      procA_snd bourgainKappa bourgainLambda = 76 / 97 := by
  constructor
  · unfold procA_fst bourgainKappa; norm_num
  · unfold procA_snd bourgainKappa bourgainLambda; norm_num

/-- **`A` strictly worsens Bourgain's pair for the pointwise exponent** — the campaign's
stationarity theorem, restated in this file's language. -/
theorem procA_worsens_bourgain_mu :
    epMu bourgainKappa bourgainLambda
      < epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold epMu bourgainKappa bourgainLambda; norm_num

/-! ### The threshold length -/

/-- The length below which `A` still improves the covering functional at Bourgain's pair. -/
def bourgainAThreshold : ℚ := 715 / 1764

/-- **Exactly below `715/1764`, `A` improves Bourgain's pair for the covering functional.** -/
theorem covA_decreases_bourgain_iff (x₀ : ℚ) :
    covFunctional x₀ (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < covFunctional x₀ bourgainKappa bourgainLambda
      ↔ x₀ < bourgainAThreshold := by
  rw [covA_decreases_iff (by unfold bourgainKappa; norm_num)]
  unfold covFunctional bourgainKappa bourgainLambda bourgainAThreshold
  constructor <;> intro h <;> nlinarith

/-- **The threshold is `1/1764` above the decoupling threshold `17/42`.** -/
theorem threshold_above_decouplingStart :
    bourgainAThreshold - decouplingStart = 1 / 1764 := by
  unfold bourgainAThreshold decouplingStart; norm_num

/-- **And `1/22932` below Huxley's reach `332/819`.** -/
theorem threshold_below_huxleyReach :
    coveringReach huxleyAlpha huxleyBeta bourgainTheta - bourgainAThreshold = 1 / 22932 := by
  rw [huxley_reach]; unfold bourgainAThreshold; norm_num

/-- **The productivity threshold of van der Corput lies strictly inside the junction at which the
published proof hands off from Huxley's bound to the decoupling bound.** -/
theorem threshold_inside_second_junction :
    decouplingStart < bourgainAThreshold ∧
      bourgainAThreshold < coveringReach huxleyAlpha huxleyBeta bourgainTheta := by
  constructor
  · unfold bourgainAThreshold decouplingStart; norm_num
  · rw [huxley_reach]; unfold bourgainAThreshold; norm_num

/-- At the critical length `A` does **not** improve Bourgain's pair: `1/2 > 715/1764`. -/
theorem covA_fails_at_critical_length :
    ¬ ((1 : ℚ) / 2 < bourgainAThreshold) := by
  unfold bourgainAThreshold; norm_num

/-- The threshold is strictly below the critical length: van der Corput is productive for every
length shorter than `T^(715/1764)` and stationary from there to the critical length. -/
theorem threshold_lt_critical : bourgainAThreshold < 1 / 2 := by
  unfold bourgainAThreshold; norm_num

/-! ### The improved low-range cap -/

/-- The demand of the `A`-image of Bourgain's pair at Huxley's starting point. -/
theorem procA_bourgain_demand :
    covDemandOfPair huxleyStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) = 907 / 6014 := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold covDemandOfPair covFunctional huxleyStart; norm_num

/-- The demand of the published low-range pair `(1/9, 13/18)` at the same point. -/
theorem expPair_demand_from_pair :
    covDemandOfPair huxleyStart (1 / 9) (13 / 18) = expPairDemand := by
  rw [expPairDemand_eq]
  unfold covDemandOfPair covFunctional huxleyStart; norm_num

/-- **The `A`-image of Bourgain's own pair beats the published low-range input.** -/
theorem procA_bourgain_beats_expPair :
    covDemandOfPair huxleyStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) < expPairDemand := by
  rw [procA_bourgain_demand, expPairDemand_eq]; norm_num

/-- **Hence the low-range input is not the binding constraint at all: its demand falls below
Huxley's, so Huxley's demand `277/1792` is the sole floor of the architecture.** -/
theorem lowRange_not_binding :
    covDemandOfPair huxleyStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) < huxleyDemand := by
  rw [procA_bourgain_demand, huxleyDemand_eq]; norm_num

/-- The demand of the `A`-image of Bourgain's pair for covering all the way to the decoupling
threshold, bypassing Huxley entirely. -/
theorem procA_bourgain_demand_at_decoupling :
    covDemandOfPair decouplingStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) = 15 / 97 := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold covDemandOfPair covFunctional decouplingStart; norm_num

/-- **Bourgain's own pair, used to cover to the decoupling threshold, demands exactly the record.**
The exponent pair and the decoupling bound meet at `13/84` from both sides. -/
theorem bourgain_pair_demand_at_decoupling :
    covDemandOfPair decouplingStart bourgainKappa bourgainLambda = bourgainTheta := by
  unfold covDemandOfPair covFunctional decouplingStart bourgainKappa bourgainLambda bourgainTheta
  norm_num

/-- **Huxley is worth `15/97 - 277/1792` in the floor.**  Removing Huxley from the chain and covering
to `17/42` with the best available exponent pair costs exactly that much. -/
theorem huxley_contribution :
    (15 : ℚ) / 97 - huxleyDemand = 11 / 173824 := by
  rw [huxleyDemand_eq]; norm_num

theorem huxley_still_needed : huxleyDemand < 15 / 97 := by
  rw [huxleyDemand_eq]; norm_num

/-- Even bypassing Huxley beats the published record. -/
theorem bypass_beats_record : (15 : ℚ) / 97 < bourgainTheta := by
  unfold bourgainTheta; norm_num

end HTGeometry
