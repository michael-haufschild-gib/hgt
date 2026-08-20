# ULF-SRFM-4 — Lean formalization record

**Card:** `superposition-saturation-hidden-history-action-density-and-global-properness-law.md`

**Modules** (all in `formal/GaloisForLFunctions/HTGeometry/`, namespace
`GaloisForLFunctions.HTGeometry`):

| Module | Content |
|---|---|
| `CountableRelativeEntropyValue.lean` | exact atom-series value of `klDiv` between countable laws |
| `PoissonOccupancyHistorySplit.lean` | Poisson / excess-count relative entropy; §2 |
| `PoissonSuperpositionSaturationProperness.lean` | §3–§6 |

All three are imported by `GaloisForLFunctions.HTGeometry` and by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card object → Lean object

| Card | Lean |
|---|---|
| `P_m = Pois(mα)` | `ProbabilityTheory.poissonMeasure ((m : ℝ≥0) * α)` (mathlib) |
| `q_m = 1 - e^{-mα}`, (2.2) | `poissonOccupancyUnit ((m : ℝ≥0) * α)` |
| `K_x`, (2.3) | `excessCountMeasure x`, atoms `excessCountWeight` |
| `C(α,β)`, (2.4) | `rateJeffreys` |
| `B_m`, (2.5) | `formationBooleanWork` |
| `H_m`, (2.6) | `formationHistoryWork` |
| `𝒜_d`, (5.1) | `orbitAction` |
| `Ā_d`, (5.2) | `completedOrbitAction` |
| `α_p(t)`, `β_p(t) = α_p(-t)`, (6.1) | `reflectedSourceRate` |

## Card result → Lean declaration

| Card result | Lean declaration |
|---|---|
| `D(Pois(x)‖Pois(y)) = x log(x/y) + y - x` | `toReal_klDiv_poissonMeasure` |
| `D(K_a‖K_b)` closed form | `toReal_klDiv_excessCountMeasure` |
| occupancy–history chain rule (one direction) | `toReal_klDiv_poissonMeasure_eq_occupancy_add_history` |
| **Theorem 2.1**, (2.7) | `poissonJeffreys_eq_boolean_add_hidden`, `formation_conservation` |
| nonnegativity of both terms | `booleanOccupancyJeffreys_nonneg`, `hiddenHistoryWork_nonneg` |
| history action vanishes iff `α = β` | `hiddenHistoryWork_eq_zero_iff` (via `excessCountMeasure_injOn`) |
| (3.1) Bernoulli Jeffreys | corpus `bernoulliJeffreysReal_formula` / `toReal_klDiv_bernoulli_baseline_interior` |
| **(3.2)** | `formationBooleanWork_eq`, `booleanOccupancyJeffreys_eq` |
| **Theorem 3.1**, (3.3) | `tendsto_poissonOccupancy_depth`, `tendsto_formationBooleanWork_zero` |
| **(3.3a)** | `isEquivalent_formationBooleanWork` |
| **(3.4)** | `tendsto_formationHistoryWork_div` |
| **Corollary 3.2**, (3.6) | `eventually_half_rateJeffreys_mul_le` |
| **(3.7)** | `orbitAction_ne_top_iff` |
| **Theorem 4.1**, (4.2) (hence (4.1)) | `tendsto_excessCountMeasure_Iic` |
| **Theorem 5.1**, (5.3) | `completedOrbitAction_ne_top_iff` |
| **(5.4)** and its compactness | `completedOrbitAction_sublevel_eq`, `isCompact_completedOrbitAction_sublevel` |
| **Corollary 5.2**, (5.5) | `liminf_formationHistoryWork` |
| §6 reflection invariance | `completedOrbitAction_symm`, `completedOrbitAction_reflectedSourceRate_reflection` |
| **Corollary 6.1**, (6.2) | `completedOrbitAction_reflectedSourceRate_ne_top_iff` |

## Method notes

* The chain rule is proved as an **exact real identity** between the three atom series, not through
  a kernel disintegration: `klDiv` of countable laws is evaluated by
  `toReal_klDiv_of_countable`, and the affine log-ratio series is summed by
  `hasSum_weight_mul_affine`.  The three cancelling ingredients are
  `log((1-q)/(1-r)) = b - a`, `log(q/r) = log((e^a-1)/(e^b-1)) + (b-a)` and
  `q · a e^a/(e^a-1) = a`.
* Injectivity of `x ↦ K_x` uses only the atoms at `0` and `1`.
* `(3.3a)` is proved through `Asymptotics.isEquivalent_of_tendsto_one` after the split
  `log((e^a-1)/(e^b-1)) = (a-b) + log((1-e^{-a})/(1-e^{-b}))` (`log_expSub_ratio_eq`).

## Verification

* `lake env lean` on each of the three modules: 0 errors, 0 warnings.
* Axiom audit: `CountableRelativeEntropyValue` + `PoissonOccupancyHistorySplit` — 44 public
  declarations; `PoissonSuperpositionSaturationProperness` — 39 public declarations.  Only
  `propext`, `Classical.choice`, `Quot.sound` throughout.
* No added hypotheses beyond the card's own standing positivity of the rates.
