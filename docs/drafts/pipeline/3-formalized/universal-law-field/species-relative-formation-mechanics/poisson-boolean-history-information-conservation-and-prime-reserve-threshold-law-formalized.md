# ULF-SRFM-2 — Lean formalization record

**Card:** `poisson-boolean-history-information-conservation-and-prime-reserve-threshold-law.md`

**Modules** (all in `formal/GaloisForLFunctions/HTGeometry/`, namespace
`GaloisForLFunctions.HTGeometry`), all imported by `GaloisForLFunctions.HTGeometry` and by
`GaloisForLFunctions.HTGeometry.UniversalLawField`:

| Module | Content |
|---|---|
| `CountableRelativeEntropyValue.lean` | exact atom-series value and finiteness test for `klDiv` on countable spaces |
| `PoissonOccupancyHistorySplit.lean` | Poisson and zero-truncated-Poisson relative entropy; the occupancy–history chain rule |
| `CountFormationSplit.lean` | §2 in full generality, plus the Poisson instance §3 |
| `ReflectedPrimeHistoryReserve.lean` | §4 |

## Card object → Lean object

| Card | Lean |
|---|---|
| `Φ`, (2.1) | `formationSplit` |
| `Ψ`, (2.3) | `formationRecovery` |
| `q_P`, (2.4) | `countOccupancy`, `countOccupancyUnit` |
| `K_P` | `countExcessLaw` (atoms `countExcessWeight`) |
| `P_λ = Pois(λ)` | `ProbabilityTheory.poissonMeasure` |
| `K_λ`, (3.2) | `excessCountMeasure` |
| `𝓡(λ,μ)`, (3.4) | `hiddenHistoryWork` |
| `a_p`, `b_p`, (4.1) | `reflectedOdds p t`, `reflectedOdds p (-t)` |
| `λ(x)`, `q(x)`, (4.2) | `oddsRate`, `oddsOccupancy` |
| `R_p(t)`, (4.3) | `primeHistoryReserve` |
| `f`, `g`, (4.6) | `oddsShape`, `oddsDefect` |

## Card result → Lean declaration

| Card result | Lean declaration |
|---|---|
| `Φ` is a bijection onto `{0} ⊔ ({1} × ℋ)`, (2.2) | `formationRecovery_formationSplit`, `formationSplit_injective`, `range_formationSplit` |
| marked packets determine `P`, `Q` | `measure_eq_of_split_eq` |
| **Theorem 2.1**, (2.5) | `toReal_klDiv_formationSplit` |
| **(2.6)** | `toReal_klDiv_formationSplit_symm` |
| (3.1), (3.2) — Poisson conditioning | `countOccupancy_poissonMeasure`, `countExcessWeight_poissonMeasure`, `countExcessLaw_poissonMeasure` |
| **Corollary 3.1**, (3.3) | `toReal_klDiv_poissonMeasure_eq_occupancy_add_history` |
| (3.4) reserve nonnegative | `hiddenHistoryWork_nonneg` |
| (3.4) reserve vanishes iff `λ = μ` | `hiddenHistoryWork_eq_zero_iff` (via `excessCountMeasure_injOn`) |
| (4.3) reserve = Poisson minus Boolean information | `primeHistoryReserve_eq` |
| **(4.4)** strict positivity | `primeHistoryReserve_pos` |
| (4.7) split into defect and shape drift | `primeHistoryReserve_split` |
| (4.8) `g(x) = x²/2 + O(x³)` | `oddsDefect_bounds`, `oddsDefect_div_sq_bounds` |
| (4.8) `log f(x) = -x/2 + O(x²)` | `abs_log_oddsShape_le` |
| (4.9) | `tendsto_oddsDefect_div_sq` |
| (4.9)–(4.10) combined | `tendsto_primeHistoryReserve_ratio` |
| **Theorem 4.1**, (4.5) | `isEquivalent_primeHistoryReserve` |
| **Theorem 4.2**, (4.11) | `summable_primeHistoryReserve_iff` |
| "at `t = 0` every reserve is zero" | `primeHistoryReserve_zero` |

## Method notes

* The countable KL chain rule is proved as an exact atom-series identity: `toReal_klDiv_of_countable`
  gives the value, `Summable.tsum_eq_zero_add` splits off the vacuum atom, and the tail factorizes
  as `q_P log(q_P/q_Q) + q_P D(K_P‖K_Q)`.  Finiteness enters only through `klDiv P Q ≠ ⊤`, which is
  converted to absolute summability by `summable_log_singleton_ratio_of_klDiv_ne_top`.
* The two-sided cubic sandwich `x - x²/2 < log(1+x) < x - x²/2 + x³/3` (`log_one_add_gt_quadratic`,
  `log_one_add_lt_cubic`) replaces all Landau bookkeeping in §4; the lower half also exists in the
  corpus as `HTGeometry.LiuSandwich.log_one_add_lower`, which imports all of Mathlib, so the pair is
  reproved here on a light import stack.
* Divergence at the threshold uses `Nat.Primes.not_summable_one_div` and the global elementary
  bound `log x ≤ x^ε/ε` (`log_le_rpow_div`) for the convergent half — no PNT input.

## Verification

* `lake env lean` on each module: 0 errors, 0 warnings.
* Axiom audit: `CountableRelativeEntropyValue` (5 + 2), `PoissonOccupancyHistorySplit` (44),
  `CountFormationSplit` (26), `ReflectedPrimeHistoryReserve` (31) public declarations — only
  `propext`, `Classical.choice`, `Quot.sound`.
