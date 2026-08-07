# The occupancy dichotomy of a product of laws on ℕ, and the Euler edge as its phase boundary

- **ID:** product-occupancy-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus audit — three independent instances of one unproved general law
- **Statement:** For probability measures `μ_i` on `ℕ` indexed by a type in bijection with `ℕ`, the
  Kolmogorov product gives almost-sure infinite occupancy iff `∑_i μ_i {0}ᶜ = ∞`; for the diagonal
  Euler activation family `q_p = p^{-σ}` that threshold sits exactly at `σ = 1`.

## Goal

Three separate places in the corpus proved the *same* Borel–Cantelli statement about a product of
local laws on `ℕ`, each with its own pushforward computation and its own independence proof:

| Instance | Local occupancy mass | Regime proved | Where |
|---|---|---|---|
| critical Euler activation, `σ = 1` | `1/(p+1)` | infinite occupancy a.s. | `RHTower/EulerActivationSquarefreeProbability.lean` |
| subcritical Euler activation, `σ > 1` | `p^{-σ}/(1+p^{-σ})` | finite occupancy a.s. | `RHTower/EulerActivationSubcriticalFiniteness.lean` |
| prime-valuation sector | `1/p` | (not proved) | `HTGeometry/PrimeValuationSector.lean` |

None of the three exposed the *threshold*: each was a one-directional implication at a fixed
parameter. The audit target was the universal law they are shadows of, plus the sharp `iff`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: the two Borel–Cantelli lemmas plus independence of coordinates of a
      product measure; no open dependency
- [x] 2 → 3  formalized: `lake build` green, axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## The universal law

`formal/GaloisForLFunctions/HTGeometry/ProductOccupancyDichotomy.lean` (2999 jobs, exit 0).

For `μ : ι → Measure ℕ` all probability measures, with `occupiedSet k = {i | k i ≠ 0}` and
`occupiedEvent i = {k | k i ≠ 0}`:

- `infinitePi_occupiedEvent` — the occupancy mass is local: `Π (occupiedEvent i) = μ i {0}ᶜ`.
- `iIndepSet_occupiedEvent` — the occupancy events are independent (one instantiation of
  `iIndepFun_infinitePi`; replaces the per-instance comap gymnastics).
- `limsup_occupiedEvent e` — occupying infinitely many coordinates *is* the limsup of the occupancy
  events, along any enumeration `e : ℕ ≃ ι`.
- `measure_infiniteOccupancy_eq_one` / `measure_finiteOccupancy_eq_one` — the two Borel–Cantelli
  directions.
- `measure_infiniteOccupancy_eq_one_iff`, `measure_finiteOccupancy_eq_one_iff` — **the dichotomy**:
  almost-sure infinite occupancy holds *exactly* when `∑_i μ_i {0}ᶜ = ∞`. There is no intermediate
  regime, so a single scalar decides the qualitative behaviour of the whole product.
- `tsum_ofReal_ne_top_iff_summable` — the hypothesis-checking device: the `ℝ≥0∞` total is finite iff
  the real family of local masses is summable.
- `measure_singleton_eq_zero_of_finite_occupiedSet` — under divergence, every finitely occupied
  configuration is null.

## Instance 1 — the sector is not carried by the integers

`formal/GaloisForLFunctions/HTGeometry/PrimeValuationInfiniteSupport.lean`.

- `tsum_primeValuationLaw_compl_zero` — the sector's local occupancy masses are the prime
  reciprocals, so they diverge (`Nat.Primes.not_summable_one_div`).
- `primeValuationMeasure_infiniteSupport` — almost every configuration is divisible by infinitely
  many primes.
- `primeValuationMeasure_finiteSupport` — finitely many prime divisors is a null event.
- `primeValuationMeasure_singleton_of_finite_occupiedSet` — strictly generalizes the sector's
  `primeValuationMeasure_zeroValuation`, and proves it from independence plus divergence of `∑ 1/p`
  instead of from the sieve-density telescope.
- `primeValuationMeasure_range_natValuationVector` — **the integers are null in the sector.** The
  valuation vectors `n ↦ (v_p(n))_p` have finite support, so the probabilistic model of a random
  integer assigns the integers themselves probability zero. The model lives on the profinite
  completion, not on ℕ; that is the measure-theoretic reason the sieve density collapses.

## Instance 2 — the Euler edge is the phase boundary

`formal/GaloisForLFunctions/RHTower/EulerActivationOccupancyPhaseTransition.lean`.

- `diagonalActivationMeasure_compl_zero`, `infinitePi_diagonalActivation_occupiedEvent` — the local
  and product occupancy masses of the activation family, for an arbitrary unit-interval parameter.
  One appeal to the universal locality lemma replaces the two hand-rolled pushforward computations.
- `eulerActivationParameter`, `eulerActivationProductMeasure` — the activation product at *every*
  exponent `σ ≥ 0`, together with the bridges `eulerActivationProductMeasure_one` (`= σ = 1`, the
  critical product) and `eulerActivationProductMeasure_of_one_lt` (`= σ > 1`, the subcritical
  product). The corpus's two products are the two ends of one family.
- `summable_diagonalActivationOccupancy_iff` — `∑_p q_p/(1+q_p)` converges **iff** `σ > 1`. Above the
  edge, comparison with `∑ p^{-σ}`; at or below it, `q_p/(1+q_p) ≥ q_p/2 ≥ 1/(2p)`.
- `eulerActivationProductMeasure_finiteOccupancy_eq_one_iff` — **the phase transition:** the
  activation source is almost surely a finite integer *exactly* when `σ > 1`.
- `eulerActivationProductMeasure_infiniteOccupancy_of_le_one` — infinite occupancy on the whole
  closed segment `0 ≤ σ ≤ 1`, which the corpus previously had only at `σ = 1`.

So `σ = 1` is not merely where the analytic Euler formulas stop converging: it is the sharp
measure-theoretic boundary between "random finite integer" and "infinitely many prime divisors", and
the boundary belongs to the divergent side.

## What this does not give

The dichotomy is a statement about the *support* of the product, indexed by a real threshold. It is
divisor-blind in the sense of the fixed-corona no-gos: it sees `∑_p μ_p {0}ᶜ` and nothing finer, so
it cannot separate `Re ρ` values. Its use is structural — it fixes which measure-theoretic object the
Euler family is on each side of the edge, and it removes the temptation to read a finite-integer
carrier into the critical model.

## Log
- 2026-08-07 — created directly in 3-formalized; three modules built green, axiom-clean; the two
  pre-existing Euler occupancy theorems are now the two one-directional shadows of the `iff`.

## Generalization — the dichotomy is a statement about local targets, not about occupancy

`ProductOccupancyDichotomy.lean` was refactored so that the law is proved once for an arbitrary local
target family `t : ι → Set ℕ`:

- `localHitSet t k = {i | k i ∈ t i}`, `localEvent t i = {k | k i ∈ t i}`;
- `infinitePi_localEvent`, `iIndepSet_localEvent`, `limsup_localEvent`,
  `measure_infiniteHit_eq_one_iff`, `measure_finiteHit_eq_one_iff`, and the `ae` forms.

Occupancy is the case `t_i = {0}ᶜ`; every previously stated occupancy theorem is retained verbatim as
a one-line corollary, so the two instance modules were unaffected. No measurability hypotheses are
needed anywhere: `ℕ` is discrete, so `MeasurableSet.of_discrete` discharges them.

This is what makes the law nontrivial rather than a repackaging: reading it at other levels gives
statements that occupancy alone cannot express.

## The level structure of a random valuation vector

`formal/GaloisForLFunctions/HTGeometry/GeometricTailMass.lean` — `geometricMeasure_Ici`: a geometric
law with success probability `p` needs at least `m` further failures with probability exactly
`(1-p)^m`. Proved by the one-step atom recursion `μ {k | m ≤ k} = μ {m} + μ {k | m+1 ≤ k}` and
cancellation, so no tail series is summed. This was a mathlib gap.

`formal/GaloisForLFunctions/HTGeometry/PrimeValuationLevelStructure.lean`:

- `primeValuationLaw_Ici` — the valuation at `p` reaches level `m` with probability exactly `p^{-m}`.
- `tsum_primeValuationLaw_Ici_ne_top (hm : 2 ≤ m)` — above level one the local masses are summable
  (comparison with `∑_p p^{-2}`, via `Nat.Primes.summable_rpow`).
- `primeValuationMeasure_finite_level`, `ae_finite_level` — for every `m ≥ 2`, almost every
  configuration has only finitely many primes of multiplicity `≥ m`.
- `ae_finite_squarefull` — **almost every configuration is squarefree away from a finite set of
  primes.**
- `ae_primeValuation_level_structure` — **the complete level structure:** almost surely
  `{p | 2 ≤ v_p}` is finite *and* `{p | v_p = 1}` is infinite. With
  `primeValuationMeasure_infiniteSupport` this pins the carrier of the sector exactly: infinitely many
  prime divisors, all but finitely many of them simple.

So level one is the exact threshold of the dichotomy for this sector: it is the only level at which
the local masses diverge. The repeated part of a random valuation vector is always finite, which is
the probabilistic reason the squarefree kernel carries the whole asymptotic content — the same
statement the corpus's squarefree Gibbs pushforward layer computes on finite palettes.

## Log addendum
- 2026-08-07 — dichotomy generalized to arbitrary local targets; `geometricMeasure_Ici` added
  (mathlib gap); level structure of the sector proved. All modules `lake build` green (9343 jobs),
  axioms `[propext, Classical.choice, Quot.sound]`, `formal_tools.py lint` clean.

## The critical model read at level two

`RHTower/EulerActivationLevelCascade.lean`, appended (9339 jobs, exit 0, axiom-clean):

- `criticalEulerProductMeasure_finiteSquarefull` — **the critical Euler source is squarefree away from a
  finite set of primes**: at `σ = 1` the level-two boundary `σ = 1/2` is already passed, so the
  squarefull part is almost surely finite.
- `criticalEulerProductMeasure_finiteLevel (2 ≤ m)` — the same at every level `m ≥ 2`.

Both are direct instantiations of the cascade at `σ = 1` through the bridge
`eulerActivationProductMeasure_one`, so they are statements about the corpus's *own* critical model that
it did not previously contain: it had almost-sure infinite occupancy at the edge and almost-sure finite
occupancy above it, but nothing about the multiplicities. Together with
`criticalEulerProductMeasure_infinite_occupancy` this pins the critical source exactly — infinitely many
occupied primes, all but finitely many of them simple, i.e. the same carrier shape proved for the
prime-valuation sector.

## Kolmogorov's zero-one law for the product — the dichotomy's qualitative half, generalized

`formal/GaloisForLFunctions/HTGeometry/ProductTailZeroOne.lean` (3007 jobs, exit 0, axiom-clean).

- `coordSigma i` — the σ-algebra generated by the `i`-th coordinate, with `coordSigma_le` and
  `measurableSet_localEvent_coordSigma` (a hitting event is measurable for its own coordinate, by
  definition of `comap`).
- `iIndep_coordSigma` — the coordinate σ-algebras are independent. This is `iIndepFun_infinitePi`
  *definitionally*: `iIndepFun f μ` unfolds to `iIndep (fun i ↦ comap (f i) _) μ`, so no new proof is
  needed — only the observation that the two statements are the same.
- `limsup_localEvent_shift` — dropping the first `n` indices changes neither the hit set's infinitude nor
  the limsup describing it (`Filter.limsup_nat_add`).
- `measurableSet_tail_infiniteHit` — hence the hitting event lies in the tail σ-algebra
  `⨅ n, ⨆ i ≥ n, coordSigma (e i)`.
- `measure_zero_or_one_of_tail` — **Kolmogorov's zero-one law for the product**: every tail event has
  measure `0` or `1`.
- `measure_infiniteHit_eq_zero_or_one` — the dichotomy's "no intermediate regime" half, now as an
  instance of the general law.

This is a genuine strengthening rather than a repackaging: the dichotomy decides the hitting event and
nothing else, while the zero-one law applies to every event that ignores finitely many coordinates —
densities of the hit set, convergence of series along it, tail asymptotics of the valuation vector. The
dichotomy remains the sharper statement where it applies, since it also says *which* of `0` and `1`.
