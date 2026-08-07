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
