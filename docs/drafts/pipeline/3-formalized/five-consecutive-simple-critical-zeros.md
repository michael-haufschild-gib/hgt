# Five consecutive simple critical zeros

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ100
- **Statement:** For all sufficiently large `T`, at least `N(T)/5000` starting positions give five consecutive occupied ordinates, each carrying exactly one simple critical zero.

## Paper proof

Let `N` count zero copies, `S` simple critical zeros, `O` occupied ordinates,
and `C` ordinates carrying exactly one simple critical zero. Reflection pairs
give `2O + S ≤ N + 2C`: every other ordinate has at least two copies,
and one also carrying a simple critical zero has at least three. Also `S ≤ O`.
For an ordered binary word with `C` good sites among `O` sites, the number `Rₖ₊₁`
of all-good consecutive blocks satisfies `Rₖ₊₁ ≥ (k+1)C − kO − k`:
among `O−k` candidate starts, each bad site spoils at most `k+1`.
With `k=4`, the census gives `R₅ ≥ C + 2S − 2N − 4`.

The distinction between simple critical zeros and clean ordinates is essential:
an off-line pair may share an ordinate with a simple critical zero.

The corpus also proves singleton-fibre lower density
`C/N ≥ H − 11π/2000`, where `H = HD(1) ≥ 0.67250070`.
Together with simple-critical lower density `S/N ≥ H`, this gives
`liminf R₅/N ≥ 3H − 2 − 11π/2000 > 0.00022`.
Since `N(T) → ∞`, the fixed endpoint loss is absorbed and
`R₅ ≥ N(T)/5000` eventually. No arithmetic premise is added.

Singleton fibres contain simple critical zeros by reflection. Increasing
enumeration of every occupied ordinate ensures no zero is skipped.

## Lean

`formal/GaloisForLFunctions/IncommensurableGaborPinching/ConsecutiveSimpleCriticalZeros.lean`:
`xi_ordinate_census`, `xi_five_runs_finite`, `xi_five_runs_positive_proportion`,
`xi_five_runs_one_five_thousandth`, `runStart_has_block`,
`IsSingletonBlock.simple_critical`, `IsSingletonBlock.simple_zeta`,
`eventually_exists_five_simple_critical_block`.

Direct check passed:
`lake --old env lean GaloisForLFunctions/IncommensurableGaborPinching/ConsecutiveSimpleCriticalZeros.lean`.
Imported by `IncommensurableGaborPinching.lean`. Axiom checks omitted as requested.

Arbitrarily long runs remain open.
