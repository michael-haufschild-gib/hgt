# T2 all-source-graph terminal reconstruction no-go

Status: **FORMALIZED IN LEAN 4**  
Date: 2026-08-30  
Route: T2  
Label: `C-T2-ALL-SOURCE-GRAPH-NOGO`

## RH proof chain being tested

The proposed chain is

`all finite prime-log graph norms of the Wold primitive in the harmonic, activation-Fisher, and literal essential-edge Hilbert sources`

`+ height-1/10 square-summable Abel increments / Bohr-Cauchy current`

`=> height-1/10 terminal disappearance`

`=> height-cofinal strict-subhalf landing`

`=> RH`.

This is the strongest route that tries to combine the already formalized Wold all-orders graph smoothness with the already formalized unsplit positive-height Bohr current. Killing it materially narrows T2's open core.

## Corpus basis

Corpus search before conjecturing found:

- `summable_xiHeatCassiniOrderedWoldResidual_logPow_oneDivEnergy`;
- `summable_xiHeatCassiniPrimeWoldResidual_activationFisherLogPowEnergy`;
- `summable_xiHeatCassiniPrimeWoldResidual_actualEssentialEdgeLogPowEnergy`;
- `t2BohrTerminalCounterCurrent_bohrCauchy` and `not_T2PrimeClockBohrTerminalLandingPrinciple`;
- `riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight_unconditional`;
- `riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero`.

The frontier ledger was read but not modified.

## Conjecture

On the literal ordered-prime clock, the existing witness

`r_N = exp(-h_N / 20)`

simultaneously has:

1. `r_N -> 0`;
2. every harmonic graph energy
   `sum_N h_N^(2k) r_N^2 / p_N < infinity`;
3. every activation-Fisher graph energy;
4. every literal essential-edge graph energy;
5. square-summable height-1/10 Abel increments and the exact finite Parseval/Bohr-Cauchy law;
6. divergent height-1/10 terminal `|r_N| exp(h_N/10) -> infinity`.

Therefore the displayed T2 chain is false before its terminal-disappearance arrow.

## Paper proof

Write `p_N = exp(h_N)`. Then `r_N^2 = p_N^(-1/10)`. For every `k`,

`h_N^(2k) r_N^2 / p_N = (log p_N)^(2k) p_N^(-11/10)`.

This is summable, by comparison with the full natural series `sum_n (log n)^(2k)n^(-11/10)`. The activation-Fisher and literal essential-edge densities are each nonnegative and bounded above by `1/p`, so their corresponding graph energies are termwise dominated by the harmonic graph energy. Items 1, 5, and 6 were proved for this exact witness in the preceding Bohr-terminal no-go.

No asymptotic computation enters this proof.

## Hostile attacks

- **Finite-order Sobolev escape:** blocked by item 2 for every order simultaneously.
- **Switch harmonic source to activation-Fisher source:** blocked by its pointwise upper bound by `1/p` and item 3.
- **Switch to literal essential-edge source:** blocked by its pointwise upper bound by `1/p` and item 4.
- **Add fixed-height Bohr convergence:** already present in item 5.
- **Use primitive vanishing:** already present in item 1.

The counterexample is not the genuine Wold sequence, so it does not rule out a coefficient-faithful arithmetic identity or a quantitatively analytic-vector estimate specific to that sequence. That is exactly the survivor.

## Positive survivor / sharp replacement

Let graph generator be multiplication by prime-log height and base Hilbert density be `1/p = exp(-h)`. Exponential graph landing at radius `t` has point mass

`exp(2t h_N) r_N^2 / p_N = r_N^2 exp((2t-1)h_N)`.

It controls terminal height `c` once `t >= c + 1/2`, because

`r_N^2 exp(2c h_N) <= r_N^2 exp((2t-1)h_N)`.

Thus the genuine positive survivor is not another finite/all-polynomial graph domain. It is one of:

- Wold-specific exponential graph landing at radius at least `c+1/2` for a cofinal family `c -> 1/2` (hence radii approaching `1`);
- an equivalent factorial-uniform analytic-vector estimate;
- a coefficient-faithful arithmetic recurrence/Tauberian identity that bypasses Hilbert point evaluation.

Lean realizes both the all-source counterexample and this exponential-radius terminal-control boundary below.

## Literature novelty audit

Classical analytic-vector and Denjoy-Carleman theory distinguishes membership in every polynomial graph domain from quantitative analytic/quasi-analytic control. Literature located in the audit discusses that abstract distinction, but no source found treats this ordered-prime Wold residual, its three literal source densities, the positive-ray Abel current, or the exact `t >= c+1/2` T2 terminal boundary. Novelty claim is restricted to this source-shaped conjunction and route-killing consequence.

## Lean realization

Module: `GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthAllSourceGraphNoGo`

Principal route kill:

- `not_T2PrimeClockBohrAllSourceGraphTerminalLandingPrinciple`

Formalized source-domain witnesses:

- `summable_t2BohrTerminalCounterResidual_allLogGraphEnergy`;
- `summable_t2BohrTerminalCounterResidual_activationFisherAllLogGraphEnergy`;
- `summable_t2BohrTerminalCounterResidual_actualEssentialEdgeAllLogGraphEnergy`.

Formalized positive survivor:

- `tendsto_primeClockTerminal_of_exponentialGraphEnergy`.

The module is imported by `GaloisForLFunctions.RHTower`.

## Verification

- Direct `lake env lean` on module: PASS.
- Targeted `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthAllSourceGraphNoGo`: PASS.
- `#print axioms` for route kill, three source-domain theorems, and positive survivor: only `propext`, `Classical.choice`, `Quot.sound`.
- Global formal lint: new module is umbrella-reachable and clean; repository lint remains red only because unrelated concurrent modules are unreachable from their umbrellas.
- No computation used. Frontier map unchanged.
