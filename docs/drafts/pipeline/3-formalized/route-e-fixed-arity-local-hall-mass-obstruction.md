# Route E fixed-arity local Hall mass obstruction

## Status

Formalized unconditionally in Lean 4. Route class killed. Frontier map unchanged (read-only).

## RH chain and discharged burden

Route E asks for
`squarefree Möbius source → local Hall/factor-replacement control → half-power bound → RH`.

This card kills every implementation whose edges replace at most a fixed number of source primes,
retain a common multiplicative spectator, and stay half-power-local. The theorem proves failure even
at the broader `N^(2/3)` locality/defect envelope.

## Theorem

Fix arity `k`. Put

- `r = 12(k+1)`,
- `N = (2Y)^r`,
- `H = (2Y)^(8(k+1)) = N^(2/3)`.

Products of `r` distinct primes in `(Y,2Y]` are squarefree source vertices. Any distinct
common-spectator replacement using at most `k` source primes has displacement greater than `H`, so
every such vertex is isolated. Prime-window counting and a fixed-depth binomial lower bound make
their Gibbs mass exceed `C H` eventually for every real constant `C`.

Therefore no fixed-arity common-spectator local Hall graph has positive isolated defect
`O(N^(2/3))`; an `N^(1/2+o(1))` producer is impossible a fortiori.

## Lean closure

- Module: `GaloisForLFunctions.RHTower.MobiusBoundaryFixedArityLocalHallMassNoGo`
- Class: `RHTower.RouteEFixedArityTwoThirdLocalHallDefectRoute`
- Premise-free kill: `RHTower.routeEFixedArityTwoThirdLocalHallDefectRouteKilled`
- Quantitative core: `RHTower.eventually_const_mul_twoThirdScale_lt_routeEFiniteIsolatedGibbsMass`
- Exact build: `lake build GaloisForLFunctions.RHTower.MobiusBoundaryFixedArityLocalHallMassNoGo`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`.

## Hard lock

Do not reopen this class by changing finite arity, adding finitely many replacement templates,
improving constants, or refining a positive degree-normalized defect. Live Route E Hall candidates
must use at least one of:

- arity unbounded with scale;
- displacement beyond `N^(2/3)`;
- non-spectator/history-dependent incidence;
- separate collective Ramaré incidence rather than local positive defect.

## Audits

- Hostile check replaced a useless single-primorial witness (only `O(1)` mass) by a near-linear
  prime-product family.
- Sign cancellation cannot repair positive isolated capacity.
- Target replacement token may be arbitrarily large; proof uses only bounded source-token arity.
- Corpus search after closure returns this theorem as the unique exact route-class statement.
- Primary-literature search through August 2026 found smooth/squarefree counting and general
  Hall/fractional-factor results, but no bounded-arity spectator/local-displacement Möbius Hall
  obstruction of this form.
