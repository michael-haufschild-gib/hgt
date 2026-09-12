# Route E whole-anchor same-reservoir transpose

- **ID:** `ROUTE-E-WHOLE-ANCHOR-SAME-RESERVOIR-TRANSPOSE-001`
- **Stage:** 5-failed
- **Type:** `[LEAN-CERTIFIED NO-GO] [PRECISE SUBCLASS] [POSITIVE SURVIVORS]`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteEWholeAnchorReverseFreshnessNoGo.lean`

## Retired conjecture

Let a whole-anchor forward certificate send a source to

\[
  q=t m
\]

by inserting a reservoir product `t` which is fresh at the forward source. Reuse the same decoded
reservoir `t` as a fresh reservoir in a reverse certificate based at `q`.

## Exact obstruction

For natural numbers `t,m`,

\[
  \gcd(t,t m)=1 \quad\Longleftrightarrow\quad t=1.
\]

Therefore every nontrivial inserted reservoir divides the terminal and cannot be fresh at that
terminal. The obstruction is structural, not a shortage in token count, interval length, or
asymptotic strength. It rules out only entrywise reverse reuse of the same whole-anchor reservoir.

Lean theorems:

- `routeE_wholeAnchor_sameReservoir_not_reverseFresh`;
- `routeE_wholeAnchor_reverseFresh_sameReservoir_iff_one`.

## Strongest positive survivor

The one-radius numerical transfer remains available for any opposite-grade predicate which is
actually pair-stable. Same-reservoir freshness is not required by the numerical theorem.

Four structural alternatives remain live:

1. decode a different reverse reservoir from the other endpoint;
2. control aggregate transpose-mismatch divergence without entrywise reverse certificates;
3. use a genuinely symmetric prime-toggle relation rather than insertion-only freshness;
4. symmetrize physical support, then prove the required reciprocal-degree or load-gradient law.

No claim is made that any survivor already supplies coefficient-one Hall/load or the all-scale
strict-half bound.

## Verification

Direct foreground check:

```text
lake env lean GaloisForLFunctions/RHTower/RouteEWholeAnchorReverseFreshnessNoGo.lean
```

The module is wired into `formal/GaloisForLFunctions/RHTower.lean`. Targeted build and axiom audit
are recorded after final audit.
