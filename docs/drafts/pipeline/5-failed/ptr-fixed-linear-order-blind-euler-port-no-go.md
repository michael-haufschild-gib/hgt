# PTR fixed linear order-blind Euler port — no-go

- **ID:** ptr-fixed-linear-order-blind-euler-port
- **Stage:** 5-failed
- **Type:** FALSIFIED (specified port, not PTR)
- **Statement:** No unital complex-linear scalar readout of the literal two-slab prime cells can be both order-blind on two distinct prime deviations and multiplicative on their first backtracking four-word.

## Route and exact obstruction

The tested chain is `literal temporal-Maxwell prime cells → fixed local linear order-blind Euler port → all-grade conormal trace → confinement → RH`. For distinct primes `p,q`, set `A=T_p²−1`, `B=T_q²−1`, and `t=tr(AB)`. The corpus proves `A²=B²=0` and `t≠0`; the source matrices also satisfy `AB+BA=t·1`. For **every** complex-linear readout `L`, put `O=L(AB)−L(BA)` and `F=L(ABBA)−L(AB)L(BA)`. Since `ABBA=0`, the exact source law is

`O² − 4F = t² L(1)²`.

Thus a unital order-blind port has the forced fusion defect `F=−t²/4≠0`. No choice of fixed linear readout can erase both defects. This is a finite four-word obstruction, not an assumption that `L` is an algebra homomorphism.

## Positive survivor and scope

The conic is the sharp survivor: a multiplicative port must retain two-prime order, and an order-blind port must retain the displayed fourth-grade failure of multiplication. Ordered, nonlinear, nonlocal, and full rotating-cylinder ports remain open. The theorem does not assert that every local OAM-diagonal observable must be order-blind or multiplicative; it kills precisely the fixed linear Euler-port branch when those required landing properties are claimed.

Paper proof is the two matrix identities above followed by `(r−s)²+4rs=(r+s)²`, where `r=L(AB)`, `s=L(BA)`, and `r+s=tL(1)`. The exact tradeoff, rigidity, no-existence result, and literal-transfer identification are closed in [PhotonicPrimeLinearPortOrderFusionNoGo.lean](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeLinearPortOrderFusionNoGo.lean). Direct `lake env lean` and targeted `lake --old build ...:olean` pass; umbrella wired. No full build or computation was used.
