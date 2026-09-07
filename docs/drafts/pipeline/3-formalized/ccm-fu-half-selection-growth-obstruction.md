# CCM-FU: unbounded actual half-selection mean and energy

- **Stage:** 3-formalized
- **Type:** unconditional growth obstruction and exact continuation transfer
- **Source:** [refuted PE5 average](../5-failed/ccm-fu-bernoulli-prime-energy.md)
- **Boundary:** independent half-probability averaging fails. Adaptive PE4, final SD1 and RH remain open.

## Closed statements

For the literal mean `H(M)=sum_d mu(d)K_d(M)/2^omega(d)`, every real C and every cutoff M₀ admit an M>=M₀ such that `C*M<|H(M)|`. This is unbounded magnitude of the normalized actual source on every tail; no sign or precise asymptotic is asserted.

For the literal averaged energy E at probability one half and original diagonal `Q(M)=sum_d C_d(M)^2`, every real K and M₀ admit M>=M₀ with `K*Q(M)<E(M)`. Hence no fixed multiplier and finite cutoff repair PE5. The direct theorem `not_forall_mobiusDivisorHalfSelectionEnergy_le_initial` expresses its original factor-one failure.

## Exact source transfer

Let `g=a*b`, with the already formal literal coefficients `a(n)=mu(n)/2^omega(n)` and `b(n)=log(n)-tau(n)+2 gamma`. Write `G_N=sum_(n<=N)g(n)` and `A_N=sum_(n<=N)(sqrt(n+1)-sqrt(n))*G_n=H(N+1)`.

The reciprocal clock `u(x)=sqrt(x)+sqrt(x+1)` satisfies `u(x)*(sqrt(x+1)-sqrt(x))=1`. For `f_s(x)=u(x)*(x^(-s)-(x+1)^(-s))`, two exact finite Abel identities give

`sum_(n<=N)g(n)n^(-s)=G_N*(N+1)^(-s)+A_N*f_s(N+1)+sum_(n<=N)A_n*(f_s(n)-f_s(n+1))`.

For x>=1 and positive sigma=Re(s), the symbolic kernel estimates are

`|f_s(x)|<=3|s|x^(-sigma-1/2)`,
`|f_s(x)-f_s(x+1)|<=(3|s||s+1|+|s|)x^(-sigma-3/2)`.

If `|A_N|<=C(N+1)` with C>=0, the infinite transformed series is absolutely convergent locally uniformly on `Re(s)>1/2`, and is holomorphic there. The weighted-prefix boundary vanishes on that half-plane. The exact increment law gives `|G_N|<=6C(N+1)^(3/2)`, so the other boundary vanishes on `Re(s)>3/2`. Wherever the literal L-series converges absolutely in that latter half-plane, the series sum equals it.

Applying this transfer to the actual source contradicts the [closed no-continuation theorem](ccm-fu-half-selection-euler-pole-obstruction.md). No external growth, zero-location or Tauberian premise survives in the final obstruction. Absorbing finitely many values excludes every tail bound. Finally the existing inequalities `H(M)^2<=E(M)` and `Q(M)<=722M^2` turn a hypothetical averaged-energy budget into the forbidden linear mean bound.

## Lean audit

- `SquareRootAbelDirichletKernel.lean`:7 public theorems; reciprocal clock, analytic kernel and both power bounds.
- `SquareRootAbelDirichletContinuation.lean`:4 public theorems; pointwise bound, absolute and locally uniform summability, holomorphy.
- `SquareRootAbelDirichletTransfer.lean`:7 public theorems; finite prefix identities, two-stage Abel identity, summatory bound, both boundary limits and literal L-series equality.
- `MobiusHalfSelectionGrowthObstruction.lean`:7 public theorems; exact actual-source landing, unconditional linear-growth failure, every-tail growth, arbitrary-budget failure and direct PE5 refutation.

All four leaves passed foreground `lake env lean`; only their exact oleans were emitted. All25 new public theorems were axiom-audited once, with only `propext`, `Classical.choice`, and `Quot.sound`. No numerical certificate, added axiom or unproved source premise enters the results. All four imports are wired once into `RHTower.lean`; no umbrella or dependency build was run.

Global formal lint was run once. Its sole error concerns the concurrent, unwired `RHTower.ThetaCuspEffectiveLikelihoodCooling` module. None of these four leaves is flagged.
