# Suzuki finite-contact width classification

- **ID:** SUZ-FCWC
- **Stage:** 3-formalized
- **Type:** THEOREM / route-class no-go
- **Source:** read-only `rh-current-frontier-map.md`; shared HB/FZZ-P/PW-B/RBH Ward producer

## Exact RH proof chain under test

For fixed `m ≥ 1`, put
`P_m(N) := E_N^m / C_N^(m-1)` (totalized at `C_N = 0`) and
`alpha_m := (m-1)/(2m)`.

`P_m = O(1)` → `G_N = O(N^alpha_m)` → `Q(log N) = O(N^alpha_m)` →
`Q(t) = O(exp(alpha_m t))` → critical-Mellin continuation on
`Re u > alpha_m - 1/2` → `XiZeroHalfPlaneBound alpha_m`.

Proved classification: order one is exactly the RH endpoint; every fixed order `m ≥ 2`
spends positive Mellin width and therefore fails as an endpoint-preserving repair through the
same compensation/CCM-abscissa mechanism.

## Corpus origin

Internal research search found the exact ingredients and no finite-order theorem:

- aligned completion: `G_N^2 ≤ E_N`, eventual `E_N ≥ 0`;
- transition core: eventual `C_N > 0` and `C_N ≤ D N`;
- completed outgoing-charge identity: `Q(log N)/2` equals Green plus uniformly bounded terms;
- logarithmic-lattice handoff: cell error at most `log 4 + 5`;
- exponential-width CCM theorem: `Q(t)=O(exp(alpha t))` with `0≤alpha<1/2` gives
  `XiZeroHalfPlaneBound alpha`.

Existing corpus stops at contact orders one and two. Search found no general finite-power residual,
no order-width law, and no theorem recovering the RH endpoint from a positive exponential rate.

## Literature audit through 2026-08-31

Suzuki's screw-function papers `arXiv:2206.03682`, `arXiv:2209.04658`, and
`arXiv:2606.09096`, together with Matsumoto--Suzuki `arXiv:2409.00888`, contain no
transition-core aligned-energy finite-contact residual or contact-order/zero-width law. Current
searches for nonlinear screw compensation, finite-contact renormalization, and Chebyshev-resolvent
power envelopes found no matching statement.

## Paper proof `[PROVED HERE]`

Assume eventually `P_m(N) ≤ B`, with `m ≥ 1`. Eventual positivity of `C_N` gives
`E_N^m ≤ B C_N^(m-1)`. From `G_N^2 ≤ E_N` and nonnegativity,

`|G_N|^(2m) ≤ E_N^m ≤ B D^(m-1) N^(m-1)`.

Let `y_N=exp(alpha_m log N)`. Algebra gives `y_N^(2m)=N^(m-1)`. For
`z_N=|G_N|/y_N`, therefore `z_N^(2m)≤B D^(m-1)`. The root-free inequality
`z≤z^(2m)+1` for `z≥0`, `m≥1`, yields

`|G_N| ≤ (B D^(m-1)+1) exp(alpha_m log N)`.

The exact Green/outgoing-charge identity transfers this to logarithmic samples of `Q`; the exact
cell handoff and a compact initial interval give the global exponential envelope. The existing
quantitative CCM continuation then gives `XiZeroHalfPlaneBound alpha_m`. Since `alpha_1=0`, order
one is the RH criterion already in the corpus. Since `0<alpha_m<1/2` for every `m≥2`, every higher
finite contact loses endpoint width.

Sharpness is not inferred from the positive exponent. For every `m≥2` and every proposed uniform
Green bound `K`, take `R=K+1` and the algebraic packet

`C=R^(2m)`, `E=R^(2(m-1))`, `G=R^(m-1)`.

Then `C>0`, `E≥0`, `G^2=E`, and `E^m/C^(m-1)=1`, while `G≥R>K`. Hence no uniform Green bound
follows from the finite-contact inequalities at any higher fixed order. This is the exact endpoint
obstruction needed to kill the compensation mechanism rather than merely exhibit a weaker bound.

## Hostile audit

- Scope is mechanism-exact: this kills endpoint preservation through generated growth plus CCM
  abscissa continuation, not every conceivable implication from `P_m=O(1)` to RH.
- No root extraction or hidden positivity premise: all powers are natural and `C_N>0` only
  eventually, exactly where division is canceled.
- No numerical optimization: theorem classifies the full infinite family of finite contact orders.
- A surviving higher-contact route must prove new cancellation improving `N^alpha_m` to `N^0`;
  the residual bound alone does not supply it.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean`.

- `suzukiTransitionCore_finiteContact_widthClassification`: order one is equivalent to RH; every
  order `m≥2` gives `XiZeroHalfPlaneBound ((m-1)/(2m))` with width strictly between `0` and `1/2`.
- `suzukiFiniteContact_algebraicEndpointNoGo`: closed sharpness theorem ruling out every uniform
  Green bound from unit-bounded higher finite-contact packets.
- `suzukiTransitionCoreFiniteContactResidual_two_eq_quadratic` and
  `suzukiFiniteContactWidth_two`: the general law recovers the quadratic residual and width `1/4`.
- Generic logarithmic-lattice propagation is proved for arbitrary nonnegative exponential rate.
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`.
- Targeted build: `13735/13735` passed.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reports no issue in this module; repository-wide failures are pre-existing unwired
  concurrent modules.

## No-go closure

- **Killed class:** every fixed nonlinear contact order `m≥2` used as an endpoint-preserving
  Suzuki/CCM compensation mechanism based only on transition-core growth and CCM abscissa.
- **Exact obstruction:** residual control permits algebraically unbounded Green amplitude and, for
  actual Suzuki quantities, yields the positive width `alpha_m=(m-1)/(2m)`.
- **Strongest positive survivor:** quantitative zero-free half-plane
  `XiZeroHalfPlaneBound alpha_m` for every fixed contact order.
- **Replacement hypothesis:** any surviving nonlinear-contact route must add a cancellation law
  strong enough to turn `G_N=O(N^alpha_m)` into `G_N=O(1)` before CCM continuation.

## Gates

- [x] corpus audit and exact four-route chain
- [x] current-literature novelty audit
- [x] conjecture C2 and hostile audit
- [x] dependency-closed paper proof
- [x] Lean formalization and targeted audit
