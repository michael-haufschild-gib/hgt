# Route RP: nonpositive complete-period packet payment fails

- **ID:** RP-25-period-sign
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/reports/rh-current-frontier-map.md`, route RP; RP-24/25 working log.
- **Statement:** Complete divisor packets cannot be assigned an eventually nonpositive full-period logarithmic half-order response, even after every quotient label is active.

## Goal

The candidate extended the verified nonpositive aligned birth value to each complete time period. Such a sign would have supplied local payments for a proposed assembly of the native signed history. Only this sign mechanism is retired. No RH conclusion or obstruction to bounded positive allowances follows.

## Gates

- [x] Well-posed actual arithmetic packet, retaining original Möbius and logarithmic coefficients.
- [x] Dependency-closed paper proof of the obstruction and positive survivor.
- [x] Formalized; targeted foreground `lake --old env lean <leaf> -o <olean>` audits passed. Separate axiom audit passed with exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] Publication-ready standalone paper.

No full or umbrella build was run, following the user's audit restriction. Global source lint reports ten unrelated unreachable modules; neither new leaf is flagged.

## Approach

Let `B_m(k)` be `routePCompleteLogarithmicRampRow m k`, with coefficient `mu(d)*(log(k)-log(d))`. For distinct primes p,q put L=p*q. The corrected quotient-ramp identity gives

`sum_{m|L} B_m(k) = log(k)*U(k)-V(k)`,

where U=(1+1/q)*ramp_p+(1+1/p)*ramp_q-ramp_L and V retains the fixed logarithms. Both channels have zero period mean. The quadratic primitive P of U satisfies

`sum_{k<L} P(k+1) = L*((1-p+1/p)*(1-q+1/q)-1)/12`.

This is strictly positive for p,q>=3. Write g_B(k) for the first difference of the half-order clock. Every fixed ratio g_B(k)/g_B(0) tends to one. Finite Abel summation therefore identifies the response divided by `log(B)*g_B(0)` with the positive primitive sum in the limit. The fixed V channel vanishes under this normalization. The logarithmic shift remainder also vanishes: its gap-normalized absolute size is uniformly bounded for each phase before division by log(B).

At B divisible by L, periodicity identifies this limit with the literal arithmetic window. Eventually B>=L^2, so every original hyperbola label is active. Infinitude of primes supplies unconditional cofinally late witnesses without numerical examples.

## No-go closure

- **Exact killing theorem:** `RHTower.not_routeP_full_period_packets_eventually_nonpositive`.
- **Strongest positive survivor:** Exact all-phase source decomposition, exact positive primitive sum, full logarithmic half-order response limit, and eventual strictly positive full-period response for every fixed distinct prime pair p,q>=3. `RHTower.routeP_positive_full_period_packets_cofinal` removes all analytic or RH premises from the witness statement.
- **New insight:** Completing a divisor packet and averaging a whole period does not restore the aligned birth sign. The signed Euler factor survives time summation. Any global payment argument must allow signed period contributions and control their actual aggregate.
- **Status:** Paper proof dependency-closed and formalized in `RoutePPeriodicLogWeightedAbel.lean` and `RoutePTwoPrimePacketTimeResponse.lean`. Twelve public theorems audited, with no added axioms or resource-limit overrides. An additional scratch proof verifies label activity throughout every late window from the retained square threshold.

## Log

- 2026-10-02 — Tested the complete-period extension of RP-24 aligned payment; formalized its failure and the exact surviving time coefficient. The complete native Route-P floor remains open.
