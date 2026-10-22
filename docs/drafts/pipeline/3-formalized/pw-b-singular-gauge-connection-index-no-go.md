# PW-B singular-gauge connection-index no-go

- **ID:** PW-B-SINGULAR-CONNECTION-INDEX
- **Stage:** 3-formalized
- **Type:** NO-GO THEOREM
- **Source:** `rh-current-frontier-map.md` PW-B surviving operator-domain/connection-invariant core
- **Statement:** In logarithmic recoil coordinate `t = log x`, the exact PW singular gauge has potential `phi(t) = sinh(t) - t/2`; both covariant derivatives `d/dt - phi'(t)` and `d/dt + phi'(t)` have trivial finite-energy horizontal kernel, while every positive reflection-unitarizing density is `exp(-2 phi(t)) h(t)` for a positive even `h`.

## Goal
Kill the last PW-B proposal that the singular Borel-edge gauge, by itself, supplies a nonzero
operator-domain or Witten/connection index selecting the self-dual wall. Full attempted RH chain:

`literal finite-energy PW first winding -> singular FE partner -> intrinsic singular-edge index -> partner balance -> Deninger Ward -> every Xi divisor is balanced -> RH`.

This test significantly reduces the remaining proof burden if true: the exact gain alone cannot
produce the required source-independent calibration. Any surviving PW-B proof must add a physical
domain/measure normalization not determined by the singular carrier, or derive partner balance
directly from source dynamics.

## Gates
- [x] 0 -> 1  in-progress: source-pure exact gain, explicit logarithmic gauge, attack idea, RH chain named
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 -> 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Put

`phi(t) = sinh(t) - t/2`, `g(t) = exp(phi(t))`, and `a(t) = exp(2 phi(t))`.

The exact positive-ray PW gain obeys `pwSingularReflectionGain(exp t) = a(t)` and `phi(-t) = -phi(t)`.
Its gauge connection is forced by logarithmic differentiation:

`phi'(t) = cosh(t) - 1/2 > 0`.

For a differentiable horizontal section, multiplication by the inverse gauge converts
`f' = phi' f` into `(f/g)' = 0`; hence `f = c g`. The opposite orientation similarly gives
`f = c/g`. Since `phi(t) >= t/2` on `t >= 0` and `phi(t) <= t/2` on `t <= 0`, `g^2` dominates
`exp(t)` on the right and `g^(-2)` dominates `exp(-t)` on the left. Thus neither nonzero
horizontal section is square-integrable.

For the maximal weighted reflection `T f(t) = a(t) f(-t)`, norm preservation in density `w`
is pointwise equivalent to

`w(-t) = a(t)^2 w(t)`.

Using `a(-t) = a(t)^(-1)`, all positive solutions are exactly

`w(t) = a(t)^(-1) h(t)`, with `h(-t) = h(t)` positive.

## Hostile attacks
1. **Coordinate artifact:** derive `a(t)` from the already-rigid positive-ray carrier, not a chosen model.
2. **Hidden zero mode:** classify every differentiable horizontal section before applying tail bounds.
3. **Only one orientation checked:** prove trivial finite-energy kernel for connection and formal adjoint orientation.
4. **A canonical weighted Hilbert space survives:** classify every symmetrizing positive density; arbitrary positive even `h` remains.
5. **Route overclaim:** kill only invariants determined by the singular gauge through its first-order connection or reflection-unitarizing density. Do not claim arbitrary source-domain laws impossible.

## No-go closure
- **Exact killing theorem/mechanism:** `[FALSIFIED][ROUTE-CLASS KILL][PROVED HERE][LEAN-PROVED]`. The exact gauge potential is `phi'(t) = cosh(t)-1/2`. Every horizontal section of the two connection orientations is respectively `c exp(phi(t))` or `c exp(-phi(t))`. The first has a positive floor on the right half-line, the second on the left, so finite square energy forces `c=0` in both cases. Therefore the natural kernel-imbalance/Witten index carries no PW balance charge.
- **Strongest positive survivor:** Every positive reflection-unitarizing density is exactly `w(t)=a(t)^(-1)h(t)` for an arbitrary positive even `h`. For all such densities, weighted reflection preserves both the maximal finite-energy domain and exact total quadratic energy. This is a complete symmetrizing-density classification, not merely the negative kernel statement.
- **New insight:** Singular Borel asymptotics do affect which neutral-space multiplication operators are unbounded, but they do not canonically choose a Hilbert geometry. Gauge data determine only the odd part of `log w`; the even part is free. A surviving PW-B chain now needs an independently source-normalized measure/domain or a direct source-dynamical partner-balance theorem.
- **Paper-proof status:** Dependency-closed. Log-coordinate algebra gives `a=exp(2phi)` and oddness of `phi`; product differentiation classifies both horizontal equations; half-line hyperbolic bounds prove nonintegrability; reciprocal gain algebra classifies all densities; measure preservation of `t -> -t` proves exact maximal-domain and energy invariance.
- **Lean status:** `RHTower.pwSingularGauge_connectionIndex_noGo` in `ThetaCuspHawkingParikhWilczekSingularGaugeConnectionIndexNoGo.lean`. Direct `lake env lean` and targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularGaugeConnectionIndexNoGo` pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `GaloisForLFunctions.RHTower`; global lint remains red only on unrelated pre-existing umbrella-reachability debt and reports no failure for this module.
- **Novelty status:** Corpus audit found the exact singular carrier and its algebraic rescaling no-go, but no logarithmic connection-index, maximal-domain, or symmetrizing-density classification. Bounded primary-literature audit found general unbounded weighted-composition operator theory, not this exact PW gain or its RH-route consequence. Priority claim remains bounded rather than absolute.

## Log
- 2026-08-30 — created directly in 1-in-progress from the frontier map's surviving PW-B singular operator-domain/connection branch.
- 2026-08-30 — hostile conjecture falsified; strongest classification proved on paper and formalized in Lean; moved to stage 3.
