# CCM ramification-density monodromy selection law

- **ID:** CCM-C36
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [CORPUS-NOVEL COMBINATION]`
  `[UNIVERSAL NORMED TARGET] [FINITE+INFINITE SCALAR DECK] [EXTERNAL NOVELTY OPEN]`
  `[NOT RH] [NOT WHOLE-CCM DEATH]`
- **Source:** `docs/handover/connes.md` §§73--77; C33--C36
- **Statement:** Positive first-order thermal density on any exponentially parametrized
  norm-holomorphic branch quantizes its ramification rate by one positive integral analytic
  charge; deck descent forces that charge into the trivial character. Nontorsion scalar deck
  descent is impossible, while finite primitive deck geometry is forced to even degree with sign
  monodromy.

## Goal

Decide the ramified analytic survivor left by C35. Remove the finite-rank, finite-dimensional, and
fixed unramified-germ restrictions, and determine whether finite or infinite scalar deck geometry
can descend a norm-holomorphic boundary branch carrying the CCM four-unit density.

## Exact universal theorem

Let `E` be any complex normed space, `q>0`, and `F : C -> E` analytic at zero. Define

```text
Delta_(q,F)(h)
  = ||F(exp(-q h))||^2 / (1-exp(-exp(-h))).             (C36.1)
```

If `Delta_(q,F)(h) -> ell` for any finite `ell>0`, then analytic order is automatically finite and

```text
m = ord_0(F) > 0,
2 q m = 1.                                              (C36.2)
```

No nonzero/local-finiteness premise is needed: positive density rules out the locally-zero branch.

Let `zeta : C` be any scalar deck generator and suppose the branch descends locally,

```text
F(zeta z)=F(z).                                         (C36.3)
```

Then its leading coefficient obeys

```text
zeta^m=1.                                               (C36.4)
```

Consequently:

1. if `zeta` is nontorsion (`zeta^n != 1` for every `n>0`), no positive finite density exists;
2. if `zeta` is primitive of finite order `r` and `q=1/r`, then `2m=r`, hence `r` is even and
   `zeta^m=-1`;
3. a finite primitive branch that is also deck invariant would require both `zeta^m=-1` and
   `zeta^m=1`, so no positive finite density exists.

These statements hold for arbitrary vector-, Hilbert-, Hilbert--Schmidt-, operator-, or
Schatten-valued analytic germs. Dimension, rank, completeness, compactness, and scalarization do
not enter.

## Proof `[PROVED HERE]`

The exact denominator law is

```text
exp(-h)/(1-exp(-exp(-h))) -> 1.                         (C36.5)
```

If `m=ord_0(F)<infinity`, norm-valued analytic factorization gives

```text
F(z)=z^m G(z),    G(0)!=0.
```

Along `z=exp(-qh)`, `(C36.1)` factors exactly as

```text
Delta_(q,F)(h)=exp((1-2qm)h) U(h),
U(h)->||G(0)||^2>0.                                    (C36.6)
```

A finite positive limit on the left forces the exponential rate in `(C36.6)` to vanish, proving
`(C36.2)`. If analytic order were infinite, `F(exp(-qh))` would be eventually zero, contradicting
`ell>0`; thus finiteness is derived.

For deck descent, compare the leading factorizations at `z` and `zeta z`, cancel `z^m` off the
origin, and take `z->0`. Since `G(0)!=0`, the result is `(C36.4)`. A nontorsion generator contradicts
`m>0`. For a primitive `r`th root, `(C36.4)` is equivalent to `r|m`; with `2m=r`, this is impossible.
Without descent, primitiveness and `2m=r` instead give `(zeta^m)^2=1` and `zeta^m!=1`, hence the
surviving branch character is exactly `-1`.

Every dependency above is proved in Lean. No RH premise, zero-free premise, asymptotic conjecture,
numerical computation, truncation, finite-rank premise, or custom axiom is used.

## CCM consequence

At the exact CCM normalization `ell=4`, every fixed norm-holomorphic scalar ramification obeys the
same selection law. C35 left ramified analytic orbits as a possible escape; C36 closes all such
orbits that descend under a finite primitive scalar deck group or an infinite-order scalar deck
generator. A branch-selected finite cover can survive only with sign monodromy and therefore does
not define a single-valued descended source map.

This is not RH and not death of whole CCM. It does not cover logarithmic universal covers,
non-scalar deck representations, aperture-dependent families with no fixed germ, nonanalytic
boundary maps, or closed graph topology invisible to ambient norm. Exact CCM endpoint remains

```text
D_Xi = closure(P_- M_(-2 Xi'/Xi)),
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,                   (C36.7)
```

equivalently source-normalized Evans nonvanishing. Next attack must derive `(C36.7)` from exact
source geometry or prove that every remaining logarithmic/graph-singular transport is impossible.

Analytic factorization and primitive-root algebra are classical ingredients. Corpus search found no
prior combined arbitrary-rate density--charge--monodromy theorem or its CCM four-unit connector.
External literature novelty remains open and must not be advertised as settled.

## Formal declarations

Module `formal/GaloisForLFunctions/RHTower/CCMFiniteRamifiedBoundaryNoGo.lean`:

- `analyticRamifiedBoundaryDensity`;
- `finiteRamifiedAnalyticBoundaryDensity`;
- `analyticOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos`;
- `two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos`;
- `analyticOrderNatAt_deckCharacter_eq_one_of_deck_invariant`;
- `analyticRamified_boundaryDensity_deckInvariant_chargeLaw`;
- `not_exists_analyticRamified_infiniteDeckInvariant_positiveBoundaryDensity`;
- `two_mul_analyticOrderNatAt_eq_ramification_of_boundaryDensity_pos`;
- `finiteRamified_boundaryDensity_forces_even_and_deckCharacter_neg_one`;
- `not_exists_finiteRamified_deckInvariant_positiveBoundaryDensity`;
- `ccmFourUnit_not_analyticRamified_infiniteDeckInvariant`;
- `ccmFourUnit_not_finiteRamified_deckInvariant`.

## Gates

- [x] corpus search across `HTGeometry`, `RHTower`, `HilbertMetric`, formalized cards, paper cards,
  and failed routes
- [x] dependency-closed paper proof
- [x] direct Lean check
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no finding in this module; repository-wide lint fails on
  pre-existing umbrella-reachability findings in other dirty-tree modules
- [x] targeted final module build:
  `GaloisForLFunctions.RHTower.CCMFiniteRamifiedBoundaryNoGo`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 — Proved arbitrary-rate density--charge law, arbitrary scalar deck-character law,
  infinite-order scalar deck exclusion, finite primitive sign selection/exclusion, and exact CCM
  four-unit connectors in arbitrary complex normed targets.
