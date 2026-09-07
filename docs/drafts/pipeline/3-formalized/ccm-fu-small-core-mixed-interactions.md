# CCM-FU: small-prime core of nonoverlapping mixed interactions

- **Stage:** 3-formalized
- **Type:** [BRIDGE], actual-source cancellation and uniform estimate
- **Goal:** Complete signed Abel bound and RH remain open.
- **Parent:** [exact successor extension](../1-in-progress/ccm-fu-exact-successor-extension.md).

## Exact cancellation

Fix distinct active unprocessed primes p,q with `p*q>=M`. Write
`E2(P)=Q_(P+p+q)-Q_(P+p)-Q_(P+q)+Q_P`. For every p,q-free retained
label R, write the four actual signed fibres as a,b,c,d at R, R+p,
R+q, R+p+q. The exact mixed identity is `E2(P)=2*sum_R(a*d+b*c)`.
The joint child d vanishes because its product is at least M. Therefore
`E2(P)=2*sum_R(b*c)`: the current parent field cancels completely.

Choose any `N>=max(floor(M/p),floor(M/q))+1` and put
`P_small={r in P : r<N}`. Prime interpolation expresses b as reflected
sqrt(p) times the exact clipped interpolation of the two source fibres
at cutoffs `floor(M/p)` and `floor(M/p)+1`, with the same P and R.
Every source label at cutoff n comes from an integer below n. Its prime
factors are therefore below n, so deleting processed primes at least N
cannot change either adjacent-cutoff fibre. The same argument applies
to c with q. Consequently

`E2(P)=E2(P_small)`.

This is an exact equality for the full signed mixed difference. There
is no bound or sign condition on the parent head, nonempty defects,
current energy, or number of other processed primes. The two primes
may occupy different quotient windows. The equality itself needs no
primality condition on P; the source amplitude estimate below does.

## Uniform bound

Apply the [localized source bound](ccm-fu-localized-mixed-interactions.md)
at P_small. The joint-child quotient is zero, giving

`|E2(P)| <= (18/25)*4^(max(card(P_small)-1,0))*M*floor((M-1)/max(p,q))`.

In particular, if both quotient cutoffs are at most L, choose N=L+1.
The core has at most L+1 elements, its natural exponent is at most L,
and the remaining quotient support has at most L elements. Hence

`|E2(P)| <= (18/25)*4^L*L*M`.

The constant depends only on quotient depth L, independently of the
full processed prime set and the number of already consumed large
primes. The product condition `p*q>=M` remains part of this result.

## Remaining source comparison

The extension target is one actual p satisfying
`Delta_p+Delta_q+E2(P;p,q)<=B-Q_P` for every other available q.
This theorem removes growth in the full processed-set cardinality from
nonoverlapping mixed pairs at fixed quotient depth. It does not pay the
first gains Delta, which still couple copied children to the current
parent field. Pairs with `p*q<M` retain the parent/joint-child term.
A complete extension proof must control those signed terms and unbounded
quotient depths under one budget. Neither a fixed-depth constant nor
pairwise absolute bounds supply that comparison. Complete extension,
PE4, SD1, the full signed Abel bound and RH remain open.

No numerical experiment was used: inactive source support and exact
four-coordinate cancellation determine these statements analytically.

## Lean surface and validation

`GaloisForLFunctions/RHTower/MobiusDivisorSmallCoreInteractions.lean` proves:

- `mobiusDivisorSelectionEnergy_mixed_eq_filter_cutoff`.
- `abs_mobiusDivisorSelectionEnergy_mixed_le_small_core`.
- `abs_mobiusDivisorSelectionEnergy_mixed_le_fixed_quotient`.

The existing localized-interaction module additionally exposes its exact
identity as `mobiusDivisorSelectionEnergy_mixed_eq`; its old estimates
and proofs are unchanged. All declarations are in namespace RHTower.

Complete scratch proofs and exact-file `lake env lean` checks passed
without warnings; only the changed dependency and new leaf oleans were
emitted. Each of the four new public declarations was axiom-audited once
from an external scratch file. All use only `propext`, `Classical.choice`,
and `Quot.sound`. No numerical premise or new axiom was introduced.
The new leaf is wired into `RHTower.lean`; no umbrella build was run.

The targeted Lake audit remains incomplete. The previously attempted
leaf `lake build --old ...:olean` expanded into prerequisite rebuilds;
that known expensive path was not repeated. This result is supported by
the successful exact-file Lean checks, not a claimed passing Lake build.
The corpus index refreshed successfully. Global `scripts/formal_tools.py lint`
reported one unrelated wiring error for concurrently added
`RHTower.MontgomeryPrimeSideIdentity`. The new CCM-FU module is reachable;
that foreign module was left to its owner. All owned Lean processes ended,
the process check found no running Lean/Lake process, and the four owned
scratch files were removed. This task made no frontier-map edit.
