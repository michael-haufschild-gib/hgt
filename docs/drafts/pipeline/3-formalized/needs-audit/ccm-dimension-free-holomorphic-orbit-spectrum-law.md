# CCM dimension-free holomorphic-orbit spectrum law

- **ID:** CCM-C35
- **Stage:** 3-formalized/needs-audit
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [CORPUS-NOVEL CLASSIFICATION]`
  `[CLASSICAL ANALYTIC CORE] [EXTERNAL NOVELTY OPEN] [NOT RH] [NOT WHOLE-CCM DEATH]`
- **Source:** `docs/handover/connes.md` §§73--76; C32--C35
- **Statement:** Every norm-holomorphic filter on every norm-holomorphic orbit through the
  augmentation point of an arbitrary complex normed space has a complete aperture spectrum
  determined by one finite integer vanishing order, or annihilates the orbit eventually.

## Goal

Remove all finiteness, scalar, rank, coordinate-cardinality, and fixed finite polynomial
restrictions from the CCM shift-spectrum obstruction. Decide whether passing to an
infinite-coordinate Banach orbit, an operator ideal, or a joint holomorphic shift calculus can
create aperture exponents absent from the one-variable fixed-shift law.

## Exact universal theorem

Let `A` and `E` be arbitrary complex normed spaces. Let

```text
gamma : C -> A,      gamma(0)=0,
F : A -> E
```

be analytic at zero, fix `q>0`, and define the physical multiplier

```text
M_(gamma,F,q)(h)=||F(gamma(exp(-q h)))||.
```

Put `G=F circle gamma`. Exactly one branch occurs.

1. If `ord_0(G)=infinity`, then `M_(gamma,F,q)` is eventually zero.
2. If `ord_0(G)=m<infinity`, then for every eventually nonnegative carrier `eta` and every real
   `epsilon`,

```text
U(M_(gamma,F,q) eta,epsilon)
  <-> U(eta,epsilon+q m),                                (C35.1)
```

where `U(eta,r)` means `eta(h)<=C exp(rh)` eventually for some `C>=0`. Consequently the filtered
carrier has zero exponential type exactly when the original carrier has every rate strictly above
`q m`.

No dimension, rank, compactness, coordinate set, completeness, scalarization, or finite-stage
assumption occurs. `A` may be an infinite-coordinate Banach space or an operator/Schatten ideal;
`E` may itself be operator-valued.

## Finite joint-shift corollary

For a finite index type and positive integers `k_i`, the commensurate shift orbit is

```text
gamma_k(z)=(z^(k_i))_i.
```

An arbitrary joint analytic filter `F((z_i)_i)` therefore obeys `(C35.1)` with

```text
m=ord_0(z |-> F((z^(k_i))_i)).                           (C35.2)
```

This order is computed after every cross-shift cancellation. If the restriction vanishes locally,
the physical joint multiplier is eventually zero even when the ambient multivariable filter is
not locally zero. Thus finite commensurate multiorbit interaction supplies no escape from the
one-order spectrum law.

## Proof `[PROVED HERE]`

Analytic composition makes `G=F circle gamma` analytic at zero. Apply the complete normed-valued
one-variable factorization from C33. In the finite joint case, each coordinate `z^(k_i)` is
analytic and positive `k_i` gives `gamma_k(0)=0`; analytic Pi assembly and composition reduce it to
the universal theorem. The composite analytic order automatically includes every cancellation,
so no genericity or noncancellation premise is used.

All claims above are formalized. There is no RH premise, numerical computation, truncation,
finite-rank premise, or conjectural analytic-continuation step.

## CCM consequence

C33 closed one fixed norm-holomorphic coordinate but explicitly left joint and infinite operator
orbits as possible survivors. C35 closes every survivor which is a fixed norm-holomorphic orbit in
any complex normed topology. Increasing coordinate cardinality, passing to an operator ideal, or
using an arbitrary analytic readout cannot change the conclusion: all aperture information is one
integer order of the composite germ.

For the published completed critical-Mellin error, Lean specializes `(C35.1)` directly to
`eta(h)=|E_crit(h)|`. Hence no regular norm-holomorphic Banach-orbit filter proves the missing
zero-type law except by assuming the same shifted rate on `|E_crit|`.

This does not prove RH and does not kill singular/cofinal CCM. Exact survivor is now narrower:

- a non-norm-holomorphic or ramified boundary orbit;
- an aperture-dependent/cofinal family with no fixed germ;
- graph-topology information invisible to every ambient norm; or
- the actual source-defined nonexpansive transport into `Q_u D_Xi`.

The analytic composition and vanishing-order core is classical. Potential novelty is the complete
dimension-free CCM no-go classification and its exact completed-source connector; external novelty
remains open and must not be advertised as settled.

## Formal declarations

Universal module `formal/GaloisForLFunctions/RHTower/CCM/CCMAnalyticOrbitSpectrumRigidity.lean`:

- `analyticOrbitGerm`;
- `normedAnalyticOrbitMultiplier`;
- `analyticAt_analyticOrbitGerm`;
- `normedAnalyticOrbitMultiplier_eq`;
- `apertureExponentialUpperBound_normedAnalyticOrbit_complete_iff`;
- `subexponentialAtApertureInfinity_normedAnalyticOrbit_complete_iff`;
- `normedAnalyticOrbitMultiplier_eventually_eq_zero_of_order_eq_top`;
- `criticalMellinCompletedError_analyticOrbit_upperBound_iff`.

Explicit joint-shift module
`formal/GaloisForLFunctions/RHTower/CCM/CCMCommensurateJointShiftSpectrumRigidity.lean`:

- `commensurateJointShiftCurve`;
- `commensurateJointShiftGerm`;
- `normedCommensurateJointShiftMultiplier`;
- `analyticAt_commensurateJointShiftCurve`;
- `analyticAt_commensurateJointShiftGerm`;
- `apertureExponentialUpperBound_normedCommensurateJointShift_complete_iff`;
- `subexponentialAtApertureInfinity_normedCommensurateJointShift_complete_iff`;
- `normedCommensurateJointShiftMultiplier_eventually_eq_zero_of_order_eq_top`;
- `criticalMellinCompletedError_commensurateJointShift_upperBound_iff`.

## Gates

- [x] corpus search; no existing arbitrary-orbit or joint-shift theorem found
- [x] dependency-closed paper proof
- [x] direct Lean checks
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no finding in these modules; repository-wide lint fails only on
  pre-existing umbrella-reachability findings outside this card
- [x] targeted module build through
  `GaloisForLFunctions.RHTower.CCM.CCMBoundaryTraceRamification`
- [ ] external novelty audit
- [ ] RH or whole-lane no-go

## Log

- 2026-07-23 — Proved arbitrary normed-source/normed-target analytic-orbit spectrum law, locally
  zero branch, zero-type equivalence, and direct completed-error connector. Formalized finite
  commensurate joint shifts as explicit corollary, including all cross-shift cancellations.
