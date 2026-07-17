# Opposite-variance comparison defects obey a boundary-channel conservation law

- **ID:** `opposite-variance-seam-conservation`
- **Stage:** 3-formalized
- **Type:** GENERAL CLOCK COMPARISON THEOREM / BOUNDARY CURRENT LAW
- **Scientific status:** `[LEAN-FORMALIZED] [EXACT POSITIVE THEOREM] [NOVELTY OPEN]`
- **Parents:**
  - `../1-in-progress/source-anomaly-boundary-colligation-field.md`
  - `../1-in-progress/gamma-opposite-variance-weyl-seam.md`
- **Statement:** When one realization is forward Ind-flat and two parameter-adjacent algebraic
  realizations are backward Pro-flat, the retained block of their higher comparison defect equals
  the lower defect plus the composition of the outgoing and incoming boundary channels.

## Setup

Let `p i=1`. Write `A_0,A_1` for an analytic realization, `B_0,B_1` for an algebraic realization,
and `C_0,C_1` for its source-parameter-shifted copy. Assume

```text
A_1 i=i A_0,                                               (1)
p B_1=B_0 p,                                               (2)
p C_1=C_0 p.                                               (3)
```

Define

```text
R_N=A_N B_N-C_N A_N,                                      (4)
kappa_A=p A_1-A_0 p,                                      (5)
gamma_B=B_1 i-i B_0.                                      (6)
```

Here `kappa_A` is the outgoing channel and `gamma_B` is the incoming channel.

## Conservation theorem

The exact Lean-formalized identity is

```text
p R_1 i=R_0+kappa_A gamma_B.                              (7)
```

Thus an old-clock comparison defect cannot simply disappear at the next resolution. It can change
only by the round trip through the paired boundary channels.

For the Gamma Weyl seam, Lean now proves

```text
R_N=-N v_N tensor top_N,
kappa_A gamma_B=+N v_N tensor top_N,                      (8)
```

so `(7)` makes the old block vanish exactly: the entire defect is recreated at the newest
boundary. This is boundary-charge migration.

The specialization is the exact map identity

```text
gammaClockWeylSeam n z=-gammaClockPairedBoundaryCurrent n z,
```

not an equality of dimensions, ranges, or determinants.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockIncomingDefect`;
- `clockComparisonSeam`;
- `truncate_comp_clockComparisonSeam_comp_extend`.

`GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona` contains the Gamma specialization:

- `gammaClockWeylSeam`;
- `gammaClockWeylSeam_apply`;
- `gammaClockWeylSeam_eq_neg_pairedBoundaryCurrent`.

The existing object cache was reused and the touched module passed direct Lean verification. No
build was run.

## Scientific boundary and significance

Equation `(7)` is a split linear comparison identity, so novelty is not claimed from the algebra
alone. Its nontrivial positive content is a rigid compatibility test for the proposed unified
field: two obstruction realizations can represent one source only if their finite comparison
defects obey the same boundary-current law. A common spectrum without `(7)` is insufficient.

The candidate-new result is a source-topological extension of `(7)` in which the current is
presentation-independent, nonterminating precisely in the HT phase, and preserved by analytic,
spectral, continuation, and polarized realizations.

## Gates

- [x] incoming defect defined
- [x] comparison seam defined
- [x] exact old-block conservation law Lean-formalized
- [x] direct Lean verification passed
- [x] Gamma rank-one cancellation specialized in Lean
- [ ] source-topological current constructed
- [ ] comparison across two genuinely different analytic categories proved
- [ ] novelty and significance independently audited
