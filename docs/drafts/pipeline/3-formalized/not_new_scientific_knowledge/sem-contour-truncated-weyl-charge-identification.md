# Completed SEM contour / truncated-Weyl charge identification

- **ID:** `sem-contour-truncated-weyl-charge-identification`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SEMTruncatedJetWeylCharge.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

Let an actual completed symmetric Euler--Maclaurin split have finite hole count `d`.  At dyadic
depth `k`, its source-defined contour/Fitting charge satisfies

```text
integralCharge_(2^k)(completed SEM contour) = 0
  iff Bottcher.dyadicRoot(k)^d = 1.                       (1)
```

For every nonzero boundary holonomy `h`, this is also equivalent to

```text
h (1-Bottcher.dyadicRoot(k)^d) = 0.                      (2)
```

When `d=n+1`, the scalar in `(2)` is exactly the `(0,n)` entry of the boundary-completed
truncated-jet Weyl defect.  Therefore

```text
completed SEM contour charge vanishes
  iff the unique top-jet Weyl boundary anomaly vanishes. (3)
```

Simultaneously over all dyadic depths and all actual right-half SEM splits,

```text
RiemannHypothesis
  iff Bottcher.dyadicRoot(k)^d = 1
      for every k and every actual hole count d.             (4)
```

## Proof

`integralJetCharge_completedSEMContourBoundaryZ` identifies the contour charge with `d` in
`ZMod (2^k)`, so its vanishing is equivalent to `2^k | d`.  The named Böttcher phase is a primitive
`2^k`-th root, making divisibility equivalent to its `d`-th power being one.  Nonzero `h` can be
cancelled in `(2)`.  `boundaryCompletedJetWeylDefect_zero_last` identifies `(2)` with the matrix
wrap entry.

## Positive statement from the no-go

The Fitting/contour and crossed-product/Weyl programs do not possess two independent gaps.  They
are two readers of one obstruction:

```text
source contour class = dyadic boundary holonomy class.
```

A proof that merely translates between these readers cannot prove RH; it is tautologically exact.
The positive residue is nevertheless decisive: any viable detour must supply a source theorem that
annihilates this shared class.  Searching separately for “Fitting charge vanishing” and “invertible
Weyl completion” would duplicate the same open core.

## Formal surface

- `completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount`
- `completedSEMContourCharge_zero_iff_dyadicTopJetAnomaly_zero`
- `completedSEMContourCharge_zero_iff_boundaryCompletedJetWeylDefect_zero`
- `riemannHypothesis_iff_all_dyadicSEMPhaseHolonomies_close`

## Verification

`lake env lean GaloisForLFunctions/RHTower/SEMTruncatedJetWeylCharge.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is a formal bridge between existing count, primitive-root, and clock--shift theorems.  No
claim of new scientific knowledge is made.  Its significance is gap consolidation: two large
detours reduce to the same source-annihilation theorem.

## Gates

- [x] 0 -> 1: both obstruction readers stated on the same actual SEM split
- [x] 1 -> 2: exact equivalence proved
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; source annihilation remains open
