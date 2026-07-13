# Irrational-circle SEM holonomy collapse

- **ID:** `irrational-circle-sem-holonomy-collapse`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[OUTLANDISH DETOUR]`
- **Consumer:** `../3-formalized/not_new_scientific_knowledge/irrational-circle-order-charge.md`
- **Prime-circle input:** `../3-formalized/not_new_scientific_knowledge/weld-charge-faithfulness-dichotomy.md`
- **Concrete long source candidate:** `gauss-quasi-inner-determinant-phase-circle-rh.md`

## Claim

Fix one prime `p`, for example `p=2`.  Construct directly from the completed prime--Gamma source an
oriented circle-valued boundary character on every right-half symmetric Euler--Maclaurin window and
prove that its holonomy closes.  The character must agree with

```text
[completed SEM contour index * log p] in R/Z.             (1)
```

Because `log p` has infinite order modulo `Z`, closure of `(1)` forces the integral contour index to
be zero.  The existing SEM index theorem then excludes every right-half Xi zero and proves RH.

## Two-ended chain

```text
completed Euler--Gamma source
  -> right-half oriented finite-window boundary character in R/Z
       [OPEN CORE A: source construction without a zero list]
  -> identify its holonomy with [SEM index * log p]
       [OPEN CORE B: source-to-contour comparison]
  -> source constraint closes the holonomy
       [OPEN CORE C: annihilation/trivialization]
  -> SEM index = 0, by infinite order of [log p]
       [PROVED: primeOrderCircleCharge_eq_zero_iff]
  -> every right-half local Xi order is zero
       [PROVED: completedSEMContourIndexZ_eq_xiOrder]
  -> no Xi zeros right of the critical line
  -> RH.
```

The target end is completely closed in Lean by
`riemannHypothesis_iff_all_completedSEMPrimeCircleCharges_close`.

## Why this differs from the dyadic and arbitrary-modulus routes

A finite target `Z/qZ` kills every additive character out of the divisible real prime-flux channel;
recovering integer order then needs unbounded moduli.  The circle `R/Z` is divisible and has
unbounded exponent.  The prime-log character survives there faithfully, and its restriction to a
single prime detects an arbitrary integer order in one shot.

The route therefore exchanges

```text
all finite-depth closures
```

for

```text
one irrational holonomy closure.
```

## Firewalls

### Target-side definition is not source closure

Defining `(1)` from `analyticOrderAt Xi` or from a SEM split that already lists the enclosed zeros is
only the proved criterion.  The missing character must be constructed from the prime--Gamma source
before the divisor is known.

### Orientation is load-bearing

Critical-line Xi zeros have positive order and hence nonzero prime-circle charge.  A global theorem
annihilating `(1)` at every zero is false.  The source construction must be genuinely right-half
oriented: it closes only the anti-critical-line window defect, not the local charge of fixed
critical-line zeros.

### Completed-ratio collapse is too coarse

The ordinary all-place local-factor ratio regularizes to the identity by the functional equation.
Its multiplication symbol has zero holonomy everywhere and cannot distinguish right-half windows.
The desired circle class must survive as a secondary finite-window boundary anomaly before this
ordinary scalar collapse.

More sharply, the formal theorem `primeOrderCircleCharge_reflectionPair_zero` proves that a paired
order contributes

```text
[m log p] + [-m log p] = 0
```

for every `m`.  Total FE-pair holonomy is therefore tautologically closed even off RH.  The source
object must be half-polarized, with the complementary half controlled rather than simply added.

### Prime-circle faithfulness does not imply annihilation

The prime-circle theorem says that real prime flux is visible; it does not say the phase vanishes.
The new scientific content must be the source constraint that closes the oriented finite-window
character.

### Normalized prime-flux residue is position- and multiplicity-blind

`CompletedPrimeFluxFittingAttachment.lean` proves that the normalized continued prime flux has
residue `-1` at every strip Xi zero and that this scalar matches the canonical non-split Fitting
boundary.  The normalization has divided out the local order.  It therefore cannot distinguish a
right-half zero from a critical-line zero and cannot close `(1)`.

The positive obligation is exact: the comparison must retain the **unnormalized** integral period
or contour index through the source boundary map, and orientation must be imposed before any
normalization that turns all nonzero multiplicities into the same scalar.

## Open core

`[CONJECTURE] [OPEN CORE A]` Produce a canonical `R/Z`-valued differential character from a
right-half prime--Gamma SEM window, compatible under changes of annulus and truncation, without
choosing Xi zeros or their multiplicities.

`[CONJECTURE] [OPEN CORE B]` Prove that its characteristic boundary is the integral SEM contour
index times the one-prime weld `log p`, including the sign/orientation convention.

`[CONJECTURE] [OPEN CORE C]` Derive trivial holonomy from a source homotopy or exact completed
constraint that remains nontrivial before the all-place ratio collapses to `1`.

## Concrete long-detour realization

`gauss-quasi-inner-determinant-phase-circle-rh.md` proposes a source for this differential
character.  The finite-place Gauss-component theory already has an explicit moving phase on
`L^2(R/Z)` and an exact critical weak-Schatten magnitude.  Its proved positive residue erases the
phase; the proposed successor retains the unsquared component in a relative determinant/eta class,
assembles the Gauss components and places, and takes a secondary window limit before the ordinary
all-place multiplier collapses to `1`.

## Positive pressure from the no-go theorems

The circle target evades both bounded-exponent collapse and packet-rank amplification.  It cannot be
reduced to untwisted Tate orbit type because its faithfulness comes from the irrational prime-log
period.  The price is exact: the missing object must be a right-half-oriented secondary differential
character, not a finite rank, ordinary determinant, scalar completion ratio, or divisor-fed phase.

## Status

- `[PROVED]` one fixed prime-circle phase is faithful on every integer order;
- `[PROVED]` its closure on all right-half SEM boundaries is equivalent to RH;
- `[OPEN]` source construction of the oriented circle character;
- `[OPEN]` source-to-SEM index identification;
- `[OPEN]` source-only holonomy closure.
- `[CLOSED SHORTCUT]` normalized prime-flux/Fitting scalar coincidence is multiplicity-blind.
