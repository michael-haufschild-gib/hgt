# Relation--incidence horizon fusion

- **ID:** ULF-RIHF-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Parent:** `1-in-progress/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`

## Statement

For a linear relation `R subset X directSum Y`, write

```text
Mul(R) = {y | (0,y) in R}.
```

For a linear incidence map `delta : Y -> Z`, define

```text
Tot_delta(R) = {(x,y) in R | delta y = 0}.
```

Then

```text
Mul(Tot_delta(R)) = Mul(R) inter ker(delta).          (RIHF.1)
```

In the actual HGT specialization, one strict-right Xi copy has scalar vertical fibre `C`, while
the all-cross-prime packet differential has kernel exactly `C eta`, where `eta` is its unit-norm
full-support horizon.  Therefore incidence converts the replicated off-line vertical fibre into
one prime-mixed line:

```text
Mul(Tot_delta(R_theta(q))) = C eta,
dim_C Mul(Tot_delta(R_theta(q))) = 1.                 (RIHF.2)
```

Its orthogonal projector is

```text
T_q x = <eta,x> eta = |eta><eta|,
Tr T_q = 1.                                          (RIHF.3)
```

## Proof

For `(RIHF.1)`, unfold definitions:

```text
y in Mul(Tot_delta(R))
iff (0,y) in R and delta y = 0
iff y in Mul(R) and y in ker(delta).
```

Closedness is preserved when `R` is closed and `delta` is continuous, since `Tot_delta(R)` is the
intersection of `R` with the inverse image of the closed subspace `{0}`.

For `(RIHF.2)`, `deningerMeyerHalfDensityXiGraph_fullVertical_of_offline` gives the complete scalar
vertical fibre for the strict-right support point.  Embed that scalar diagonally into the actual
cross-prime packet using `c |-> c eta`.  The theorem
`ker_deningerCalderonWittPacketKoszulDifferential` identifies the incidence kernel with the range
of this embedding.  Since `eta` is nonzero, the range has dimension one.

For `(RIHF.3)`, `||eta||=1`; the rank-one operator `|eta><eta|` is the orthogonal projector onto
`C eta`.  Its trace is `<eta,eta>=1`.

## Meaning for ULF-INHD-001

The target integer is no longer conjectural and no Hodge/Fredholm surrogate is needed.  Closed
relation verticality supplies the local integer; all-cross-prime incidence makes it one global,
prime-mixed unit.  Remaining RH-bearing theorem is solely the pre-divisor source identity

```text
Pi_Mul(R_theta^+(s)) - Pi_Mul(R_ar^+(s))
  = A_s* Gamma_hom A_s,
||A_s||_2^2 < 1.
```

At a strict-right specialization, the left side is `(RIHF.3)`, while the right side has trace norm
strictly below one.

## Lean dependencies and target

Existing certificates:

- `RHTower.DeningerMeyerHalfDensityXiGraphClosure`
- `RHTower.DeningerMeyerHalfDensityFiniteXiVerticalDefect`
- `RHTower.DeningerCalderonWittAllCrossPrimeIncidenceKoszul`
- `HTGeometry.PointedFisherCutoffWardTrace`

New target module:

```text
RHTower.IntegralNuclearRelationIncidenceHorizon
```

It must define the actual strict-right scalar-to-packet horizon, prove it equals the cross-prime
incidence kernel, define the rank-one `T_q`, and prove its trace is one.  No RH premise or new
axiom is permitted.

