# Mass-shifted native source contact residue

- **ID:** mass-shifted-native-source-contact-residue
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** §9.3 native adaptive mixed/completed first-contact producer

## Frozen conjecture

At every finite first contact, signed native adaptive source and newborn admission-norm leading
coefficient contain same first Padé defect.  Exact division cancels defect.  Resulting intrinsic
source/admission residue depends only on admission degree, contact order, and parity:

```text
even d: (2*m+d) / choose (2*m+d) d
odd d:  2 / choose (2*m+d) d.
```

Thus shrinking arithmetic defect is not independent escape mechanism.  Only increasing degree or
contact order can suppress native contact residue.

## Falsifiers

- Must use literal parity-native completed source, not generic bilinear surrogate.
- Sign must be inserted before quotient; odd native source is negative on right-chamber contact.
- Must prove actual strict-frontier norm-limit quotient, not only algebraic coefficient identity.
- No RH premise, computation, representing measure, or fixed reporter.

## Attack

Define canonical parity-selected native source value.  Extract even/odd witness from existing
first-contact source law.  Prove signed positivity and defect-cancellation identity.  Combine with
exact arbitrary-order newborn-norm limit to obtain universal strict-frontier residue.

## Log

- 2026-08-13 — frozen after corpus audit found native all-contact producer and exact newborn norm
  coefficient existed separately but had not been divided against each other.
- 2026-08-13 — proved parity-selected literal source value, forced multiplier, signed positivity,
  and division-free defect cancellation.
- 2026-08-13 — combined with arbitrary-order newborn-norm contact limit.  Native source/admission
  residue is universal and positive.  Simple odd and first even contacts both equal `2/(2m+1)`.
- 2026-08-13 — proved forced admission/contact counterweight converts every finite native residue
  to exact unit charge.

## Exact theorem

Put `m=n+2`, `delta=delta_(2m+d)`, and

```text
M(m,d) = if d even then 2*m+d else 2.
```

Parity-native completed source is exactly `M(m,d)*delta`.  Newborn norm coefficient is
`(-1)^d*choose(2*m+d,d)*delta`.  Hence signed scaled source/admission residue is

```text
R(m,d) = M(m,d) / choose(2*m+d,d) > 0.
```

No arithmetic defect magnitude remains.  Moreover

```text
[choose(2*m+d,d)/M(m,d)] * R(m,d) = 1.
```

This normalization is forced by same admission contact coefficient, not chosen reporting data.

Let `D_m(u)=det H_(m+1)(y+u)` and `Delta_m=det H_m(y)>0`.  Power-series uniqueness and exact
contact coefficient identify native source with first live analytic admission jet:

```text
iteratedDeriv j D_m 0 = 0                    for j < d,
M(m,d) * iteratedDeriv d D_m 0
  = d! * Delta_m * choose(2*m+d,d) * ((-1)^d * A_native),
0 < iteratedDeriv d D_m 0.
```

This removes normalization-choice objection.  Same source is canonical first nonzero determinant
jet, while residue law is its Schur/admission quotient.

## Lean

- `formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierNativeSourceContactResidue.lean`
- wired into `RHTower.lean`
- direct check and targeted module build pass
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only
- no computation, representing measure, infinite extension, RH premise, or added axiom

## Sharp boundary

Defect shrinkage and parity are closed as escape mechanisms.  Raw residue still decays with degree
and contact order.  Unit normalization removes that decay algebraically but requires combinatorial
admission weight, which may grow rapidly.  Remaining theorem is a common arithmetic action budget
that naturally pays this forced weight across cofinal degree--mass renewals.  Counting unit events
without proving finite weighted budget would be theatre.
