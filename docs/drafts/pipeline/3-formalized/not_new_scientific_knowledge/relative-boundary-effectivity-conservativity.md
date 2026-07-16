# Relative boundary effectivity and joint conservativity

- **ID:** `relative-boundary-effectivity-conservativity`
- **Stage:** 3-formalized
- **Type:** GENERAL DIFFERENCE-BOUNDARY BRIDGE / EXACT NO-GO WITH POSITIVE SUCCESSOR
- **Scientific status:** `[BRIDGE — NOT NEW SCIENTIFIC KNOWLEDGE] [LEAN-FORMALIZED]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/DifferenceDifferential.lean`
- **Analytic application:**
  `../../2-fully-proven/new_scientific_knowledge/irrational-elliptic-gamma-hypertranscendence-matroid.md`

## Exact boundary kernel

Let a field `K` carry commuting difference automorphisms `sigma_i` and a commuting derivation.  Put

```text
boundary(x)_i=sigma_i(x)-x.
```

Lean proves

```text
boundary(x)=boundary(y)
  iff x-y is fixed by every sigma_i.                         (1)
```

Thus the blind subspace of the complete boundary family is not guessed: it is exactly the joint
fixed field.

**No-go.** If there is a nonzero joint-fixed element, the unpointed boundary family is not
injective.

**Positive successor.** For any additive calibration `c`, the pointed observation

```text
x |-> (boundary(x),c(x))
```

is injective if and only if

```text
jointFixed(z) and c(z)=0 imply z=0.                          (2)
```

Calibration is therefore neither cosmetic nor automatically sufficient.  It is exactly the
separation of the residual joint-fixed gauge.

## Relative effectivity

Let `B` be an additive subgroup of the ambient field.  Define a relative boundary escape by

```text
boundary(x)_i in B for every i, but x notin B.               (3)
```

Assume every joint-fixed element belongs to `B`.  Lean proves that `(3)` is equivalent to

```text
boundary(x)_i in B for every i,
and there is no b in B with boundary(b)=boundary(x).         (4)
```

This is the exact zero-dimensional effectivity theorem behind a differential-algebraic anomaly:
all local source increments lie in the finite-law sector, but their compatible global primitive
exists only in a larger analytic sector.

The no-go and positive result are inseparable:

- local internality of all boundary observations does **not** imply internality of the primitive;
- the escaping primitive canonically certifies a nontrivial relative effectivity class, and `(4)`
  says exactly what it obstructs.

## Analytic meaning

For the irrational elliptic gamma function, take the ambient field to be meromorphic functions,
`B` to be the DA meromorphic sector, and the two automorphisms to be translation by `tau` and
`sigma` on the 1-periodic field.  The two logarithmic-theta boundaries lie in `B`; the joint fixed
field is `C`; and the elliptic-gamma logarithmic derivative escapes `B`.  Hence its paired boundary
is locally DA but has no DA primitive.  A scalar calibration kills the constant ambiguity and
makes the paired observation conservative.

The analytic premises are proved on paper in the application card, not by these generic Lean
declarations.

## Anti-theatre and novelty gate

Equations `(1)`--`(4)` are elementary kernel/intersection and relative-coboundary algebra.  In
cohomological language they are the degree-zero edge of the long exact sequence for a coefficient
inclusion.  They are useful because they state the exact interface needed by the analytic theorem,
not because they are scientifically new.

The candidate new knowledge is the nonzero class for the actual irrational elliptic gamma
function, together with its exact translation spectrum and matroid.  Lean verification of this
bridge is not evidence for the analytic novelty claim.

## Lean declarations

- `CommutingDifferenceDifferentialField.boundaryFingerprint`;
- `CommutingDifferenceDifferentialField.pointedBoundaryFingerprint`;
- `CommutingDifferenceDifferentialField.boundaryFingerprint_eq_iff_sub_jointFixed`;
- `CommutingDifferenceDifferentialField.pointedBoundaryFingerprint_eq_iff`;
- `CommutingDifferenceDifferentialField.pointedBoundaryFingerprint_injective_iff`;
- `CommutingDifferenceDifferentialField.boundaryFingerprint_not_injective_of_jointFixed`;
- `CommutingDifferenceDifferentialField.pointedBoundaryFingerprint_injective`;
- `CommutingDifferenceDifferentialField.RelativeBoundaryEscape`;
- `CommutingDifferenceDifferentialField.relativeBoundaryEscape_iff`.

## Gates

- [x] unpointed nonconservativity proved from a nonzero fixed gauge
- [x] calibration criterion proved as an if and only if
- [x] relative local-to-global no-trivializer criterion proved as an if and only if
- [x] every no-go paired with a positive retained object or exact successor
- [x] no analytic premise hidden in the Lean theorem
- [x] generic theorem demoted to bridge
