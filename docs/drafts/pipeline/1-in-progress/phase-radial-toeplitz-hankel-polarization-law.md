# Phase--radial Toeplitz--Hankel polarization law

- **ID:** `phase-radial-toeplitz-hankel-polarization-law`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CARRIER CONSTRAINT / REFLECTION GEOMETRY
- **Scientific status:** `[BRIDGE]` abstractly; combined HT/RH application `[NOVELTY UNVERIFIED]`

## Statement

Let `v_0,v_1,...` be vectors in a real Hilbert space.  Suppose their Gram kernel is invariant under
simultaneous forward translation,

```text
<v_(i+1),v_(j+1)> = <v_i,v_j>,                             (1)
```

as happens for an isometric or unitary phase orbit.  If the same kernel is Hankel,

```text
<v_i,v_j> = m_(i+j),                                       (2)
```

then

```text
m_(n+2) = m_n.                                             (3)
```

Consequently every Hankel matrix `[m_(i+j)]_(0<=i,j<d)` with `d>=3` has equal rows zero and two,
has determinant zero, and is not strictly positive definite.

Thus an all-order strictly reflection-positive carrier cannot be only a unitary phase orbit.  It
must possess a radial/self-adjoint semigroup polarization transverse to its phase polarization.

## HT geometry

Unit-phase prime coefficients naturally generate Toeplitz cross-Hadamard kernels: simultaneous
translation of the exponent labels preserves the Gram value.  Reflection-positive moment
problems generate Hankel kernels: the value depends on the sum of the labels.  Equations `(1)`--
`(3)` show that these are not two descriptions of one rich scalar orbit.  Their intersection has
rank at most two.

The positive carrier requirement is therefore bipolar:

```text
phase / unitary / Toeplitz polarization
                  x
radial / self-adjoint / Hankel polarization.                (4)
```

The two faces may be coupled by a reflection constraint, but they cannot be collapsed into one
all-order scalar Gram orbit.

## Interaction with the metric-radical law

The cofinite Gram-polarization theorem proves that changing strictly positive coordinate weights
changes the metric but not its radical.  Hence a full-support KMS/temperature reweighting cannot
manufacture the missing radial Hankel constraint from a phase Toeplitz carrier.  A genuine change
must occur through one of:

1. support loss;
2. passage to a non-summable boundary followed by a specified renormalization;
3. adjoining a transverse reflection/divisor coordinate.

This is a positive structural trichotomy for HT carriers, not merely a failed construction.

## RH application

The normalized continued prime--Gamma moments form the source-side Hankel sequence whose
reflection-positive realization is equivalent to RH.  The prime-orientation tail, by contrast,
is a phase/Hadamard object.  Therefore an RH-capable HT construction must retain both layers:

```text
prime phase tail  -> differential freedom and arithmetic pointing;
Xi reciprocal-square radial orbit -> reflected Hankel positivity.   (5)
```

The recent reciprocal-square realization uses a real positive spectral coordinate under RH,
exactly as `(4)` predicts.  The present law does not construct that radial orbit unconditionally;
it identifies why the prime phase orbit cannot substitute for it.

## Attacks

1. **Classical intersection attack.**  Toeplitz/Hankel structure and reflection-positive
   semigroups are classical.  The abstract two-periodicity theorem is a bridge, not new science.
2. **Rank attack.**  The rank collapse concerns one kernel simultaneously satisfying both laws.
   A larger block carrier may contain separate Toeplitz and Hankel components; this is the point
   of the bipolar requirement, not a contradiction.
3. **Weight attack.**  Positive reweighting can alter entries substantially, but the formal
   support-stratified radical law shows that it cannot alter which coefficient combinations have
   zero energy while the support is fixed.
4. **RH upcast attack.**  Bipolarity is necessary architecture, not sufficient for RH.  The open
   core is the source-built incidence law coupling the actual prime tail and archimedean
   completion to the canonical reciprocal-square Hankel moments.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/ToeplitzHankelPolarization.lean` proves:

- `hankelShiftInvariant_iff_twoPeriodic`;
- `det_momentHankelMatrix_add_three_eq_zero`;
- `not_posDef_momentHankelMatrix_add_three_of_shiftInvariant`;
- `hankelShiftInvariant_of_shiftInvariantGram`;
- `not_posDef_momentHankelMatrix_add_three_of_shiftInvariantGram`.

The support-invariance input is formalized in
`formal/GaloisForLFunctions/HTGeometry/CofiniteTailGramPolarization.lean`.

## Gates

- [x] exact Toeplitz--Hankel intersection theorem isolated
- [x] unconditional source-level formal proof
- [x] narrow build and axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] incorporate the bipolar carrier theorem into the operator-tail paper
- [ ] complete primary-literature audit
- [ ] formulate and attack the prime-tail/archimedean radial incidence open core
