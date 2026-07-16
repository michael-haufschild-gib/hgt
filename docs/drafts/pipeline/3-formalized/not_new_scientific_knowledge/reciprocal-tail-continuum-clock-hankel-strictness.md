# Reciprocal-tail continuum clock and strict all-order Hankel geometry

- **ID:** `reciprocal-tail-continuum-clock-hankel-strictness`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, constructive infinite-memory observation law
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ReciprocalTailHankelStrict`

## Statement

Define the canonical algebraic observation tail

```text
r_n = 1/(n+1).
```

It has the exact continuum moment representation

```text
r_n = integral_[0,1] x^n dx.                              (1)
```

Lebesgue measure on `[0,1]` retains positive mass after deletion of every finite set.  Therefore
every finite moment Hankel block of `r` is positive definite and

```text
det H_N(r) > 0                                             (2)
```

for every `N`.

Consequences formalized for every prescribed finite bound `d`:

- `r` has no modal presentation of width at most `d`;
- `r` is not in the local finite-window closure of spectral models with fixed width `d`;
- `r` is not in the local finite-window closure of linear hidden-state models with fixed dimension
  `d`, even if the model may change with the observation window.

## Positive statement after the finite-model no-go

The essential theorem is not merely that a reciprocal tail defeats finite modal or state-space
models.  Equation `(1)` constructs its hidden observation palette: a continuum of nodes on
`[0,1]`.  Equation `(2)` says every finite polynomial reporter sees a strictly positive Gram
energy.  Infinite memory is thus certified positively by continuum observability rather than by an
appeal to temporal evolution.

## Black-hole, spacetime, and gravitational-wave connection

Black-hole perturbations are modal during the intermediate ringdown regime but commonly exhibit
power-law tails in other regimes.  The reciprocal tail is the simplest rigorously formalized
algebraic-tail prototype.  It separates two observation structures:

```text
finite QNM packet       -> some oversized Hankel determinant is zero;
continuum algebraic tail -> every finite Hankel determinant is positive.
```

This is relevant to event-horizon and spacetime response because late-time tails encode scattering
and hereditary propagation that cannot be reduced to a uniformly bounded packet of damped modes.
It also supplies a clean formal prototype for gravitational-wave memory kernels and compact-object
responses with a continuum relaxation spectrum.

Primary sources motivating the tail interface:

- H. Yang et al., *Quasinormal modes of nearly extremal Kerr spacetimes: spectrum bifurcation and
  power-law ringdown*, arXiv:1307.8086.
- S. Okuzumi, K. Ioka, and M. Sakagami, *Possible discovery of a nonlinear tail and second-order
  quasinormal modes in black hole ringdown*, arXiv:0803.0501.
- S. R. Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  arXiv:2210.15935, which explicitly separates the intermediate QNM regime from late-time
  power-law behavior.

## Lean surface

- `reciprocalTailClock`
- `reciprocalTailMeasure`
- `reciprocalTailClock_eq_moment`
- `reciprocalTailMeasure_integrable_moments`
- `reciprocalTailMeasure_infiniteSupport`
- `det_momentHankelMatrix_reciprocalTailClock_pos`
- `reciprocalTailClock_not_finiteModalWidthAtMost`
- `reciprocalTailClock_not_fixedSpectralWidthLocalClosure`
- `reciprocalTailClock_not_fixedStateSpaceDimensionLocalClosure`

## General HTGeometry significance

The module gives a concrete, unconditional witness for the slogan that hypertranscendental
complexity concerns the observability structure of a clock.  The label `n` does not need to be a
physical time.  Strictness comes from the continuum of reportable nodes and survives every finite
observation depth.

It also connects three previously separate interfaces in the corpus: infinite-support moments,
finite modal Hankel rank, and finite state-space local closure.

## RH impact and boundary

The result clarifies the useful target shape for the completed prime--Gamma source.  A finite-mode
or fixed-state source would force an oversized determinant to vanish; an infinite-support positive
moment representation would make all determinants positive and would feed existing RH-equivalent
Hankel criteria.  The reciprocal tail proves that this mechanism is mathematically coherent and
already supported by the general HTGeometry corpus.

It does not identify the completed prime--Gamma moments with the reciprocal tail or construct their
required positive representing measure.  That source-identification problem remains the RH-bearing
step.

## Verification

- [x] exact module target builds and is cached
- [x] touched file checks directly
- [x] no numerical computation used
