# Differential-clock reference-frame covariance

- **ID:** differential-clock-reference-frame-covariance
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE
- **Source:** relational reference-frame covariance transferred to differential fields
- **Statement:** A derivation-preserving algebra equivalence transports every finite jet, finite jet-observable field, finite clock test, hypertranscendence, and the exact finite-resolution clock-erosion law.

## Goal

Make the general hypertranscendental clock geometry independent of the differential-field
coordinates used to present it.  This is the differential-algebraic analogue of quantum
reference-frame covariance and applies to every hypertranscendental element, not only zeta or an
`RHTower` specialization.

## Gates

- [x] 0 → 1 in-progress: frame-covariance interface identified in the existing HT clock API
- [x] 1 → 2 fully-proven: jets, observable fields, tests, HT, and erosion transported exactly
- [x] 2 → 3 formalized: exact-module build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: combine with an intrinsic formulation of the HT clock boundary

## Physics source

- P. A. Höhn and A. Vanrietvelde, *How to switch between relational quantum clocks*, arXiv:1810.04153, derives clock changes through a clock-neutral constrained theory.
- A. Vanrietvelde, P. A. Höhn, F. Giacomini, and E. Castro-Ruiz, *A change of perspective: switching quantum reference frames via a perspective-neutral framework*, arXiv:1809.00556, describes reference-frame descriptions as gauge choices on a common constraint surface.
- T. Thiemann, *(Quantum) reference frames, relational observables, gauge reduction and physical interpretation*, arXiv:2603.04072, separates covariance of relational observables from any assertion that different clocks generate the same Hamiltonian evolution.

The transfer made here is algebraic: a map is admitted as a frame change only when it is an algebra
equivalence and intertwines the derivations.  Under exactly that hypothesis, the HT clock data are
invariant.

## Exact relation

Let `e : L ≃ₐ[F] L'` satisfy

```text
e(delta x) = delta' (e x).
```

Then for every `n` and `N`,

```text
e(delta^n x) = delta'^n(e x),
e(P_N(x)) = P_N(e x),
ClockTest(delta,x,N,a) iff ClockTest(delta',e x,N,e a).
```

The same equivalence transports all finite clock-test families and gives

```text
HypertranscendentalOver(F,x) iff HypertranscendentalOver(F,e x).
```

Most importantly, the complete clock-erosion statement is invariant:

```text
a belongs to the r-test core of P_N(x)
iff
e a belongs to the r-test core of P_N(e x).
```

No time parameter or state propagation is introduced.  The invariant is the finite observability
structure of the derivation clock.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/DifferentialClockReferenceFrameCovariance.lean` proves:

- `differentialJet_algEquiv`;
- `jetObservableField_map_algEquiv`;
- `differentialClockTest_algEquiv_iff` and the finite-family form;
- `jetObservable_clockTests_algEquiv_iff`;
- `hypertranscendentalOver_algEquiv_iff`;
- `hypertranscendental_clock_erosion_algEquiv_iff`.

## Corpus value

Every later theorem stated solely through the jet-observable fields and clock tests can now be
transported across a differential-algebraic change of reference frame.  In particular, the core
general-HT erosion theorem no longer needs to be reproved for equivalent presentations of the
ambient differential field.

## Status

[PROVED IN LEAN] The exact-module build refreshed only the stale direct dependency and this new
module; the subsequent touched-file check passes.  The audited exports depend only on Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No full project build, numerical
experiment, or concurrent Lean process was run.
