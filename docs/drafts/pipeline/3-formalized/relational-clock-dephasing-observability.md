# Relational-clock dephasing is static observable erasure

- **ID:** relational-clock-dephasing-observability
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE / RHTOWER HYPOTHESIS DISCHARGE
- **Scientific status:** `[BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Source:** relational quantum clocks, Lindblad double commutators, and constrained observer algebras
- **Statement:** For an involutive clock `U`, the double commutator `[U,[U,X]]` is exactly four times the observable component erased by the two-reading clock twirl.  Its kernel is the clock commutant using only `U²=1`.  On a normalized stationary state, hidden-clock QFI is one quarter of the squared double-commutator value.

## Goal

Test whether the double-commutator decoherence term arising from finite-resolution relational
clocks supplies a new dynamical mechanism or reduces to the static clock-observability structure
already present in `HTGeometry`.  Retain the relation only if it removes hypotheses or gives an
exact value conversion with a concrete `RHTower` consumer.

## Physics source

R. Gambini, R. A. Porto, and J. Pullin, *A relational solution to the problem of time in quantum
mechanics and quantum gravity induces a fundamental mechanism for quantum decoherence*, New J.
Phys. 6 (2004), arXiv:gr-qc/0402118, equations (40)--(42), derives a relational-clock master
equation whose dissipative term is `-sigma [H,[H,rho]]` and places it in Lindblad form.

The formal result below is the exact involutive-clock operator identity relevant to this corpus.
It does not formalize the paper's continuum approximation, cosmological estimate, or temporal
evolution, and it is not claimed as new physics.

## Exact relations

Let `U²=1` and let

```text
E_U(X) = (X + U X U)/2
```

be the two-reading observable conditional expectation.  Direct algebra gives

```text
[U,[U,X]] = 2(X-U X U) = 4(X-E_U(X)).                 (1)
```

Therefore

```text
[U,[U,X]] = 0  iff  E_U(X)=X  iff  U X = X U.         (2)
```

Only `U²=1` is used in `(1)` and `(2)`.  In particular the existing self-adjointness of `X` and
unitarity/isometry of `U` required by the Kadison-defect route are unnecessary for the fixed-point
and commutant criterion.

If `U psi = psi`, then

```text
[U,[U,X]] psi = 2 (XU-UX) psi.                         (3)
```

Combining `(3)` with the formalized finite-clock QFI identity gives

```text
QFI(psi; hidden clock tangent)
  = ||(XU-UX) psi||²
  = (1/4) ||[U,[U,X]] psi||².                          (4)
```

Equation `(4)` identifies the apparent relational-clock decoherence value with the observability
structure of the clock, rather than with an independently supplied temporal flow.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteInvolutiveClockDephasing.lean` proves:

- `finiteInvolutiveClockDoubleCommutator_eq_four_smul_disturbance`;
- `finiteInvolutiveClockDoubleCommutator_apply_of_fixed`;
- `sub_finiteInvolutiveObservableTwirl_eq_zero_iff_commutes`;
- `finiteInvolutiveClockDoubleCommutator_eq_zero_iff_commutes`.

`formal/GaloisForLFunctions/HTGeometry/FiniteClockObservableFixedPoint.lean` extends the
fixed-point discharge from involutions to every nonempty finite-period clock:

- `finiteCyclicObservableTwirl_eq_self_iff_commutes`;
- `sub_finiteCyclicObservableTwirl_eq_zero_iff_commutes`.

`formal/GaloisForLFunctions/HTGeometry/FiniteInvolutiveClockQuantumFisherDephasing.lean` proves:

- `finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq`;
- `finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_quarter_doubleCommutatorNormSq`.

`formal/GaloisForLFunctions/RHTower/SoninLogClockDephasing.lean` specializes `(1)` and `(2)` to
logarithmic Fourier scattering and proves a twirl-fixed criterion with no self-adjointness premise.
`formal/GaloisForLFunctions/RHTower/SoninLogClockQuantumFisher.lean` applies `(4)` to normalized
physical Sonin states.

## Corpus value

The general theorem applies to every involutive observer clock in `HTGeometry`; it is not tied to
zeta or to the Sonin model.  It supplies an operator rewrite for any later double-commutator or
dephasing hypothesis and gives a premise-free fixed-point detector for arbitrary continuous
linear observables.  Its fixed-point component has also been promoted to arbitrary nonempty
finite-period clocks, so every cyclic observer twirl now exposes its exact commutant without
self-adjointness, positivity, or isometry assumptions.

The `RHTower` specialization directly strengthens the existing logarithmic-scattering corpus:
`soninLogFourierObservableTwirl X = X` is now equivalent to commutation for arbitrary `X`, whereas
the older Kadison-defect zero theorem required `X` to be self-adjoint.  The Sonin QFI theorem now
also accepts the double-scattering-commutator value without a separate conversion hypothesis.

The time-band/holographic observer-algebra audit produced no additional theorem: the live Sonin
time-band corpus already discharges exterior strictness and has exact correction and residual
energies.  No duplicate time-band wrapper was added.

## Gates

- [x] relational-clock source contains an explicit double-commutator dissipator
- [x] exact static observer-algebra identity isolated
- [x] general `HTGeometry` theorem removes existing hypotheses
- [x] direct `RHTower` fixed-point and QFI consumers formalized
- [x] missing exact targets built serially and every touched source checked directly
- [x] axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] identify a source-bearing observable whose nonzero double-commutator value has an independent analytic lower bound

## Status

[PROVED IN LEAN] No numerical computation, full project build, or concurrent Lean process was
run.  The result is a corpus-strengthening bridge, not a novelty claim or an RH proof.
