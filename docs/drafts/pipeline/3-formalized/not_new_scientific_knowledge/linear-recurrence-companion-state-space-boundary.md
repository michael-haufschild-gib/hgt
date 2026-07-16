# Linear recurrence companion realization and continuum-clock boundary

- **ID:** `linear-recurrence-companion-state-space-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, explicit finite-memory realization and exclusion
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.LinearRecurrenceStateSpace`
  - `GaloisForLFunctions.HTGeometry.ReciprocalTailHankelStrict`
  - `GaloisForLFunctions.HTGeometry.EuclideanSpectralHankelStrict`
  - `GaloisForLFunctions.RHTower.CompletedPrimeGammaComplexStateSpaceBoundary`

## Constructive realization theorem

Let `u` solve a positive order-`d` linear recurrence

```text
u_(n+d) = sum_(i<d) a_i u_(n+i).                           (1)
```

Its canonical hidden state is the observation window

```text
x_n = (u_n, u_(n+1), ..., u_(n+d-1)).                     (2)
```

Mathlib's `LinearRecurrence.tupleSucc` advances `(2)` by one label.  The new module takes the
matrix of that linear map, uses the initial window as input state, and reports the first coordinate.
It proves the exact value identity

```text
u_n = output dot A^n input                                (3)
```

for every `n`.  Thus every positive order-`d` recurrence solution has a `d`-state realization and

```text
det H_(d+1)(u) = 0.                                       (4)
```

The proof is field-generic.

## Positive statement

This is not only a finite-memory no-go.  Equations `(2)`--`(3)` construct the exact hidden state,
transition matrix, input, and reporter from the recurrence itself.  They turn the corpus's
state-space boundary into a reusable classification tool for every recurrence already expressed
through mathlib's `LinearRecurrence` API.

## Cross-domain value

The same companion realization is the common finite-memory skeleton of:

- scalar outputs of linear recurrent neural networks;
- unary weighted finite automata and spectral-learning models;
- finite-order system-identification models;
- finite-state linear observation models used as approximations to genomic and genetic sequence
  processes;
- finite-memory response kernels and finite-mode physical clocks.

Literature motivating these interfaces:

- G. Rabusseau, T. Li, and D. Precup, *Connecting Weighted Automata and Recurrent Neural Networks
  through Spectral Learning*, arXiv:1807.01406.
- T. Li, D. Precup, and G. Rabusseau, *Connecting Weighted Automata, Tensor Networks and Recurrent
  Neural Networks through Spectral Learning*, arXiv:2010.10029.
- U. K. R. Tadipatri et al., *Nonconvex Linear System Identification with Minimal State
  Representation*, arXiv:2504.18791.

## Continuum applications

The strict-Hankel continuum results now directly exclude recurrences:

```text
reciprocalTailClock_not_linearRecurrence
euclideanSpectralMoments_not_linearRecurrence
```

The reciprocal continuum clock and every integrable infinite-support Euclidean spectral sequence
satisfy no positive finite-order real linear recurrence.  Their positive continuum moment
representations explain why: every finite Hankel determinant is positive, contradicting `(4)`.

## RHTower application

For the completed moving complex prime--Gamma moments,

```text
finite recurrence
  -> companion state-space realization of the same order
  -> fixed-dimensional local state-space closure.          (5)
```

Under RH, the completed source at `sigma=1/2` has a nonzero determinant in every size, so `(5)` is
impossible.  The formal corollary is

```text
not_completedMovingComplexLinearRecurrence_one_half_of_riemannHypothesis.
```

This closes the finite-recurrence escape route beyond diagonal QNM packets and arbitrary finite
nonnormal/Jordan realizations.

## Lean surface

- `linearRecurrenceWindow`
- `linearRecurrence_tupleSucc_window`
- `linearRecurrence_tupleSucc_pow_initial`
- `linearRecurrenceCompanionMatrix`
- `linearRecurrenceCompanionMatrix_pow_mulVec`
- `linearRecurrenceOutput`
- `algebraicStateSpaceResponse_linearRecurrence`
- `algebraicStateSpaceDimensionAtMost_of_linearRecurrence`
- `det_algebraicHankelMatrix_succ_eq_zero_of_linearRecurrence`
- `completedMovingComplexStateSpaceDimensionAtMost_of_linearRecurrence`
- `not_completedMovingComplexLinearRecurrence_one_half_of_riemannHypothesis`

## RH impact and boundary

The theorem expands the model classes excluded by any nonzero completed-source Hankel determinant:
finite linear recurrences, linear RNNs, unary weighted automata, and companion systems are now
formally subsumed by the existing state-space boundary.

It remains a consumer theorem.  It does not produce the required completed-source determinant or
positive spectral measure, so it does not prove RH.  Its value is exact reconstruction on the
finite side and exact exclusion once a source determinant is available.

## Verification

- [x] general recurrence module checks directly
- [x] exact recurrence target builds and is cached
- [x] reciprocal and Euclidean consumer files check directly and are cached
- [x] completed-source RHT consumer checks directly and is cached
- [x] no numerical computation used
