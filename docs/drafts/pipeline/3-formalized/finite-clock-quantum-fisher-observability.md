# Finite-clock quantum-Fisher observability

- **ID:** finite-clock-quantum-fisher-observability
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE / RHTOWER VALUE DISCHARGE
- **Source:** quantum-clock metrology, information leakage, and constrained observer algebras
- **Statement:** On a normalized state fixed by a finite periodic clock, the observable tangent erased by clock averaging is automatically projectively orthogonal to the state, so its pure-state quantum Fisher value is exactly four times the clock Kadison observability variance; for logarithmic Sonin scattering this is exactly the squared scattering--observable commutator.

## Goal

Connect the finite static clock-observability API to the existing projective quantum-Fisher API
without treating the clock operator as temporal evolution.  The useful gate is elimination of the
projective-overlap input: clock stationarity must force it to vanish.

## Gates

- [x] 0 → 1 in-progress: isolated the erased observable tangent and the QFI overlap term
- [x] 1 → 2 fully-proven: proved automatic orthogonality, QFI/Kadison equality, and the exact log-Sonin commutator specialization
- [x] 2 → 3 formalized: repaired the previously uncached QFI source module, built only the missing exact targets serially, checked every touched source directly, and passed the axiom audit
- [ ] 3 → 4 publication-ready: identify an Euler, resolvent, or seam observable whose scattering commutator has an independently controlled nonzero or coercive value

## Physics source

P. Faist, M. P. Woods, V. V. Albert, J. M. Renes, J. Eisert, and J. Preskill,
*Time-energy uncertainty relation for noisy quantum metrology*, PRX Quantum 4, 040336 (2023),
arXiv:2207.13707, proves that QFI about clock time lost through a noisy channel is balanced by QFI
about a complementary energy parameter gained by the environment and characterizes metrological
codes that preserve clock accuracy.

The Lean result is the static orthogonal-projection relation required by this corpus.  It does not
formalize the full channel theorem and is not claimed as new quantum-metrology science.

## Exact relation

Let `U` be an isometric finite-period clock, `P` its cyclic average, `psi` a normalized stationary
state, and `X` a self-adjoint observable.  Orthogonal projection gives

```text
<psi, (1-P) X psi> = 0.                                  (1)
```

Consequently the projective Gram numerator loses its overlap term:

```text
G(psi, (1-P)X psi) = ||(1-P)X psi||^2.                   (2)
```

The existing finite-clock conditional-variance theorem identifies the right side with the
stationary Kadison defect `V_U,X(psi)`.  Therefore

```text
QFI(psi; (1-P)X psi) = 4 V_U,X(psi).                     (3)
```

For the logarithmic Sonin scattering involution `S`, the existing physical commutator identity
then yields

```text
QFI(psi; (1-P_S)X psi) = ||[X,S] psi||^2.                (4)
```

Equation `(1)` is the premise discharge: no independent phase/gauge orthogonality assumption is
needed.  Equation `(4)` removes a separate conversion between metrological sensitivity, clock
variance, and the Sonin scattering commutator.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteClockQuantumFisher.lean` proves:

- `inner_finiteClockErasedTangent_eq_zero`;
- `finiteClock_observabilityVariance_eq_projectiveQuantumTangentEnergy`;
- `finiteClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance`.

`formal/GaloisForLFunctions/RHTower/SoninLogClockQuantumFisher.lean` proves:

- `soninLogClock_erasedPureStateQuantumFisherValue_eq_four_mul_observabilityVariance`;
- `soninLogClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq`.

`ProjectiveQuantumFisherValue.lean` was repaired at four previously latent source failures: a
commuted real product in a division inequality and three missing explicit scalar-field arguments.
This restores its cache and makes all downstream QFI consumers buildable from source.

## Corpus value

The general theorem applies to every finite periodic clock in `HTGeometry`, independently of zeta
or the Sonin model.  It makes “clock observability” a projective-information value rather than an
evolution law: a state may satisfy the static clock constraint while a chosen observable retains
nonzero QFI precisely through its erased observer-algebra component.

The log-Sonin theorem is an exact downstream consumer, not a renamed wrapper.  A later theorem may
now replace the pair of assumptions “the erased tangent is phase-orthogonal” and “its QFI equals
commutator energy” by physicality, normalization, and self-adjointness alone.  The remaining hard
analytic task is to control `||[X,S] psi||` for a source-bearing observable `X`.

## Status

[PROVED IN LEAN] Exact-target and direct-source checks pass for both new modules and for the
repaired QFI dependency.  The audited theorems use only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.  No numerical computation, full project build, or
concurrent Lean process was run.
