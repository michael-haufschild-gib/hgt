# Quantum-Fisher clock reparameterization and invariant observability length

- **ID:** `quantum-fisher-clock-reparametrization`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, clock-observability value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.QuantumFisherClockReparametrization`

## General value law

For vacuum mass `m`, tangent overlap `a`, tangent speed `v`, and a local clock-rate change `r`,
the projective tangent value and pure-state quantum Fisher information satisfy

```text
P(m, r a, r^2 v) = r^2 P(m,a,v),
QFI(m, r a, r^2 v) = r^2 QFI(m,a,v).                    (1)
```

Thus QFI is a quadratic density in the chosen clock coordinate.  It is not itself an invariant
clock length.

Define the local Fisher line value by

```text
L(m,a,v; dtheta) = QFI(m,a,v) (dtheta)^2.
```

Then

```text
L(m, r a, r^2 v; dphi) = L(m,a,v; r dphi).              (2)
```

Whenever the coordinate increments obey the reciprocal clock-change law
`r dphi = dtheta`, equation `(2)` gives exact invariance of Fisher length.  If `r != 0`, equation
`(1)` also proves that QFI is zero, respectively strictly positive, before the change exactly when
it is zero, respectively strictly positive, afterwards.

## Finite observer-algebra application

The existing finite-clock theorem identifies the pure-state QFI of the tangent erased by cyclic
clock averaging with four times the static Kadison observability variance.  The new module lifts
that identity to the coordinate-free line law

```text
erased-tangent Fisher line = 4 * observability variance * (dtheta)^2.   (3)
```

This directly separates the observer algebra from its arbitrary clock calibration.  The cyclic
average decides which tangent is visible; a reparameterization changes only the density used to
describe the same Fisher length.  No Hamiltonian trajectory or temporal-evolution premise is
needed.

Every existing moment-state QFI identity in `HTGeometry`, including the Feshbach and normalized
moment-variance bridges, supplies a scalar triple `(m,a,v)` to equations `(1)` and `(2)`.  Hence the
same clock-coordinate law applies to general moment sources, not only to zeta or to a particular
finite quantum model.

## Physics provenance

- S. L. Braunstein and C. M. Caves, *Statistical distance and the geometry of quantum states*,
  Phys. Rev. Lett. 72 (1994), 3439--3443, DOI 10.1103/PhysRevLett.72.3439.
- D. Cafasso, N. Pranzini, J. Y. Malo, V. Giovannetti, and M. Chiofalo, *Quantum Time and the
  Time-Dilation induced Interaction Transfer mechanism*, Phys. Rev. D 110 (2024), 106014,
  DOI 10.1103/PhysRevD.110.106014.
- S. S. Wani, J. Q. Quach, and M. Faizal, *Time Fisher Information associated with Fluctuations
  in Quantum Geometry*, EPL 139 (2022), 62002, arXiv:2106.07121.

The recent preprint J. Sumaya-Martinez, *Fisher-Informational Time*, arXiv:2605.03958, proposes
accumulated Fisher distance as operational clock time.  That interpretation is not assumed by the
formal theorem; only its coordinate-change value law is retained.

## Lean surface

- `quantumFisherClockLineValue`
- `projectiveQuantumTangentValue_clockRateScale`
- `pureStateQuantumFisherValue_clockRateScale`
- `quantumFisherClockLineValue_reparameterize`
- `quantumFisherClockLineValue_invariant_of_reciprocalClockChange`
- `pureStateQuantumFisherValue_clockRateScale_eq_zero_iff`
- `pureStateQuantumFisherValue_clockRateScale_pos_iff`
- `finiteClockObservabilityLineValue`
- `finiteClockObservabilityLineValue_reparameterize`
- `finiteClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue`

## RH impact and boundary

This discharges clock-coordinate dependence for every RH route phrased through the existing
projective-QFI, finite-clock-variance, or moment-QFI values.  A redshift, dilation, or change of
relational clock cannot create or erase strict Fisher observability; only a degenerate clock map
can do so.  Fisher-based RH gates should therefore be stated using the invariant line value or
the coordinate-free zero/positive predicate, not a raw numerical QFI threshold.

The same result is also a no-go: changing clocks cannot turn a Fisher-blind source into a visible
one.  Its significant positive replacement is equation `(3)`, which provides a calibration-free
observable value that can be transported across finite clocks, moment states, redshifted clocks,
and relational-time models.

It does not supply the missing prime--archimedean source positivity or identify a positive
spectral measure, so it does not prove RH.

## Verification

- [x] exact module target built and cached
- [x] touched Lean file checks directly
- [x] no full or concurrent build used
- [x] no numerical computation used
