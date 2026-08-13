# Hedenmalm theta anomaly: functional-equation pair polarization

- **Label:** `P-G125`
- **Route:** P
- **Parents:** `P-G123`, `P-G124`
- **Status:** theorem and reflection-average no-go proved in Lean

## Conjecture tested

Critical-line conjugation sends centered spectral coordinate `z` to `conj(z)`.  Test whether
P-G123 Ward realification is exactly the symmetric sector of this genuine functional-equation
pair, and whether Ward anomaly is its antisymmetric sector.

Writing `R(q)` for raw multiplicity numerator and `q#` for line conjugate, conjecture

```text
D(q#)=D(q),
P(q)=(R(q)+R(q#))/2,
K(q)=(R(q#)-R(q))/2,
K(q#)=-K(q).
```

For normalized connections, conjecture

```text
WardRealified(q)=(Connection(q)+Connection(q#))/2=Re(z).
```

## Scientific decision gate

- **Success:** identify exact source provenance of Ward anomaly as anti-invariant
  functional-equation sector.  Reflection pairing constructs realification but cannot force fixed
  points; antisymmetric-sector vanishing remains exact RH condition.
- **Failure:** Ward anomaly contains additional non-reflection source data; isolate it as new
  producer candidate.
- Formal target must prove completed multiplicity mass invariance, pair average/difference,
  anomaly oddness, normalized connection average, and exact pair-collapse criterion.

## Verification log

- 2026-08-13 — Corpus contains line-conjugate root-energy invariance and rank-two correction
  blindness, but no multiplicative-jet Ward pair average/difference theorem.  Conjecture opened.
- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmThetaAnomalyFunctionalEquationPairPolarization.lean`.
- 2026-08-13 — Exact module build passed: `[12947/12947]`.
- 2026-08-13 — `#print axioms` on completed mass invariance, Ward mass invariance, pair average,
  half-difference, anomaly oddness, connection average, pair-collapse line criterion, and global RH
  equivalence reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Result and no-go closure

Conjecture is true.  Completed first-divided Xi energy and Burnol frame energy are separately
line-conjugation invariant, hence so is genuine Ward mass.  Lean proves

```text
P(q)=(R(q)+R(q#))/2,
K(q)=(R(q#)-R(q))/2,
K(q#)=-K(q),
WardRealified(q)=(Connection(q)+Connection(q#))/2.
```

Thus P-G123 anomaly is not an ad hoc counterterm: it is exact anti-invariant functional-equation
sector.  Symmetric sector is exact realification.  Raw pair numerators agree iff anomaly vanishes,
iff copy lies on critical line; global pair collapse is equivalent to RH.

Functional-equation averaging is therefore retired as independent producer.  It canonically splits
each orbit into invariant and anti-invariant sectors but does not force anti-invariant sector zero.
Strongest survivor is precise source architecture: any successful passivity theorem must suppress
anti-invariant Ward sector before orbit averaging, not infer suppression from existence of pair.

## Integration audit

- 2026-08-13 — Wired into `GaloisForLFunctions.RHTower`; full umbrella build passed
  `[19833/19833]`.
