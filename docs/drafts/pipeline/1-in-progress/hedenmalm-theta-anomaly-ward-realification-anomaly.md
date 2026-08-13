# Hedenmalm theta anomaly: Ward realification anomaly

- **Label:** `P-G123`
- **Route:** P
- **Parents:** `P-G120`, `P-G122`
- **Status:** theorem proved in Lean; anomaly-free boundary remains open

## Conjecture tested

P-G122 proves any genuine selector must be a noncovariant counterterm anomaly.  P-G120's
same-fibre theta current is the first source-derived candidate.  Let

```text
E = burnolTwoPrimeFrameEnergy(z),
N = ||completedXiFirstDividedL2||^2,
T = pi*M*thetaBoundaryFlux,
J = -zE.
```

Same-fibre law gives `T=Im(z)N`.  Test the division-free Ward anomaly

```text
K = i E T = i Im(z) E N.
```

For multiplicity-scaled raw mass `D=EN` and numerator `JN`, conjecture

```text
JN + K = -Re(z) D,
-(JN+K)/D = Re(z).
```

## Scientific decision gate

- **Success:** construct exact source-derived P-G122 anomaly and prove it realifies spectral
  connection.  Prove anomaly vanishes iff critical-line placement.  This is not RH: Ward channel
  absorbs radial charge rather than proving its absence.
- **Failure:** source current is not compatible with multiplicative-jet mass; pivot to a different
  signed source channel.
- Formal target must be division-free, retain actual Xi multiplicity energy, prove strict mass
  positivity, identify exact P-G122 anomaly quotient, and state per-copy/global RH equivalences
  without claiming them unconditionally.

## Verification log

- 2026-08-13 — Corpus search found no prior realified multiplicative-jet connection or exact
  P-G122 anomaly quotient; existing modules contain its two separate channel identities only.
- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmThetaAnomalyWardRealification.lean`.
- 2026-08-13 — Exact module build passed: `[12945/12945]`.
- 2026-08-13 — `#print axioms` on aggregate landing, positive mass, anomaly, division-free
  numerator, normalized realification, zero classifier, line criterion, and global RH equivalence
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-13 — Full `GaloisForLFunctions.RHTower` umbrella build passed: `[19804/19804]`.

## Result

Conjecture is true.  On every actual Xi multiplicity copy, genuine mass `D=EN` is strictly
positive and theta boundary flux gives exact P-G122 anomaly

```text
K = i Im(z) D.
```

Lean proves division-free and normalized laws

```text
JN + K = -Re(z)D,
-(JN+K)/D = Re(z).
```

The singleton `2*3` P-G122 aggregate with genuine completed-Xi multiplicity weight is definitionally
identified with this mass and numerator.  Thus natural source Ward current does provide required
noncovariant anomaly, but it is a realification projector: it removes radial charge from reported
connection without proving charge zero.  Anomaly vanishes, and raw and realified connections agree,
iff that Xi copy lies on critical line.  Their global equality is equivalent to RH.  No unconditional
RH claim is made.

## Higher principle and next gate

Route P obstruction is now sharpened from “find anomaly” to “prove anomaly-free compatibility.”
Hermitian Ward completion canonically maps complex connection to fixed real locus.  RH requires
source domain to make this projection faithful—raw and projected connections must coincide—not
merely to define projection.  Next conjecture must derive or refute such faithfulness from a
pre-specialization source law; imposing it on Xi copies restates RH.
