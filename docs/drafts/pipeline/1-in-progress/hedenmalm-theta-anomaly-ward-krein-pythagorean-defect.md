# Hedenmalm theta anomaly: Ward Krein/Pythagorean defect

- **Label:** `P-G124`
- **Route:** P
- **Parents:** `P-G120`, `P-G123`
- **Status:** theorem proved in Lean; positivity-upgrade producer remains open

## Conjecture tested

P-G120 gives opposite signed channels whose sum is zero.  P-G123 identifies their common magnitude
as Ward realification anomaly.  Test whether indefinite cancellation hides an exact positive
Pythagorean defect.

With `D>0`, `z=xiSpectralPoint(q)`, raw multiplicity numerator `R=-zD`, realified numerator
`P=-Re(z)D`, and anomaly `K=i Im(z)D`, conjecture

```text
normSq(R) = normSq(P) + normSq(K).
```

If theta and arithmetic Ward channels are `T` and `A`, conjecture

```text
T = Im(z)D,
A = -Im(z)D,
T+A=0,
T^2+A^2 = 2 normSq(K).
```

## Scientific decision gate

- **Success:** prove exact conversion from Krein-null conservation to positive Euclidean defect.
  Defect vanishes iff critical-line placement; strict off-line Ward cancellation is nonzero null
  current, not flat current.
- **Failure:** identify missing orthogonality and retain exact cross term as next source invariant.
- Formal target must prove channel identities, Pythagorean law, positive defect, per-copy line
  classifier, and global RH equivalence without assuming positivity upgrade.

## Verification log

- 2026-08-13 — Existing P-G49 Pythagorean budget checked; it concerns Julia/Gamma clock splitting,
  not multiplicative-jet Ward realification.  No corpus duplicate found.
- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmThetaAnomalyWardKreinPythagoreanDefect.lean`.
- 2026-08-13 — Exact module build passed: `[12946/12946]`.
- 2026-08-13 — `#print axioms` on channel, cancellation, Pythagorean, Euclidean defect, norm-loss,
  strict positivity, and global RH capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-13 — Full `GaloisForLFunctions.RHTower` umbrella build passed: `[19819/19819]`.

## Result

Conjecture is true.  Lean identifies theta and arithmetic channels as

```text
T= Im(z)D,
A=-Im(z)D,
```

so their signed sum vanishes.  It simultaneously proves

```text
normSq(raw) = normSq(realified) + normSq(anomaly),
T^2+A^2 = 2 normSq(anomaly),
normSq(raw)-normSq(realified) = normSq(anomaly) >= 0.
```

Thus Ward realification is an orthogonal norm contraction, and P-G120 conservation is a nonzero
Krein-null pair off line.  At every hypothetical right-half Xi copy Euclidean Ward defect is
strictly positive.  Defect zero on one copy is equivalent to critical-line placement; global zero
is equivalent to RH.

## Higher principle and next gate

Repeated Route P cancellations are shadows of isotropic vectors in an indefinite conservation
space.  Euclidean completion resolves isotropic current into a positive radial defect but does not
force it zero.  Missing theorem is now a source passivity or coisometry law making Ward
realification norm-preserving on completed source domain.  Specializing norm preservation only to
Xi copies is RH-equivalent and cannot be assumed.
