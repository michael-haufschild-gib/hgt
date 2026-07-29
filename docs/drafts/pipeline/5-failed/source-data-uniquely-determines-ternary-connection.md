# Source data does not uniquely determine a ternary connection

- **ID:** `source-data-uniquely-determines-ternary-connection`
- **Stage:** 5-failed
- **Type:** connection-reconstruction no-go
- **Scientific status:** `[FALSIFIED] [PAPER-PROVED] [POSITIVE SURVIVOR]`
- **Parent:** `../1-in-progress/reality-obstruction-fixed-point-law.md`

## Failed statement

> Dagger ternary locality plus reciprocal positive observations uniquely determines the
> source-compatible connection.

This is false even in complex dimension one.

## Exact counterexample

Give \(X=\mathbb C\) the ternary product

\[
[x,y,z]=x\overline y z.
\]

For each \(\lambda\in\mathbb R\), define the complex-linear map

\[
\delta_\lambda(z)=i\lambda z.
\]

Then

\[
\begin{aligned}
&\delta_\lambda(x)\overline y z
+x\overline{\delta_\lambda(y)}z
+x\overline y\delta_\lambda(z)\\
&=(i\lambda-i\lambda+i\lambda)x\overline y z\\
&=i\lambda x\overline y z
=\delta_\lambda([x,y,z]).
\end{aligned}
\]

Hence every \(\delta_\lambda\) is a ternary derivation.  They are distinct because
\(\delta_\lambda(1)=i\lambda\).

The reciprocal positive observable is \(\overline z z\).  Its infinitesimal derivative is

\[
\overline{\delta_\lambda(z)}z+\overline z\,\delta_\lambda(z)
=-i\lambda\overline z z+i\lambda\overline z z
=0.
\]

All phase derivations are therefore invisible to reciprocal-square observation.

## Verdict

`FALSE`.

No theorem may claim reconstruction of one literal connection from reciprocal positive data
without phase calibration or equivalent extra source structure.

## Strongest positive survivor

Connection nonuniqueness is structured:

```text
compatible connection reconstructions
  = affine family;

differences invisible to reciprocal observables
  = vertical stabilizer derivations.
```

The one-dimensional kernel is the Lie algebra \(\mathfrak u(1)\).  This suggests the corrected
physical target:

> gauge symmetry is the stabilizer ambiguity left by source reconstruction, and gauge force is
> curvature of that reconstruction torsor.

Affine connection spaces and gauge stabilizers are standard parents.  Candidate novelty would be a
source theorem deriving the torsor and classifying its minimal stabilizer as the Standard Model
gauge group.

## Lean target

Create a small unconditional module proving:

1. `phaseTernaryDerivation λ` satisfies the ternary Leibniz identity;
2. its infinitesimal reciprocal-square derivative is zero;
3. evaluation at \(1\) distinguishes unequal real parameters.

## Status

- counterexample: dependency-closed paper proof;
- positive survivor: exact in dimension one;
- Lean formalization: pending;
- higher-dimensional spatial-stabilizer classification: open.
