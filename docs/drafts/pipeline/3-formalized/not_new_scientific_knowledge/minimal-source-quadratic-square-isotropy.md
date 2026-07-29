# The minimal source-selected quadratic square is isotropic

- **ID:** minimal-source-quadratic-square-isotropy
- **Stage:** 3-formalized
- **Type:** THEOREM + NO-GO (paper + Lean)
- **Parent:** `source-colligation-quadratic-transfer-selector.md`
- **Statement:** Every symmetric quadratic transfer selected by the minimal retained/created
  source polarity has reciprocal square equal to one nonnegative scalar times identity.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/MinimalSourceQuadraticSquareIsotropy.lean`

## Goal

Determine what positive law is produced when the unique minimal paired amplitude is reciprocally
squared. Test whether the quadratic selector can already distinguish gravitational, gauge, or
matter response.

## Gates

- [x] complete paper proof `[PROVED HERE]`
- [x] unconditional Lean theorem
  `minimalSourceQuadratic_reciprocalSquare_isotropic`
- [x] final target build and axiom audit
- [ ] generated index and project-wide lint
- [ ] higher-rank source singular-spectrum selector

## Theorem

`[PROVED HERE]`

Let

\[
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]

and let \(Q_J(T)\) be the source-derived symmetric quadratic transfer for
\(J=\operatorname{diag}(1,-1)\). Then

\[
Q_J(T)=bX
\]

for \(b=Q_J(T)_{01}\), and

\[
\boxed{
Q_J(T)^\dagger Q_J(T)=|b|^2 I_2.
}                                                             \tag{MSI1}
\]

### Proof

The source quadratic transfer is symmetric and \(J\)-odd. The earlier polarity theorem therefore
gives \(Q_J(T)=bX\). Since \(X^\dagger=X\) and \(X^2=I_2\),

\[
Q_J(T)^\dagger Q_J(T)
=(\overline bX)(bX)
=|b|^2I_2.
\]

## Exact killing mechanism

The minimal quadratic successor can select only:

1. one paired amplitude direction \(X\); and
2. one overall weight \(|b|^2\).

Its positive square is isotropic. It cannot distinguish:

- external from internal response;
- gravitational from gauge coupling;
- Lorentzian directions;
- chirality or generations;
- multiple force scales; or
- any nontrivial curvature.

Therefore minimal \(q_2\) is a seed, not a theory of everything.

## Projective-scale obstruction

The preceding projective-congruence theorem intentionally quotients by nonzero rescaling
\(b\mapsto\lambda b\). But `(MSI1)` depends on \(|b|^2\). The equivalence relation that makes the
quadratic orbit unique removes precisely the datum needed for a physical coupling scale.

This yields a strict separation:

```text
projective orbit  -> interaction type;
singular weight   -> physical scale.
```

Orbit selection cannot derive constants of nature.

## Strongest positive survivor

The positive square canonically converts the remaining amplitude coefficient into a common
source scale. The first genuinely physical finite invariant after projective selection is the
**calibrated singular weight**

\[
\omega_2(e)=|Q_J(T)_{01}|^2.
\]

The unresolved source problem is no longer “which minimal tensor?” but:

> What source law fixes its normalization, and what higher structure splits the common scalar
> into the observed gravity, gauge, Higgs, and matter spectra without independent tuning?

## Lean certificate

`[LEAN-PROVED]`

Declarations:

- `pairRecordMatrix_conjTranspose_complex`
- `pairRecordMatrix_mul_self_complex`
- `smul_pairRecord_reciprocalSquare_isotropic`
- `minimalSourceQuadratic_reciprocalSquare_isotropic`

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or
computation-based proof appears in the module.
Final audit:

```text
lake build GaloisForLFunctions.HTGeometry.MinimalSourceQuadraticSquareIsotropy
✔ Built GaloisForLFunctions.HTGeometry.MinimalSourceQuadraticSquareIsotropy
Build completed successfully (2952 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile novelty audit

The matrix identity is elementary and the singular-value interpretation is standard. Door grade:
`[BRIDGE]`.

It does not derive a physical normalization, force coupling, spacetime metric, or prediction.

## New insight for the universal target

The missing higher incompatibility law must do two distinct jobs:

1. select the graded composition orbit; and
2. calibrate its singular spectrum.

Bar--cobar equivalence up to algebraic isomorphism normally forgets metric normalization. A
physical positive transcategorical duality must retain a source-calibrated dagger/weight structure
strong enough to make coupling scales invariant and recoverable.

## Log

- 2026-07-29 — squared the unique minimal paired transfer.
- 2026-07-29 — proved exact scalar isotropy and exposed loss of physical scale under projective
  equivalence.
- 2026-07-29 — isolated source-calibrated singular spectrum as next finite target.
- 2026-07-29 — final target build and axiom audit passed.
