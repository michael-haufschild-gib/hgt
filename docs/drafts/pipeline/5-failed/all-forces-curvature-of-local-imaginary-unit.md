# All forces are not the curvature of a local imaginary unit

- **ID:** `all-forces-curvature-of-local-imaginary-unit`
- **Stage:** 5-failed
- **Type:** UNIVERSAL PHYSICS CONJECTURE / COMPLEX-STRUCTURE UNIFICATION
- **Scientific status:** `[FALSIFIED AS LITERAL LAW] [POSITIVE SURVIVOR LEAN-FORMALIZED]`
- **Parent:** `../1-in-progress/dynamical-composition-universal-law.md`
- **Freeze date:** `2026-07-30`

## Frozen headline

> **Every force is curvature of nature's local imaginary unit.**

Expanded form:

> Ordered real event composition generates the local complex structure used by quantum
> amplitudes. Gauge symmetry is its stabilizer. Gravity is the source-changing curvature of
> comparing it across events. The three Standard Model forces and gravity are therefore the
> vertical and external curvatures of one event-generated imaginary unit.

This was frozen as a proof-independent jump after the exact source matrices

\[
J=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]

were found to generate

\[
\mathcal I=JS,\qquad \mathcal I^2=-I.
\]

## Priority collision

The broad mathematical components are occupied.

1. Moretti and Oppio derive a Poincaré-invariant complex structure, unique up to sign and
   commuting with the observable algebra, for irreducible relativistic quantum systems over real
   or quaternionic Hilbert spaces:
   [real case](https://arxiv.org/abs/1611.09029),
   [quaternionic case](https://arxiv.org/abs/1709.09246).
2. Hackl and Bianchi characterize pure bosonic and fermionic Gaussian states by compatible
   Kähler data \((G,\Omega,J)\), with \(J^2=-1\):
   [arXiv:2010.15518](https://arxiv.org/abs/2010.15518).
3. Krasnov proves that the Standard Model gauge group is the subgroup of
   \(\operatorname{Spin}(9)\) commuting with a distinguished complex structure on its spinor
   space:
   [arXiv:1912.11282](https://arxiv.org/abs/1912.11282).
4. Krasnov's pure-spinor characterization inside \(\operatorname{Spin}(10)\) uses two aligned
   commuting orthogonal complex structures whose product gives the \(6+4\) split:
   [arXiv:2209.05088](https://arxiv.org/abs/2209.05088).

Therefore none of these is available as this programme's discovery:

- complex structure from relativistic symmetry;
- quantum states encoded by Kähler complex structures;
- Standard Model symmetry as a complex-structure stabilizer; or
- a \(6+4\) product structure from two pure-spinor complex structures.

The source-generated ordered pair is a different upstream mechanism, but novelty of its input does
not rescue the literal force law.

## Exact killing mechanism

A complex structure does not determine a connection or its curvature.

On the trivial real rank-two bundle over \(\mathbb R^2\), fix

\[
\mathcal I=
\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]

For every \(\lambda\in\mathbb R\), define

\[
\nabla^\lambda=d+\lambda x\,dy\,\mathcal I.
\]

Because the connection form is a scalar multiple of \(\mathcal I\),

\[
\nabla^\lambda\mathcal I=0
\]

for every \(\lambda\). Yet its curvature is

\[
F_{\nabla^\lambda}
=\lambda\,dx\wedge dy\,\mathcal I.
\]

The same constant complex structure therefore admits zero curvature when \(\lambda=0\) and
arbitrarily scaled nonzero curvature when \(\lambda\ne0\). No local complex structure selects even
the electromagnetic field, its normalization, or its dynamics.

The gravitational claim fails more directly. Standard complex quantum fields and spinor bundles
use one globally fixed scalar \(i\) on both flat and curved spacetimes. Metric/spin connections are
complex linear, so they preserve that \(i\) while Riemann curvature can be zero or nonzero.
Curvature of spacetime is not failure to preserve the scalar imaginary unit.

Thus:

\[
\boxed{
\text{generated complex structure}
\not\Rightarrow
\text{connection, curvature, metric, or force dynamics}.
}
\]

The literal headline is false by underdetermination, independently of whether the source
generation mechanism is physical.

## Strongest positive survivor

The source matrices do prove an exact maximal finite statement:

1. \(J\) and \(S\) are involutions;
2. they anticommute;
3. their ordered product squares to \(-I\);
4. reversing their order reverses the generated complex structure;
5. the centralizer of \(\mathcal I=JS\) in \(M_2(K)\) is exactly
   \[
   \{aI+b\mathcal I:a,b\in K\};
   \]
6. over \(\mathbb R\), this centralizer is the ordinary complex scalar algebra; and
7. the same algebra is exactly the fixed algebra of the involutive automorphism that simultaneously
   reverses \(J\) and \(S\).

The paper and Lean proof are recorded in
[`source-ordered-pair-complex-structure.md`](../3-formalized/not_new_scientific_knowledge/source-ordered-pair-complex-structure.md).

The viable physical successor is narrower:

> **Ordered event composition may generate the local complex phase algebra. The complete boundary
> colligation—not the complex structure alone—must independently generate transport, curvature,
> spacetime, and forces.**

This keeps the generated-\(i\) clue inside compositional relativity without asking it to determine
data it mathematically cannot contain.

## New insight

Complex structure is kinematics of orientation preservation. Connection is law of comparison.
Curvature is obstruction accumulated by that law. Conflating the three recreates the exact
curvature-only completeness error already killed by the clock boundary-colligation theorem.

The universal object must therefore retain at least:

```text
generated local complex orientation
  + source-selected comparison/transport
  + boundary self-law
  + anchor/soldering to public causal directions.
```

No one component determines the others.

## Status

- literal universal force law: falsified;
- exact finite complex-structure survivor: paper-proved and Lean-formalized;
- source-derived restriction of amplitudes to the complex centralizer: open;
- source-derived connection, anchor, continuum dynamics, and force classification: open;
- Nature manuscript claim: prohibited.

## Log

- 2026-07-30 — frozen the headline after discovering the ordered source square root of \(-I\).
- 2026-07-30 — priority-audited against Moretti--Oppio, Hackl--Bianchi, and Krasnov.
- 2026-07-30 — falsified the literal law: one fixed complex structure admits arbitrary
  complex-linear connections and curvatures.
- 2026-07-30 — extracted and Lean-formalized the exact centralizer/complex-phase survivor.
- 2026-07-30 — strengthened the survivor in Lean: simultaneous source reversal is an involutive
  multiplicative parity whose fixed algebra is exactly the complex centralizer.
