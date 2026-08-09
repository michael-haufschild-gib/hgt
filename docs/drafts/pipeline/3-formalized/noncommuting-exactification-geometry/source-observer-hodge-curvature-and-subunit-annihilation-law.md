# Source--observer Hodge curvature and subunit annihilation

- **ID:** `source-observer-hodge-curvature-subunit-annihilation`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/noncommuting-exactification-geometry/noncommuting-exactification-geometry-program.md`
- **Statement:** The energy of a source-exact physical co-closed field is exactly supported by
  source--observer comparison curvature; exact comparison, subunit curvature gain, or a strict
  upper bound on signed curvature work forces the field to vanish.

## Goal

Give arithmetic exactness, Fourier/Cartier comparison, and geometric Hodge positivity one common
equation.  The theorem must do more than rename the missing RH assertion.  Its positive leverage is
that it replaces an exact comparison requirement by two strictly weaker quantitative targets: a
source-first comparison-curvature gain smaller than one, or a source energy condition controlling
only the signed work of curvature on the actual physical field.

No zeta zero, RH hypothesis, or positivity conjecture occurs in the proof.

## Gates

- [x] 0 -> 1 in-progress: typed Hilbert-complex statement and non-circularity gate fixed
- [x] 1 -> 2 fully-proven: complete paper proof below, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: no Lean authorized in this research turn
- [ ] 3 -> 4 publication-ready: external collision audit and source-native application required

## 1. Setup

Work over `R` or `C`.  In the complex case the inner product is linear in its first variable.
Let

\[
 S^{-1}\mathrel{\mathop{\longrightarrow}^{d_S}}S^0,
 \qquad
 H^{-1}\mathrel{\mathop{\longrightarrow}^{d_H}}H^0                 \tag{1}
\]

be two densely defined Hilbert-complex arrows.  Only `d_H` needs an adjoint.  Let

\[
 A_{-1}:S^{-1}\longrightarrow H^{-1},
 \qquad
 A_0:S^0\longrightarrow H^0                                      \tag{2}
\]

be linear comparison maps on the vectors under discussion.  Assume

\[
 a\in\operatorname{Dom}d_S,
 \qquad
 A_{-1}a\in\operatorname{Dom}d_H.                                \tag{3}
\]

Define comparison curvature on `a` by

\[
 \Omega_Aa=A_0d_Sa-d_HA_{-1}a.                                   \tag{4}
\]

This is the chain-level Beck--Chevalley defect.  It is zero exactly when the comparison commutes
with the two displayed differentials on `a`.

Allow also a source residual `r in S^0`.  Put

\[
 b=d_Sa+r,
 \qquad
 y=A_0b,                                                          \tag{5}
\]

and assume `y in Dom(d_H^*)`.

## 2. Source--observer Gauss--Hodge identity

### Theorem 2.1 `[PROVED HERE]`

Under `(1)`--`(5)`,

\[
 \boxed{
 \|y\|^2
 =\langle A_{-1}a,d_H^*y\rangle
  +\langle \Omega_Aa+A_0r,y\rangle .}
                                                                        \tag{6}
\]

In particular,

\[
 \|y\|^2
 \leq
 \|A_{-1}a\|\,\|d_H^*y\|
 +\|\Omega_Aa+A_0r\|\,\|y\|.                                  \tag{7}
\]

### Proof

Equations `(4)` and `(5)` give

\[
 y=d_HA_{-1}a+\Omega_Aa+A_0r.                                  \tag{8}
\]

Take the inner product of `(8)` with `y`.  The domain assumptions and definition of the adjoint
give

\[
 \langle d_HA_{-1}a,y\rangle
 =\langle A_{-1}a,d_H^*y\rangle.
\]

Substitution proves `(6)`.  Cauchy--Schwarz proves `(7)`.  `QED`

Equation `(6)` is the exact three-face merger:

```text
arithmetic/source face       b = d_S a + r
spectral/Fourier face        A and its curvature Omega_A
geometric/Hodge face         d_H^* y and ||y||^2.
```

No one face alone contains the equality.

## 3. Exact, subunit, and dissipative annihilation

### Corollary 3.1 — exact comparison

Assume `r=0`, `d_H^*y=0`, and `Omega_A a=0`.  Then `y=0`.

If `A_0` is faithful on the distinguished source boundary `b=d_Sa`, meaning

\[
 A_0b=0\Longrightarrow b=0,                                      \tag{9}
\]

then `b=0`.

### Proof

Equation `(6)` gives `||y||^2=0`.  Hence `y=0`; `(9)` gives `b=0`.  `QED`

### Corollary 3.2 — subunit curvature annihilation

Assume `d_H^*y=0` and that for some real `kappa<1`,

\[
 \|\Omega_Aa+A_0r\|\leq\kappa\|y\|.                            \tag{10}
\]

Then `y=0`.

### Proof

By `(7)`,

\[
 \|y\|^2\leq\kappa\|y\|^2.
\]

Since `1-kappa>0`, this forces `||y||=0`.  `QED`

The result is strict.  At `kappa=1`, take any nonzero `y`, let `d_H=0`, `r=0`, and choose data
with `Omega_Aa=y`.  Then `(6)` holds with equality and no vanishing follows.

### Corollary 3.3 — source energy condition

Assume `d_H^*y=0` and that for some real `kappa<1`,

\[
 \operatorname{Re}\langle\Omega_Aa+A_0r,y\rangle
 \leq\kappa\|y\|^2.                                             \tag{11}
\]

Then `y=0`.  In particular, the dissipativity condition

\[
 \operatorname{Re}\langle\Omega_Aa+A_0r,y\rangle\leq0
\]

forces `y=0`.

### Proof

Take real parts in `(6)`.  Co-closure removes the first term, hence

\[
 \|y\|^2
 =\operatorname{Re}\langle\Omega_Aa+A_0r,y\rangle
 \leq\kappa\|y\|^2.
\]

Since `1-kappa>0`, `y=0`.  `QED`

Condition `(11)` is directional.  It does not bound the norm of curvature on every vector; it
controls only curvature work on the distinguished source/field pair.  Consequently it is not
implied by a general small-operator theorem and can remain accessible when `Omega_A` is singular
or has large transverse components.  Conversely, `(10)` implies `(11)` by Cauchy--Schwarz.  Thus
`(11)` is a genuine weakening of the subunit norm target on these data.

### Corollary 3.4 — approximate co-closure

Under `(10)`,

\[
 (1-\kappa)\|y\|^2
 \leq\|A_{-1}a\|\,\|d_H^*y\|.                                  \tag{12}
\]

Thus a uniform bound on source antecedents converts quantitative co-closure into quantitative
field control without requiring exact comparison.

### Proof

Insert `(10)` in `(7)` and move the curvature term to the left.  `QED`

## 4. Gauge covariance

### Theorem 4.1 `[PROVED HERE]`

Let `U_{-1}:H^{-1}->H'^{-1}` and `U_0:H^0->H'^0` be unitary.  Define

\[
 d'_H=U_0d_HU_{-1}^{-1},\quad
 A'_{-1}=U_{-1}A_{-1},\quad
 A'_0=U_0A_0.                                                \tag{13}
\]

Then

\[
 \Omega_{A'}a=U_0\Omega_Aa,\quad
 y'=U_0y,\quad
 (d'_H)^*y'=U_{-1}d_H^*y.                                   \tag{14}
\]

Consequently `(6)`--`(12)` are invariant under unitary changes of observer frame.

### Proof

Using `(13)`,

\[
 \begin{aligned}
 \Omega_{A'}a
 &=U_0A_0d_Sa-U_0d_HU_{-1}^{-1}U_{-1}A_{-1}a\\
 &=U_0(A_0d_Sa-d_HA_{-1}a).
 \end{aligned}
\]

The formula for the adjoint follows from unitary conjugation.  Unitaries preserve inner products
and norms, proving the claim.  `QED`

## 5. Why this is stronger than the old exact-comparison target

The usual Hodge argument asks for all of the following:

1. source exactness `b=d_Sa`;
2. an exact chain comparison `Omega_Aa=0`;
3. physical co-closure `d_H^*A_0b=0`;
4. faithfulness of `A_0` on `b`.

Corollary 3.2 replaces item 2 by `(10)`.  This is genuinely weaker: nonzero comparison curvature
is allowed, and it may even vary with source aperture, provided its gain on the actual source
antecedent remains uniformly below one.  Corollary 3.3 weakens this again to the one scalar
curvature-work inequality `(11)`.  Corollary 3.4 permits both comparison curvature and a small
Hodge residual.

For the current Route-R architecture, the source boundary, singular fixed-physical landing,
Cartier wall trace, and Gamma--Bockstein transgression have now been constructed in the corpus.
The remaining reflection-odd first-wall orientation is naturally a source energy condition: it is
enough to prove `(11)` for the resulting principal conormal.  Perfect same-fibre Cartier equality
and an all-directions norm contraction are both sufficient but unnecessary.

This statement does not claim that the needed estimate is already available.  It says exactly
what weaker theorem would still annihilate the Hodge-mate field.

## 6. Anti-circularity test

A proposed application is circular if any of the following occurs:

1. `a`, `A`, or its domain is chosen after inspecting a zero or the desired field `y`;
2. `Omega_A` is defined as `y` or divided by the horizontal displacement;
3. `(10)` or `(11)` is checked only after assuming `y=0` or critical-line placement;
4. faithfulness `(9)` is replaced by a zero-equivalent scalar detector;
5. co-closure is imposed by quotienting away the nonzero source boundary.

A valid RH application must construct the source antecedent and comparison before divisor
specialization, retain prime/depth/multiplicity provenance, and prove one uniform `kappa<1` from
literal arithmetic source structure.

## 7. Novelty and scope

The abstract proof is an integration-by-parts identity in Hilbert complexes and is not claimed as
new parent mathematics.  Candidate-new content is its role as the exact merger law for the HGT
route atlas and the strict weakening it exposes in the Route-R open core.  Historical priority for
that application remains unaudited.

The theorem does not prove RH.  It gives a non-circular forcing mechanism and identifies signed
curvature work as a smaller analytic target once source, comparison, and Hodge landing are
constructed.  In the current Route-R corpus those organs exist; the source-derived sign does not.

## Lean return notes

Later formalization should use two bounded maps plus one densely defined target differential and
its adjoint.  Likely reusable areas include the existing Hodge/Green and Route-R fixed-corona
modules.  Exact file names and declarations must be found with
`scripts/formal_tools.py research` before writing Lean.  No Lean was written or built here.

## Log

- 2026-08-08 — exact source--observer energy identity, frame covariance, strict subunit
  annihilation, sharpness at unit gain, and approximate co-closure estimate paper-proved.
- 2026-08-08 — added paper-proof of the directional source energy condition; reconciled its
  dissipative sign with the latest Burnol Cartier-wall and Gamma--Bockstein frontier.
