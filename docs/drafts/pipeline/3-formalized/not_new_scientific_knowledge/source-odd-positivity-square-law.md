# Positivity cannot be odd; reciprocal squares are the positive survivor

- **ID:** source-odd-positivity-square-law
- **Stage:** 3-formalized
- **Type:** THEOREM + NO-GO (paper + Lean)
- **Parent:** `source-colligation-quadratic-transfer-selector.md`
- **Statement:** A positive-semidefinite law cannot occupy a nonzero source-odd sector. Every
  nonzero polarity-changing transfer must be amplitude-like; its two reciprocal squares are
  positive, source-even, and equal in rank.
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceOddPositivitySquareLaw.lean`

## Goal

Determine whether the source-derived odd quadratic transfer can itself be the positive metric or
probability object required by a physical successor theory. Close the no-go by extracting the
strongest positive construction forced by the obstruction.

## Gates

- [x] exact no-go mechanism
- [x] nontrivial positive survivor
- [x] dependency-closed paper proof `[PROVED HERE]`
- [x] unconditional Lean theorems
- [x] final target build, generated index, and axiom audit
- [ ] project-wide lint (blocked by unrelated pre-existing unreachable modules)
- [ ] source-derived physical identification of the reciprocal squares

## Odd-positivity obstruction

`[PROVED HERE]`

Let \(A,Q\in M_n(\mathbb C)\). Suppose

\[
A^\dagger=A,\qquad Q\succeq0,\qquad AQA=-Q.                   \tag{OPS1}
\]

Then

\[
Q=0.                                                         \tag{OPS2}
\]

### Proof

Positive semidefiniteness is preserved by congruence, so

\[
A^\dagger Q A\succeq0.
\]

Using `(OPS1)`, this matrix is \(-Q\). Hence both \(Q\succeq0\) and \(-Q\succeq0\).
The positive-semidefinite cone is pointed, so \(Q=0\).

### Exact consequence

A nonzero object that changes retained/created polarity cannot itself be a positive metric,
density, probability kernel, or Hamiltonian. The paired tensor selected in the preceding card is
an amplitude-level transfer, not yet a positive physical law.

## Strongest positive survivor: reciprocal squaring

`[PROVED HERE]`

For any rectangular complex matrix \(D\in M_{m,n}(\mathbb C)\), define

\[
H_{\rm in}=D^\dagger D,\qquad H_{\rm out}=DD^\dagger.         \tag{OPS3}
\]

Then

\[
H_{\rm in}\succeq0,\qquad H_{\rm out}\succeq0,\qquad
\operatorname{rank}H_{\rm in}
=\operatorname{rank}H_{\rm out}
=\operatorname{rank}D.                                      \tag{OPS4}
\]

If \(m=n\), \(A^2=I\), \(A^\dagger=A\), and

\[
ADA=-D,                                                       \tag{OPS5}
\]

then

\[
AH_{\rm in}A=H_{\rm in},\qquad AH_{\rm out}A=H_{\rm out}.     \tag{OPS6}
\]

### Proof

For every vector \(x\),

\[
x^\dagger D^\dagger D x=\|Dx\|^2\ge0;
\]

the second positivity statement is identical with \(D^\dagger\). Kernel identities

\[
\ker(D^\dagger D)=\ker D,\qquad
\ker(DD^\dagger)=\ker D^\dagger
\]

give `(OPS4)` by rank-nullity and equality of the ranks of \(D\) and \(D^\dagger\).

Equation `(OPS5)` and \(A^2=I\) give

\[
AD=-DA,\qquad AD^\dagger=-D^\dagger A.
\]

Therefore

\[
A(D^\dagger D)A=(-D^\dagger A)(-AD)=D^\dagger D
\]

and similarly for \(DD^\dagger\), proving `(OPS6)`.

## Lean certificate

`[LEAN-PROVED]`

Exact declarations:

- `posSemidef_sourceOdd_eq_zero`
- `reciprocalDomainSquare`
- `reciprocalCodomainSquare`
- `reciprocalDomainSquare_posSemidef`
- `reciprocalCodomainSquare_posSemidef`
- `reciprocalSquare_rank_eq`
- `sourceOdd_reciprocalSquares_even`

Direct foreground check:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceOddPositivitySquareLaw.lean
lake build GaloisForLFunctions.HTGeometry.SourceOddPositivitySquareLaw
```

No `sorry`, `admit`, axiom declaration, opaque declaration, unsafe declaration, or
computation-based proof appears in the module.
The final target build completed all 3,182 jobs. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile priority audit

The mathematics is established parent theory:

- supersymmetric quantum mechanics uses partner Hamiltonians \(D^\dagger D\) and
  \(DD^\dagger\);
- Hodge theory squares an odd differential plus adjoint to obtain a positive Laplacian;
- spectral triples and the Chamseddine--Connes spectral action derive gravity, gauge, and Higgs
  terms from a supplied Dirac operator and supplied noncommutative geometry
  ([arXiv:hep-th/9606001](https://arxiv.org/abs/hep-th/9606001));
- the quantum geometric tensor already combines quantum metric and Berry curvature, and its
  positivity yields metric--curvature inequalities
  ([Phys. Rev. B 81, 245129](https://doi.org/10.1103/PhysRevB.81.245129),
  [Phys. Rev. Lett. 136, 116602](https://doi.org/10.1103/8312-ntt5)).

Thus “physics is the square of an odd operator” is `[REDISCOVERED]`. Door grade for the exact
theorems: `[BRIDGE]`.

## What the obstruction changes

The active incompatibility law previously asked the source-odd quadratic record to generate
positivity directly. `(OPS2)` proves that reading impossible. The architecture must have two
levels:

```text
odd source-changing transfer D
          ↓ reciprocal squaring
positive even laws D†D and DD†.
```

This is not optional representation choice. Nonzero odd positivity is algebraically impossible.

## Universal jump exposed by the survivor

`[CONJECTURE — NOT SCIENTIFIC KNOWLEDGE]`

### Reciprocal square law of reality

> **Reality is the square of what cannot happen together.**

Sharper physical form:

> **Gravity and quantum law are the same incompatibility transfer, multiplied in opposite
> orders.**

For a source-complete objective event \(e\), conjecture a source-generated, category-changing
transfer

\[
\mathcal D_e:\mathcal H_h\longrightarrow\mathcal H_{he}
\]

such that

\[
\boxed{
\mathsf Q_e=\mathcal D_e^\dagger\mathcal D_e,\qquad
\mathsf G_e=\mathcal D_e\mathcal D_e^\dagger.
}                                                             \tag{OPS7}
\]

Candidate interpretation:

- \(\mathcal D_e\): amplitude by which mutually incompatible quantum futures become one event;
- \(\mathsf Q_e\): retained/internal quantum and gauge response;
- \(\mathsf G_e\): created/external clock-order and gravitational response;
- zero-mode imbalance/index of \(\mathcal D_e\): persistent chiral matter;
- off-diagonal source structure of \(\mathcal D_e\): Higgs/soldering;
- iterated non-finite closure of \(\mathcal D_e\): hypertranscendent history/time.

Every bullet is conjectural.

## Why this is not yet supersymmetry or spectral action with new names

The candidate-new requirement is not `(OPS3)`. It is that an event source uniquely generates
\(\mathcal D_e\), its two Hilbert/operational sides, adjoint, positivity, composition, and
calibration before spacetime, field content, or a spectral triple is supplied. A fixed-space
supercharge, Hilbert complex, or Dirac operator fails this requirement.

The needed mathematical object is a **positive transcategorical differential**: a morphism whose
adjoint composites live in different event-generated operational categories, while a bar
construction recovers the complete source incompatibility nerve.

## Falsifiers

Retire the physical jump if:

1. source axioms admit inequivalent \(\mathcal D_e\) with different reciprocal squares;
2. adjoint or positivity requires a pre-existing spacetime/Hilbert category;
3. the construction reduces to a fixed spectral triple or supersymmetric partner Hamiltonian;
4. \(D^\dagger D\) and \(DD^\dagger\) cannot reproduce exact \(3+1\) Lorentz gravity and
   \(S(U(2)\times U(3))\) with observed chiral matter;
5. it permits extra force sectors or independent gravity/gauge tuning;
6. the proposed two-sided spectral relation has no operational observable; or
7. no finite parameter-free prediction follows.

## Log

- 2026-07-29 — proved nonzero positive source-odd law impossible.
- 2026-07-29 — extracted reciprocal positive squares as mandatory positive survivor.
- 2026-07-29 — proved positivity, equal-rank reciprocity, and evenness in Lean.
- 2026-07-29 — isolated source-generated transcategorical differential as novelty boundary.
- 2026-07-29 — final target build and axiom audit passed; generated index refreshed. Global lint
  remains red only on unrelated pre-existing unreachable modules.
