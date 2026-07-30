# Projective source disagreement forces joint visibility

- **ID:** `projective-source-visibility-parity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PROJECTIVE-COCYCLE BRIDGE / NOT NEW MATHEMATICS
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [PARENT ALGEBRA]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NO PHYSICS PROVED]`
- **Parents:** `source-ordered-pair-complex-structure.md`,
  `joint-source-realization-common-kernel-criterion.md`,
  `../../1-in-progress/jointly-conservative-future-shape-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveSourceVisibilityParity.lean`
- **Statement:** A nontrivial scalar commutator between two source changes makes their two
  individually lossy defect reports jointly injective. For the standard order-two source pair,
  the same sign obstruction generates a complex structure and gives an exact odd/even visibility
  law on symmetric successor layers.

## Goal

Ask what the source-pair complex-structure theorem and the common-kernel criterion are jointly
telling us.

The first says that two anticommuting real source involutions generate an operator squaring to
\(-1\). The second says that a family of defect reports is jointly conservative exactly when its
common fixed sector vanishes. The missing bridge is whether the same source relation that creates
phase also forces the common fixed sector to vanish.

It does.

## The scalar-cocycle visibility theorem

Let \(K\) be a field, \(V\) a \(K\)-vector space, \(A,B:V\to V\) linear, and
\(\zeta\in K\) with \(\zeta\ne1\). Suppose

\[
AB=\zeta BA.
\tag{PV.1}
\]

Define the two source-defect reports

\[
\delta_A(v)=v-Av,\qquad
\delta_B(v)=v-Bv
\tag{PV.2}
\]

and their joint fingerprint

\[
\Delta_{A,B}(v)=\bigl(\delta_A(v),\delta_B(v)\bigr).
\tag{PV.3}
\]

### Theorem 1

`[PROVED HERE]`

Under `(PV.1)`, \(\Delta_{A,B}\) is injective.

### Proof

Suppose \(\Delta_{A,B}(x)=\Delta_{A,B}(y)\) and put \(z=x-y\). Linearity gives

\[
Az=z,\qquad Bz=z.
\tag{PV.4}
\]

Therefore

\[
z=A(Bz)=\zeta B(Az)=\zeta z.
\tag{PV.5}
\]

Since \(K\) is a field and \(\zeta\ne1\), equation `(PV.5)` forces \(z=0\). Hence \(x=y\).
\(\square\)

Equivalently, a nontrivial projective commutator forbids a nonzero vector fixed by both source
changes. This is the exact common-kernel calculation; injectivity is not obtained by hiding an
identity reporter inside the product.

## One obstruction, two consequences

Now let \(J,S:V\to V\) be involutions over a field of characteristic not two:

\[
J^2=S^2=1.
\tag{PV.6}
\]

### Theorem 2

`[PROVED HERE]`

If \(JS=-SJ\), then:

1. the ordered product \(I=JS\) satisfies \(I^2=-1\); and
2. \(\Delta_{J,S}\) is injective.

Conversely, under `(PV.6)`, \(I^2=-1\) implies \(JS=-SJ\).

### Proof

Anticommutation and `(PV.6)` give

\[
I^2=JSJS=-J^2S^2=-1.
\tag{PV.7}
\]

Theorem 1 with \(\zeta=-1\) proves joint injectivity. Conversely, multiply
\(JSJS=-1\) on the left by \(J\) and on the right by \(S\); `(PV.6)` gives
\(SJ=-JS\). \(\square\)

Thus the exact source relation generating a local complex orientation also prevents any nonzero
state from being invisible to both source-relative change reports.

## Exact symmetric-successor parity law

Let \(V=Kx\oplus Ky\), with the standard source actions

\[
Jx=x,\quad Jy=-y,\qquad Sx=y,\quad Sy=x.
\tag{PV.8}
\]

They induce actions \(J_n,S_n\) on the degree-\(n\) symmetric layer
\(\operatorname{Sym}^n(V)\). Tensor functoriality gives

\[
J_nS_n=(-1)^n S_nJ_n.
\tag{PV.9}
\]

Define

\[
\Delta_n(w)=\bigl(w-J_nw,\;w-S_nw\bigr).
\tag{PV.10}
\]

### Theorem 3

`[PROVED HERE]`

For every positive \(n\), \(\Delta_n\) is injective exactly when \(n\) is odd.

### Proof

If \(n\) is odd, `(PV.9)` is anticommutation. Theorem 1 proves injectivity.

If \(n\) is even, the nonzero symmetric tensor

\[
w_n=x^n+y^n
\tag{PV.11}
\]

is fixed by both \(J_n\) and \(S_n\). Hence \(\Delta_n(w_n)=0=\Delta_n(0)\), so
\(\Delta_n\) is not injective. \(\square\)

Each component in `(PV.10)` is individually noninjective at every positive degree: \(x^n\) is
\(J_n\)-fixed, while \((x+y)^n\) is \(S_n\)-fixed. Odd-degree joint injectivity is therefore
genuinely relational.

## General periodic form

If `(PV.1)` holds, the induced tensor relation at depth \(n\) is

\[
A_nB_n=\zeta^nB_nA_n.
\tag{PV.12}
\]

Therefore every layer with \(\zeta^n\ne1\) is jointly visible to the two defect reports. Layers
where \(\zeta^n=1\) are precisely those on which this cocycle obstruction no longer rules out a
common invisible sector. Existence of such a sector requires a separate representation-specific
proof; Theorem 3 supplies it for the standard order-two source pair.

## What this means for the programme

The corpus had treated three facts separately:

1. ordered real source operations can generate a complex orientation;
2. multiple lossy reporters can be jointly conservative; and
3. source-odd and source-even successor layers behave differently.

They are shadows of one algebraic datum: a nontrivial projective source commutator.

```text
nontrivial source cocycle
  -> ordered product carries phase
  -> no common fixed sector
  -> source-defect views are jointly conservative
  -> tensor depth raises the cocycle
  -> periodic visible / potentially hidden layers.
```

This does not yet identify physical states, observations, bosons, fermions, time, spacetime, or
forces. It changes the stronger conjecture: joint conservativity should not be imposed as an
independent reconstruction axiom if it can instead be forced by the projective coherence of
source-changing completion functors.

The next mathematical target is a higher version in which:

- source changes act on the full completion object rather than one vector space;
- their coherence is a nontrivial \(2\)-cocycle or higher obstruction;
- the corresponding family of homotopy-defect reporters is jointly conservative; and
- transgression through source succession produces comparison transport rather than assuming a
  connection.

## Relation to the quintic successor modulus

Source polarity alone leaves a continuous projective modulus at symmetric arity five. Theorem 3
does not select one value of that modulus. Instead it proves that, once the paired source change
\(S\) is retained with \(J\), every odd quintic tensor is recoverable from its two source-relative
defects.

This separates two questions that had been conflated:

1. **visibility:** can the full successor tensor be reconstructed from source-relative changes?
   At odd depth, yes.
2. **dynamics:** which visible successor orbit is physically realized? The quintic modulus shows
   this remains open.

Joint visibility does not select a law. It ensures that the law-selection problem is not hidden
in a common source gauge.

## Parent and novelty audit

The algebra belongs to standard Clifford, Pauli, twisted-group-algebra, and projective
representation theory. Tensor powers multiply projective cocycles, and nontrivial scalar
commutators forbid common eigenvectors with eigenvalue one. No novelty is claimed for Theorems
1--3.

Relevant parent directions include:

- the corpus's earlier matrix/common-eigenline specialization:
  [`weyl-common-character-line-nogo.md`](weyl-common-character-line-nogo.md);
- projective representations encoded by unitary \(2\)-cocycles:
  [De Commer--Martos--Nest](https://arxiv.org/abs/2112.04365);
- cocycle twists by the Klein four group:
  [Davies](https://arxiv.org/abs/1502.06101); and
- transgression of symmetry cocycles to projective boundary actions:
  [Müller--Szabo](https://arxiv.org/abs/1811.05446).

Candidate novelty can only begin with a source-only derivation of the cocycle and a higher
joint-conservativity theorem for the endogenous completion object.

## Hostile-review audit

- **Identity-reporter objection:** pass. Neither component of `(PV.10)` is injective.
- **Common-kernel theatre:** pass. The common kernel is calculated and vanishes by `(PV.5)`.
- **Complex-structure overclaim:** pass. No connection, metric, positivity, or force follows.
- **Parity overclaim:** pass. The even converse is proved only for the explicit standard source
  representation.
- **Physics derivation:** fail/open. Physical source changes and physical defect reports have not
  been reconstructed.
- **Novel mathematics:** fail. The finite theorem is parent algebra.
- **Programme value:** pass. Phase, joint visibility, and successor parity now have one exact
  antecedent instead of three unrelated assumptions.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/ProjectiveSourceVisibilityParity.lean`.

It formalizes unconditionally:

- the scalar-cocycle common-fixed-vector no-go;
- joint-defect injectivity for every nontrivial scalar commutator;
- both directions between anticommutation and ordered square \(-1\) for involutions;
- odd-degree anticommutation of binary-form polarity and swap;
- odd-degree joint-defect injectivity;
- the explicit nonzero even-degree endpoint sector fixed by both source changes; and
- the exact equivalence between joint-defect injectivity and odd degree.

Direct `lake env lean` checking passed. The exact module build passed
`1826/1826`. Axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide formal lint reached an unrelated existing umbrella failure:
`GaloisForLFunctions.HTGeometry.LocalSpectralExtensionRelationRigidity` is unreachable from
`GaloisForLFunctions.HTGeometry`. The new module is imported by that umbrella and contains no
`sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 → 1 in-progress: exact source relation, reporters, and falsifiers specified
- [x] 1 → 2 fully-proven: dependency-closed paper proofs of Theorems 1--3
- [x] 2 → 3 formalized: exact unconditional Lean theorems, axiom audit, module build
- [ ] source-only derivation of the projective cocycle
- [ ] higher completion-object joint-conservativity theorem
- [ ] physical instantiation or quantitative prediction

## Log

- 2026-07-30 — Derived scalar-cocycle joint-visibility theorem from the common-kernel criterion.
- 2026-07-30 — Proved exact odd/even symmetric-successor visibility law for the standard source
  pair.
- 2026-07-30 — Recorded that this is standard projective/Clifford algebra and isolated the higher
  source-completion theorem as the actual novelty target.
- 2026-07-30 — Formalized the complete theorem family in
  `ProjectiveSourceVisibilityParity.lean`; direct check, axiom audit, and exact module build pass.
