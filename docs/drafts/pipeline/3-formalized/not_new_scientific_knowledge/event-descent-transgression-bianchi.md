# Endpoint stories, event seams, and triangle-defect transgression

- **ID:** `event-descent-transgression-bianchi`
- **Stage:** 3-formalized
- **Type:** EXACT THEOREM / DESCENT NO-GO / BRIDGE
- **Parent:** `../../1-in-progress/actuality-conservation-boundary-colligation-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE]`
  `[NO PHYSICAL CLAIM PROVED]`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/EventDescentTransgression.lean`
- **Statement:** Group-valued edge comparisons come from one endpoint-indexed story exactly when
  every triangle holonomy is trivial; for linear event seams, failure of the two-step seam defect
  to equal the direct seam defect is exactly the covariant defect of the triangle mismatch.

## Goal

Close two exact mathematical gaps left by fixed-carrier unitary-completion flatness:

1. prove the converse reconstruction theorem—flat comparison triangles admit one global
   endpoint-indexed account; and
2. identify the exact algebraic relation between representation mismatch on event edges and
   composition mismatch on event triangles.

The theorem tests only a proposed language for the actuality programme. It does not identify a
group-valued comparison with a physical event, a triangle defect with force, or a linear
endomorphism with a gauge or gravitational law.

## Part I: endpoint-story reconstruction

Let \(X\) be a nonempty type of event labels, \(G\) a group, and
\(\tau:X\times X\to G\) a family of directed comparisons. Define
\[
\Omega_\tau(x,y,z)
=
\tau(x,y)\tau(y,z)\tau(x,z)^{-1}.                         \tag{1}
\]
Say that \(\tau\) has an **endpoint story** if there is a family \(U:X\to G\) such that
\[
\tau(x,y)=U(x)^{-1}U(y)                                   \tag{2}
\]
for every \(x,y\).

### Theorem 1

The following are equivalent:

1. \(\tau\) has an endpoint story;
2. every comparison triangle is flat,
   \[
   \tau(x,y)\tau(y,z)=\tau(x,z);
   \]
3. \(\Omega_\tau(x,y,z)=1\) for every \(x,y,z\).

Consequently,
\[
\neg\text{EndpointStory}(\tau)
\quad\Longleftrightarrow\quad
\exists x,y,z,\ \Omega_\tau(x,y,z)\ne1.                  \tag{3}
\]

### Dependency-closed proof

Assume `(2)`. Then
\[
\begin{aligned}
\tau(x,y)\tau(y,z)
&=U(x)^{-1}U(y)U(y)^{-1}U(z)\\
&=U(x)^{-1}U(z)
=\tau(x,z),
\end{aligned}
\]
so every triangle is flat.

Conversely, assume every triangle is flat. Choose one base event \(b\in X\) and define
\[
U(x)=\tau(b,x).
\]
Flatness of the triangle \((b,x,y)\) gives
\[
\tau(b,x)\tau(x,y)=\tau(b,y).
\]
Multiplication on the left by \(\tau(b,x)^{-1}\) yields
\[
\tau(x,y)=\tau(b,x)^{-1}\tau(b,y)=U(x)^{-1}U(y),
\]
which is `(2)`.

Finally,
\[
\Omega_\tau(x,y,z)=1
\iff
\tau(x,y)\tau(y,z)\tau(x,z)^{-1}=1
\iff
\tau(x,y)\tau(y,z)=\tau(x,z).
\]
This proves all equivalences and `(3)`. \(\square\)

## Part II: seam--triangle Bianchi identity

Let \(R\) be a commutative ring and let \(K,I,C\) be \(R\)-modules. Supply endpoint laws
\[
a\in\operatorname{End}_R(K),\qquad
d\in\operatorname{End}_R(I),\qquad
p\in\operatorname{End}_R(C)
\]
and event seams
\[
b:I\to K,\qquad r:C\to I,\qquad \eta:C\to K.
\]
For a seam \(f:Y\to X\) between endpoint laws \(A\) and \(B\), define its covariant defect
\[
\mathcal D_{A,B}(f)=Af-fB.                                 \tag{4}
\]
Define the triangle mismatch
\[
\mathcal K(b,r,\eta)=br-\eta.                              \tag{5}
\]

### Theorem 2

The edge and triangle defects obey the exact identity
\[
\boxed{
\mathcal D_{a,d}(b)r
+b\mathcal D_{d,p}(r)
-\mathcal D_{a,p}(\eta)
=
\mathcal D_{a,p}\!\left(\mathcal K(b,r,\eta)\right).
}                                                          \tag{6}
\]

If the triangle is flat, \(br=\eta\), this reduces to
\[
\mathcal D_{a,d}(b)r+b\mathcal D_{d,p}(r)
=\mathcal D_{a,p}(\eta).                                   \tag{7}
\]
In particular, if both component seams are covariantly constant, then their composite is
covariantly constant.

### Dependency-closed proof

Expand the left side of `(6)`:
\[
\begin{aligned}
&(ab-bd)r+b(dr-rp)-(a\eta-\eta p)\\
&=abr-bdr+bdr-brp-a\eta+\eta p\\
&=a(br-\eta)-(br-\eta)p\\
&=\mathcal D_{a,p}\!\left(\mathcal K(b,r,\eta)\right).
\end{aligned}
\]
No commutativity of the endpoint endomorphisms is used. Setting \(br=\eta\) gives `(7)`.
If both component defects vanish, the left side of `(7)` is zero, so the composite defect
vanishes. \(\square\)

## Hostile audit

1. Theorem 1 is elementary nonabelian cocycle reconstruction on the pair groupoid. It is not new
   mathematics.
2. Theorem 2 is a covariant Leibniz identity. It is adjacent to discrete gauge theory and Bianchi
   identities. It is not new mathematics.
3. Equation `(6)` does **not** prove conservation of a norm, dimension, probability, information,
   or physical obstruction. It only identifies one exact algebraic equality.
4. Nontrivial interaction need not imply nontrivial triangle holonomy. Exact factorizations such
   as \(S_3=C_3\rtimes C_2\) can carry a nontrivial mutual action with strict associativity and
   trivial associator holonomy. The complete physical primitive cannot be curvature alone.
5. Arbitrary laboratory channels, bundle connections, and representation seams instantiate the
   same formulas without producing spacetime or a fundamental force.
6. The theorem neither selects the exceptional \(4/6/4\) event nor derives
   \(S(U(2)\times U(3))\), Lorentzian signature, Einstein dynamics, matter, or a finite
   prediction.

## Positive survivor

The exact result sharpens two boundaries:

1. on a complete comparison graph, zero triangle holonomy is not merely necessary but sufficient
   for one endpoint-only global account; and
2. when representation and path comparisons are both present, their defects are not independent:
   equation `(6)` gives their precise covariant transfer law.

This is the smallest algebraic shadow of the proposed statement that a source-selected physical
incompatibility may reappear at a different compositional degree. The physical statement remains
a conjecture because `(6)` does not say which defect is real, source-selected, positive, or
exhaustive.

## Relation to the live theory-of-everything conjecture

The live interpretation is no longer “force equals curvature.” Corpus counterexamples show that
reciprocal action is logically prior to curvature. The stronger conjectural dependency is:

```text
source-selected exceptional objective event
  -> reciprocal possibility-to-causal and causal-to-possibility actions
  -> complete non-product feedback process
  -> seam and curvature shadows related by (6)
  -> gravity and the three gauge forces as four continuum responses.
```

The theorem certifies only the fourth arrow conditional on supplied linear data.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and hostile boundary fixed
- [x] 1 → 2 fully-proven: complete dependency-closed proof
- [x] 2 → 3 formalized: exact Lean declarations and audit
- [ ] 3 → 4 publication-ready: not expected; bridge theorem is standard

## Log

- 2026-07-29 — extracted after global unitary-completion flatness and the reciprocal-action false
  zero separated endpoint globalizability, seam mismatch, and triangle curvature.
- 2026-07-29 — complete paper proofs closed the endpoint-story equivalence and the
  seam--triangle Bianchi identity. Classified both as rediscovered bridges.
- 2026-07-29 — exact theorems formalized unconditionally and passed direct Lean, single-module
  build, axiom, proof-debt, generated-index, repository-lint, and stale-process audits.

## Lean certificate

Exact declarations:

- `completionTriangleHolonomy`;
- `HasEndpointStory`;
- `HasFlatTriangles`;
- `hasEndpointStory_iff_hasFlatTriangles`;
- `hasEndpointStory_iff_triangleHolonomy_eq_one`;
- `noEndpointStory_iff_exists_nontrivial_triangle`;
- `eventSeamDefect`;
- `eventTriangleDefect`;
- `eventSeam_triangleDefect_bianchi`;
- `eventSeam_compose_of_triangle_flat`; and
- `eventSeam_comp_parallel`.

Verification:

- direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/EventDescentTransgression.lean` passed;
- final module build:
  `lake build GaloisForLFunctions.HTGeometry.EventDescentTransgression` passed
  (`2944/2944`);
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- proof-debt scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- formal API index regenerated and contains every declaration;
- `scripts/formal_tools.py lint --check-generated`: passed; and
- no stale Lean or Lake process remained.
