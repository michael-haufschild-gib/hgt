# Confocal envelope hull completeness and exposed-face recovery

- **ID:** `confocal-envelope-hull-completeness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** The complete confocal upper field of any bounded source determines an idempotent canonical hull of its lifted points `(Re z, |z|)`; singleton exposed faces, including isolated ones, are exactly recoverable, while non-singleton faces are the exact residual ambiguity.

## Goal

Answer the paper's geometric open question and remove cofinite transverse neutrality from the
geometry itself.  Neutrality should remain only a sufficient hypothesis for transporting the
moment observable to the confocal field, not a hypothesis of envelope reconstruction.

## Gates

- [x] 0 → 1 in-progress: exact statement and hostile attack recorded
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: exact Lean theorem(s), narrow leaf build, axiom audit
- [ ] 3 → 4 publication-ready: integrated into the single master theorem of the paper

## Exact claim

Lift a complex source by

```text
Lambda(z) = (x,a) = (Re z, |z|),       |x| <= a,
g_R(x,a) = a + sqrt(R^2 - 2Rx + a^2).
```

For a nonempty bounded lifted source `S` and a nonempty radius domain `D`, let

```text
G_S(R) = sup_(q in S) g_R(q).
```

Define its confocal hull by

```text
H_D(S) = { (x,a) : |x| <= a and, for every R in D,
  a <= G_S(R),
  R x - G_S(R) a >= (R^2-G_S(R)^2)/2 }.
```

Then:

1. `S subset H_D(S)`.
2. `H_D(S)` is a closed convex subset of the Lorentz half-plane and is the largest source `T`
   satisfying `G_T<=G_S` on `D`.
3. `G_(H_D(S)) = G_S` on `D`.
4. `H_D(H_D(S)) = H_D(S)`.
5. `G_S = G_T` on `D` iff `H_D(S)=H_D(T)`.
6. For each `R in D`, the field determines the exposed face

   ```text
   F_R = H_D(S) intersect
     { (x,a) : R x-G_S(R)a=(R^2-G_S(R)^2)/2 }.
   ```

   Every source orbit active at `R` lies in `F_R`.  If `F_R` is a singleton, its point
   `(x,a)` and hence the conjugation orbit `x +/- i sqrt(a^2-x^2)` are recovered even when the
   branch is active only at that single radius.
7. The result is optimal: adjoining any lifted point of `H_D(S)` leaves the full field unchanged.
   Thus the field cannot distinguish individual points inside a non-singleton exposed face or in
   the unexposed interior of the hull.

The algebraic engine is the exact Lorentz half-space equivalence

```text
g_R(x,a) <= L
  iff a <= L and R x-L a >= (R^2-L^2)/2,
```

valid on `|x| <= a`.

## Approach

Prove the half-space equivalence by isolating and squaring the single nonnegative square root.
The hull is then the intersection of all half-spaces encoded by the observed field.  Extensivity,
field invariance, idempotence, and the equality classification follow formally.  Singleton-face
recovery is immediate from field equality; optimal ambiguity follows by adjoining hull points.

## Hostile audit

- `[LITERATURE]` Support functions, half-space reconstruction, and exposed faces are classical
  convex geometry.
- `[BRIDGE]` The theorem is a nonlinear confocal/Lorentz specialization of that parent mechanism.
- The exact self-consistent normal `(R,-G_S(R))`, idempotent closure, and maximal orbit-
  identifiability statement were not located in the targeted comparison; novelty is unverified.
- The theorem does not claim recovery of raw atomic weights or every raw node.  It proves the
  exact maximal quotient seen by the full upper field and supplies counterpresentations for all
  additional point-level claims.

## Log

- 2026-07-19 — created in Stage 1 after the paper's second open question was isolated.

## Complete paper proof

Fix a nonempty radius domain `D`.  Work in the Lorentz half-plane

```text
C = {(x,a) in R^2 : |x| <= a}.
```

For `q=(x,a) in C`, the radicand

```text
R^2-2Rx+a^2=(R-x)^2+(a^2-x^2)
```

is nonnegative, so `g_R(q)` is well-defined.

### Half-space lemma

Let `L` be real.  If `g_R(x,a)<=L`, then `a<=L` and

```text
sqrt(R^2-2Rx+a^2) <= L-a.
```

Both sides are nonnegative.  Squaring and cancelling `a^2` gives

```text
R x-L a >= (R^2-L^2)/2.                                (1)
```

Conversely, assume `a<=L` and (1).  Rearrangement gives

```text
R^2-2Rx+a^2 <= (L-a)^2.
```

Both sides are nonnegative, hence taking square roots yields `g_R(x,a)<=L`.  Thus the half-space
equivalence in the exact claim holds.  Equality in the branch inequality is equivalent to equality
in (1).

### Extensivity and field invariance

Let `q in S` and `R in D`.  By definition, `g_R(q)<=G_S(R)`.  The half-space lemma with
`L=G_S(R)` proves that `q` satisfies every defining inequality of `H_D(S)`.  Hence

```text
S subset H_D(S).                                       (2)
```

The Lorentz half-plane `C` is closed and convex.  For each fixed `R`, the two remaining defining
conditions are closed affine half-spaces.  Their arbitrary intersection is therefore closed and
convex.  Moreover, if a source `T` satisfies `G_T(R)<=G_S(R)` on `D`, then every `q in T` obeys
`g_R(q)<=G_T(R)<=G_S(R)` for every `R`.  The half-space lemma places `q` in `H_D(S)`.  Hence
`H_D(S)` is the largest source whose field is pointwise bounded by `G_S` on `D`.

Conversely, every `q in H_D(S)` satisfies the two half-space inequalities for every `R in D`.
The reverse direction of the lemma gives

```text
g_R(q)<=G_S(R).                                        (3)
```

Taking the supremum over the hull gives `G_(H_D(S))(R)<=G_S(R)`.  Inclusion (2) gives the reverse
inequality, so

```text
G_(H_D(S))=G_S on D.                                   (4)
```

The definition of the hull depends only on the field on `D`.  Substituting (4) into that definition
proves idempotence

```text
H_D(H_D(S))=H_D(S).                                    (5)
```

If two fields agree, their defining half-spaces agree, and therefore their hulls agree.  Conversely,
if the hulls agree, (4) applied to both sources gives equality of fields.  This proves

```text
G_S=G_T on D iff H_D(S)=H_D(T).                        (6)
```

Thus `H_D` is the maximal quotient determined by the complete confocal field.

### Exposed-face recovery

For fixed `R in D`, the field determines both the hull and the boundary line

```text
R x-G_S(R)a=(R^2-G_S(R)^2)/2.
```

It therefore determines their intersection `F_R`.  If a source point `q` is active at `R`, then
`g_R(q)=G_S(R)`; the equality case of the half-space lemma places `q` in `F_R`.

Suppose now that `F_R={q_R}`.  Any other source with the same complete field has the same hull by
(6), hence the same face.  Every one of its active points at `R` must equal `q_R`.  Writing
`q_R=(x,a)`, the Lorentz inequality gives `a^2-x^2>=0`, so the corresponding complex points are
exactly

```text
x +/- i sqrt(a^2-x^2).
```

The conjugation orbit is recovered from a single radius.  No open interval of stable exposure is
needed.

### Optimality

Let `q in H_D(S)`.  Equation (3) shows that adjoining `q` to `S` cannot raise the field, while the
original source remains included.  Therefore

```text
G_(S union {q})=G_S on D.                              (7)
```

The field cannot decide whether any additional hull point was present in the raw source.  In
particular, the individual membership pattern inside a non-singleton exposed face, and every
unexposed interior point, is invisible.  Combined with singleton-face recovery, (7) is the exact
identifiability boundary.

The proof uses no summability, moment representation, cofinite neutrality, or asymptotic selection.
Those hypotheses belong only to the separate transport from a moment observable to the field.
Geometrically, the theorem applies to every nonempty source for which the displayed suprema are
finite on `D`; bounded sources are the principal case.

## Paper-proof verdict

`[PAPER-PROVED]`.  The proof is dependency-closed.  The mechanism is classical half-space/support-
function geometry, but the exact confocal closure and maximal orbit-identifiability classification
remain `[NOVELTY UNVERIFIED]` pending specialist priority review.
