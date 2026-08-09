# Locally finite realization tower, global section, and nonproperness-necessity law

- **ID:** ULF-REG-KONIG-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / FIELD ACCEPTANCE GATE
- **Source:** Realization End Geometry compactness attack
- **Statement:** Every coherent inverse tower of nonempty finite realization types has a compatible global section; therefore finite-local/global failure requires noncoherence, noncompactness, or an additional nonclosed admission doctrine.
- **Status:** [LEAN-PROVED] [DEPENDENCY-CLOSED] [FIELD ACCEPTANCE GATE]

## 1. Setup

Let \((X_n)_{n\ge0}\) be nonempty types. For every \(i\le j\), let

\[
\pi_{ij}:X_j\longrightarrow X_i
\tag{K.1}
\]

satisfy

\[
\pi_{ii}=\operatorname{id}_{X_i},
\qquad
\pi_{ik}=\pi_{ij}\pi_{jk}\quad(i\le j\le k).
\tag{K.2}
\]

Assume \(X_0\) is finite and every one-step fibre

\[
\{y\in X_{n+1}:\pi_{n,n+1}(y)=x\}
\tag{K.3}
\]

is finite. Finite realization types are a special case.

## 2. Theorem — proper finite realization towers have ends

There exists a compatible global realization

\[
x=(x_n)_{n\ge0},
\qquad
\pi_{ij}(x_j)=x_i\quad(i\le j).
\tag{K.4}
\]

### Proof

Form the graded set

\[
T=\coprod_{n\ge0}X_n.
\tag{K.5}
\]

Join \(x\in X_n\) to \(y\in X_{n+1}\) when \(\pi_{n,n+1}(y)=x\). Every level is nonempty.
Every vertex has finitely many children by (K.3), and there are finitely many roots by finiteness of
\(X_0\).

At least one root has descendants at arbitrarily large levels. Otherwise each root would have a
finite height bound; the maximum of finitely many bounds would contradict nonemptiness of all
levels. Kőnig's infinity lemma now gives an infinite rooted path

\[
x_0\leftarrow x_1\leftarrow x_2\leftarrow\cdots.
\tag{K.6}
\]

One-step compatibility and (K.2) imply (K.4) for every \(i\le j\). QED.

## 3. Corollary — obstruction-location law

Suppose every finite aperture has at least one realization but no admitted global law exists. Then
the obstruction cannot be “absence of a set-theoretic end” inside a coherent locally finite total
tower. At least one of the following occurs:

1. the alleged transition system is partial or violates coherence;
2. some root set or transition fibre is infinite/noncompact;
3. a compatible set-theoretic section exists but is removed by a global effectivity, topology,
   domain, positivity, source-normality, or other admission condition not preserved by the inverse
   limit.

This is a logical exhaustion: under negation of all three clauses, the theorem produces an admitted
global section.

## 4. Sharpness

### 4.1 Infinite branching permits escape

Let \(X_n=\{k\in\mathbb N:k\ge n\}\) and let every restriction map be the identity on the underlying
integer whenever defined as a relation. Every stage is nonempty, but no integer belongs to every
stage. The system is not a tower of total maps (K.1); equivalently, the extension relation has an
infinite nonproper escape. This shows total coherent transport is load-bearing.

### 4.2 Effectivity can remove an existing end

Finite-support Boolean profiles realize every finite prefix of the all-true profile. The inverse
limit contains the all-true end, but the declared finite-support effective class excludes it. The
gap is admission/effectivity, not absence of a compatible set-theoretic profile.

### 4.3 Compact Hausdorff extension

The finite theorem is the discrete case of the standard fact that a cofiltered inverse system of
nonempty compact Hausdorff spaces has nonempty limit. Thus “finite” can be replaced by a genuine
properness/compactness hypothesis, but not by arbitrary closed-looking stage data.

## 5. Field leverage

The theorem rules out a common explanatory failure. One cannot explain a corpus finite-to-global
obstruction by drawing a locally finite tree with all levels occupied and then declaring its end
missing. A viable model must identify the exact nonproper, noncoherent, or admission-changing event.

For source-normal Stokes/Bockstein dagger landing this yields a precise constraint: any enlargement
that kills all finite prime classes while retaining their finite valuation coframe cannot be a
coherent locally finite exact tower. It must cross a coframe-extension anomaly, nonclosed completion,
domain wall, or another explicitly typed admission failure. This agrees with, but does not prove,
the existing coframe nonerasure theorem.

## 6. Lean certificate

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveRealizationKonig`.

Closed theorem:
`constitutiveLocallyFiniteRealizationTower_hasGlobalSection`.

Finite-type corollary:
`constitutiveFiniteRealizationTower_hasGlobalSection`.

The formal proof uses the existing mathlib Kőnig theorem
`exists_seq_forall_proj_of_forall_finite`, adds no project axioms, and joins the
universal-law-field umbrella. Targeted foreground build:

```text
lake build GaloisForLFunctions.HTGeometry.ConstitutiveRealizationKonig
Build completed successfully (852 jobs).
```

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 7. Hostile scope

- Kőnig compactness is established mathematics.
- The theorem is an acceptance gate for a new field, not a new proof of compactness.
- It does not construct the HGT arithmetic realization tower.
- It does not prove source-normal dagger landing or RH.
- It is significant because it falsifies every locally finite toy explanation of a persistent
  finite/global obstruction.

## Log

- 2026-08-09 — dependency-closed paper proof fixed; Lean target selected.
- 2026-08-09 — full locally finite theorem and finite-level corollary closed in Lean; promoted to
  Stage 3.
