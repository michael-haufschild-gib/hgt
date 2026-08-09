# Finite-jet realization boundary and continuous-classifier no-go

- **ID:** ULF-RBD-JET-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ANALYTIC REALIZATION-BOUNDARY LAW
- **Source:** Realization Boundary Dynamics field charter
- **Statement:** Every finite analytic jet is shared by a differentially algebraic law and a hypertranscendental law; both law classes are dense, have empty interior, are nonclosed in the finite-jet topology, and admit no continuous binary classifier.
- **Status:** [LEAN-PROVED] [CLOSED] [FIELD-LEVEL ANALYTIC CALIBRATION]

## Goal

Give the proposed field a non-Boolean analytic theorem. The theorem identifies a genuine
realization boundary: every finite observer fibre meets two globally incompatible constitutive
doctrines. It therefore separates finite observational effectivity from global law effectivity
without identifying hypertranscendence with ordinary orbit noncompactness.

## Setup

For a function germ (f:\mathbb C\to\mathbb C), define its (j)-th observed jet coordinate by

\[
J_j(f)=f^{(j)}(0).
\tag{1}
\]

Let \(\mathcal J=(\mathbb C^{\mathbb C},\tau_J)\), where \(\tau_J\) is the initial topology of the
full jet map

\[
J:\mathcal J\longrightarrow\mathbb C^{\mathbb N},
\qquad f\longmapsto(J_j(f))_{j\ge0}.
\tag{2}
\]

Write \(\mathrm{DA}\subset\mathcal J\) for the differentially algebraic functions and
\(\mathrm{HT}=\mathcal J\setminus\mathrm{DA}\) for the hypertranscendental functions.

## Theorem 1 — exact finite-jet double realization

For every \(r\ge0\) and every prescribed sequence \(c:\mathbb N\to\mathbb C\), there exist
functions \(p,h:\mathbb C\to\mathbb C\) such that

\[
J_j(p)=J_j(h)=c_j\qquad(0\le j\le r),
\tag{3}
\]

with \(p\in\mathrm{DA}\) and \(h\in\mathrm{HT}\).

### Proof

Set

\[
P_{r,c}(z)=\sum_{k=0}^{r}\frac{c_k}{k!}z^k.
\tag{4}
\]

Then \(J_j(P_{r,c})=c_j\) for \(j\le r\), and \(P_{r,c}\) is differentially algebraic because its
\((r+1)\)-st derivative vanishes.

Fix one entire hypertranscendental function \(W\). Let \(T_rW\) be its Taylor polynomial of degree
\(r\) at zero and put

\[
h=W+P_{r,c}-T_rW.
\tag{5}
\]

The polynomial correction makes the first \(r+1\) jet coordinates of \(h\) equal to those of
\(P_{r,c}\). If \(h\) were differentially algebraic, subtracting the polynomial
\(P_{r,c}-T_rW\) would make \(W\) differentially algebraic, contradiction. Thus \(h\) is
hypertranscendental. QED.

## Theorem 2 — topological realization boundary

Both \(\mathrm{DA}\) and \(\mathrm{HT}\) are dense in \(\mathcal J\). Consequently

\[
\operatorname{int}(\mathrm{DA})=operatorname{int}(\mathrm{HT})=\varnothing,
\qquad
\mathrm{DA}\text{ and }\mathrm{HT}\text{ are not closed}.
\tag{6}
\]

### Proof

A neighbourhood in the initial finite-jet topology contains a cylinder restricting only finitely
many jet coordinates. Apply Theorem 1 to those coordinates. One realization lies in
\(\mathrm{DA}\) and one in \(\mathrm{HT}\), so both classes meet every neighbourhood.

Since the two classes are complements, density of either implies empty interior of the other. Each
class is nonempty. If one dense class were closed, it would equal all of \(\mathcal J\), contradicting
nonemptiness of its complement. QED.

## Theorem 3 — no continuous finite-jet classifier

There is no continuous map \(\Phi:\mathcal J\to\{0,1\}\) with

\[
\Phi(f)=0\quad(f\in\mathrm{DA}),
\qquad
\Phi(f)=1\quad(f\in\mathrm{HT}),
\tag{7}
\]

where \(\{0,1\}\) has the discrete topology.

### Proof

A continuous map from a space into a Hausdorff space that is constant on a dense subset is constant
on the whole space. Density of \(\mathrm{DA}\) would force \(\Phi\equiv0\), while any
hypertranscendental witness must map to \(1\). QED.

## Field interpretation

The coordinate-free object is not the label “DA” or “HT.” It is the realization map from global
constitutive laws to finite observer jets. Theorems 1–3 identify three intrinsic features of this
map:

1. every finite observer fibre crosses the global doctrine boundary;
2. the two global strata are mutually adherent in observer topology;
3. no continuous finite-observer decision law descends from the global classification.

This is stronger than saying that finite data are incomplete. The observer quotient is maximally
nonseparating for this global law dichotomy. Any future universal-law geometry that claims to carry
hypertranscendence through a finite observer must either add nonlocal history, strengthen the
observer topology, or expose a discontinuous/singular boundary operation.

## Hostile scope

- The theorem does not say hypertranscendence causes ordinary dynamical noncompactness.
- It does not distinguish DA from HT using an infinite jet; the full-jet fibre can still contain
  nonanalytic pathologies because the ambient carrier is all functions.
- It does not choose a physical cost, positivity structure, recurrence clock, or arithmetic source.
- It proves an exact analytic realization boundary, not a complete universal-law field equation.

## Lean certificate

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveFiniteJetBoundary`.

Closed declarations:

- `constitutiveFiniteJet_noContinuousBoolClassifier`;
- `constitutiveFiniteJet_realizationBoundary_law`.

The module imports the dependency-closed analytic construction in
`HTGeometry.FiniteJetIndistinguishability`, adds no project axioms or premises, and is wired into
the `HTGeometry.UniversalLawField` umbrella. Targeted foreground build:

```text
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFiniteJetBoundary
Build completed successfully (8876 jobs).
```

`#print axioms` reports only Lean/mathlib foundations `propext`, `Classical.choice`, and
`Quot.sound`; no project postulate occurs.

## Log

- 2026-08-09 — exact finite-jet double realization and topological nonseparation selected as first
  analytic Realization Boundary Dynamics theorem.
- 2026-08-09 — closed in Lean and promoted to Stage 3.
