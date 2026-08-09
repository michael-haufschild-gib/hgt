# Proper-face matching map, four phases, and total-law defect law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [HIGHER SYNTHESIS]
  [CONTEXTUALITY + INTERACTION] [COORDINATE-FREE MATCHING MAP]
  [CANDIDATE UNIVERSAL PRIMITIVE] [NOT RH] [NO LEAN]

## 1. Setup

Let \(\mathcal S\) be the infinity-category of spaces. Fix a finite observer set
\(I=\{1,\ldots,n\}\). A **polyscopic law diagram** is a contravariant functor

\[
 X:\mathcal P(I)^{\mathrm{op}}\longrightarrow\mathcal S,
\tag{MM.1}
\]

where \(X_I\) is the total law object and \(X_S\) is its shadow on observer face \(S\).

Define the proper-face matching object

\[
 M_{\partial I}(X)
 :=
 \lim_{S\in\mathcal P_{<I}(I)^{\mathrm{op}}}X_S.
\tag{MM.2}
\]

Restriction from the total law gives the canonical matching map

\[
 \mu_X:X_I\longrightarrow M_{\partial I}(X).
\tag{MM.3}
\]

For a compatible proper-face datum \(m:*\to M_{\partial I}(X)\), define its realization space

\[
 \mathcal R_m(X)
 :=
 X_I\times_{M_{\partial I}(X)}*.
\tag{MM.4}
\]

No observer metric, curvature, positivity, or dynamics is used in these definitions.

## 2. Universal matching theorem

### Theorem 2.1 — realizability and ambiguity are fibres of one map

For every compatible face datum \(m\):

1. \(m\) is globally realizable if and only if \(\mathcal R_m(X)\) is nonempty;
2. realizations of \(m\), including their higher equivalences, form exactly
   \(\mathcal R_m(X)\);
3. \(m\) has a unique realization up to contractible choice if and only if
   \(\mathcal R_m(X)\) is contractible.

Consequently:

\[
 \boxed{
 \mu_X\text{ is an equivalence}
 \Longleftrightarrow
 \text{every compatible proper-face law has a contractibly unique total law}.}
\tag{MM.5}
\]

### Theorem 2.2 — four polyscopic phases

The matching map has four logically distinct phases.

1. **Reconstructible phase:** \(\mu_X\) is an equivalence.
2. **Contextual phase:** \(\mu_X\) is \((-1)\)-truncated but not
   \((-1)\)-connected. Some compatible face data have no realization, while realized data have at
   most one up to contractible choice.
3. **Interaction phase:** \(\mu_X\) is \((-1)\)-connected but not
   \((-1)\)-truncated. Every compatible face datum is realizable, but some have a
   noncontractible realization space.
4. **Mixed phase:** \(\mu_X\) is neither. Unrealizable face data and hidden total-law
   multiplicity coexist.

These phases are invariant under objectwise equivalence of polyscopic diagrams.

### Corollary 2.3 — linear kernel/cokernel shadow

In a separate linear coefficient chart, let
\(X:\mathcal P(I)^{\mathrm{op}}\to\mathcal D\) take values in a stable infinity-category
\(\mathcal D\) with finite limits. There is an exact triangle

\[
 K_X\longrightarrow X_I
 \xrightarrow{\mu_X}M_{\partial I}(X)
 \longrightarrow K_X[1],
\tag{MM.6}
\]

where

\[
 K_X=\operatorname{fib}(\mu_X).
\]

In an ordinary finite-dimensional linear chart:

- \(\ker\mu_X\) is hidden irreducible interaction invisible on every proper face;
- \(\operatorname{coker}\mu_X\) is the space of compatible-looking face data not produced by a
  total law.

Thus contextual obstruction and hidden interaction are the cokernel and kernel shadows of one
matching geometry.

### Corollary 2.4 — higher interaction spectrum

The homotopy groups

\[
 \pi_j\mathcal R_m(X),\qquad j\geq0,
\tag{MM.7}
\]

measure successively higher ambiguity of total laws with identical proper faces. Empty realization
spaces measure effectivity failure. Hence one matching map supports both a contextual obstruction
hierarchy and a higher-interaction hierarchy.

## 3. Proof

Equation (MM.4) is the homotopy fibre of \(\mu_X\) over \(m\). Statements 1--3 of Theorem 2.1 are
the defining universal property of a homotopy fibre. A map of spaces is an equivalence exactly
when every homotopy fibre is contractible, proving (MM.5).

A map is \((-1)\)-truncated exactly when every fibre is empty or contractible. It is
\((-1)\)-connected exactly when every fibre is nonempty. The four possible truth values of these
two independent properties give Theorem 2.2. Objectwise equivalence preserves limits, matching
maps up to equivalence, and their fibres.

In a stable infinity-category, every fibre sequence extends canonically to an exact triangle,
giving (MM.6). Passing to an abelian heart gives the ordinary kernel and cokernel interpretation.
Equation (MM.7) is the homotopy of the realization fibre.

## 4. Two exact native realizations

### 4.1 Contextual realization

For a connected odd-charge parity context system, take the standard measurement-event presheaf
on its context cover and form the associated Cech face diagram. Then
\(M_{\partial I}(X)\) is the space of compatible local parity laws and \(X_I\) is the space of
global deterministic assignments. The matching object is nonempty, but the odd-charge component
has empty realization fibre.

This is the contextual phase.

### 4.2 Irreducible-interaction realization

For the \(n\)-color minimal \(L_\infty\) law with only
\(\ell_n(x_1,\ldots,x_n)=z\), every proper face is the zero law. Let the total-law parameter be
\(\lambda\in k\) multiplying \(\ell_n\). Then

\[
 X_I\simeq k,\qquad M_{\partial I}(X)\simeq *,
\]

so the matching fibre is \(k\). All proper faces coincide while total interaction varies.

This is the interaction phase.

## 5. New field interpretation

The primitive is not “curvature” and not “contextuality.” It is the total-to-boundary matching map
(MM.3).

- Empty fibres: compatible observer shadows with no total law.
- Noncontractible fibres: multiple total laws with identical shadows.
- Higher fibre homotopy: equivalences and coherences among hidden laws.
- A tower of observer sets or jet orders: changing matching geometry across scale.

This suggests a field of **polyscopic law geometry**: the topology and homotopy theory of law
realization relative to all observer faces.

NHG becomes one differential-geometric chart on a realization fibre. Contextuality describes empty
fibres. Operadic law genesis describes nontrivial fibres. Neither is universal alone.

## 6. Predictions

1. Any scalar “total obstruction” conflates empty and noncontractible fibres and is incomplete.
2. A proof that all proper observer faces are consistent says nothing about total realizability or
   uniqueness.
3. Genuine source selection must either choose a point in a noncontractible realization fibre or
   change the component of the matching object so that an empty fibre becomes inhabited.
4. Hypertranscendental behaviour should appear as nonstabilization of a tower of matching maps,
   not necessarily as curvature or contextuality at one finite stage.
5. Positive states may extend over matching data even when deterministic realization fibres are
   empty.
6. Recurrent observer history is a loop in a matching object; open lifted history is its
   nontrivial monodromy action on the realization fibre.

## 7. Fatal boundaries

1. The observer diagram must be source-defined. Choosing faces after seeing the desired defect is
   theatre.
2. Matching geometry alone supplies no preferred topology, positivity, dynamics, or cost.
3. A full field must define admissible changes of observer set and prove invariance under
   cofinal/refinement equivalence.
4. If decisive proof systems cannot be organized into compatible face diagrams, polyscopic law
   geometry fails as a universal ontology.
5. The theorem is general descent machinery. Field significance depends on new constitutive
   theorems linking matching towers to source-generated mathematics.
6. Space-valued matching fibres retain homotopy type but not automatically simple-homotopy
   torsion, determinant history, or quantitative filling cost. The exact no-go is proved in
   derived-homotopy-endpoint-insufficiency-for-torsion-and-filling-cost-law.md.
