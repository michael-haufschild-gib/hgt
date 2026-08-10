# Three-stage downstream-kernel obstruction filtration and exact-tower law

- **ID:** ULF-DKO-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** In a three-stage history, total law birth has a canonical filtration whose layers
  are local failures modulo the kernels of their entire future tails.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [DOWNSTREAM-KERNEL FILTRATION] [EXACT TOWER] [LEAN-CERTIFIED] [AXIOM-AUDITED]
  [UMBRELLA-BUILT] [NOT RH]

## 1. Setup

Let

\[
D\xrightarrow{R}E\xrightarrow{S}K\xrightarrow{T}A
\tag{DKO.1}
\]

be linear maps over a field. Put

\[
C_0=A/\operatorname{im}(TSR),\qquad
C_1=A/\operatorname{im}(TS),\qquad
C_2=A/\operatorname{im}T.
\tag{DKO.2}
\]

The range inclusions induce surjections

\[
C_0\xrightarrow{q_1}C_1\xrightarrow{q_2}C_2.
\tag{DKO.3}
\]

Define the first and second survival filtrations

\[
F_1=\ker q_1,
\qquad
F_2=\ker(q_2q_1).
\tag{DKO.4}
\]

## 2. Exact filtration theorem

### Theorem 2.1

There is a canonical filtration

\[
0\subseteq F_1\subseteq F_2\subseteq C_0
\tag{DKO.5}
\]

with identifications

\[
\boxed{F_1\cong E/(\operatorname{im}R+\ker(TS)),}
\tag{DKO.6}
\]

\[
\boxed{F_2/F_1\cong K/(\operatorname{im}S+\ker T),}
\tag{DKO.7}
\]

and

\[
\boxed{C_0/F_2\cong A/\operatorname{im}T.}
\tag{DKO.8}
\]

Equivalently, restriction of `q₁` gives a canonical short exact sequence

\[
0\longrightarrow F_1\longrightarrow F_2
 \xrightarrow{q_1}\ker q_2\longrightarrow0,
\tag{DKO.9}
\]

while ULF-PSB-1 identifies `F₁` with (DKO.6) and `ker q₂` with (DKO.7).

### Proof

If `x` lies in `F₁`, then `q₁x=0`, hence `q₂q₁x=0`; therefore `F₁⊆F₂`.

Restrict `q₁` to `F₂`. Its image lies in `ker q₂` by definition. It is surjective: for
`y∈ker q₂`, surjectivity of `q₁:C₀→C₁` supplies `x` with `q₁x=y`, and then
`q₂q₁x=q₂y=0`, so `x∈F₂`. Its kernel is exactly `F₁`. This proves (DKO.9).

Apply ULF-PSB-1 first to `R` followed by the future tail `TS`. It identifies

\[
\ker q_1\cong E/(\operatorname{im}R+\ker(TS)).
\]

Apply it again to `S` followed by `T`. It identifies

\[
\ker q_2\cong K/(\operatorname{im}S+\ker T).
\]

The first isomorphism theorem applied to (DKO.9) gives (DKO.7). Finally, `q₂q₁` is surjective and
has kernel `F₂`, giving (DKO.8). \(\square\)

## 3. Mechanism laws

### Law A -- prospective survival

A failure born in `E` is not graded by `coker R` alone. It is graded by

\[
E/(\operatorname{im}R+\ker(TS)).
\tag{DKO.10}
\]

The kernel of the entire future tail is exact downstream erasure freedom.

### Law B -- survival depth

The filtration index records the first stage at which a defect can no longer be erased by future
maps. The total cokernel records existence of final failure; the filtration records its history.

### Law C -- extension, not direct sum

The theorem produces short exact sequences, not canonical splittings. Interactions between grades
are extension data. Replacing the filtration by a list of dimensions destroys this information.

### Law D -- completion can insert homology

ULF-CHM-1 shows that closure can break exactness between adjacent grades in two independent ways.
Thus the algebraic filtration is the zero-homology chamber of a larger completion-relative
obstruction spectrum.

## 4. Why this is a higher pivot

The theorem asks neither for a preferred geometric object nor for an RH source-native annihilator.
It gives a law of histories:

> local failure is measured relative to both past attainment and future erasure.

The two-stage primary/secondary theorem is the first truncation. Three stages reveal filtration and
extension data; this cannot be represented faithfully by one scalar curvature.

## 5. Scope

This theorem does not yet prove:

- the general finite-history formula;
- invariance under refactorization;
- a canonical splitting of the filtration;
- closure-doctrine differentials between grades;
- nonlinear or torsorial analogues;
- any RH endpoint.

## 6. Lean certificate

Module `HTGeometry.ConstitutiveObstructionFiltration` certifies the two transitions, nested kernels,
filtration inclusion, restricted middle-layer map, its surjectivity, exactness at the middle,
identification of both local layers with the ULF-PSB-1 carrier sectors, and the unconditional
three-stage capstone.

Direct foreground elaboration and the final Universal Law Field umbrella audit pass. The build
completed with `11,547` jobs. Source-level axiom prints on all headline declarations report only
`propext`, `Classical.choice`, and `Quot.sound`.
