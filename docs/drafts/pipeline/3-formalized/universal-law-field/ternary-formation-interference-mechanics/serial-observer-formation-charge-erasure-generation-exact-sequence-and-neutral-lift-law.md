# Serial observer formation charge, erasure--generation exact sequence, and neutral-lift law

- **ID:** ULF-TFIM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SERIAL COMPOSITION LAW
- **Parent:** `symmetric-formation-homology-observer-overlap-recovery-duality-and-fisher-nullity-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FIVE-TERM EXACT SEQUENCE]`
  `[ERASURE--GENERATION CONSERVATION] [INFORMATION-NEUTRAL LIFT CLASSIFICATION]`
  `[SERIAL TELESCOPING] [DUAL REPORTER SEQUENCE] [NOT RH]`
  `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
- **Statement:** Under serial linear observation, composite formation interference is upstream
  interference minus the part killed by the new recovery kernel plus interference newly created by
  the downstream observer.  A canonical five-term exact sequence proves the law and classifies
  precisely when a lift is information-neutral.

## 1. Setup

Let `k` be a field, let `A,B subset V` be vector subspaces, and let

\[
 V\xrightarrow{L}Y\xrightarrow{M}Z
 \tag{SOF.1}
\]

be linear maps.  For a map `T` and subspaces `P,Q` of its domain, define the observer-created
formation overlap

\[
 \mathsf O_T(P,Q)
 :=\frac{T(P)\cap T(Q)}{T(P\cap Q)}.
 \tag{SOF.2}
\]

By ULF-TFIM-1,

\[
 \mathsf O_T(P,Q)
 \simeq\mathsf H(\ker T,P,Q),
 \tag{SOF.3}
\]

so this quotient is intrinsic formation homology in a kernel chart.

Put

\[
 S_0=L(A\cap B),
 \qquad S_1=L(A)\cap L(B),
 \qquad K=\ker M.
 \tag{SOF.4}
\]

Then `S_0 subset S_1`.  Define the upstream charge erased by the second observer:

\[
 \mathsf E_M(L;A,B)
 :=\frac{K\cap S_1}{K\cap S_0}.
 \tag{SOF.5}
\]

This is well typed because `K cap S_0 subset K cap S_1`.

## 2. Five-term exact composition theorem

### Theorem 2.1 -- serial observer formation sequence

There is a canonical exact sequence

\[
 \boxed{
 0\longrightarrow \mathsf E_M(L;A,B)
 \xrightarrow{\iota}
 \mathsf O_L(A,B)
 \xrightarrow{M_*}
 \mathsf O_{M\circ L}(A,B)
 \xrightarrow{\pi}
 \mathsf O_M(L(A),L(B))
 \longrightarrow0.}
 \tag{SOF.6}
\]

The maps are

\[
 \begin{aligned}
 \iota([x])&=[x],\\
 M_*([y])&=[M y],\\
 \pi([z])&=[z],
 \end{aligned}
 \tag{SOF.7}
\]

where the last map is the quotient induced by

\[
 M(S_0)\subset M(S_1)\subset M(L(A))\cap M(L(B)).
 \tag{SOF.8}
\]

### Proof

Write

\[
 T_0=M(S_0),
 \qquad T_1=M(S_1),
 \qquad T_2=M(L(A))\cap M(L(B)).
 \tag{SOF.9}
\]

Then

\[
 \mathsf O_L(A,B)=S_1/S_0,
 \quad
 \mathsf O_{ML}(A,B)=T_2/T_0,
 \quad
 \mathsf O_M(L(A),L(B))=T_2/T_1.
 \tag{SOF.10}
\]

The map `M_*:S_1/S_0 -> T_2/T_0` is well defined because `M(S_0)=T_0`.  Its kernel consists
of classes `[y]` for which `M y in M(S_0)`.  Thus there is `y_0 in S_0` with
`y-y_0 in K`, so

\[
 \ker M_*
 =\frac{S_0+(K\cap S_1)}{S_0}
 \simeq\frac{K\cap S_1}{K\cap S_0}
 =\mathsf E_M(L;A,B).
 \tag{SOF.11}
\]

This proves exactness at the first two nonzero terms.

The image of `M_*` is `T_1/T_0`.  The natural quotient

\[
 T_2/T_0\longrightarrow T_2/T_1
 \tag{SOF.12}
\]

is surjective and has kernel `T_1/T_0`.  This proves exactness at the remaining terms.  QED.

## 3. Erasure--generation conservation

Assume finite dimension and write

\[
 o_L=\dim\mathsf O_L(A,B),
 \quad
 o_{ML}=\dim\mathsf O_{ML}(A,B),
 \quad
 o_M=\dim\mathsf O_M(L(A),L(B)),
 \quad
 e_M=\dim\mathsf E_M(L;A,B).
 \tag{SOF.13}
\]

### Corollary 3.1 -- exact charge budget

Taking alternating dimensions in `(SOF.6)` gives

\[
 \boxed{o_{ML}=o_L-e_M+o_M.}
 \tag{SOF.14}
\]

The three terms have distinct meanings:

1. `o_L` is charge already created upstream;
2. `e_M` is upstream charge erased by the new kernel;
3. `o_M` is charge newly created when `M` observes the two upstream images.

The composite defect is not monotone under arbitrary postprocessing because erasure and generation
are independent.  Formula `(SOF.14)` is the exact replacement for a false monotonicity law.

### Corollary 3.2 -- rank-slack chain law

For `r_T(P)=dim T(P)`, ULF-TFIM-1 identifies each `o_T` with the submodularity slack

\[
 \partial_T(P,Q)=r_T(P)+r_T(Q)-r_T(P+Q)-r_T(P\cap Q).
 \tag{SOF.15}
\]

Therefore

\[
 \boxed{
 \partial_{ML}(A,B)
 =\partial_L(A,B)-e_M+partial_M(L(A),L(B)).}
 \tag{SOF.16}
\]

This is a chain rule for failure of observer rank to be modular.

## 4. Exact information-neutrality classification

### Theorem 4.1 -- neutral lift criterion

The induced map

\[
 M_*:\mathsf O_L(A,B)\longrightarrow\mathsf O_{ML}(A,B)
 \tag{SOF.17}
\]

is an isomorphism if and only if both conditions hold:

\[
 \boxed{
 \begin{aligned}
 K\cap S_1&=K\cap S_0,
 \tag{SOF.18a}\\
 M(L(A))\cap M(L(B))&=M(S_1).
 \tag{SOF.18b}
 \end{aligned}}
\]

Condition `(SOF.18a)` says no upstream charge is erased.  Condition `(SOF.18b)` says no new
downstream charge is created.  Together they are necessary and sufficient; neither alone is.

### Proof

By `(SOF.11)`, `M_*` is injective exactly when `(SOF.18a)` holds.  By exactness of `(SOF.6)`, it
is surjective exactly when the final quotient

\[
 [M(L(A))\cap M(L(B))]/M(S_1)
\]

vanishes, which is `(SOF.18b)`.  QED.

### Corollary 4.2 -- invertible and faithful lifts are neutral

If `M` is injective on `L(A)+L(B)`, then both conditions in `(SOF.18)` hold and

\[
 \boxed{\mathsf O_L(A,B)\simeq\mathsf O_{ML}(A,B).}
 \tag{SOF.19}
\]

Indeed, injectivity prevents erasure, and an injective linear map preserves intersections of
subspaces.  In particular every invertible functional-equation action transports formation charge
information-neutrally.  It may permute or reverse representatives, but it cannot select zero.

### Corollary 4.3 -- composite exactness classification

The composite charge vanishes exactly when

\[
 \boxed{
 \mathsf O_M(L(A),L(B))=0
 \quad\text{and}\quad
 \mathsf E_M(L;A,B)=\mathsf O_L(A,B).}
 \tag{SOF.20}
\]

The second equality means that every upstream class is erased.  Thus an exact composite does not
imply an exact upstream observer: postprocessing can hide all prior interference.  Conversely,
downstream creation must vanish as well.

## 5. Dual reporter sequence

Assume finite dimension.  Dualizing `(SOF.6)` is exact and reverses arrows.

### Theorem 5.1 -- reporter migration conservation

There is a canonical exact sequence

\[
 \boxed{
 0\longrightarrow
 \mathsf O_M(L(A),L(B))^*
 \longrightarrow
 \mathsf O_{ML}(A,B)^*
 \longrightarrow
 \mathsf O_L(A,B)^*
 \longrightarrow
 \mathsf E_M(L;A,B)^*
 \longrightarrow0.}
 \tag{SOF.21}
\]

The first term consists of reporters born downstream.  The middle restriction maps composite
reporters to upstream reporters.  The final quotient records upstream reporters that cannot
survive the downstream kernel.  This is dual to the charge budget, not an additional premise.

### Proof

Finite-dimensional linear duality is exact.  Apply it to `(SOF.6)`.  QED.

## 6. Positive and Fisher consequences

Choose inner products on the finite-dimensional charge spaces.  Every exact sequence splits
orthogonally after a choice, though no splitting is canonical.  Hence the canonical associated
graded dimension law is

\[
 \operatorname{rank}P_{ML}
 =\operatorname{rank}P_L-operatorname{rank}P_E+operatorname{rank}P_M,
 \tag{SOF.22}
\]

where each `P` is the harmonic projection from ULF-TFIM-1.

For Gaussian location observations, those ranks are precisely submodularity slacks of Fisher
information.  Thus serial data processing can:

1. preserve nonidentifiability exactly;
2. erase an upstream nonidentifiability direction;
3. create a new common-image nonidentifiability direction;
4. do both in one stage, with net result governed by `(SOF.14)`.

No scalar data-processing inequality separates these four cases; the exact sequence does.

## 7. Sharp countermodels

Work over `R` or `C`.

### 7.1 Neutral transport

Let

\[
 V=k^2,
 \quad A=k(e_1+e_2),
 \quad B=k e_2,
 \quad L(x,y)=y,
 \quad M=\operatorname{id}_k.
 \tag{SOF.23}
\]

Then `O_L(A,B)=k`, `E_M=0`, `O_M=0`, and `O_{ML}=k`.  The charge survives exactly.

### 7.2 Pure erasure

Use the same `A,B,L` but let `M:k -> 0` be zero.  Then

\[
 o_L=1,
 \qquad e_M=1,
 \qquad o_M=0,
 \qquad o_{ML}=0.
 \tag{SOF.24}
\]

The composite looks exact only because every upstream class was destroyed.

### 7.3 Pure downstream generation

Let `L=id_V`, keep the same distinct lines `A,B`, and let `M(x,y)=y`.  Then

\[
 o_L=0,
 \qquad e_M=0,
 \qquad o_M=1,
 \qquad o_{ML}=1.
 \tag{SOF.25}
\]

An exact upstream formation can become nonexact after the second observation.

These three models prove that preservation, erasure, and generation are logically independent.

## 8. Arbitrary serial chains

Consider observers

\[
 V_0\xrightarrow{L_1}V_1\xrightarrow{L_2}\cdots
 \xrightarrow{L_N}V_N
 \tag{SOF.26}
\]

and fixed source subspaces `A,B subset V_0`.  Let `A_j,B_j` be their images after the first `j`
maps.  Put

\[
 q_j=\dim\mathsf O_{L_j\cdots L_1}(A,B),
 \tag{SOF.27}
\]

and let `e_j` and `g_j` be, respectively, the erased upstream charge and newly generated charge at
stage `L_{j+1}`.

### Theorem 8.1 -- serial telescoping conservation

For every `N`,

\[
 \boxed{
 q_N=q_1+\sum_{j=1}^{N-1}(g_j-e_j).}
 \tag{SOF.28}
\]

### Proof

Apply `(SOF.14)` at each stage:

\[
 q_{j+1}=q_j-e_j+g_j.
\]

Sum and cancel the intermediate charges.  QED.

### Corollary 8.2 -- neutral towers cannot select

If every stage satisfies the neutral conditions `(SOF.18)`, then

\[
 q_N=q_1
 \tag{SOF.29}
\]

for all `N`.  A tower of functional-equation isomorphisms, unitary gauges, exact recovery lifts,
or faithful coordinate changes cannot turn nonzero formation charge into zero.  Selection requires
either a genuine erasure mechanism, a source exactness law preventing birth, or the global
properness exclusion of ULF-TFIM-1.

## 9. Relation to existing corpus laws

1. **Positive false-overlap composition.** That law gives an additive nonnegative decomposition
   for pushed-forward profiles.  Linear formation charge can also be erased, so the correct law is
   the signed budget `old - erased + new`, categorified by `(SOF.6)`.
2. **Completion kernel-pair transversality.** That theorem says downstream processing cannot
   recover distinctions already lost.  The present theorem refines it for formation interference:
   a downstream stage can create a different charge even while erasing the old one.
3. **Functional-equation packet lift.** That lift is information-neutral because it is invertible
   on the relevant formed packet.  Corollary 4.2 explains this as one chamber of a general
   classification rather than a packet-specific accident.
4. **Formation holonomy and Bianchi laws.** Those compare affine histories around squares.  Here
   no loop or connection is needed; serial nonexactness is governed by a five-term sequence.
5. **Linear-family supermodularity.** ULF-TFIM-1 identifies one-stage slack with formation
   homology.  Formula `(SOF.16)` is its serial chain rule.

## 10. Literature boundary and hostile status

The proof uses classical quotient exact sequences, the first isomorphism theorem, and exactness of
finite-dimensional duality.  General exact and half-exact functor machinery is established; see,
for example, Prest, [*Modules as exact functors*](https://arxiv.org/abs/1801.08015).  Multiview
identifiability via subspace intersections is also classical; see
Sorensen--Kanatsoulis--Sidiropoulos,
[*Generalized Canonical Correlation Analysis: A Subspace Intersection Approach*](https://arxiv.org/abs/2003.11205).

The honest status is `[BRIDGE] [NEW-TO-CORPUS EXACT SEQUENCE] [NOVELTY UNVERIFIED]`.  The field
advance is the interpretation and coupling:

\[
 \text{formation homology}
 \longleftrightarrow
 \text{serial observer erasure/generation}
 \longleftrightarrow
 \text{reporter migration}
 \longleftrightarrow
 \text{Fisher rank slack}.
\]

### Anti-theatre tests

1. Removing every interpretation leaves the nontrivial exact sequence `(SOF.6)`.
2. The three countermodels prove its four terms cannot be collapsed to one monotone scalar law.
3. Invertibility gives a theorem, not a metaphor: exact neutral transport `(SOF.19)`.
4. Composite zero is fully classified and does not get misread as source exactness.
5. Serial composition gives the falsifiable telescoping identity `(SOF.28)`.

## 11. RH pressure test

This theorem still does not prove RH.  It blocks a large class of false final steps:

- if every remaining comparison in a proposed proof is invertible, unitary, or faithful, its
  formation charge is conserved and cannot be selected away;
- if a final quotient makes the observed defect vanish, one must prove whether it erased the old
  charge or whether the charge was absent at source;
- any claimed global cancellation must satisfy the exact ledger `(SOF.28)`.

The live final gate is now typed: construct one literal arithmetic stage with either

1. source exactness preventing the relevant formation class;
2. controlled erasure whose dual reporter anomaly is independently accounted for; or
3. noncontracting persistence plus finite-action properness, forcing zero by ULF-TFIM-1.

## 12. Lean status

Fully Lean-certified in `GaloisForLFunctions.HTGeometry.SerialObserverFormationCharge`; see the
`-formalized.md` companion for the statement-by-statement map.

## Gates

- [x] 0 -> 1: exact serial question and independent erasure/generation falsifiers
- [x] 1 -> 2: five-term proof, duality, neutral classification, countermodels, and telescoping law
- [x] 2 -> 3: Lean formalization of quotient sequence and finite-rank corollaries
- [ ] 3 -> 4: literal arithmetic serial-observer realization and specialist priority review

## Log

- 2026-08-14 -- derived from the observer-created-overlap theorem; exact composition sequence,
  erasure--generation conservation, neutral lift classification, dual reporter migration, and
  arbitrary-chain telescoping closed on paper.
