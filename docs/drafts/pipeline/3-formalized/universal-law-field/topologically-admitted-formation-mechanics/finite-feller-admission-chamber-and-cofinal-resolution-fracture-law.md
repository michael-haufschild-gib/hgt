# Finite Feller admission chamber and cofinal resolution fracture law

- **ID:** ULF-TAFM-4
- **Stage:** `3-formalized`
- **Status:** `[FORMALIZED]`; `[NO PROJECT AXIOMS]`; `[NOVELTY UNVERIFIED]`
- **Lane:** topologically admitted formation mechanics
- **Claim:** finite Feller images of a mutually singular full-support binary source experiment are
  exactly pairs of finite probability laws with equal support
- **Parents:** ULF-TAFM-2, ULF-TAFM-3, Blackwell comparison, Feller kernels, finite-dimensional
  convexity
- **Lean:** exact finite-image classification, tensor-power admission, Neyman--Pearson/Hellinger
  escape, Lipschitz blow-up, and source-homeomorphism covariance are certified in
  `HTGeometry.TopologicallyAdmittedFellerAdmission` and
  `HTGeometry.TopologicallyAdmittedFellerTensorFracture`

## 1. Mathematical delta

The earlier hostile countermodel showed that one Bernoulli product source has exact Feller
formations at every finite depth. That example leaves open whether all-depth Feller admission is a
special coordinate accident.

It is not.

Let two mutually singular probability laws live on the same compact topology and both charge every
nonempty open set. Then every finite target experiment whose two laws have the same support is an
exact Feller image. Conversely, full support forces every finite Feller image to have equal target
supports. Thus the finite admission geometry has an exact description:

\[
 \boxed{
 \mathfrak A_Y(\mu_0,\mu_1)
 =\{(p_0,p_1)\in\Delta(Y)^2:
       \operatorname{supp}p_0=\operatorname{supp}p_1\}.}
 \tag{FAC.1}
\]

Every common-support tensor power remains in this chamber. If the target laws are distinct, their
decision effects nevertheless escape every compact uniform gauge as depth grows. Finite admission
and cofinal properness are therefore different laws.

## 2. Setup

Let \(X\) be a nonempty compact metric space. Let \(\mu_0,\mu_1\) be Borel probability
measures such that

\[
 \mu_0\perp\mu_1,
 \qquad
 \operatorname{supp}\mu_0=\operatorname{supp}\mu_1=X.
 \tag{FAC.2}
\]

Let \(Y\) be a nonempty finite set and let

\[
 \Delta(Y)=\left\{p:Y\to[0,1]:\sum_{y\in Y}p(y)=1\right\}.
\]

A finite-output Feller kernel is equivalently a continuous map

\[
 k:X\longrightarrow\Delta(Y).
\]

Its pushforward of \(\mu_i\) is the probability mass

\[
 (k_*\mu_i)(y)=\int_X k_y(x)\,d\mu_i(x),
 \qquad k_y(x)=k(x)(y).
 \tag{FAC.3}
\]

Define the finite Feller admission set

\[
 \mathfrak A_Y(\mu_0,\mu_1)
 =\{(k_*\mu_0,k_*\mu_1):k\in C(X,\Delta(Y))\}.
 \tag{FAC.4}
\]

For nonempty \(S\subseteq Y\), write \(\Delta_S(Y)\) for the face consisting of laws supported
in \(S\), and \(\operatorname{ri}\Delta_S(Y)\) for its relative interior, namely the laws whose
support is exactly \(S\).

## 3. Two elementary convex lemmas

### Lemma 3.1 -- dense convex subsets contain the relative interior

Let \(P\) be a nonempty finite-dimensional compact convex set and let \(C\subseteq P\) be convex
with \(\overline C=P\). Then

\[
 \operatorname{ri}P\subseteq C.
 \tag{FAC.5}
\]

#### Proof

Work in the affine hull of \(P\), of dimension \(m\). The case \(m=0\) is immediate. Fix
\(x\in\operatorname{ri}P\). A sufficiently small relative ball about \(x\) lies in \(P\). Inside
that ball choose an \(m\)-simplex with vertices \(z_0,\ldots,z_m\) and with \(x\) in its strict
interior.

For an affinely independent vertex tuple, the barycentric coordinates of a fixed point depend
continuously on the vertices. All barycentric coordinates of \(x\) relative to the \(z_j\) are
strictly positive. Hence there are neighbourhoods \(U_j\) of \(z_j\) such that every choice
\(c_j\in U_j\) remains affinely independent and has \(x\) in the convex hull of the \(c_j\).
Density supplies \(c_j\in C\cap U_j\). Convexity then gives
\(x\in\operatorname{conv}\{c_0,\ldots,c_m\}\subseteq C\). QED.

### Lemma 3.2 -- the admission set is convex and dense in the full product simplex

Under `(FAC.2)`,

\[
 \overline{\mathfrak A_Y(\mu_0,\mu_1)}=\Delta(Y)^2.
 \tag{FAC.6}
\]

Moreover, \(\mathfrak A_Y(\mu_0,\mu_1)\) is convex.

#### Proof

Convexity is pointwise mixing: if kernels \(k,\ell\) produce two admitted pairs, then
\(tk+(1-t)\ell\) is a continuous simplex-valued kernel producing their convex combination.

For density, choose a measurable singular separator \(E\subseteq X\) with

\[
 \mu_0(E)=1,
 \qquad
 \mu_1(E)=0.
\]

Fix arbitrary \(q_0,q_1\in\Delta(Y)\) and \(\varepsilon>0\). Inner regularity gives disjoint
compact sets

\[
 F_0\subseteq E,
 \qquad
 F_1\subseteq E^c,
 \qquad
 \mu_0(F_0)>1-\varepsilon,
 \qquad
 \mu_1(F_1)>1-\varepsilon.
\]

Urysohn's lemma supplies \(u\in C(X,[0,1])\) with \(u=1\) on \(F_0\) and \(u=0\) on
\(F_1\). Define

\[
 k(x)=u(x)q_0+(1-u(x))q_1.
 \tag{FAC.7}
\]

This is a continuous \(\Delta(Y)\)-valued kernel. Put \(a_i=\int u\,d\mu_i\). Then

\[
 a_0>1-\varepsilon,
 \qquad
 a_1<\varepsilon,
\]

and

\[
 k_*\mu_i=a_iq_0+(1-a_i)q_1.
\]

Thus \(k_*\mu_0\to q_0\) and \(k_*\mu_1\to q_1\) as \(\varepsilon\downarrow0\).
Since \((q_0,q_1)\) was arbitrary, `(FAC.6)` follows. QED.

No atomlessness assumption is used. Singularity supplies approximate topological separation;
finite-dimensional convexity turns approximation of interior targets into exact realization.

## 4. Exact admission-chamber theorem

### Theorem 4.1 -- finite Feller image classification

Under `(FAC.2)`, for every nonempty finite \(Y\),

\[
 \boxed{
 \mathfrak A_Y(\mu_0,\mu_1)
 =\{(p_0,p_1)\in\Delta(Y)^2:
       \operatorname{supp}p_0=\operatorname{supp}p_1\}.}
 \tag{FAC.8}
\]

Equivalently,

\[
 \boxed{
 \mathfrak A_Y(\mu_0,\mu_1)
 =\bigcup_{\varnothing\ne S\subseteq Y}
   \operatorname{ri}\Delta_S(Y)\times
   \operatorname{ri}\Delta_S(Y).}
 \tag{FAC.9}
\]

#### Proof: necessity

Let \(k\in C(X,\Delta(Y))\) and put \(p_i=k_*\mu_i\). Fix \(y\in Y\). If \(p_0(y)=0\),
then the continuous nonnegative function \(k_y\) has zero \(\mu_0\)-integral. If it were positive
at some point, continuity would make it bounded below by a positive constant on a nonempty open
set. Full support of \(\mu_0\) would give a positive integral, a contradiction. Hence
\(k_y\equiv0\), so \(p_1(y)=0\). Interchanging the measures proves

\[
 p_0(y)=0\quad\Longleftrightarrow\quad p_1(y)=0.
\]

Therefore the target supports agree.

#### Proof: sufficiency

Suppose \(p_0,p_1\) have common nonempty support \(S\). Regard both as strictly positive laws on
\(S\). Lemma 3.2 applied with output set \(S\) says that the corresponding admission set is a
dense convex subset of \(\Delta(S)^2\). The pair \((p_0,p_1)\) lies in the relative interior of
that product simplex. Lemma 3.1 therefore supplies a continuous kernel

\[
 k_S:X\to\Delta(S)
\]

with \((k_S)_*\mu_i=p_i\). Extend it to \(Y\) by assigning zero to coordinates outside \(S\).
The resulting continuous kernel has the required pushforwards. QED.

### Corollary 4.2 -- geometry of the chamber

The admission chamber is convex and dense in \(\Delta(Y)^2\). If \(|Y|\ge2\), it is not closed:
it excludes every pair \((\delta_y,\delta_z)\) with \(y\ne z\), while full-support pairs can
converge to such a pair.

Its strata are the diagonal face products

\[
 \operatorname{ri}\Delta_S(Y)^2,
 \qquad \varnothing\ne S\subseteq Y,
 \tag{FAC.10}
\]

of relative dimension \(2(|S|-1)\). The missing strata are precisely asymmetric face pairs.

This is the exact topological fracture. Measurable singular separation admits the whole product
simplex; Feller admission removes only mismatched-support boundary faces, not the interior.

## 5. Universal finite-depth formation

Let \(p_0,p_1\in\Delta(Y)\) have common support. For every positive integer \(d\),

\[
 \operatorname{supp}(p_0^{\otimes d})
 =\operatorname{supp}(p_1^{\otimes d}).
\]

### Corollary 5.1 -- arbitrary-depth exact Feller admission

For every \(d\ge1\), there exists a Feller kernel

\[
 K_d:X\rightsquigarrow Y^d
\]

such that

\[
 (K_d)_*\mu_i=p_i^{\otimes d}
 \qquad(i=0,1).
 \tag{FAC.11}
\]

#### Proof

Apply Theorem 4.1 to the finite output set \(Y^d\). QED.

This statement does not assert that the kernels can be chosen projectively compatible, Lipschitz
with a common modulus, source-canonical, or arithmetic. It proves that no finite-depth Feller
existence obstruction can perform selection.

## 6. Cofinal resolution fracture

Assume now that \(p_0\ne p_1\) and their supports agree. Their Hellinger affinity

\[
 A=\sum_{y\in Y}\sqrt{p_0(y)p_1(y)}
\]

satisfies \(0<A<1\). For each admitted \(K_d\), choose a Neyman--Pearson event
\(B_d\subseteq Y^d\) and let

\[
 e_d(x)=K_d(x,B_d).
\]

Exact pushforward gives

\[
 \int e_d\,d(\mu_1-\mu_0)
 =\operatorname{TV}(p_0^{\otimes d},p_1^{\otimes d})
 \ge1-A^d.
 \tag{FAC.12}
\]

### Theorem 6.1 -- finite admission and uniform cofinal escape

Every finite depth is Feller-admitted, but the decision effects \((e_d)\) escape every
equicontinuous subset of \(C(X,[0,1])\). Equivalently, for every compatible metric \(\rho\) on
\(X\),

\[
 \boxed{\operatorname{Lip}_\rho(e_d)\longrightarrow+\infty.}
 \tag{FAC.13}
\]

#### Proof

If a subsequence were equicontinuous, boundedness and Arzela--Ascoli would give a uniformly
convergent further subsequence with continuous limit \(e\). Equation `(FAC.12)` would imply

\[
 \int e\,d\mu_1-\int e\,d\mu_0=1.
\]

Since \(0\le e\le1\), this forces \(e=1\) \(\mu_1\)-almost everywhere and \(e=0\)
\(\mu_0\)-almost everywhere. Continuity and full support force both \(e\equiv1\) and
\(e\equiv0\), impossible.

For a fixed compatible metric, bounded Lipschitz constants would make the effects equicontinuous.
More strongly, if `(FAC.13)` failed to tend to infinity, a bounded-Lipschitz subsequence would
contradict the first part. QED.

The theorem gives an exact two-level law:

\[
 \boxed{
 \text{every finite formation exists}
 \quad\text{but}\quad
 \text{no cofinal family remains uniformly admitted}.}
 \tag{FAC.14}
\]

## 7. Three-organ fusion and fourth-organ prediction

The theorem fuses three structurally different organs without identifying them:

1. **singular source organ:** measurable superselection makes the two source laws perfectly
   distinguishable;
2. **positive decision organ:** every finite target pair in one support face is an exact barycentric
   image;
3. **topological formation organ:** full support forbids only asymmetric target faces, while
   compact-uniform admission fails cofinally.

It predicts a theorem in the observer/recurrence organ:

> Every fixed finite observer can be realized exactly and continuously from an off-neutral
> full-support singular source, yet any cofinal observer family resolving tensor confidence must
> carry an open, non-equicontinuous lifted history.

This prediction is exactly Theorem 6.1, not an analogy.

For the Gamma-six occupancy source and the prime--Poisson torus source already identified in the
corpus, off-neutral singularity plus common full topological support therefore rules out every
selection attempt based only on failure of a finite continuous reporter. Any producer must constrain
coherence, modulus, provenance, or source-derived cost across the entire depth family.

## 8. Functional-equation action

Let \(\tau:X\to X\) be a homeomorphism and transport both source laws by \(\tau\). Precomposition
gives a bijection between continuous kernels before and after transport, preserving pushforwards.
Hence

\[
 \mathfrak A_Y(\tau_*\mu_0,\tau_*\mu_1)
 =\mathfrak A_Y(\mu_0,\mu_1).
 \tag{FAC.15}
\]

Permuting \(Y\) merely permutes the diagonal face strata. Functional-equation symmetry is
information-neutral and admission-neutral; it cannot remove the cofinal escape.

## 9. Hostile audit

### 9.1 Correctness attacks

1. **Could density fail to give exact realization?** Yes for arbitrary dense sets; no here because
   the admission image is convex and the target pair lies in a finite-dimensional relative interior.
   Lemma 3.1 is the exact missing step.
2. **Could a zero output coordinate occur for only one law?** No. Nonnegative continuity plus full
   support makes zero integral equivalent to the coordinate function being identically zero.
3. **Could common-support boundary pairs be missed?** No. Restricting to their common face makes
   them an interior pair, where Lemma 3.1 applies.
4. **Is atomlessness hidden?** No. The approximation uses regularity, singular compact cores, and
   Urysohn separation only.
5. **Does the theorem construct one coherent infinite-depth kernel?** No. It classifies each finite
   output exactly. Projective coherence is a separate, stronger problem.
6. **Does Feller admission bound resolution?** No. Theorem 6.1 proves the opposite.

### 9.2 Internal corpus boundary

- `[CORPUS]` `finiteFormationClone_exists_iff` in
  `formal/GaloisForLFunctions/HTGeometry/FormationCloneRigidityCompletion.lean` classifies exact
  cloning from one **finite** source packet: identical or pointwise-singular source laws. It does
  not classify continuous images of an infinite compact full-support singular experiment.
- `[LOCAL-RESEARCH]` ULF-TAFM-2 constructs arbitrary-depth measurable formation from a singular
  separator and proves uniform compactness escape, but not finite Feller existence.
- `[LOCAL-RESEARCH]` ULF-TAFM-3 gives one Bernoulli all-depth Feller countermodel. Theorem 4.1
  replaces that example by an exact universal finite-output classification.
- `scripts/formal_tools.py research` found Feller projectors, finite clone rigidity, simplex
  carriers, and singular-measure infrastructure, but no theorem with statement `(FAC.8)`.

### 9.3 External boundary

The proof uses occupied parent mathematics, not a claim of component novelty:

- vector-measure range and transition-probability purification:
  Dai--Feinberg, <https://arxiv.org/abs/1006.0371>;
- Lyapunov range convexity and subranges:
  Dai--Feinberg, <https://arxiv.org/abs/1102.2534>;
- Blackwell comparison on standard Borel information structures:
  Hogeboom-Burr--Yuksel, <https://arxiv.org/abs/2005.06673>;
- semi-uniform Feller preservation under integration:
  Feinberg--Kasyanov--Zgurovsky, <https://arxiv.org/abs/2107.02207>.

Those works study measurable vector ranges, purification, information ordering, or Feller
preservation. The exact equal-support classification `(FAC.8)` was not found in the audited primary
sources. Absence from this audit is not a priority claim.

### 9.4 Verdict

`[PAPER-PROVED]` as an exact bridge theorem and new corpus-level classification. Scientific novelty
remains unverified. Its significance does not depend on novelty: it kills the entire class of
finite-depth Feller nonexistence selectors and exposes the genuinely cofinal gate.

## 10. Exact RH consequence and remaining open core

This theorem is not RH. It changes the permissible architecture.

Any proposed RH producer that uses an off-neutral full-support singular source must now supply a
source theorem about a whole formation family, for example:

- a common modulus or compact effect hull;
- a source-generated resolution-action bound;
- projective coherence plus a proper graph-domain constraint;
- arithmetic provenance excluding the generic convex realization.

The first exact unresolved implication is:

`[OPEN CORE]` Construct the literal zero-independent arithmetic formation family and prove one
source-native cofinal admission bound that generic convex Feller realizations do not satisfy.

Finite Feller existence cannot be that bound.

## Gates

- [x] 0 -> 1: exact source-pure claim and explicit falsifiers
- [x] 1 -> 2: dependency-closed proof of `(FAC.8)` and `(FAC.13)`
- [x] 2 -> 3: all claims `(FAC.8)`--`(FAC.15)` formalized unconditionally
- [ ] 3 -> 4: publication and independent priority audit

## Log

- 2026-08-31 -- universalized the Bernoulli Feller countermodel: proved the exact diagonal-face
  admission chamber, all finite common-support tensor powers, and unavoidable cofinal uniform
  escape.
- 2026-08-31 -- Lean-certified `(FAC.8)` and the Arzelà--Ascoli/Lipschitz forms of `(FAC.13)`;
  no project axioms or computation certificates.
- 2026-08-31 -- Lean-certified common-support tensor powers, exact finite Neyman--Pearson effects,
  Hellinger-product contrast convergence, cofinal equicontinuity/Lipschitz fracture, and
  homeomorphic source-transport invariance; promoted complete card to Stage 3.
