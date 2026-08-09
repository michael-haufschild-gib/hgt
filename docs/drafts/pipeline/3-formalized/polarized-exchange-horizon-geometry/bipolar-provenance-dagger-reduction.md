# Bipolar provenance and dagger reduction

- **ID:** bipolar-provenance-dagger-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / DAGGER TOPOLOGY / POSITIVITY-PLACEMENT NO-GO
- **Scientific status:** [LEAN-FORMALIZED] [PAPER-PROVED] [DEPENDENCY-CLOSED] [NOT RH]
  [NEW CORPUS SYNTHESIS] [CLASSICAL LINEAR PARENTS]
- **Source:** ../../1-in-progress/polarized-exchange-horizon-geometry/
  polarized-exchange-horizon-geometry-program.md
- **Statement:** Dagger reverses a provenance flag and dualizes its spectral quotient, but is not
  continuous in one-sided provenance topology; its minimal bipolar refinement is dagger-stable,
  while positive-definite chain-level self-duality forbids every nonzero boundary.

## Goal

Explain why source Green--Stokes structure must be formed before positive Hilbert polarization.
The previous card identifies arithmetic, geometry, and spectrum with \(B\), \(Z\), and \(Z/B\).
This card adds analytic dagger. It proves two obstructions:

1. dagger has opposite topological variance from source provenance;
2. a positive chain-level self-dual flag cannot carry nonzero arithmetic boundaries.

The positive survivor is a two-stage architecture: indefinite or alternating Green--Stokes
duality on cochains, exact reduction by \(B\), then positive polarization on surviving quotient.

## 1. Algebraic dagger of an exactness flag

Let \(k=\mathbb R\) or \(\mathbb C\), and let \(V\) be finite-dimensional. For
\(A\subseteq V\), write

\[
 A^\circ=\{\phi\in V^\vee:\phi(A)=0\}.
\tag{1}
\]

Define

\[
 \mathbb D_V:\mathsf{ExFlag}(V)\longrightarrow\mathsf{ExFlag}(V^\vee),
 \qquad
 \mathbb D_V(B,Z)=(Z^\circ,B^\circ).
\tag{2}
\]

This is well-defined because \(B\subseteq Z\) implies \(Z^\circ\subseteq B^\circ\).

[PROVED HERE] [EXACTNESS_FLAG_DAGGER_DUALITY]

Under canonical \(V\cong V^{\vee\vee}\), map (2) is an involution. There is a canonical perfect
pairing

\[
 (Z/B)\times(B^\circ/Z^\circ)\longrightarrow k,
 \qquad
 ([z],[\phi])\longmapsto\phi(z),
\tag{3}
\]

and therefore a canonical isomorphism

\[
 (Z/B)^\vee\cong B^\circ/Z^\circ.
\tag{4}
\]

### Proof

Finite-dimensional double annihilator gives \((A^\circ)^\circ=A\), proving involutivity. Pairing
(3) is well-defined: changing \(z\) by \(b\in B\) does not change its value for
\(\phi\in B^\circ\), and changing \(\phi\) by an element of \(Z^\circ\) does not change its value
on \(z\in Z\). Restriction gives a surjection

\[
 B^\circ\longrightarrow(Z/B)^\vee.
\tag{5}
\]

Surjectivity follows by extending a linear functional from \(Z\) to \(V\). Kernel of (5) is
\(Z^\circ\). First isomorphism theorem proves (4), hence perfection of (3).

Thus analytic dual is not a second spectrum. It is the opposite exactness flag whose middle
homology is dual to the original spectral quotient.

## 2. One-sided topology is not dagger-continuous

Give \(\mathsf{ExFlag}(V)\) the provenance topology from
provenance-exactness-flag-topology.md: lower topology on \(B\), Scott topology on \(Z\).

[PROVED HERE] [PROVENANCE_DAGGER_DISCONTINUITY]

If \(k\) is infinite and \(\dim V\geq2\), map (2) is not continuous for provenance topologies.

### Proof

Choose nonzero \(\phi\in V^\vee\), let \(K=\ker\phi\), and consider target cycle-membership open

\[
 \mathcal O_\phi
 =\{(B',Z'):\phi\in Z'\}.
\tag{6}
\]

Its inverse image under (2) is

\[
 \mathbb D_V^{-1}(\mathcal O_\phi)
 =\{(B,Z):B\subseteq K\}.
\tag{7}
\]

Flag \((K,V)\) lies in (7). A basic provenance neighbourhood imposes finitely many conditions
\(v_i\notin B\) and finitely many conditions \(w_j\in Z\). Keep \(Z=V\). Since \(k\) is infinite,
choose a line \(L\) not contained in \(K\) and containing none of finitely many \(v_i\). Then
\((L,V)\) lies in that neighbourhood but not in (7). Hence (7) is not open.

This failure is structural. Source topology treats negative boundary membership as observable.
Dagger asks for the universal condition that an entire boundary be annihilated by a phase
covector; that is not a one-sided lower-open operation.

## 3. Minimal bipolar topology

Define

\[
 \tau_{\rm bi}(V)
 =\tau_{\rm prov}(V)
 \vee
 \mathbb D_V^{-1}\tau_{\rm prov}(V^\vee),
\tag{8}
\]

the join of source provenance topology and its dagger pullback.

[PROVED HERE] [BIPOLAR_PROVENANCE_DAGGER_TOPOLOGY]

Topology (8) is the coarsest refinement of provenance topology for which dagger is continuous into
the provenance topology of \(V^\vee\). It is also dagger-stable:

\[
 \mathbb D_V:
 \mathsf{ExFlag}(V)_{\rm bi}
 \xrightarrow{\ \cong\ }
 \mathsf{ExFlag}(V^\vee)_{\rm bi}
\tag{9}
\]

is a homeomorphism. Besides source tests \(v\notin B\) and \(v\in Z\), a generating dagger-phase
test is

\[
 \mathcal A_\phi
 =\{(B,Z):B\subseteq\ker\phi\}.
\tag{10}
\]

The specialization order remains

\[
 (B,Z)\preceq(B',Z')
 \quad\Longleftrightarrow\quad
 B'\subseteq B\subseteq Z\subseteq Z'.
\tag{11}
\]

### Proof

Coarseness in first assertion is definition of join topology. Pull (8) on \(V^\vee\) back through
\(\mathbb D_V\). Involutivity gives

\[
 \mathbb D_V^{-1}\tau_{\rm bi}(V^\vee)
 =
 \mathbb D_V^{-1}\tau_{\rm prov}(V^\vee)
 \vee\tau_{\rm prov}(V)
 =\tau_{\rm bi}(V),
\tag{12}
\]

so dagger and its inverse are continuous.

Pullback of dual cycle test \(\phi\in B^\circ\) is exactly (10). Pullback of dual boundary test
\(\phi\notin Z^\circ\) says that some \(z\in Z\) has \(\phi(z)\neq0\); it is union of source
Scott-opens \(z\in Z\). Hence (10) is only new generator type.

Provenance topology already forces specialization order (11). Every new open (10) also respects
it: if \(B'\subseteq B\subseteq\ker\phi\), then \(B'\subseteq\ker\phi\). Thus no specialization
relations are removed, proving (11).

The pair \((\tau_{\rm prov},\tau_{\rm bi})\) records two stages: oriented source transport first,
then a dagger-stable refinement. Collapsing them erases the very variance carried by the source.

## 4. Continuous phase certificates

Let \(V\) now be a Hausdorff locally convex real or complex vector space, let \(B\subseteq Z\subseteq
V\), and assume \(B\) is closed.

[PROVED HERE] [NONBOUNDARY_CONTINUOUS_PHASE_CERTIFICATE]

For \(v\in Z\),

\[
 [v]\neq0\text{ in }Z/B
 \quad\Longleftrightarrow\quad
 \exists\phi\in V'
 \bigl(\phi(B)=0\text{ and }\phi(v)\neq0\bigr).
\tag{13}
\]

### Proof

Right-to-left is immediate. Conversely, \(v\notin B\) gives a nonzero point in Hausdorff locally
convex quotient \(V/B\). Hahn--Banach separation supplies a continuous functional on \(V/B\)
nonzero at that point. Compose with quotient map.

For the strict Meyer--Poisson embedding, literal boundary graph \(\mathcal B_{\rm P}\) is closed in
reflected graph \(\Gamma_{\rm sec}\). Therefore every class in
\(\Gamma_{\rm sec}/\mathcal B_{\rm P}\) has a continuous dagger-phase certificate.

This is progress but not source theorem. Hahn--Banach chooses no canonical covector, proves no
Euler/Gamma covariance, gives no Green--Stokes chain map, and supplies no positive weight-one
family. Missing Route-L object is therefore not existence of separators; it is a source-canonical,
covariant, jointly faithful phase reporter.

## 5. Positivity-placement no-go

Let \(V\) carry a nondegenerate bilinear, alternating, or Hermitian form \(g\). For
\(A\subseteq V\), write \(A^\perp\) for its orthogonal subspace. Call flag \(B\subseteq Z\)
**Green self-dual** when

\[
 Z=B^\perp
 \qquad\text{equivalently}\qquad
 B=Z^\perp.
\tag{14}
\]

[PROVED HERE] [EXACTNESS_FLAG_GREEN_REDUCTION]

If (14) holds, then \(B\) is isotropic and \(g\) descends to a nondegenerate form on

\[
 H_g=B^\perp/B=Z/B.
\tag{15}
\]

If \(g\) is positive-definite Hermitian, the only Green self-dual exactness flag is

\[
 (B,Z)=(0,V).
\tag{16}
\]

Consequently no nontrivial chain complex with nonzero boundary space can be simultaneously
Green self-dual and positive-definite before quotient.

### Proof

Inclusion \(B\subseteq Z=B^\perp\) says \(B\) is isotropic. For \(z,z'\in B^\perp\), changing
either by an element of \(B\) leaves \(g(z,z')\) unchanged, so form descends to (15). Its radical
is

\[
 \bigl(B^\perp\cap(B^\perp)^\perp\bigr)/B
 =B/B=0,
\tag{17}
\]

using nondegeneracy and finite dimension.

If \(g\) is positive-definite and \(b\in B\subseteq B^\perp\), then \(g(b,b)=0\), hence \(b=0\).
Thus \(B=0\), and (14) gives \(Z=V\). This proves (16).

The rank-one exchange flags show both regimes algebraically. On \(V=\mathbb R^2\), hyperbolic form

\[
 G=
 \begin{pmatrix}0&1\\1&0\end{pmatrix}
\tag{18}
\]

makes \(L=\mathbb Re_1\) satisfy \(L^\perp=L\), so off-horizon flag \((L,L)\) is Green self-dual.
Horizon flag \((0,V)\) is also Green self-dual. No positive-definite form can realize off-horizon
flag this way.

Hence source Green--Stokes geometry must be indefinite, alternating, or relational before
reduction. A positive Hilbert form may be constructed on \(Z/B\) afterward, but it is additional
polarization data; positivity does not descend automatically from indefinite source form.

## 6. Conjecture--failure loop

1. **Conjecture:** one-sided provenance topology already supports dagger.
   **Failed by (6)--(7).** Dagger asks for boundary annihilation, not pointwise nonmembership.
2. **Conjecture:** fix failure by forgetting source orientation and using only dagger-invariant
   Hilbert topology.
   **Failed by (16).** Positive self-duality before quotient deletes every nonzero boundary.
3. **Conjecture:** a continuous phase separator for every nonboundary solves source incidence.
   **Failed as producer.** Hahn--Banach proves existence after closed boundary is known but provides
   no canonical source construction, covariance, positivity, or joint faithfulness.
4. **Positive survivor:** use bipolar topology for comparison, indefinite Green--Stokes form on
   cochains, exact provenance reduction \(B\subseteq Z\), and positive dagger only on \(Z/B\).

## 7. Consequence for live RH routes

This theorem explains three otherwise separate corpus facts.

1. A diagonal nonnegative prime-circle energy cannot also serve as chain-level Green self-duality:
   exactness needs isotropic boundary directions, impossible in positive-definite self-dual
   geometry. Corpus separately proves concrete diagonal-weight failure.
2. The open source theorem is explicitly **unsquared and non-diagonal before Hermitian
   polarization** because Green--Stokes duality must first create \(B=Z^\perp\).
3. Inverse-equals-adjoint is a statement after provenance reduction. Imposing it globally on
   cochains either forces false functoriality or collapses nonzero boundaries.

A sufficient bioriented producer compatible with theorem has narrower order:

\[
 \text{construct source Green relation}
 \Longrightarrow
 B=Z^\perp
 \Longrightarrow
 H=Z/B
 \Longrightarrow
 \text{prove source-canonical positive dagger on }H.
\tag{19}
\]

For Route L, \(Z=\Gamma_{\rm sec}\) is proved and \(B=\mathcal B_{\rm P}\) is classified. A
perfect-pairing implementation would need source Green relation realizing \(B=Z^\perp\) with
Euler/Gamma covariance; a more general implementation may use same statement as a closed linear
relation between paired degrees. Either way, another positive kernel energy is insufficient. For
polarized exchange, missing map must preserve provenance reduction and be nonzero on \(H\).

## 8. Hostile novelty and literature audit

1. **Classical parents.** Annihilator duality, quotient duals, Hahn--Banach, isotropic reduction,
   Krein spaces, Green boundary relations, and symplectic reduction are classical. Relevant
   literature includes arXiv:2307.15954 and arXiv:1205.6519.
2. **New claim kept narrow.** Candidate-new corpus content is exact placement of those structures
   against provenance topology and proved RH-route obstructions: dagger discontinuity,
   positivity-before-reduction no-go, and identification of source-canonical phase family as
   missing object.
3. **No physical inference.** Hyperbolic form (18) mathematically resembles a causal bulk metric,
   while quotient polarization resembles boundary unitarity. No wormhole or black-hole model is
   assumed. Any such model must realize (14)--(19), including source provenance.
4. **No positivity claim.** Theorem proves where positivity cannot live. It does not construct
   positive form on Meyer quotient or prove RH.
5. **Lean status.** Sections 1--5 are now unconditional Lean theorems in
   `formal/GaloisForLFunctions/HTGeometry/ExactnessFlagDaggerDuality.lean`,
   `ExactnessFlagBipolarTopology.lean`, `ExactnessFlagPhaseCertificate.lean`, and
   `ExactnessFlagGreenReduction.lean`; see the companion certificate card. The quotient duality is
   proved without finite-dimensionality, and the phase certificate over any `RCLike` field.

## Gates

- [x] 0 -> 1: dagger continuity and positivity placement posed with explicit falsifiers
- [x] 1 -> 2: dual quotient, discontinuity, bipolar topology, phase separation, and positivity
  no-go paper-proved
- [x] exact application to rank-one exchange and Meyer--Poisson range recorded
- [x] broad current literature boundary recorded
- [x] 2 -> 3: unconditional Lean formalization
  (`bipolar-provenance-dagger-reduction-formalized.md`)
- [ ] 3 -> 4: external boundary-triples/Krein specialist audit

## Log

- 2026-08-09 — Formalized in Lean 4 without hypotheses: the dagger flag, its perfect pairing and
  the isomorphism \((Z/B)^\vee\cong B^\circ/Z^\circ\), involutivity, the provenance discontinuity,
  the bipolar refinement with its coarsest-refinement property, generator classification,
  unchanged specialization order, dagger homeomorphism, the continuous phase certificate, and the
  Green reduction with its positivity no-go and hyperbolic witness.
- 2026-08-08 — Proved that exactness-flag dagger dualizes spectral quotient but is discontinuous
  in one-sided provenance topology; constructed minimal dagger-stable bipolar refinement.
- 2026-08-08 — Proved positive-definite chain-level Green self-duality forces zero boundaries.
  This explains why source Green--Stokes must be unsquared/indefinite before quotient and why
  positive Hilbert dagger belongs after provenance reduction.
