# Split \(L_\infty\) observer extension field and nonlinear Gauss--Codazzi law

- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** [PAPER-PROVED] [LEAN FORMALIZED — DOCUMENTED IN PLACE] [LEAF CHECK CLEAN]
  [ROUTE-INDEPENDENT] [NONLINEAR OBSERVER FIELD] [MAURER--CARTAN EXTENSION]
  [GAUGE-COVARIANT] [NOT RH]

## 1. Setup

Work over a characteristic-zero field. Let \(K,H\) be complete filtered graded vector spaces and
put \(E=K\oplus H\). Let

\[
 \widehat S^c(sE)
\]

be the completed cofree conilpotent symmetric coalgebra. Let \(Q_K,Q_H\) be filtration-increasing
degree-one coderivations on \(\widehat S^c(sK)\) and \(\widehat S^c(sH)\), with

\[
 Q_K^2=Q_H^2=0.
\tag{NLG.1}
\]

Extend them to the direct-product coderivation

\[
 Q_0=Q_K\oplus Q_H
\tag{NLG.2}
\]

on \(\widehat S^c(sE)\).

Let \(\mathfrak L_{K\triangleleft E}\) be the complete filtered graded Lie algebra of coderivations
\(D\) of \(\widehat S^c(sE)\) such that:

1. every Taylor coefficient of \(D\) takes values in \(sK\);
2. \(D\) vanishes when all inputs lie in \(sK\).

Thus \(\mathfrak L_{K\triangleleft E}\) contains pure-horizontal maps
\(S^n(sH)\to sK\) and all mixed maps with at least one \(H\)-input and \(K\)-valued output.

## 2. Nonlinear observer theorem

### Theorem 2.1 — extension fields are Maurer--Cartan elements

The commutator

\[
 d_0D=[Q_0,D]
\tag{NLG.3}
\]

makes \(\mathfrak L_{K\triangleleft E}\) a complete differential graded Lie algebra. For
\(\tau\in\mathfrak L_{K\triangleleft E}^1\), put

\[
 Q_E=Q_0+\tau.
\tag{NLG.4}
\]

Then

\[
 \boxed{
 Q_E^2=0
 \quad\Longleftrightarrow\quad
 d_0\tau+\frac12[\tau,\tau]=0.}
\tag{NLG.5}
\]

When (NLG.5) holds:

- \(K\) is an \(L_\infty\) ideal of \(E\);
- the quotient is \(H\);
- the strict projection \(q:E\to H\) is an \(L_\infty\) observer;
- \(\tau\) is the complete nonlinear relative observer field.

### Corollary 2.2 — nonlinear Gauss--Codazzi hierarchy

Decompose

\[
 \tau=\sum_{a,b\geq0,\ a+b\geq1}\tau_{a,b},
 \qquad
 \tau_{a,b}:S^a(sK)\widehat\otimes S^b(sH)\to sK,
\tag{NLG.6}
\]

with \(\tau_{a,0}=0\). The components with \(a=0\),

\[
 \Omega_b:=\tau_{0,b}:S^b(sH)\to sK,
\tag{NLG.7}
\]

are the pure-horizontal splitting defects. Components with \(a>0\) are mixed vertical transport
and nonlinear second fundamental laws.

Equation (NLG.5), resolved by input bidegree, is the complete nonlinear
Gauss--Codazzi--Ricci hierarchy. In particular, the pure-horizontal tensors \(\Omega_b\) do not
form a closed field system unless all mixed terms required by (NLG.5) are retained.

### Corollary 2.3 — exact product criterion

\[
 \tau=0
\quad\Longleftrightarrow\quad
(E,Q_E)\cong(K,Q_K)\times(H,Q_H)
\tag{NLG.8}
\]

through the declared splitting. Thus vanishing of the full extension field, not vanishing of one
horizontal component, is the exact local product criterion.

### Corollary 2.4 — change of splitting is gauge

Let \(F\) be a filtration-unipotent coalgebra automorphism of \(\widehat S^c(sE)\) whose
restriction to \(\widehat S^c(sK)\) is the identity and whose induced automorphism on
\(\widehat S^c(sH)\) is the identity. Then

\[
 Q_E'=FQ_EF^{-1}=Q_0+\tau'
\tag{NLG.9}
\]

for another Maurer--Cartan element \(\tau'\in\mathfrak L_{K\triangleleft E}\). The two extension
fields lie in the same pronilpotent gauge orbit. Conversely, every such gauge transformation is a
change of split presentation of the same pointed extension.

Therefore

\[
 [\tau]\in
 \operatorname{MC}(\mathfrak L_{K\triangleleft E})/\text{gauge}
\tag{NLG.10}
\]

is the intrinsic local extension class of the observer fibration.

### Corollary 2.5 — cyclic extension action

Assume in addition that \(\mathfrak L_{K\triangleleft E}\) carries a continuous nondegenerate
invariant graded-symmetric pairing of degree \(-3\). Define

\[
 \mathcal S_{\mathrm{ext}}(\tau)
 =\frac12\langle\tau,d_0\tau\rangle
 +\frac16\langle\tau,[\tau,\tau]\rangle.
\tag{NLG.11}
\]

Then for every degree-one variation \(\eta\),

\[
 \delta\mathcal S_{\mathrm{ext},\tau}(\eta)
 =
 \left\langle
 \eta,d_0\tau+\frac12[\tau,\tau]
 \right\rangle.
\tag{NLG.12}
\]

Hence the extension-field equation (NLG.5) is precisely the Euler--Lagrange equation of
\(\mathcal S_{\mathrm{ext}}\), and its twisted Bianchi identity is the infinitesimal Noether
identity.

## 3. Proof

The defining conditions of \(\mathfrak L_{K\triangleleft E}\) are preserved under commutator.
Indeed, inserting a \(K\)-valued output into another relative coderivation still gives a
\(K\)-valued output, and both coderivations vanish on an all-\(K\) word. Since \(Q_0\) preserves
the direct factors,

\[
 [Q_0,\mathfrak L_{K\triangleleft E}]
 \subseteq\mathfrak L_{K\triangleleft E}.
\]

Moreover,

\[
 d_0^2D=[Q_0,[Q_0,D]]
 =\frac12[[Q_0,Q_0],D]=0
\]

by (NLG.1). Thus (NLG.3) is a differential.

Now

\[
 Q_E^2
 =\frac12[Q_E,Q_E]
 =\frac12[Q_0,Q_0]+[Q_0,\tau]+\frac12[\tau,\tau].
\]

The first term vanishes, proving (NLG.5). Because every component of \(\tau\) is \(K\)-valued and
vanishes on all-\(K\) inputs, restriction to \(K\) is \(Q_K\), quotient by \(K\) is \(Q_H\), and
the projection is a strict \(L_\infty\) morphism.

Decomposition by the number of \(K\)- and \(H\)-inputs is unique. Projecting (NLG.5) to each
bidegree gives Corollary 2.2. Equation (NLG.8) follows immediately from (NLG.4).

Conjugation preserves the square-zero equation, the ideal \(K\), and the quotient \(H\). Hence
\(FQ_EF^{-1}-Q_0\) is another element of the same relative coderivation algebra satisfying
(NLG.5). In a complete pronilpotent filtration, such unipotent automorphisms are exponentials of
degree-zero relative coderivations, and conjugation is precisely the standard Maurer--Cartan gauge
action. This proves Corollary 2.4.

For Corollary 2.5, vary the two summands in (NLG.11). Graded symmetry, invariance, and cyclicity
combine the two differential contributions and the three bracket contributions, giving
(NLG.12). Nondegeneracy identifies critical points with (NLG.5). Applying the twisted differential
to the Maurer--Cartan expression gives zero by the differential graded Jacobi identity, which is
the Noether/Bianchi identity.

## 4. Hostile countermodel: horizontal curvature is incomplete

Let \(K=kz\) and \(H=kx\) be ordinary degree-zero Lie spaces. Define two Lie algebras on
\(E=K\oplus H\):

1. the abelian algebra;
2. the affine semidirect algebra with
   \[
   [x,z]=z.
   \tag{NLG.13}
   \]

In both cases every pure-horizontal defect \(S^bH\to K\) vanishes: there is only one horizontal
generator, so \(\Omega_b=0\) for all \(b\). But the second algebra has a nonzero mixed component
\(\tau_{1,1}\), nontrivial vertical transport, and is not the direct product.

Therefore pure-horizontal curvature data do not determine the observer extension. The full mixed
Maurer--Cartan field \(\tau\) is load-bearing.

## 5. NHG interpretation

The true nonlinear field strength of a split observer is not one scalar, one two-form, or even the
list of pure-horizontal higher forms. It is the gauge class (NLG.10). Its faces are:

- \(\Omega_b\): horizontal curvature-like defects;
- mixed \(\tau_{a,b}\): vertical law transport and nonlinear observer coupling;
- the Maurer--Cartan equation: higher Bianchi/Gauss--Codazzi coherence;
- its gauge orbit: independence of split presentation.

This is the nonlinear local model of the NHG relative law-fibre. Global integration, Spencer
prolongation, polarization, and analytic completion enrich this extension field; they do not
replace it.

## 6. Sharp scope

1. Characteristic zero and complete pronilpotent filtration are used.
2. The theorem concerns split local presentations. The gauge orbit removes splitting dependence,
   but global nonsplit descent requires a stack of such charts.
3. A general observer not presented as an ideal quotient requires homotopy replacement before this
   theorem applies.
4. Cyclicity and polarization restrict the allowed coderivations and gauges but are not needed for
   the algebraic Maurer--Cartan identity.
5. The theorem gives kinematics and coherence, not a source constitutive dynamics.
6. No arithmetic or endpoint statement is claimed.

## 7. Parent boundary

Coderivation deformation theory and Maurer--Cartan classification of algebra extensions are
established machinery. Direct parents include:

- Fialowski--Penkava, *Deformation Theory of Infinity Algebras*,
  <https://arxiv.org/abs/math/0101097>;
- Frégier, *Non abelian cohomology of extensions of Lie algebras as Deligne groupoid*,
  <https://arxiv.org/abs/1310.0959>;
- Calaque--Grivaux, *Formal moduli problems and formal derived stacks*,
  <https://arxiv.org/abs/1802.09556>.

NHG's field claim is not priority over this machinery. Its load-bearing proposal is to treat the
extension Maurer--Cartan orbit as the nonlinear local field strength of an observer law-fibre, then
couple that same object functorially to Atiyah--Spencer curvature, higher holonomy, polar reduction,
prolongation, and proper history. Those global couplings remain the research frontier.

## 8. Lean formalization status

Formalized and promoted to Stage 3:

- `SplitLInfinityObserverExtension.lean` works in the completed-law operator algebra already built
  for cyclic coderivations. It defines a bracket-closed relative sector, proves the exact square
  expansion and Maurer--Cartan equivalence, proves the background deformation complex is
  square-zero, and resolves the equation through a jointly detecting input-bidegree family.
- It formalizes split-presentation gauge conjugation and square-zero covariance, the exact declared
  product criterion, the cyclic cubic extension action with Euler--Lagrange equation, and the
  twisted Bianchi identity.
- A concrete affine semidirect bracket proves all pure-horizontal brackets can vanish while a mixed
  vertical component remains nonzero. Foreground `lake env lean <file>` passes with no warnings or
  errors. Umbrella import is wired; aggregate build and axiom audit remain in final all-card audit.
