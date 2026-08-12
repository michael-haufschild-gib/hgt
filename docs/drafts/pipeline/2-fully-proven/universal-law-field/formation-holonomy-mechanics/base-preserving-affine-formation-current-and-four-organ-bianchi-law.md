# Base-preserving affine formation current and four-organ Bianchi law

- **ID:** ULF-FHM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Formation Holonomy Mechanics; strict vertical theorem ULF-FHM-1
- **Statement:** Every linear comparison preserving a common recovered base has a unique affine vertical normal form consisting of a formation current and a vertical transport; composition couples them by a semidirect law, triangle defects are purely vertical, and associativity imposes exact four-organ Bianchi identities on both current and transport defects.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [GENERATION + TRANSPORT FUSION] [FINITE PACKET/KMS REALIZATION] [LEAN OPEN: READ-ONLY FORMAL PHASE] [NOT RH]

## 1. Setup

Let \(K\) be a field. For every index \(i\), let

\[
 X\xrightarrow{f_i}Z_i\xrightarrow{p_i}X,
 \qquad p_if_i=1_X
 \tag{AFC.1}
\]

be linear maps. Put

\[
 V_i=\ker p_i.
 \tag{AFC.2}
\]

As in ULF-FHM-1, the maps

\[
 \Phi_i(x,v)=f_ix+v,
 \qquad
 \Psi_i(z)=\bigl(p_iz,z-f_ip_iz\bigr)
 \tag{AFC.3}
\]

are inverse isomorphisms \(X\oplus V_i\cong Z_i\).

Let \(C_{ji}:Z_i\to Z_j\) preserve the recovered base:

\[
 p_jC_{ji}=p_i.
 \tag{AFC.4}
\]

Unlike the strict theorem, do **not** assume \(C_{ji}f_i=f_j\).

## 2. Affine vertical normal form

Define

\[
 a_{ji}:X\to Z_j,
 \qquad
 a_{ji}=C_{ji}f_i-f_j,
 \tag{AFC.5}
\]

and let \(L_{ji}=C_{ji}|_{V_i}\).

### Theorem 2.1 -- unique generation/transport decomposition

The maps in (AFC.5) and \(L_{ji}\) land in \(V_j\), and

\[
 \boxed{
 \Psi_jC_{ji}\Phi_i
 =
 \begin{pmatrix}
 1_X&0\\
 a_{ji}&L_{ji}
 \end{pmatrix}.}
 \tag{AFC.6}
\]

The pair \((a_{ji},L_{ji})\) is unique. Moreover:

\[
 a_{ji}=0
 \iff C_{ji}f_i=f_j,
 \tag{AFC.7}
\]

and

\[
 a_{ji}=0=L_{ji}
 \iff C_{ji}=f_jp_i.
 \tag{AFC.8}
\]

#### Proof

Base preservation gives

\[
 p_ja_{ji}=p_jC_{ji}f_i-p_jf_j=p_if_i-1_X=0,
\]

so \(a_{ji}\) lands in \(V_j\). If \(v\in V_i\), then

\[
 p_jC_{ji}v=p_iv=0,
\]

so \(L_{ji}\) is also well-defined. For \(x\in X,v\in V_i\),

\[
 C_{ji}(f_ix+v)
 =f_jx+a_{ji}x+L_{ji}v.
\]

Applying \(\Psi_j\) proves (AFC.6). Evaluation on \((x,0)\) and \((0,v)\) proves uniqueness.
Equation (AFC.7) is the definition. If both blocks vanish, (AFC.6) is \(1_X\oplus0\), which is
the split form of \(f_jp_i\); the converse is immediate. ∎

The current \(a_{ji}\) measures **formation generation**: the comparison preserves recovered source
but changes how that source is formed in the target fibre. The map \(L_{ji}\) transports already
vertical information.

## 3. Semidirect composition law

Let \(C_{ji}:Z_i\to Z_j\) and \(C_{kj}:Z_j\to Z_k\) preserve the recovered base. Write their normal
forms as \((a_{ji},L_{ji})\) and \((a_{kj},L_{kj})\).

### Theorem 3.1 -- generation is transported before addition

The composite has normal form

\[
 \boxed{
 (a_{kj},L_{kj})\star(a_{ji},L_{ji})
 =\bigl(a_{kj}+L_{kj}a_{ji},\ L_{kj}L_{ji}\bigr).}
 \tag{AFC.9}
\]

#### Proof

Multiply the block matrices:

\[
 \begin{pmatrix}1&0\\a_{kj}&L_{kj}\end{pmatrix}
 \begin{pmatrix}1&0\\a_{ji}&L_{ji}\end{pmatrix}
 =
 \begin{pmatrix}
 1&0\\
 a_{kj}+L_{kj}a_{ji}&L_{kj}L_{ji}
 \end{pmatrix}.
\]

∎

Thus an inner formation current cannot be added directly at the outer stage; it must first be
transported by the outer vertical law. This is the exact intervention/generation grammar missing
from the strict common-recovery corner.

## 4. Joint triangle defect

For three base-preserving comparisons, define

\[
 \Omega_{kji}=C_{kj}C_{ji}-C_{ki}.
 \tag{AFC.10}
\]

Put

\[
 \alpha_{kji}=a_{kj}+L_{kj}a_{ji}-a_{ki},
 \qquad
 \Lambda_{kji}=L_{kj}L_{ji}-L_{ki}.
 \tag{AFC.11}
\]

### Theorem 4.1 -- generated and transported defect split

The triangle defect has exact vertical block form

\[
 \boxed{
 \Psi_k\Omega_{kji}\Phi_i
 =
 \begin{pmatrix}
 0&0\\
 \alpha_{kji}&\Lambda_{kji}
 \end{pmatrix}.}
 \tag{AFC.12}
\]

In particular,

\[
 \boxed{p_k\Omega_{kji}=0.}
 \tag{AFC.13}
\]

The strict theorem ULF-FHM-1 is the special case \(a_{ji}=0\), where only \(\Lambda\) remains.

#### Proof

Theorem 3.1 gives the two blocks of \(C_{kj}C_{ji}\). Subtract the normal form of \(C_{ki}\).
The base block \(1_X-1_X\) vanishes, yielding (AFC.12); (AFC.13) follows. ∎

## 5. Four-organ Bianchi identities

For four indices \(i,j,k,\ell\), associativity gives the full-map identity

\[
 C_{\ell k}\Omega_{kji}+\Omega_{\ell ki}
 =\Omega_{\ell kj}C_{ji}+\Omega_{\ell ji}.
 \tag{AFC.14}
\]

### Theorem 5.1 -- coupled current/transport conservation

The vertical transport defects satisfy

\[
 \boxed{
 L_{\ell k}\Lambda_{kji}+\Lambda_{\ell ki}
 =\Lambda_{\ell kj}L_{ji}+\Lambda_{\ell ji}.}
 \tag{AFC.15}
\]

The affine formation-current defects satisfy

\[
 \boxed{
 L_{\ell k}\alpha_{kji}+\alpha_{\ell ki}
 =\alpha_{\ell kj}+\Lambda_{\ell kj}a_{ji}+\alpha_{\ell ji}.}
 \tag{AFC.16}
\]

The mixed term \(\Lambda_{\ell kj}a_{ji}\) is load-bearing: a transport-composition defect acts on
the inner generated current. Current and transport curvature cannot be assigned independently.

#### Proof

Identity (AFC.14) follows by expanding both sides to

\[
 C_{\ell k}C_{kj}C_{ji}-C_{\ell i}.
\]

For the transport block, compose the lower-right blocks in (AFC.14), obtaining (AFC.15).

For the lower-left block, \(C_{\ell k}\Omega_{kji}\) contributes
\(L_{\ell k}\alpha_{kji}\), because \(\Omega_{kji}\) has zero base output. On the right,
\(\Omega_{\ell kj}C_{ji}\) contributes

\[
 \alpha_{\ell kj}+\Lambda_{\ell kj}a_{ji}.
\]

Adding the remaining triangle-current blocks proves (AFC.16). ∎

This is the first exact law in the programme coupling **generation**, **transport**, and
**four-organ coherence** in one equation.

## 6. Finite diagonal/reset realization

Let \(A\) be a finite nonempty set and work over \(\mathbb R\). Put

\[
 X=\mathbb R^A,
 \qquad
 Z=\mathbb R^{A\times A}.
\]

Let recovery be first marginal:

\[
 (pz)_a=\sum_{b\in A}z_{ab}.
 \tag{AFC.17}
\]

Fix a probability vector \(q=(q_a)\). Define two sections:

\[
 (f_\Delta x)_{ab}=\mathbf1_{a=b}x_a,
 \qquad
 (f_Rx)_{ab}=x_aq_b.
 \tag{AFC.18}
\]

Both obey \(pf_\Delta=1_X=pf_R\). Regard the identity map \(C=1_Z\) as a comparison from the
diagonal chart to the reset chart. It preserves the base but not the section.

### Theorem 6.1 -- reset displacement is the affine formation current

The identity comparison has

\[
 L=1_{\ker p},
 \qquad
 a=f_\Delta-f_R.
 \tag{AFC.19}
\]

At the formed probability vector \(q\),

\[
 \boxed{a(q)=\Delta_q-q\otimes q\in\ker p.}
 \tag{AFC.20}
\]

The reverse identity comparison has current \(-a\) and the same vertical transport. Their
semidirect composite current vanishes exactly, although any positive norm or divergence of
\(a(q)\) is nonzero for non-Dirac \(q\).

#### Proof

Because the ambient comparison is the identity, its restriction to \(\ker p\) is the identity.
Definition (AFC.5) gives \(a=f_\Delta-f_R\). Evaluating at \(q\) gives (AFC.20). Reversing the
charts changes the sign. Theorem 3.1 gives \((-a,1)\star(a,1)=(0,1)\). ∎

For positive \(q_a\), the established exact shadows are

\[
 \operatorname{TV}(\Delta_q,q\otimes q)=1-\sum_aq_a^2,
 \tag{AFC.21}
\]

\[
 D(\Delta_q\Vert q\otimes q)=H(q),
 \tag{AFC.22}
\]

and for the diagonal density state \(\rho_q=\operatorname{diag}(q)\),

\[
 S_{\mathrm{vN}}(\rho_q)=H(q).
 \tag{AFC.23}
\]

Thus one affine vertical current has exact process/history, information, and operator/KMS shadows;
first-marginal recovery erases it identically. Algebraic reversal cancels the signed current, while
positive execution work does not cancel. This is the precise closed-observer/open-history split.

## 7. Four-organ prediction

Suppose a fourth formation chart is added to a diagonal/reset/observer comparison system. Once its
edge currents \(a\), vertical transports \(L\), and three adjacent triangle defects are computed,
the fourth triangle current is not free: it must satisfy (AFC.16). In particular, any proposed
fourth-organ scalar that ignores the mixed term \(\Lambda a\) cannot be the image of a
base-preserving formation comparison unless that mixed term vanishes under the scalar reporter.

This supplies an immediate corpus falsifier:

> A claimed fusion of generation and transport that uses additive currents alone is invalid whenever
> the transport triangle has nonzero defect acting nontrivially on the inner formation current.

## 8. Hostile loops

### Loop A -- all base-preserving comparisons are homogeneous

- **Failure:** changing the chosen formation section produces \(a\ne0\) even for the ambient identity.
- **Survivor:** unique affine current plus vertical transport.

### Loop B -- generated currents add directly

- **Failure:** (AFC.9) transports the inner current before addition.
- **Survivor:** semidirect intervention/generation law.

### Loop C -- current and transport defects satisfy separate Bianchi laws

- **Failure:** (AFC.16) contains \(\Lambda a\).
- **Survivor:** coupled four-organ conservation.

### Loop D -- algebraic cancellation removes positive history work

- **Failure:** reverse currents cancel as signed vectors, while TV, KL, and entropy remain
  nonnegative and accumulate under repeated reset.
- **Survivor:** signed coherence and positive work are distinct field grades.

### Loop E -- the finite realization proves RH

- **Failure:** no arithmetic source comparison or bounded positive work is constructed.
- **Survivor:** exact source target: construct literal \((a,L)\) maps across three route organs,
  verify the fourth-organ identity, then prove proper/passive work.

## 9. Significance and parent boundary

Affine block matrices, semidirect products, split exact sequences, and Bianchi identities from
associativity are classical. The result is promoted as a dependency-closed universal-law-field
theorem because it supplies the missing typed coupling between generated formation and latent
transport, embeds the diagonal/reset/KMS conservation law as a literal affine current, and yields an
exact four-organ falsifier. No external priority claim is made.

## Gates

- [x] affine normal form proved
- [x] semidirect composition proved
- [x] joint triangle defect proved
- [x] coupled four-organ Bianchi identities proved
- [x] finite diagonal/reset/KMS realization proved
- [ ] Lean formalization (deferred in current read-only Lean audit phase)
- [ ] literal arithmetic three-organ comparison
- [ ] source-generated positive properness law

## Log

- 2026-08-11 -- generalized strict vertical theorem by retaining section mismatch. Exact
  generation/transport fusion and finite diagonal/reset realization proved on paper. No Lean files
  edited or built.
