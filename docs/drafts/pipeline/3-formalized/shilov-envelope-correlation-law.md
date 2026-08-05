# Shilov envelope-correlation cohomology law

- **ID:** shilov-envelope-correlation-law
- **Stage:** 3-formalized
- **Type:** THEOREM CANDIDATE
- **Source:** ../2-fully-proven/spectral-boundary-migration-shilov-exactness.md · universal-shadow continuation requested 2026-08-04
- **Statement:** `[PROVED HERE — NOVELTY AUDIT ACTIVE]` Shilov ideals of every quotient diagram admit a canonical
  join completion to a simplicial coefficient system. Its quotient coefficient system has
  degree-zero sections equal to compatible envelope correlations, and the resulting long exact
  cohomology sequence is the universal obstruction law for \(C^*\)-envelope descent.

## Goal

Replace paper's obstruction list by one canonical object and one path law. Envelope maps may fail
to exist, but envelope correlations always do. Their vertical ideals record ambiguity and kernel;
composition joins transported Shilov ideals. Publication threshold: unconditional
arbitrary-quotient correlation extension, finite-path join formula, diagrammatic cohomology exact
sequence, and a realization theorem
showing that the new cohomology carries arbitrary noncommutative information. Finite Čech
acyclicity is supporting infrastructure already present in distributive-lattice cohomology, not a
novelty claim.

## Exact frozen candidate

For a complete-order quotient $q:S\twoheadrightarrow T$, write
$A_S=C_u^*(S)$, $E_S=C_e^*(S)=A_S/J_S$, and let
$\alpha_q:A_S\twoheadrightarrow A_T$ be universal `*`-epimorphism. Define canonical
**envelope correlation**

\[
 \Gamma_q:=\{(a+J_S,\alpha_q(a)+J_T):a\in A_S\}
 \subseteq E_S\oplus E_T. \tag{EC}
\]

It is a closed subdirect `C*`-product. With

\[
 D_q:=J_S\cap\alpha_q^{-1}(J_T),
\]

there is a canonical isomorphism $\Gamma_q\cong A_S/D_q$. If $p_S,p_T$ are coordinate
projections and $\mathcal K_q$ is image of $\ker\alpha_q$ in $\ker p_T$, then

\[
 \ker p_S\cong\operatorname{Esc}(q),\qquad
 0\longrightarrow\mathcal K_q\longrightarrow\ker p_T
 \longrightarrow\operatorname{Def}(q)\longrightarrow0. \tag{VE}
\]

When escape vanishes, $p_S$ is an isomorphism, $\Gamma_q$ is graph of canonical envelope
epimorphism, and `(VE)` becomes paper's kernel-generation formula. Thus `(VE)` extends that
formula to quotients for which no envelope map exists.

## Edge pullback and minimal join theorem — paper proof

`[PROVED HERE]` Put

\[
 M_q:=J_T+\alpha_q(J_S)\triangleleft A_T,\qquad Q_q:=A_T/M_q.
\]

There are canonical surjective \(*\)-homomorphisms

\[
 \rho_S:E_S\longrightarrow Q_q,\quad
 \rho_S(a+J_S)=\alpha_q(a)+M_q,
 \qquad
 \rho_T:E_T\longrightarrow Q_q,\quad
 \rho_T(b+J_T)=b+M_q.
\]

Then

\[
 \boxed{\Gamma_q=E_S\times_{Q_q}E_T.} \tag{PB}
\]

Moreover, \(M_q\) is the least ideal of \(A_T\) which contains \(J_T\) and makes the transported
map from \(E_S\) well-defined. Its two endpoint quotients are

\[
 M_q/J_T\cong\Esc(q),\qquad
 M_q/\alpha_q(J_S)\cong\Def(q). \tag{FQ}
\]

**Proof.** The endpoint maps are well-defined and onto because
\(\alpha_q(J_S),J_T\subseteq M_q\) and \(\alpha_q\) is onto. A pair
\((a+J_S,b+J_T)\) belongs to the pullback precisely when

\[
 b-\alpha_q(a)\in J_T+\alpha_q(J_S).
\]

Write \(b-\alpha_q(a)=j_T+\alpha_q(j_S)\). Then the same pair equals

\[
 (a+j_S+J_S,\alpha_q(a+j_S)+J_T)\in\Gamma_q.
\]

The reverse inclusion is immediate, proving `(PB)`. Any ideal \(N\triangleleft A_T\) for which
both endpoint quotient maps exist must contain \(J_T\) and \(\alpha_q(J_S)\), hence \(M_q\subseteq
N\). Finally, `(FQ)` is the second isomorphism theorem. ∎

`[PROVED HERE]` The vertical extension `(VE)` follows without any descent hypothesis. Indeed,
the canonical map

\[
 \theta_q:A_S\longrightarrow E_S\oplus E_T,\qquad
 \theta_q(a)=(a+J_S,\alpha_q(a)+J_T)
\]

has kernel \(D_q=J_S\cap\alpha_q^{-1}(J_T)\); its image is closed because it is a \(C^*\)-algebra
quotient. The source-vertical kernel is

\[
 \{(0,\alpha_q(j)+J_T):j\in J_S\}
 \cong\alpha_q(J_S)/(\alpha_q(J_S)\cap J_T)=\Esc(q).
\]

The opposite vertical kernel is \(\alpha_q^{-1}(J_T)/D_q\). The map

\[
 [a]\longmapsto \alpha_q(a)+(\alpha_q(J_S)\cap J_T)
\]

from this kernel onto \(\Def(q)\) is well-defined and surjective. Its kernel is exactly the image
of \(\ker\alpha_q\): if \(\alpha_q(a)=\alpha_q(j)\) for some \(j\in J_S\), then
\([a]=[a-j]\) and \(a-j\in\ker\alpha_q\). This proves `(VE)`.

Because both pullback projections in `(PB)` are \(C^*\)-epimorphisms, they are surjective on
positive cones at every matrix level. Thus every positive matrix over either envelope admits a
positive matrix coupling in \(\Gamma_q\), with the usual quotient norm control. This is the
unconditional matricial lifting law; zero deficit is the stronger assertion that lifts can be
chosen inside the source Shilov ideal.

## Finite path join law

For a finite quotient path

\[
 S_0\xrightarrow{q_1}S_1\longrightarrow\cdots\xrightarrow{q_n}S_n,
\]

put $\alpha_{n:i}=\alpha_{q_n}\cdots\alpha_{q_{i+1}}$ and
$I_i^{(n)}=\alpha_{n:i}(J_i)\triangleleft A_{S_n}$, with $I_n^{(n)}=J_n$. For each visited
vertex set $P\subseteq\{0,\ldots,n\}$ containing $0,n$, the frozen ambiguity law is

\[
 \boxed{
 \operatorname{Amb}(P)=\frac{J_n+\sum_{i\in P\setminus\{n\}}I_i^{(n)}}{J_n}.} \tag{J}
\]

Here $\operatorname{Amb}(P)$ is the target-vertical ideal of the composed envelope correlation.
Path refinement acts by ideal join on ambiguity. In particular,

\[
 \Gamma_{rq}\subseteq\Gamma_r\circ\Gamma_q. \tag{OL}
\]

This assignment is normal oplax under inclusion. Finite Čech acyclicity for several ideals in one
algebra is imported from distributive ideal-lattice theory, not claimed new and not confused with
migration cohomology across several algebras. The latter can be nonzero already on a two-edge
path.

`[PROVED HERE]` Relational composition is closed and associative, and `(J)` holds. If
\(R\subseteq A\oplus B\) and \(T\subseteq B\oplus C\) are closed subdirect \(C^*\)-products, form
their fiber product over \(B\). It is a \(C^*\)-algebra, and its image under the endpoint
projection into \(A\oplus C\) is closed because it is the image of a \(*\)-homomorphism.
Set-theoretic relational composition is associative, hence so is this operation.

For a path through the vertices in \(P\), induction on path length gives

\[
 \Gamma_P=
 \left\{\left(a+J_0,\
 \alpha_{n:0}(a)+
 \sum_{i\in P\setminus\{0,n\}}\alpha_{n:i}(j_i)+J_n\right):
 a\in A_{S_0},\ j_i\in J_i\right\}. \tag{PC}
\]

Indeed, equality of two intermediate envelope classes says their representatives differ by an
element of the intermediate Shilov ideal, producing exactly the next transported summand. The
target-vertical ideal of `(PC)` is obtained by additionally varying \(a\) through \(J_0\), and is
therefore `(J)`. The direct correlation uses only \(J_0,J_n\), so adding intermediate vertices
can only enlarge the relation. This proves `(OL)`. ∎

For an arbitrary tower put

\[
 M_n:=J_n+\alpha_n(J_{n+1}),\qquad
 C^0_{\rm mig}:=\prod_nJ_n,\qquad C^1_{\rm mig}:=\prod_nM_n,
\]

and

\[
 d_{\rm mig}((j_n))=(j_n-\alpha_n(j_{n+1}))_n. \tag{MC}
\]

This is cellular boundary cohomology on the quotient path: vertex stalks are $J_n$, edge stalks
are joins $M_n$, and endpoint maps are inclusion and transported inclusion. Each edge recovers
paper's exchange pair:

\[
 M_n/J_n\cong\operatorname{Esc}(q_n),\qquad
 M_n/\alpha_n(J_{n+1})\cong\operatorname{Def}(q_n). \tag{ED}
\]

Let $\Gamma_n\subset E_{n+1}\oplus E_n$ be `(EC)` and define relational inverse limit

\[
 R_\Gamma:=\{(x_n)\in\prod_nE_n:(x_{n+1},x_n)\in\Gamma_n\text{ for all }n\}.
\]

For $A=\varprojlim A_n$ and
$J_{\rm loc}=\{(a_n)\in A:a_n\in J_n\ \forall n\}$, the exact universal law is

\[
 \boxed{0\longrightarrow A/J_{\rm loc}\longrightarrow R_\Gamma
 \xrightarrow{\delta}H^1(C^\bullet_{\rm mig})\longrightarrow0.} \tag{MR}
\]

Map $\delta$ sends a relational family to mismatch class of arbitrary representatives.
When every link has zero escape, $M_n=J_n$, $R_\Gamma=\varprojlim E_n$, and `(MR)` is exactly
paper's Roos sequence. Local-envelope minimality then kills $H^1=\varprojlim^1J_n$.

## Frozen simplicial coefficient law

`[PROVED HERE — FROZEN BEFORE PROOF 2026-08-04]` Let
\(A_i=C_u^*(S_i)\) be any small diagram of universal covers whose arrows
\(\alpha_f:A_i\twoheadrightarrow A_j\) come from complete-order quotients. For a composable
nondegenerate string

\[
 \sigma=(i_0\xrightarrow{f_1}i_1\to\cdots\xrightarrow{f_p}i_p)
\]

put

\[
 \mathcal A(\sigma)=A_{i_p},\qquad
 \mathcal M(\sigma)=\sum_{k=0}^{p}\alpha_{p:k}(J_{i_k}),\qquad
 \mathcal Q(\sigma)=\mathcal A(\sigma)/\mathcal M(\sigma). \tag{SC}
\]

For a nonterminal face, omission of one vertex removes one summand from the join and induces the
quotient map into `(SC)`. For the terminal face, the last epimorphism transports the prefix join
into `(SC)`. These maps should make \(\mathcal M\subset\mathcal A\) and \(\mathcal Q\) canonical
coefficient systems on the nerve and give a short exact sequence

\[
 0\longrightarrow C^\bullet(\mathcal M)
 \longrightarrow C^\bullet(\mathcal A)
 \longrightarrow C^\bullet(\mathcal Q)\longrightarrow0. \tag{SET}
\]

Hence there is a natural long exact sequence

\[
 \cdots\to H^k(\mathcal A)\to H^k(\mathcal Q)
 \xrightarrow{\partial}H^{k+1}(\mathcal M)
 \to H^{k+1}(\mathcal A)\to\cdots. \tag{LES}
\]

At vertices \(\mathcal Q(i)=C_e^*(S_i)\). On an edge \(f:i\to j\),

\[
 \mathcal Q(f)=A_j/(J_j+\alpha_fJ_i),
\]

and the degree-zero cocycle condition is exactly
\((x_i,x_j)\in\Gamma_f\). Therefore \(H^0(\mathcal Q)\) is the algebra of compatible envelope
correlations. For the one-dimensional semisimplicial path, \(H^1(\mathcal A)=0\) by recursive
lifting along the universal epimorphisms, and `(LES)` reduces to `(MR)`. This is the universal
law of which
escape, deficit, oplax composition, inverse-limit continuity, and derived Shilov acyclicity are
low-dimensional shadows.

Unlike ordinary ideal Čech theory, \(\mathcal M(\sigma)\) lives in changing universal covers and its
face maps mix ideal inclusion with quotient transport.

**Coefficient-system proof.** Work first with an oriented semisimplicial quotient diagram \(K\):
each ordered simplex \(\sigma=[i_0,\ldots,i_p]\) carries compatible composite universal
epimorphisms \(\alpha_{l:k}:A_{i_k}\to A_{i_l}\). The nerve of a quotient category is one example;
a bare quotient path is its one-dimensional semisimplicial version.

For the face \(\partial_k\sigma\), define the coface map into the coefficient at \(\sigma\) as
follows. If \(k<p\), the terminal algebra is unchanged and the map on \(\mathcal A\) is the
identity. The face join omits precisely the transported ideal from \(i_k\), so
\(\mathcal M(\partial_k\sigma)\subseteq\mathcal M(\sigma)\). If \(k=p\), use the last universal
epimorphism \(\alpha_{p:p-1}\); it sends the prefix join into the full join. These maps induce the
maps on \(\mathcal Q\).

Every two iterated cofaces agree. Away from the terminal face both maps are ideal inclusions. When
a terminal face occurs, equality is the identity

\[
 \alpha_{p:p-2}=\alpha_{p:p-1}\alpha_{p-1:p-2},
\]

which follows from uniqueness of universal extensions. Thus the alternating coface sum squares to
zero and \(\mathcal M,\mathcal A,\mathcal Q\) are coefficient systems. At every simplex,

\[
 0\to\mathcal M(\sigma)\to\mathcal A(\sigma)\to\mathcal Q(\sigma)\to0
\]

is exact. Taking products over \(p\)-simplices is exact in complex vector spaces, and the coface
maps commute with inclusion and quotient. This proves `(SET)`; the standard connecting-map
argument proves `(LES)`. The construction is also compatible with involution.

The join completion is minimal. If \(\mathcal N\subseteq\mathcal A\) is any coefficient subsystem
whose value at vertex \(i\) contains \(J_i\), then transport along the inclusion of each vertex
face \(i_k\subset\sigma\) forces

\[
 \alpha_{p:k}(J_{i_k})\subseteq\mathcal N(\sigma).
\]

Hence \(\mathcal M(\sigma)\subseteq\mathcal N(\sigma)\). Equivalently, \(\mathcal Q\) is the
largest quotient coefficient system whose vertex values are the \(C^*\)-envelopes.

In degree zero, the edge equation in \(C^\bullet(\mathcal Q)\) is

\[
 a_j+M_f=\alpha_f(a_i)+M_f.
\]

By `(PB)`, this is precisely the condition that the two endpoint classes lie in
\(\Gamma_f\). Hence \(H^0(\mathcal Q)\) is exactly the compatible-correlation algebra.

For the one-dimensional inverse path, the ambient differential is

\[
 d_{\mathcal A}((a_n))=(a_n-\alpha_n(a_{n+1}))_n.
\]

It is onto: start with \(a_0=0\) and lift recursively along the surjective \(\alpha_n\). Therefore
\(H^1(\mathcal A)=0\), while

\[
 H^0(\mathcal A)=\varprojlim A_n,\qquad
 H^0(\mathcal M)=J_{\rm loc},\qquad
 H^0(\mathcal Q)=R_\Gamma.
\]

The degree-zero part of `(LES)`, after quotienting its first map, is exactly `(MR)`. For an
infinite diagram this assertion is algebraic; \(H^1\) need not be Hausdorff unless the coboundary
range is closed. In the transmutation theorem below it is canonically the Banach space \(D\), and
in the zero-escape local-envelope theorem it vanishes, so both principal applications are
Hausdorff. ∎

## Claimed shadows

1. Escape is vertical/multivalued ideal $\ker p_S$ of `(EC)`.
2. Deficit is unforced quotient of opposite vertical kernel in `(VE)`.
3. Zero escape is functional graph locus; this recovers maximal envelope-functorial category.
4. Positive matricial lifting follows from both coordinate epimorphisms of $\Gamma_q$.
5. Paper's composition sequence is a three-vertex face of `(J)`.
6. Prescribed deficits are graded pieces of monotone transported-ideal flags; downstream kernels
   erase pieces by paper's exact first-kernel formula.
7. Roos sequence, local envelope continuity, and derived acyclicity are countable shadows.
8. Boundary representations and faithful positive representations detect vertex and edge joins.

## Universal exact law — paper proof

`[PROVED HERE]` Let

\[
 \cdots\xrightarrow{q_2}S_2\xrightarrow{q_1}S_1\xrightarrow{q_0}S_0
\]

be an arbitrary countable inverse sequence of unital operator systems and complete-order
quotients. Write \(A_n=C_u^*(S_n)\), let
\(\alpha_n:A_{n+1}\twoheadrightarrow A_n\) be the universal epimorphism, and let
\(J_n\triangleleft A_n\) be the Shilov ideal. Then `(MR)` is an exact sequence of complex vector
spaces (and of involutive vector spaces). No zero-escape or zero-deficit assumption is required.

**Proof.** For \(x=(x_n)\in R_\Gamma\), choose arbitrary representatives
\(a_n\in A_n\) with \(a_n+J_n=x_n\). The correlation condition gives, for each \(n\), an element
\(b_{n+1}\in A_{n+1}\) such that

\[
 b_{n+1}-a_{n+1}\in J_{n+1},\qquad
 \alpha_n(b_{n+1})-a_n\in J_n.
\]

Consequently

\[
 c_n:=a_n-\alpha_n(a_{n+1})\in J_n+\alpha_n(J_{n+1})=M_n.
\]

Replacing \(a_n\) by \(a_n+j_n\), with \(j_n\in J_n\), replaces \(c\) by
\(c+d_{\rm mig}(j)\). Hence \(\delta(x)=[c]\) is well-defined. A coherent family
\((a_n)\in\varprojlim A_n\) has zero mismatch, so the coordinate quotient map factors through an
injective map \(A/J_{\rm loc}\to R_\Gamma\).

If \(\delta(x)=0\), then \(c_n=j_n-\alpha_n(j_{n+1})\) for some \(j_n\in J_n\). The corrected
representatives \(a_n-j_n\) are coherent and still represent \(x_n\); hence \(x\) lies in the
image of \(A/J_{\rm loc}\). Conversely every coherent family has zero class, proving exactness in
the middle. Finally, given an arbitrary \(c=(c_n)\in\prod M_n\), start with \(a_0=0\) and choose
recursively

\[
 \alpha_n(a_{n+1})=a_n-c_n.
\]

This is possible because every \(\alpha_n\) is surjective. Then
\((a_n+J_n)_n\in R_\Gamma\) and its mismatch is \(c\), so \(\delta\) is onto. ∎

The edge identities `(ED)` follow from the second isomorphism theorem:

\[
 (J_n+\alpha_nJ_{n+1})/J_n
 \cong \alpha_nJ_{n+1}/(J_n\cap\alpha_nJ_{n+1}),
\]

and symmetrically after quotienting by \(\alpha_nJ_{n+1}\). Thus escape and deficit are literally
the two quotient stalks of the same edge join.

## Universal transmutation theorem — paper proof

`[PROVED HERE]` Every unital \(C^*\)-algebra \(D\) occurs in one split two-edge
operator-system path simultaneously as

\[
 D\cong\Def(q_1)\cong\Esc(q_0)
 \cong (\Gamma_{q_0}\circ\Gamma_{q_1})/\Gamma_{q_0q_1}
 \cong H^1(C^\bullet_{\rm mig}), \tag{UT}
\]

where the third term means the vertical composition excess and the final two identifications are
canonical as involutive vector spaces. Both \(q_1,q_0\) split by ucp maps, \(q_1\) and the
composite \(q_0q_1\) have zero escape, while \(q_0\) has maximal correlation
\(\Gamma_{q_0}=C_e^*(S_1)\oplus C_e^*(S_0)\).

**Construction.** Put

\[
 S_0=D,\qquad S_1=D\oplus D,\qquad q_0(a,b)=\tfrac12(a+b).
\]

The diagonal \(d\mapsto(d,d)\) is a ucp section, so \(q_0\) is a split complete-order quotient.
For \(v=(1,-1)\in S_1\), the canonical correlation contains \((v,0)\), hence also
\((1,0)=(v,0)^*(v,0)\). Together with its unit this gives \((0,1)\); multiplying these central
projections against the generating graph shows

\[
 \Gamma_{q_0}=(D\oplus D)\oplus D.
\]

In particular \(\Esc(q_0)\cong D\), the full target vertical ideal.

Let \(K=C([0,1],D)\), \(I=\{f\in K:f(0)=0\}\), and
\(\lambda(t)=\frac12+\frac14t\). Define the ucp map

\[
 \Phi:D\oplus D\longrightarrow K,\qquad
 \Phi(a,b)(t)=\lambda(t)a+(1-\lambda(t))b.
\]

With \(B=(D\oplus D)\oplus K\) and \(r(x)=(x,\Phi(x))\), set

\[
 S_2=r(S_1)+(0\oplus I)\subset B,qquad
 q_1(r(x)+(0,i))=x.
\]

First coordinate projection and \(r\) are respectively a ucp quotient and ucp section; the sum is
closed because its inverse coordinate map is bounded. Thus \(q_1\) is a split complete-order
quotient with kernel \(0\oplus I\).

We next compute its envelope, rather than assume it. Since
\(\Phi(v)(t)=t/2\),

\[
 r(1)-r(v)^*r(v)=(0,1-t^2/4).
\]

The spectrum of this element in \(B\) is contained in
\(\{0\}\cup[3/4,1]\). Continuous functional calculus therefore gives the central projection
\(0\oplus1_K\in C^*(S_2)\). The second coordinates \(\Phi(S_1)\) contain all constant functions
from \(D\) and the central coordinate \(t\), so they generate \(K\). It follows that
\(C^*(S_2)=B\).

The graph subsystem \(r(S_1)\) has Shilov ideal \(0\oplus K\), since its quotient by that ideal is
the minimal cover \(D\oplus D\). Any boundary ideal for the larger subsystem \(S_2\) is therefore
contained in \(0\oplus K\). Complete isometry on the contained subspace \(0\oplus I\) forces its
intersection with \(0\oplus I\) to vanish. The ideal \(I\) is essential in \(K\): multiplying a
nonzero continuous section by a scalar function vanishing at \(0\) produces a nonzero member of
\(I\). Hence the boundary ideal is zero and

\[
 C_e^*(S_2)=B.
\]

The envelope map induced by \(q_1\) is first projection \(p:B\to D\oplus D\), so
\(\Esc(q_1)=0\). Its kernel is \(0\oplus K\), whereas the ideal generated by
\(\ker q_1=0\oplus I\) is \(0\oplus I\). The kernel formula gives

\[
 \Def(q_1)\cong K/I\cong D.
\]

The composite has the envelope epimorphism

\[
 \pi:B\longrightarrow D,\qquad \pi((a,b),f)=f(0),
\]

because \(\Phi(a,b)(0)=\frac12(a+b)\) and \(I(0)=0\). Thus
\(\Esc(q_0q_1)=0\) and \(\Gamma_{q_0q_1}\) is the graph of \(\pi\). On the other hand,
\(\Gamma_{q_1}\) is the graph of \(p\) and \(\Gamma_{q_0}\) is full, whence

\[
 \Gamma_{q_0}\circ\Gamma_{q_1}=B\oplus D
 \supsetneq \operatorname{graph}(\pi)=\Gamma_{q_0q_1}.
\]

The vertical quotient of this inclusion is \(D\). Already on this finite path,
\(R_\Gamma\cong B\oplus D\), while the coherent envelope image is
\(\operatorname{graph}(\pi)\). Exact law `(MR)` (with finite products) identifies the quotient
with \(H^1(C^\bullet_{\rm mig})\), and explicitly

\[
 [(b,d)]\longmapsto d-\pi(b)
\]

identifies it with \(D\) as an involutive vector space. This proves `(UT)`. ∎

The theorem is a transmutation law, not a size example: one and the same \(D\) changes role from
unlifted boundary mass, to multivalued envelope mass, to strict oplax composition excess, and
finally to degree-one migration cohomology, even though the composite quotient itself has zero
escape.

## Risky new consequences

1. `(VE)` applies when no canonical envelope map exists.
2. Every complete-order quotient has bidirectional positive matrix coupling through
   $M_k(\Gamma_q)_+$; escape measures target ambiguity over fixed source data.
3. Finite migration cohomology need not vanish: every unital \(C^*\)-algebra already
   occurs in degree one on a split two-edge path.
4. Direct-versus-staged transport has canonical domain transgression, separating annihilation from
   genuine boundary re-entry.
5. Every unital \(C^*\)-algebra is a migration-cohomology obstruction, even in a tower
   whose two-edge composite has a canonical envelope epimorphism.

## Closest parents and novelty residue

- Goursat/subdirect-product and pullback theory for `C*`-algebras;
- Weaver–Daws quantum relations and CP-map support relations;
- partial maps and restriction categories;
- Shilov ideals, boundary representations, and $C^*$-envelopes;
- distributive ideal lattices, Mayer–Vietoris/Čech complexes, and Roos derived limits.

Goursat theory classifies given subdirect product but does not construct `(EC)` from operator
system quotient or identify vertical ideals with escape and deficit. Quantum relations are
commutant bimodules, not subdirect envelope correlations. Restriction categories give partial-map
grammar but not join half, `(VE)`, or local-envelope completion. Novelty residue must be operator-
boundary conjunction `(EC)`–`(LES)` and consequence unavailable from any parent alone.

## Falsifiers

1. $\Gamma_q$ is not closed or coordinate projections are not surjective.
2. $\ker p_S$ fails to identify canonically with $\operatorname{Esc}(q)$.
3. Exact sequence `(VE)` fails without zero escape.
4. Relational composition is not closed/associative or fails `(OL)`.
5. Three-stage ambiguity formula `(J)` fails.
6. Universal epimorphisms fail to preserve finite ideal sums.
7. Simplicial face maps in `(SC)` fail a cosimplicial identity or `(SET)` is not exact.
8. Published source contains full Shilov correlation law and completion consequences.
9. New consequences collapse to paper's one-step formulas.
10. Universal transmutation construction fails to have the asserted envelopes, correlations, or
    degree-one quotient.
11. `(LES)` reduces to ordinary diagram cohomology without retaining any Shilov-specific datum.

## Gates
- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: `localMigrationSequence_shortExact`,
      `envelopeCorrelation_eq_correlationPullback`, `correlationVerticalTarget_exact`,
      `pathJoin_eq`, `simplicialJoinCochainShortComplex_shortExact`,
      `simplicialJoin_homology_exact₁`/`₂`/`₃`, `transmutationCohomologyEquiv`;
      `lake build GaloisForLFunctions.HTGeometry` green; axioms audited
- [ ] 3 → 4 publication-ready: standalone paper, novelty audit, hostile review

## Approach

1. Audit Goursat/pullback, quantum-relation, restriction-category, Shilov, Čech, and Roos parents.
2. Prove or kill each falsifier using ideal arithmetic and explicit function systems.
3. Derive arbitrary-quotient vertical extension and bidirectional matrix lifting.
4. Prove finite path and simplicial coefficient laws; isolate countable completion theorem.
5. Demand theorem not expressible from one-step escape/deficit alone.
6. Only after dependency-closed paper proof, formalize exact algebraic core in Lean.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** finite ideal Čech acyclicity does not imply migration
  acyclicity; the two-edge transmutation theorem gives arbitrary finite \(H^1\).
- **Strongest positive survivor:** minimal Shilov join completion and its correlation long exact
  sequence.
- **New insight:** envelope nonfunctoriality is repaired canonically by the least subdirect
  correlation generated by the quotient graph; boundary-specific cohomology is
  \(\operatorname{im}\partial\), not all coefficient cohomology.
- **Status:** dependency-closed paper proof; external priority audit remains active.

## Log
- 2026-08-04 — partial-transport truth-hunch frozen before proof search.
- 2026-08-04 — partial-map-only route demoted as `[BRIDGE]`; correlation join law promoted after
  arbitrary-quotient vertical extension and finite-path formulas emerged.
- 2026-08-04 — countable migration exact law proved directly by representative correction and
  recursive lifting; no escape hypothesis used.
- 2026-08-04 — arbitrary noncommutative transmutation theorem proved: deficit becomes escape,
  strict oplax composition excess, and migration \(H^1\), while the composite has zero escape.
- 2026-08-04 — false slogan retired: finite ideal-lattice Čech acyclicity does not imply finite
  migration acyclicity. Two-edge transmutation is a counterexample. Simplicial join-completion
  law `(SC)`–`(LES)` frozen before proof audit.
- 2026-08-04 — edge minimality and unconditional path short exact sequence formalized in
  `GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationLaw`; targeted Lean source and module
  builds pass, with only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-05 — `(EC)`, `(PB)`, `(FQ)`, edge minimality, the vertical extension `(VE)`, and
  bidirectional entrywise matricial coupling formalized in
  `GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationPullback`.  Relational composition,
  its associativity, the exact one-step ambiguity composition law, `(OL)`, the path composition
  law `(PC)`, and the path ambiguity join law `(J)` formalized in
  `GaloisForLFunctions.HTGeometry.ShilovCorrelationPathJoin`.  Both modules compile
  unconditionally; `(SC)`/`(SET)`/`(LES)` and the algebraic core of `(UT)` remain.
- 2026-08-05 — `(SC)` formalized for the nerve of an arbitrary small diagram in
  `GaloisForLFunctions.HTGeometry.ShilovSimplicialJoinSystem`: the transported boundary join is a
  coefficient system, it is the least one with the prescribed vertex values, and its degree-zero
  edge condition is exactly membership in the envelope correlation of that edge.  `(SET)` and
  `(LES)` formalized in `GaloisForLFunctions.HTGeometry.ShilovSimplicialJoinCohomology`: the three
  coefficient systems are cosimplicial modules, their alternating coface complexes form a short
  exact sequence of cochain complexes, and the connecting map with its three exactness statements
  is the long exact sequence.  The algebraic core of `(UT)` formalized in
  `GaloisForLFunctions.HTGeometry.ShilovTransmutationTower`: on one explicit two-edge tower an
  arbitrary prescribed module is simultaneously the upper deficit, the lower escape, the strict
  composition excess, and degree-one migration cohomology, while the upper link and the composite
  are both escape-free.  All headline declarations audited with `#print axioms`; they use only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Lean formalization map

| Paper item | Lean declaration | Module |
|---|---|---|
| `(EC)` | `envelopeCorrelation` | `ShilovEnvelopeCorrelationPullback` |
| `D_q` | `ker_correlationMap` | `ShilovEnvelopeCorrelationPullback` |
| `(PB)` | `envelopeCorrelation_eq_correlationPullback` | `ShilovEnvelopeCorrelationPullback` |
| minimal join | `edgeJoin_least` | `ShilovEnvelopeCorrelationPullback` |
| `(FQ)` | `escapeEdgeQuotientEquiv`, `deficitEdgeQuotientEquiv` | `ShilovEnvelopeCorrelationPullback` |
| `(VE)` source half | `correlationSourceKernelEquivEscape` | `ShilovEnvelopeCorrelationPullback` |
| `(VE)` target half | `correlationTargetKernelEquiv`, `ker_correlationDeficitMap`, `correlationDeficitMap_surjective`, `correlationVerticalTarget_exact` | `ShilovEnvelopeCorrelationPullback` |
| matricial lifting | `exists_entrywise_correlation_lift_source`, `exists_entrywise_correlation_lift_target` | `ShilovEnvelopeCorrelationPullback` |
| relational composition | `relationalComp`, `relationalComp_assoc` | `ShilovCorrelationPathJoin` |
| one-step composition law | `relationalComp_ambiguousCorrelation`, `relationalComp_envelopeCorrelation` | `ShilovCorrelationPathJoin` |
| `(OL)` | `envelopeCorrelation_comp_le_relationalComp`, `envelopeCorrelation_le_pathCorrelation` | `ShilovCorrelationPathJoin` |
| `(PC)` | `pathCorrelation_eq` | `ShilovCorrelationPathJoin` |
| `(J)` | `pathJoin_eq`, `pathCorrelation_zero_mem_iff` | `ShilovCorrelationPathJoin` |
| strict oplax criterion | `ambiguousCorrelation_eq_envelopeCorrelation_iff`, `relationalComp_eq_envelopeCorrelation_iff` | `ShilovCorrelationPathJoin` |
| `(MC)`, `(MR)` | `localMigrationSequence_shortExact` | `ShilovEnvelopeCorrelationLaw` |
| `(ED)` | `escapeEdgeQuotientEquiv`, `deficitEdgeQuotientEquiv` at a tower edge | `ShilovEnvelopeCorrelationPullback` |
| `(SC)` coefficient system | `simplexJoin`, `simplexJoin_map_le`, `isJoinCoefficientSystem_simplexJoin` | `ShilovSimplicialJoinSystem` |
| `(SC)` minimality | `simplexJoin_le_of_isCoefficientSystem` | `ShilovSimplicialJoinSystem` |
| vertex and edge values | `simplexJoin_zero`, `simplexJoin_one` | `ShilovSimplicialJoinSystem` |
| `H⁰(𝒬)` = compatible correlations | `edge_quotient_eq_iff_mem_envelopeCorrelation` | `ShilovSimplicialJoinSystem` |
| `(SET)` | `simplicialJoinCochainShortComplex_shortExact` | `ShilovSimplicialJoinCohomology` |
| `(LES)` | `simplicialJoinConnecting`, `simplicialJoin_homology_exact₁`, `simplicialJoin_homology_exact₂`, `simplicialJoin_homology_exact₃` | `ShilovSimplicialJoinCohomology` |
| `(UT)` deficit becomes escape | `transmutationDeficitEquiv`, `transmutationEscapeEquiv` | `ShilovTransmutationTower` |
| `(UT)` zero escape of link and composite | `transmutation_escapeFree_upper`, `transmutation_escapeFree_composite` | `ShilovTransmutationTower` |
| `(UT)` strict composition excess | `transmutation_relationalComp_ne`, `transmutationCompositionExcessEquiv` | `ShilovTransmutationTower` |
| `(UT)` degree-one obstruction | `transmutationCohomologyEquiv` | `ShilovTransmutationTower` |

The Lean layer is the exact algebraic core: coefficient modules and boundary submodules stand for
universal covers and Shilov ideals, and linear maps stand for universal `*`-epimorphisms.  No
operator-system, positivity, topology, closed-range, or Shilov-minimality assertion is assumed.
