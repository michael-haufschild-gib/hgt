# Spectral boundary migration and Shilov-exact local envelope descent

## Metadata

- Status: 2-fully-proven on paper after universal-law correction 2026-08-03
- Route: operator-system boundary theory
- Exact claim label: [THEOREM] [SHILOV_LIM_ONE_ACYCLICITY]
- Novelty status: [PLAUSIBLY NOVEL — PRIMARY-SOURCE AUDIT PASSED 2026-08-03]
- Paper-proof status: Theorems A--E and universal acyclicity dependency-closed; renewed hostile audit passed 2026-08-03
- Lean status: literal derived exact sequence, comparison criterion, composition, lifting, and faithful-kernel core compile; analytic local-envelope layer pending
- Open core: renew primary-source/hostile audit for countable continuity and prescribed-deficit cancellation, formalize analytic envelope layer, then write and hostile-review paper.

## Frozen exact claim

Let $q:S\to T$ be a complete order quotient between separable unital operator systems. Let

\[
  \alpha:C_u^*(S)\twoheadrightarrow C_u^*(T)
\]

be canonical surjective unital $*$-homomorphism between universal $C^*$-covers, and let $J_S\triangleleft C_u^*(S)$ and $J_T\triangleleft C_u^*(T)$ be Shilov ideals. Put

\[
 I_q:=\alpha(J_S)\cap J_T,
 \qquad
 \mathfrak E(q):=\alpha(J_S)/I_q,
 \qquad
 \mathfrak D(q):=J_T/I_q.
\]

Proposed theorem has three parts.

1. **Spectral boundary-migration criterion.** Following are equivalent:
   - $\mathfrak E(q)=0$, equivalently $\alpha(J_S)\subseteq J_T$;
   - $q$ extends to a surjective $*$-homomorphism
     $C_e^*(S)\twoheadrightarrow C_e^*(T)$;
   - every boundary representation of $T$, pulled back along $\alpha$, factors through $C_e^*(S)$;
   - under nc-state-space duality, every nc extreme boundary point of quotient state space lies in spectral closure of nc extreme boundary of source state space.

2. **Shilov-matricial lifting criterion.** Assuming equivalent conditions in part 1, following are equivalent:
   - $\mathfrak D(q)=0$, equivalently $\alpha(J_S)=J_T$;
   - $\alpha|_{J_S}:J_S\twoheadrightarrow J_T$ is a surjective $*$-homomorphism;
   - every positive element of every matrix algebra $M_r(J_T)$ has a positive lift in $M_r(J_S)$, with usual quotient-norm control;
   - target Shilov ideal contains no boundary direction invisible to source Shilov lifts.

3. **Universal derived Shilov-limit law.** Let
   $(S_n,\alpha_n)_{n\geq 1}$ be a countable inverse sequence of separable unital operator systems, put $A_n=C_u^*(S_n)$, and assume each
   $\alpha_n:A_{n+1}\twoheadrightarrow A_n$ is canonical map induced by a complete order quotient $S_{n+1}\twoheadrightarrow S_n$, with
   $\alpha_n(S_{n+1})=S_n$. Assume escape vanishes at every link, so
   $\alpha_n(J_{n+1})\subseteq J_n$. If
   $S=\varprojlim S_n\subseteq A=\varprojlim A_n$, then
   $J_{\mathrm{loc}}=\varprojlim J_n$ and there is a natural exact sequence
   \[
     0\longrightarrow C_{e,\mathrm{loc}}^*(S)
       \xrightarrow{\Theta}\varprojlim_n C_e^*(S_n)
       \xrightarrow{\partial}\varprojlim{}^1_n J_n
       \longrightarrow0,
   \]
   algebraically and continuously, where $\varprojlim{}^1J_n$ has its
   Roos-cokernel quotient topology.  In fact the Shilov system is always
   derived-acyclic:
   \[
     \varprojlim{}^1_nJ_n=0,
     \qquad
     C_{e,\mathrm{loc}}^*(S)
       \cong\varprojlim_n C_e^*(S_n).
   \]
   This holds with no deficit hypothesis. Pulled-back stage boundary
   representations form a faithful local positive representation, while
   prescribed link deficits may be arbitrary separable unital
   $C^*$-algebras.

Claim is frozen at this universal strength. A proof may not replace spectral closure by ordinary closure, replace complete-order quotients by operator-space quotients, assume without proof that $\alpha(J_S)=J_T$, or confuse linkwise cokernels with the globally vanishing derived-limit obstruction.

## Why this is right hard problem

Complete-order quotients already provide $\varepsilon$-positive lifts at every matrix level. That information controls operator-system quotient but does not control which representations survive in $C^*$-envelope. Local Shilov theory likewise proves only

\[
  \overline{\pi_n(J_{\mathrm{loc}})}\subseteq J_n,
\]

not equality. Proposed defect pair separates two logically different failures hidden by a single word such as “compatibility”:

- $\mathfrak E(q)$: source Shilov elements become visible in target envelope;
- $\mathfrak D(q)$: target Shilov elements have no source Shilov lift.

Inverse-limit theorem exposes unexpected cancellation law: zero escape is
exact condition needed to form envelope tower, whereas deficits may be
arbitrary at every link yet Shilov ideal pro-system remains
\(\varprojlim^1\)-acyclic and local envelope commutes with limit.

## Pre-freeze killed strengthening

[FALSE] A split complete order quotient with a ucp section always extends to a quotient of $C^*$-envelopes.

Take $K=[-1,1]^2$, $L=\{0\}\times[-1,1]$, $S=A(K)$, and $T=A(L)$. Restriction $q:S\to T$ is a split complete order quotient; ucp section extends an affine function of $y$ constantly in $x$. Nevertheless,

\[
  C_e^*(S)=C(\operatorname{ext}K)=C(\{(\pm1,\pm1)\}),
  \qquad
  C_e^*(T)=C(\operatorname{ext}L)=C(\{(0,\pm1)\}).
\]

Any extending $*$-homomorphism would, by Gelfand duality, send each endpoint of $L$ to a vertex of $K$ while agreeing with evaluation of every affine function. Affine functions separate these points, forcing $(0,\pm1)$ to be vertices of $K$, contradiction. Thus split positivity, exact linear lifting, and all-level complete-order lifting do not prevent boundary migration.

### Positive survivor from failure

At scalar commutative level, restriction $A(K)\to A(L)$ can descend to Shilov envelopes only when every extreme point of $L$ lies in source Shilov boundary (or, without closedness, in appropriate spectral/Shilov closure). Boundary preservation, not existence of a positive section, is missing invariant.

## Internal prior-art audit

- formal/GaloisForLFunctions/HTGeometry/FaithfulSplitKadison.lean proves exact Kadison-defect annihilation from a faithful positive split map under explicit Schwarz hypotheses. It does not construct operator-system quotients or $C^*$-envelopes.
- docs/drafts/pipeline/1-in-progress/source-localization-modular-defect-conservation-law.md already names [XI_COFINAL_MATRICIAL_SOURCE_SATURATION], but does not construct its local operator system or prove Shilov base change.
- Same prior route already kills factorially expansive recovery as a Schwarz-positive map. Present route does not retry that false recovery arrow.
- Existing finite-clock Kadison modules are bridge infrastructure only; they do not address boundary migration.

## External state of art

- Kavruk--Paulsen--Todorov--Tomforde construct quotient operator systems by Archimedeanization and prove universal property. Operator-system quotient matrix norms can differ from operator-space quotient norms.
- Han characterizes complete order quotient maps by $\varepsilon$-positive matricial lifting and, for complete operator systems, by dual complete-order embeddings.
- Kennedy--Kim--Manor identify operator-system quotients with nc convex subsets and realize minimal $C^*$-covers through nc extreme boundaries. Their spectral-closure criterion detects when an irreducible point representation factors through minimal cover.
- Klep--Štrekelj prove matrix extreme points of matrix multifaces remain matrix extreme in ambient matrix convex set. This is weaker than spectral boundary condition needed for $C^*$-envelope descent.
- Joiţa constructs local Shilov ideal as intersection of local boundary-representation kernels. Her proof yields only coordinate inclusion into stage Shilov ideals.
- Joiţa--Şimon characterize Fréchet local Shilov ideal by $\Gamma$-boundary representations. They do not give a complete-quotient, ideal-lifting, or inverse-limit $C^*$-envelope exactness theorem.
- Koot proves minimal tensor products commute with $C^*$-envelopes; this is tensorial, not quotient or inverse-limit functoriality.

## Hostile falsity audit

1. **Chosen cover dependence.** Parts 1--2 use universal $C^*$-covers. Any arbitrary-cover version must transport defects and prove invariance.
2. **Boundary versus spectral boundary.** Ordinary inclusion of boundary representations is too strong in non-type-I settings. Factorization is governed by spectral closure.
3. **Operator-space confusion.** A complete quotient in operator-space norm need not identify operator-system quotient unless required hypotheses are checked.
4. **False split recovery.** A ucp section alone cannot imply envelope descent; square-to-segment example forbids it.
5. **Local coordinate gap.** Equality $\overline{\pi_n(J_{\mathrm{loc}})}=J_n$ is false as a necessary condition and is not used. Global envelope uniqueness replaces coordinatewise lifting.
6. **Inverse-limit trap.** Surjectivity of $A_{n+1}\to A_n$ does not by itself make restricted Shilov maps surjective. Exact Roos sequence must be proved first; stage-envelope minimality then forces its $\varprojlim^1$ term to vanish globally.
7. **Faithfulness overclaim.** A direct sum of target boundary representations is faithful only after quotienting by target Shilov ideal. Local statement must compute its kernel exactly.
8. **Novelty risk.** Parts of proof are short ideal/factorization arguments once formulated. Publication significance depends on countable continuity of maximal envelope functor, derived acyclicity despite arbitrary prescribed link deficits, spectral identification, and noncommutative realizability—not on repackaging kernel inclusion.

## Proof obligations

- [x] Verify canonical universal-cover map for every complete order quotient and its exact kernel.
- [x] Prove part 1 in both ideal and nc spectral language.
- [x] Prove part 2 at every matrix level, including quotient-norm control.
- [x] Prove inverse-limit comparison by an explicit coherent-lift argument.
- [x] Replace false pointwise converse by literal Roos exact sequence and prove Shilov $\varprojlim^1$-acyclicity.
- [x] Realize arbitrary prescribed sequences of separable unital $C^*$-algebras as link deficits with global cancellation.
- [x] Compute kernel of local boundary direct sum and prove faithfulness.
- [x] Construct explicit split commutative examples with nonzero escape defect.
- [x] Determine whether deficit can be nonzero when escape vanishes: yes, even for split commutative complete order quotients.
- [x] Audit citation ancestry and post-2021 descendancy for exact defect pair and local comparison theorem.
- [x] Run renewed hostile paper-proof and novelty review for universal acyclicity before Stage 2.

## Resolved hard branch: independent deficit

[NEW RESULT — PAPER PROOF] Escape can vanish while deficit is nonzero, even for a split complete order quotient of separable commutative operator systems.

Let \(K=\overline{\mathbb D}\subset\mathbb R^2\), let
\(T=A(K)\), and let \(E=\partial\mathbb D\). Choose a closed disk
\(Z\subset\operatorname{int}K\), a nonempty closed subset
\(F\subset Z\) with empty interior in \(Z\), and put
\(U=Z\setminus F\). Since \(E\) and \(Z\) are disjoint compact sets,

\[
  B=C(E\sqcup Z)=C(E)\oplus C(Z).
\]

Let \(r:T\to B\) be restriction to \(E\sqcup Z\), let

\[
  I_F=\{f\in C(Z):f|_F=0\},
  \qquad
  S=r(T)+(0\oplus I_F)\subset B,
\]

and define \(q:S\to T\) by

\[
  q\bigl(r(t)+(0,f)\bigr)=t.
\]

Then:

1. \(r(T)\) contains constants, is self-adjoint, and separates points of
   \(E\sqcup Z\), so \(C^*(S)=C^*(r(T))=B\) by Stone--Weierstrass.
2. Restriction \(T\to C(E)\) is canonical complete-order embedding
   into \(C_e^*(T)=C(E)\). Hence \(q\) is ucp, \(r:T\to S\) is ucp, and
   \(q\circ r=\mathrm{id}_T\). Thus \(q\) is a split complete order
   quotient.
3. \(\ker q=0\oplus I_F\).
4. Every point of \(E\) is a peak point for \(S\), using an affine
   supporting function of the disk.
5. Every \(z\in U\) is a peak point for \(S\). For example,
   \[
     f_z(w)=
       \frac{d(w,F)}
            {d(w,F)+d(w,z)}
   \]
   lies in \(I_F\), equals \(1\) at \(z\), and is strictly less than
   \(1\) elsewhere.
6. Since \(U\) is dense in \(Z\) and Shilov boundary is closed,
   Shilov boundary of \(S\) is all of \(E\sqcup Z\). Therefore
   \(C_e^*(S)=B\).
7. Envelope extension is projection
   \[
     \bar q:B=C(E)\oplus C(Z)\twoheadrightarrow C(E),
   \]
   so escape vanishes and \(\ker\bar q=0\oplus C(Z)\).
8. Ideal of \(C_e^*(S)\) generated by \(\ker q\) is
   \(0\oplus I_F\), a proper essential ideal of
   \(0\oplus C(Z)\).

General deficit identification below therefore gives

\[
  \mathfrak D(q)
    \cong
  \ker\bar q\big/\operatorname{Ideal}_{C_e^*(S)}(\ker q)
    \cong
  C(Z)/I_F
    \cong
  C(F).
\]

Taking \(F=\{0\}\) gives one-dimensional nonzero deficit. Taking a
Cantor subset gives infinite-dimensional deficit. Thus deficit size is
not controlled by split positivity or complete-order lifting.

### Universality of commutative deficits

[THEOREM — PAPER PROOF] Every separable unital commutative
\(C^*\)-algebra occurs as deficit of a split complete order quotient
whose escape vanishes.

Let \(F\) be any nonempty compact metrizable space. Put

\[
  Z_0=F\times[0,1],
  \qquad
  F_0=F\times\{0\},
  \qquad
  Y=Z_0\times\{0,1\}.
\]

For \(z\in Z_0\), define mixed state on \(C(Y)\) by

\[
  \mu_z
    =
  \tfrac12\delta_{(z,0)}
    +
  \tfrac12\delta_{(z,1)}.
\]

Let \(E=\{\delta_y:y\in Y\}\) and
\(Z=\{\mu_z:z\in Z_0\}\). These are disjoint compact subsets of state
space of \(T=C(Y)\). Distinct states are separated by elements of
\(C(Y)\), so evaluation map

\[
  r:T\to C(E\sqcup Z)
\]

has \(C^*\)-generating range by Stone--Weierstrass. Set

\[
  I_{F_0}
    =
  \{f\in C(Z):f|_{F_0}=0\},
  \qquad
  S=r(T)+(0\oplus I_{F_0}).
\]

This sum is closed: pure-state component gives
\(\|t\|\leq\|r(t)+(0,f)\|\), and then
\(\|f\|\leq2\|r(t)+(0,f)\|\). Hence \(S\) is an operator system.
Projection to pure-state component defines split complete order
quotient \(q:S\to T\) with section \(r\). Every point of \(E\) peaks:
choose a continuous function on metrizable \(Y\) peaking at
corresponding \(y\); its value at every selected mixed state is
strictly smaller. Every point of
\(Z\setminus F_0\) peaks using \(I_{F_0}\). Since
\(Z\setminus F_0\) is dense in \(Z\), Shilov boundary of \(S\) is all
of \(E\sqcup Z\). Hence

\[
  C_e^*(S)=C(E)\oplus C(Z),
  \qquad
  C_e^*(T)=C(E),
\]

escape vanishes, and algebraic deficit formula gives

\[
  \mathfrak D(q)
    \cong
  C(Z)/I_{F_0}
    \cong
  C(F_0)
    \cong
  C(F).
\tag{13}
\]

Thus deficit is a representation-complete invariant: even under ucp
splitting and exact all-level operator-system lifts, it can carry
arbitrary compact metrizable topology.

### Full noncommutative universality

[THEOREM — PAPER PROOF] Every separable unital \(C^*\)-algebra occurs
as deficit of a split complete order quotient with zero escape.

Let

\[
  \mathcal T_\infty
    =
  \overline{\operatorname{span}}
  \{1,u_j,u_j^*:j\geq1\}
    \subset
  C^*(\mathbb F_\infty),
\]

where \(u_j\) are canonical free unitaries. This operator system is
coproduct of countably many copies of
\(\operatorname{span}\{1,z,z^*\}\subset C(\mathbb T)\). It contains
enough unitaries, so

\[
  C_e^*(\mathcal T_\infty)=C^*(\mathbb F_\infty).
\tag{13a}
\]

Neither assertion hides an infinite-coproduct hypothesis. The finite
subsystem
\(\mathcal T_n=\operatorname{span}\{1,u_j,u_j^*:1\leq j\leq n\}\)
is the coproduct of \(n\) copies of the universal operator system of
one contraction. Compatible ucp maps on the \(\mathcal T_n\)'s are
contractive and therefore extend uniquely to \(\mathcal T_\infty\).
The canonical unitaries contained in \(\mathcal T_\infty\) generate
\(C^*(\mathbb F_\infty)\); the enough-unitaries theorem therefore gives
(13a).

Let \(D\) be separable unital \(C^*\)-algebra and set

\[
  K=C([0,1],D),
  \qquad
  I=C_0((0,1],D)=\{f\in K:f(0)=0\}.
\]

Ideal \(I\) is essential in \(K\): if nonzero ideal \(H\triangleleft K\)
contains \(h\neq0\), continuity gives \(t>0\) with \(h(t)\neq0\);
multiplication by scalar function supported near \(t\) produces
nonzero element of \(H\cap I\).

Choose contractions \(k_j\in K\) with \(k_1=0\) and
\(C^*(1,k_2,k_3,\ldots)=K\). Coproduct universal property gives ucp
map

\[
  \Phi:\mathcal T_\infty\to K,
  \qquad
  \Phi(u_j)=k_j.
\tag{13b}
\]

Put

\[
  B=C^*(\mathbb F_\infty)\oplus K,
  \qquad
  r(t)=(t,\Phi(t)).
\]

Although \(r\) is only ucp on operator system, its range generates
all of \(B\). Indeed,

\[
  r(u_1)^*r(u_1)-r(1)=(0,-1_K),
\]

so \(C^*(r(\mathcal T_\infty))\) contains central projection
\((0,1_K)\). It then contains \((0,k_j)\) for every \(j\), hence
\(0\oplus K\); subtracting second coordinates from \(r(t)\) gives
\(C^*(\mathbb F_\infty)\oplus0\). Thus

\[
  C^*(r(\mathcal T_\infty))=B.
\tag{13c}
\]

Now define

\[
  S=r(\mathcal T_\infty)+(0\oplus I)\subset B
\]

and

\[
  q:S\to\mathcal T_\infty,
  \qquad
  q(r(t)+(0,i))=t.
\]

First coordinate shows sum is closed, \(q\) is ucp,
\(r:\mathcal T_\infty\to S\) is ucp, and \(q\circ r=\mathrm{id}\).
Hence \(q\) is split complete order quotient and
\(\ker q=0\oplus I\).

It remains to compute source envelope. Shilov ideal of
\(r(\mathcal T_\infty)\) in cover \(B\) is \(0\oplus K\), because
projection \(B\to C^*(\mathbb F_\infty)\) is envelope quotient by
(13a). If \(H\triangleleft B\) is boundary ideal for larger system
\(S\), then it is boundary ideal for
\(r(\mathcal T_\infty)\), so \(H\subseteq0\oplus K\). Complete
isometry on \(S\) forces

\[
  H\cap(0\oplus I)=0.
\]

Essentiality of \(I\) gives \(H=0\). Therefore

\[
  C_e^*(S)=B.
\tag{13d}
\]

Envelope map induced by \(q\) is first projection, with kernel
\(0\oplus K\), while ideal generated by operator-system kernel is
\(0\oplus I\). Algebraic deficit formula yields

\[
  \mathfrak E(q)=0,
  \qquad
  \mathfrak D(q)
    \cong
  K/I
    \cong
  D.
\tag{13e}
\]

Thus deficit realizes arbitrary separable unital noncommutative ideal
structure, representation theory, and \(K\)-theory. No dimensional,
nuclearity, or type-I bound can follow from split complete-order
lifting alone.

## Tower universality and cancellation at infinity

[THEOREM E — PAPER PROOF] Let \((D_m)_{m\geq1}\) be any sequence of
separable unital \(C^*\)-algebras. There is a countable inverse tower

\[
  \cdots\twoheadrightarrow S_3\twoheadrightarrow S_2
  \twoheadrightarrow S_1=\mathcal T_\infty
\tag{13f}
\]

of separable unital operator systems such that every bonding map is a
split complete order quotient with zero escape,

\[
  \mathfrak D(S_{m+1}\to S_m)\cong D_m,
\tag{13g}
\]

and nevertheless

\[
  C_{e,\mathrm{loc}}^*(\varprojlim S_m)
  \cong \varprojlim C_e^*(S_m).
\tag{13h}
\]

Thus even an arbitrary prescribed sequence of nonzero, noncommutative
link deficits can cancel globally. Pointwise deficits are presentation
data; the derived Shilov class is the universal obstruction.

Proof. Partition the free generators of \(\mathcal T_\infty\) into an
infinite sentinel set \(\{u_{s_m}:m\geq1\}\) and countably infinite
blocks \(G_m\). Set

\[
  K_m=C([0,1],D_m),\qquad
  I_m=\{f\in K_m:f(0)=0\}.
\]

As above, \(I_m\) is essential and \(K_m/I_m\cong D_m\). For every
\(m\), choose contractions \(k_{m,j}\in K_m\) so that

1. \(k_{m,s_m}=0\);
2. \(k_{m,s_\ell}=1\) for every \(\ell>m\);
3. \(\{k_{m,j}:j\in G_m\}\) generates \(K_m\) unitally.

The coproduct property of \(\mathcal T_\infty\) gives a ucp map
\(\Phi_m:\mathcal T_\infty\to K_m\) with
\(\Phi_m(u_j)=k_{m,j}\).

We construct recursively a cover \(B_m=C_e^*(S_m)\), a split complete
order quotient \(p_m:S_m\to\mathcal T_\infty\), and a ucp section
\(r^{(m)}:\mathcal T_\infty\to S_m\). Start with

\[
  B_1=C^*(\mathbb F_\infty),\quad
  S_1=\mathcal T_\infty,\quad p_1=r^{(1)}=\mathrm{id}.
\]

Given stage \(m\), put \(\Psi_m=\Phi_m\circ p_m\) and

\[
  B_{m+1}=B_m\oplus K_m,
  \qquad
  S_{m+1}
    =\{(x,\Psi_m(x)):x\in S_m\}+(0\oplus I_m).
\tag{13i}
\]

First-coordinate projection \(q_m:S_{m+1}\to S_m\) is a split
complete order quotient, with graph section. Set
\(p_{m+1}=p_m\circ q_m\) and let \(r^{(m+1)}\) be the composite of the
old section with the graph section. The sum in (13i) is closed: its
first coordinate controls \(\|x\|\), and then
\(\|i\|\leq2\|(x,\Psi_m(x)+i)\|\).

For the sentinel \(v_m=r^{(m)}(u_{s_m})\), all earlier sentinel
coordinates equal unitaries by condition 2, so \(v_m\) is a unitary in
\(B_m\), while \(\Psi_m(v_m)=0\). Hence

\[
  (v_m,0)^*(v_m,0)-(1_{B_m},1_{K_m})=(0,-1_{K_m})
\]

belongs to the algebra generated by the graph. Conditions 2--3 then
show that the graph generates \(B_m\oplus K_m\).

The graph copy of \(S_m\) has Shilov ideal \(0\oplus K_m\). If
\(H\triangleleft B_m\oplus K_m\) is a boundary ideal for the larger
system \(S_{m+1}\), then \(H\subseteq0\oplus K_m\). Complete isometry
on the contained subspace \(0\oplus I_m\) gives
\(H\cap(0\oplus I_m)=0\). Essentiality of \(I_m\) forces \(H=0\).
Thus

\[
  C_e^*(S_{m+1})=B_m\oplus K_m.
\]

The induced envelope map is first projection. Its kernel is
\(0\oplus K_m\), while the ideal generated by \(\ker q_m\) is
\(0\oplus I_m\). The algebraic deficit formula gives (13g), and
existence of the envelope projection gives zero escape.

Finally put \(B=\varprojlim B_m\) and \(S=\varprojlim S_m\). Surjective
bonding maps make every coordinate projection \(S\to S_m\) onto, so
\(S\) locally generates \(B\). If \(H\triangleleft B\) is a local
boundary ideal, closure of its \(m\)-th coordinate is a boundary ideal
for \(S_m\subset B_m=C_e^*(S_m)\), hence is zero. Therefore \(H=0\),
so \(B=C_{e,\mathrm{loc}}^*(S)\). Since also
\(B=\varprojlim C_e^*(S_m)\), (13h) follows. By Theorem B, the
associated universal Shilov ideal system has
\(\varprojlim{}^1J_m=0\) despite the prescribed deficits (13g).

## Algebraic deficit formula

[LEMMA — PAPER PROOF] Suppose escape vanishes and let
\(\bar q:C_e^*(S)\twoheadrightarrow C_e^*(T)\) be induced envelope map.
Then

\[
  \mathfrak D(q)
    \cong
  \ker\bar q\big/
  \operatorname{Ideal}_{C_e^*(S)}(\iota_S(\ker q)).
\]

Proof skeleton:

1. Quotient universal property gives
   \[
     \ker\alpha
       =
     \operatorname{Ideal}_{C_u^*(S)}(\iota_u(\ker q)).
   \]
2. If \(\epsilon_S:C_u^*(S)\twoheadrightarrow C_e^*(S)\) is envelope
   quotient, then
   \[
     \epsilon_S(\ker\alpha)
       =
     \operatorname{Ideal}_{C_e^*(S)}(\iota_S(\ker q)).
   \]
3. Commutativity
   \(\bar q\circ\epsilon_S=\epsilon_T\circ\alpha\) yields
   \[
     \alpha^{-1}(J_T)=\epsilon_S^{-1}(\ker\bar q).
   \]
4. Two applications of third isomorphism theorem give
   \[
   \begin{aligned}
     J_T/\alpha(J_S)
       &\cong
     \alpha^{-1}(J_T)/(J_S+\ker\alpha)\\
       &\cong
     \ker\bar q/\epsilon_S(\ker\alpha).
   \end{aligned}
   \]

This converts abstract universal-cover deficit into concrete failure:
envelope kernel can strictly exceed ideal generated by operator-system
kernel.

## Paper proof of spectral and matricial criteria

[THEOREM A — PAPER PROOF] Let \(q:S\to T\) satisfy frozen
hypotheses. Then parts 1 and 2 of frozen claim hold.

### Universal-cover setup

Write

\[
  u_S:S\to C_u^*(S),\qquad
  u_T:T\to C_u^*(T)
\]

for universal embeddings and

\[
  \epsilon_S:C_u^*(S)\twoheadrightarrow C_e^*(S),\qquad
  \epsilon_T:C_u^*(T)\twoheadrightarrow C_e^*(T)
\]

for envelope quotients. Universal property gives unique
\(*\)-homomorphism \(\alpha\) satisfying

\[
  \alpha\circ u_S=u_T\circ q.
\]

It is surjective because its range contains \(u_T(q(S))=u_T(T)\),
which generates \(C_u^*(T)\). Since \(T\) is completely order
isomorphic to \(S/\ker q\), universal quotient theorem gives

\[
  \ker\alpha
    =
  \operatorname{Ideal}_{C_u^*(S)}(u_S(\ker q)).
\tag{1}
\]

### Escape and envelope descent

If \(\alpha(J_S)\subseteq J_T\), formula

\[
  \bar q(a+J_S)=\alpha(a)+J_T
\tag{2}
\]

defines a surjective \(*\)-homomorphism
\(C_e^*(S)\twoheadrightarrow C_e^*(T)\) extending \(q\).

Conversely, suppose \(\bar q:C_e^*(S)\to C_e^*(T)\) is a
\(*\)-homomorphism extending \(q\). Maps

\[
  \bar q\circ\epsilon_S,\qquad
  \epsilon_T\circ\alpha
\]

are \(*\)-homomorphisms from \(C_u^*(S)\) to \(C_e^*(T)\) agreeing on
generating set \(u_S(S)\), hence are equal. Therefore

\[
  a\in J_S
  \Longrightarrow
  \epsilon_T(\alpha(a))=0
  \Longrightarrow
  \alpha(a)\in J_T.
\]

Thus \(\mathfrak E(q)=0\) is equivalent to envelope descent.

### Escape and boundary representations

For separable \(T\), boundary representations determine Shilov ideal:

\[
  J_T
    =
  \bigcap_{\pi\in\operatorname{Ch}(T)}\ker\pi.
\tag{3}
\]

Consequently,

\[
\begin{aligned}
  \alpha(J_S)\subseteq J_T
  &\Longleftrightarrow
  J_S\subseteq\ker(\pi\circ\alpha)
  \quad\text{for every }\pi\in\operatorname{Ch}(T)\\
  &\Longleftrightarrow
  \pi\circ\alpha\text{ factors through }C_u^*(S)/J_S
  \quad\text{for every }\pi\in\operatorname{Ch}(T).
\end{aligned}
\tag{4}
\]

This is boundary-representation formulation.

### Spectral formulation

Let \((\mathcal K_S,0)\) and \((\mathcal K_T,0)\) be pointed compact nc
quasistate spaces. Dual of \(q\) identifies \(\mathcal K_T\) with
closed pointed nc convex subset of \(\mathcal K_S\). Under continuous
nc-function model,

\[
  C_u^*(S)=C(\mathcal K_S,0),
  \qquad
  C_e^*(S)=C(\partial\mathcal K_S,0),
\]

and similarly for \(T\). If \(y\in\partial\mathcal K_T\setminus\{0\}\),
pulled-back boundary representation is evaluation representation
\(\delta_y\) on \(C(\mathcal K_S,0)\). Spectral-closure theorem for
minimal covers states

\[
  \delta_y\text{ factors through }C(\partial\mathcal K_S,0)
  \Longleftrightarrow
  y\in\overline{\partial\mathcal K_S\setminus\{0\}}^{\,\mathrm{sp}}.
\tag{5}
\]

Apply (5) to every boundary point \(y\) and combine with (4). This
proves spectral boundary-migration criterion. Spectral closure is
essential; ordinary topology is not a substitute.

### Deficit and matricial Shilov lifting

Assume escape vanishes. Then

\[
  \mathfrak D(q)=J_T/\alpha(J_S).
\]

Hence deficit vanishes exactly when restriction

\[
  \alpha|_{J_S}:J_S\to J_T
\]

is surjective. A surjective \(*\)-homomorphism of \(C^*\)-algebras
remains surjective after every matrix amplification, and positive cone
of a \(C^*\)-quotient is image of positive cone. Thus for every
\(r\geq1\), every \(b\in M_r(J_T)_+\), and every \(\varepsilon>0\),
there is \(a\in M_r(J_S)_+\) such that

\[
  \alpha^{(r)}(a)=b,
  \qquad
  \|a\|\leq\|b\|+\varepsilon.
\tag{6}
\]

Conversely, positive lifting for \(r=1\) implies surjectivity: write
every self-adjoint element as difference of positive elements and every
element as linear combination of two self-adjoint elements. This proves
part 2.

## Paper proof of universal derived Shilov-limit law

[THEOREM B — PAPER PROOF] In setting of part 3, let \(J_n\) be Shilov
ideal of \(S_n\) in \(A_n=C_u^*(S_n)\), let

\[
  A=\varprojlim_n A_n,\qquad S=\varprojlim_n S_n,
\]

and let \(J_{\mathrm{loc}}\) be local Shilov ideal of \(S\) in \(A\).
Assume escape vanishes at every link. Then there is a canonical exact
sequence

\[
  0\longrightarrow A/J_{\mathrm{loc}}
    \xrightarrow{\Theta}\varprojlim_n A_n/J_n
    \xrightarrow{\partial}\varprojlim{}^1_nJ_n
    \longrightarrow0.
\tag{7}
\]

This sequence is algebraically exact and continuous when the last term
is assigned its Roos-cokernel quotient topology.  The map \(\Theta\) is
a Fréchet local \(C^*\)-isomorphism exactly when
\(\varprojlim{}^1J_n=0\).  In particular, linkwise zero deficit is a
sufficient Mittag--Leffler condition.  Stage boundary representations
produce a faithful local positive representation without assuming
linkwise zero deficit.

### Identification of local Shilov ideal

Zero escape gives

\[
  \alpha_n(J_{n+1})\subseteq J_n
\tag{8}
\]

for every \(n\). Local boundary-representation theorem and stage
identity (3) imply

\[
\begin{aligned}
  J_{\mathrm{loc}}
    &=
  \bigcap_{n\geq1}
  \bigcap_{\pi\in\operatorname{Ch}(S_n)}
  \ker(\pi\circ p_n)\\
    &=
  \{a=(a_n)\in A:a_n\in J_n\text{ for every }n\}\\
    &=
  \varprojlim_n J_n,
\end{aligned}
\tag{9}
\]

where \(p_n:A\to A_n\) is coordinate map.

There is also a representation-free maximality check, which closes a
possible local-boundary gap. Put

\[
  J^\infty=\{a\in A:p_n(a)\in J_n\text{ for every }n\}.
\]

For \(s\in M_r(S)\), quotienting the \(n\)-th coordinate by the
smaller ideal \(\overline{p_n(J^\infty)}\subseteq J_n\) gives a norm
bounded above by \(\|s_n\|\) and below by
\(\|s_n+M_r(J_n)\|=\|s_n\|\). Hence \(J^\infty\) is a local boundary
ideal. Conversely, if \(H\) is any local boundary ideal, then
\(\overline{p_n(H)}\) is a stage boundary ideal for \(S_n\), so
\(\overline{p_n(H)}\subseteq J_n\) for every \(n\). Thus
\(H\subseteq J^\infty\). This independently proves
\(J_{\mathrm{loc}}=J^\infty\).

If deficit also vanishes at every link, (8) is equality.  Restricted
ideal maps are then surjective; recursive lifting gives

\[
  p_n(J_{\mathrm{loc}})=J_n
\tag{10}
\]

for every \(n\).

### Zero-deficit corollary

Define

\[
  \Theta:A/J_{\mathrm{loc}}
    \longrightarrow
  \varprojlim_n A_n/J_n,
  \qquad
  \Theta(a+J_{\mathrm{loc}})=(a_n+J_n)_n.
\tag{11}
\]

Its kernel is zero by (9).

For surjectivity, take compatible cosets
\((b_n+J_n)_n\). Choose representative \(a_1=b_1\). Suppose
\(a_n\) has been chosen. Choose any representative \(c_{n+1}\) of
\(b_{n+1}+J_{n+1}\). Compatibility gives

\[
  \alpha_n(c_{n+1})-a_n\in J_n.
\]

By (8), choose \(d_{n+1}\in J_{n+1}\) with

\[
  \alpha_n(d_{n+1})
    =
  \alpha_n(c_{n+1})-a_n.
\]

Then \(a_{n+1}=c_{n+1}-d_{n+1}\) represents same coset and satisfies
\(\alpha_n(a_{n+1})=a_n\). Recursion yields \(a=(a_n)\in A\) with
\(\Theta(a+J_{\mathrm{loc}})=(b_n+J_n)_n\).

By (10), quotient seminorm at coordinate \(n\) on
\(A/J_{\mathrm{loc}}\) is exactly \(C^*\)-norm on \(A_n/J_n\).
Hence \(\Theta\) and inverse preserve every defining seminorm, proving
(7) as local \(C^*\)-isomorphism. No uniform norm control across
different \(n\) is required: Fréchet locally \(C^*\)-topology records
each coordinate seminorm separately.

### Boundary-migration cocycle and exactness

Put \(\phi_n=\alpha_n|_{J_{n+1}}\) and define the Roos difference

\[
  \Delta_J:\prod_{n\geq1}J_n\longrightarrow\prod_{n\geq1}J_n,
  \qquad
  \Delta_J((x_n))=(x_n-\phi_n(x_{n+1}))_n.
\tag{12a}
\]

By definition,

\[
  \varprojlim{}^1J_n=\operatorname{coker}\Delta_J.
\tag{12b}
\]

Let \((\dot b_n)_n\in\varprojlim A_n/J_n\), and choose arbitrary
representatives \(b_n\in A_n\). Compatibility gives

\[
  c_n=\alpha_n(b_{n+1})-b_n\in J_n.
\tag{12c}
\]

If representatives are changed to \(b_n+x_n\), the mismatch changes
from \(c\) to \(c-\Delta_Jx\). Hence

\[
  \partial((\dot b_n)_n)=[c]\in\varprojlim{}^1J_n
\tag{12d}
\]

is well defined and linear. Its class vanishes exactly when
\(c=\Delta_Jx\). In that case

\[
  a_n=b_n+x_n
\]

satisfies \(\alpha_n(a_{n+1})=a_n\), so \((\dot b_n)\) lies in the
image of \(\Theta\). Conversely, any coherent representative has zero
mismatch. This proves exactness at the middle term. The kernel of
\(\Theta\) is \(\varprojlim J_n=J_{\mathrm{loc}}\), proving injectivity.

Finally, \(\partial\) is onto. Given \(c=(c_n)\in\prod J_n\), choose
\(b_1=0\) and recursively choose \(b_{n+1}\) with

\[
  \alpha_n(b_{n+1})=b_n+c_n;
\]

this is possible because every universal-cover bonding map is
surjective. The quotient classes of \(b_n\) are compatible and have
mismatch \(c\). This proves (7).

Consequently,

\[
  \Theta\text{ is onto}
  \quad\Longleftrightarrow\quad
  \varprojlim{}^1J_n=0.
\tag{12e}
\]

The operator-system structure now forces the right side of (12e) for
every zero-escape tower. Put

\[
  B=\varprojlim_n C_e^*(S_n).
\]

The map \(S\to B\) is a local complete order embedding. Every coordinate
projection \(S\to S_n\) is onto by recursive lifting, and each \(S_n\)
generates its envelope. Hence \(S\) locally generates \(B\): a polynomial
approximation at coordinate \(n\) lifts generator by generator to \(S\)
and controls all earlier seminorms.

The local Shilov ideal of \(S\) in \(B\) is zero. Indeed, if
\(H\triangleleft B\) is a local boundary ideal, then
\(H_n=\overline{p_n(H)}\) is a boundary ideal for
\(S_n\subset C_e^*(S_n)\). Minimality of the stage envelope gives
\(H_n=0\) for every \(n\), hence \(H=0\). Thus \(B\) is a local
\(C^*\)-cover with trivial local Shilov ideal.

The quotient \(A/J_{\mathrm{loc}}\) is the other such cover. Local
\(C^*\)-envelope uniqueness implements the identity on \(S\) by a local
\(*\)-isomorphism

\[
  A/J_{\mathrm{loc}}\cong B.
\]

Both maps agree with coordinate envelope quotients on the generating
system \(S\), so this isomorphism is precisely \(\Theta\). Therefore

\[
  \varprojlim{}^1J_n=0
\tag{12f}
\]

for every Shilov system arising from a zero-escape complete-order
quotient tower. This is not formal Mittag--Leffler vanishing: the maps
\(J_{n+1}\to J_n\) may have arbitrary prescribed nonzero cokernels by
Theorem E. Boundary minimality forces their global Roos coboundary map
to be onto anyway. The abstract vector-space example with zero bonding
maps shows that linkwise nonsurjectivity and global \(\varprojlim^1\)
vanishing are logically independent; Theorem E realizes the separation
inside operator systems.

### Faithful local positive representation

For each \(n\), let

\[
  \rho_n=\bigoplus_{\pi\in\operatorname{Ch}(S_n)}\pi.
\]

Then \(\rho_n\) is a \(*\)-representation of \(A_n\) with kernel
\(J_n\), so it is faithful on \(A_n/J_n\). Let
\(\mathcal H_n\) be its Hilbert space, put

\[
  \mathcal H^{(N)}=\bigoplus_{n\leq N}\mathcal H_n,
  \qquad
  \mathcal D=\bigcup_N\mathcal H^{(N)},
\]

and define diagonal local representation by

\[
  \rho(a)|_{\mathcal H^{(N)}}
    =
  \bigoplus_{n\leq N}\rho_n(a_n).
\tag{12}
\]

Each finite restriction is bounded and positive. Its global kernel is

\[
  \ker\rho
    =
  \bigcap_n p_n^{-1}(J_n)
    =
  J_{\mathrm{loc}}
\]

by (9). Therefore (12) descends to faithful local
\(*\)-representation, hence faithful local completely positive
representation, of \(C_{e,\mathrm{loc}}^*(S)\).

### Representable K-theory consequence

Phillips' Milnor sequence for a \(\sigma\)-\(C^*\)-algebra, combined
with (12f), gives for \(i\in\mathbb Z/2\mathbb Z\) a natural exact
sequence

\[
  0\longrightarrow
  \varprojlim{}^1_n K_{i+1}(C_e^*(S_n))
  \longrightarrow
  RK_i(C_{e,\mathrm{loc}}^*(S))
  \longrightarrow
  \varprojlim_n K_i(C_e^*(S_n))
  \longrightarrow0.
\tag{12g}
\]

Thus boundary migration introduces no additional local-envelope
correction beyond the classical Milnor term of stage envelopes.
Theorem E shows this survives towers whose individual deficits carry
arbitrary prescribed ideal structure and K-theory.

## Maximal functorial category and composition law

[THEOREM C — FORCED CONSEQUENCE] Let
\(\mathbf{OS}_{\mathrm{adm}}\) have separable unital operator systems
as objects and zero-escape complete order quotients as morphisms.

1. \(\mathbf{OS}_{\mathrm{adm}}\) is a category.
2. \(S\mapsto C_e^*(S)\) and \(q\mapsto\bar q\) define a covariant
   functor from \(\mathbf{OS}_{\mathrm{adm}}\) to unital
   \(C^*\)-algebras and surjective \(*\)-homomorphisms.
3. It is maximal among subcategories of complete order quotient maps
   on which canonical \(C^*\)-envelope extension exists.
4. It preserves countable inverse limits after passage to Fréchet local
   \(C^*\)-envelopes:
   \[
     C_{e,\mathrm{loc}}^*(\varprojlim S_n)
       \cong\varprojlim C_e^*(S_n).
   \]
5. Zero-deficit morphisms form a wide subcategory
   \(\mathbf{OS}_{\mathrm{ex}}\subset\mathbf{OS}_{\mathrm{adm}}\).

Proof. Identity maps preserve Shilov ideals. For composable maps

\[
  S\xrightarrow{q}T\xrightarrow{r}U
\]

write \(\alpha,\beta\) for universal-cover maps. If

\[
  \alpha(J_S)\subseteq J_T,
  \qquad
  \beta(J_T)\subseteq J_U,
\]

then

\[
  (\beta\circ\alpha)(J_S)\subseteq J_U.
\]

Universal property identifies universal map of \(r\circ q\) with
\(\beta\circ\alpha\), so zero escape is closed under composition.
Formula (2) shows induced envelope maps compose and identities remain
identities. Maximality is converse direction of Theorem A: any
canonical envelope extension forces zero escape. Countable continuity
is Theorem B. If both maps have
zero deficit, then

\[
  (\beta\circ\alpha)(J_S)
    =
  \beta(J_T)
    =
  J_U,
\]

so zero deficit is also closed under composition.

[THEOREM D — DEFICIT COMPOSITION EXACTNESS] For composable
zero-escape morphisms as above, there is canonical exact sequence of
\(C^*\)-algebras

\[
  \mathfrak D(q)
    \xrightarrow{\ \beta_*\ }
  \mathfrak D(r\circ q)
    \longrightarrow
  \mathfrak D(r)
    \longrightarrow
  0,
\tag{14}
\]

where

\[
  \beta_*(x+\alpha(J_S))
    =
  \beta(x)+\beta\alpha(J_S).
\]

Indeed,

\[
\begin{aligned}
  \mathfrak D(q)
    &=J_T/\alpha(J_S),\\
  \mathfrak D(r\circ q)
    &=J_U/\beta\alpha(J_S),\\
  \mathfrak D(r)
    &=J_U/\beta(J_T).
\end{aligned}
\]

Natural quotient from middle term to final term is surjective and has
kernel

\[
  \beta(J_T)/\beta\alpha(J_S)
    =
  \operatorname{im}\beta_*.
\]

More precisely,

\[
  \ker\beta_*
    =
  \frac{\alpha(J_S)+(J_T\cap\ker\beta)}
       {\alpha(J_S)}.
\tag{15}
\]

Thus (14) becomes short exact after quotienting
\(\mathfrak D(q)\) by (15), and it is short exact as written whenever
\(J_T\cap\ker\beta\subseteq\alpha(J_S)\).

Equations (14)--(15) show exact mechanism by which one quotient can
erase part of earlier lifting deficit. In particular, Shilov-exact
morphisms compose, while nonzero deficits propagate by a controlled
right-exact law.

## Detection by faithful positive representations

Let \(\rho_T\) be direct sum of boundary representations of \(T\).
It is a \(*\)-representation of \(C_u^*(T)\) with kernel \(J_T\) and
is faithful on \(C_e^*(T)\). First isomorphism theorem gives

\[
  \mathfrak E(q)
    \cong
  \rho_T(\alpha(J_S))
    \triangleleft
  \rho_T(C_u^*(T))
    \cong
  C_e^*(T).
\tag{16}
\]

Thus escape is exactly source Shilov mass detected by faithful target
boundary representation. Under zero escape, deficit formula identifies
remaining obstruction as portion of envelope kernel not generated by
operator-system kernel. Together (16) and algebraic deficit formula
give faithful-positive representation interpretation of both defects.

## Universal-law audit correction (2026-08-03)

[WITHDRAWN AS UNIVERSAL CLAIM] The assertion in the converse paragraph that
global local-envelope exactness forces every individual restriction
αₙ|Jₙ₊₁ to be surjective is too rigid.  Linkwise zero deficit is a
strong sufficient Mittag--Leffler condition, not the universal invariant of
an inverse tower.  Later boundary coordinates can recover information lost
at one fixed coordinate, so a global locally C*-isomorphism need not preserve
the chosen stage seminorms term by term.

[THEOREM B — PAPER PROOF; ALGEBRAIC LEAN PROOF] For every countable zero-escape tower, define

\[
  \Delta_J:\prod_{n\geq1}J_n\longrightarrow\prod_{n\geq1}J_n,
  \qquad
  \Delta_J((x_n))=(x_n-\alpha_n(x_{n+1}))_n,
\]

and \(\varprojlim{}^1J_n:=\operatorname{coker}\Delta_J\) in complex
vector spaces (with its quotient locally convex structure when needed).
For a compatible family of envelope classes, arbitrary representatives
\(b_n\in A_n\) determine the boundary-migration cocycle

\[
  c_n=\alpha_n(b_{n+1})-b_n\in J_n.
\]

Changing representatives changes \((c_n)\) by an element of
\(\operatorname{ran}\Delta_J\).  The universal law is the
natural exact sequence

\[
  0\longrightarrow A/J_{\rm loc}
   \xrightarrow{\Theta}\varprojlim_n A_n/J_n
   \xrightarrow{\partial}\varprojlim{}^1J_n
   \longrightarrow0,
\]

using surjectivity of the cover maps to kill \(\varprojlim{}^1A_n\).
It identifies local C*-envelope exactness with vanishing of one global
derived Shilov class; linkwise deficits are its degree-zero presentation
data, and linkwise zero deficit kills it by recursive lifting.  Lean theorem
`stageBoundaryDerivedSequence_shortExact` proves the literal exact sequence,
and `localBoundaryComparison_surjective_iff` proves the vanishing
criterion without analytic axioms.  Card may return to Stage 2 only after
operator-system prescribed-deficit cancellation and renewed novelty audit
are closed.

## Falsifier

Route fails at publication strength if closer bibliographic search finds the
exact defect-pair classification, countable continuity of the maximal
zero-escape envelope functor, Shilov \(\varprojlim^1\)-acyclicity, or
arbitrary prescribed-deficit cancellation; if the recursive sentinel tower
does not generate every stage cover; or if analytic formalization exposes an
unrecorded hypothesis in local-envelope uniqueness or coordinate boundary
ideals.

## Next attack

Formalize analytic local-envelope layer over compiled literal Roos sequence.
Then move card to Stage 3, write paper around Theorems A--E and countably
continuous maximal envelope functor, and subject complete manuscript to hostile
general-journal review.

## Primary-source dependency and novelty audit (2026-08-03)

- Kavruk--Paulsen--Todorov--Tomforde, *Quotients, exactness, and
  nuclearity in the operator system category*, Theorem 3.7, supplies
  \(C_u^*(S/\ker q)\cong C_u^*(S)/\operatorname{Ideal}(\ker q)\).
- Han, *On maximal tensor products and quotient maps of operator
  systems*, supplies all-matrix \(\varepsilon\)-positive lifting
  criterion for complete order quotients.
- Farenick--Kavruk--Paulsen--Todorov, *Operator systems from discrete
  groups*, Proposition 4.1 and coproduct discussion, supplies universal
  contraction systems used in (13a)--(13b).
- Kavruk, *Nuclearity related properties in operator systems*,
  Proposition 5.6, supplies enough-unitaries computation of free-group
  \(C^*\)-envelope.
- Kennedy--Kim--Manor, *Nonunital operator systems and noncommutative
  convexity*, Proposition 9.2, supplies exactly spectral-closure
  factorization equivalence used in (5).
- Joi\c{t}a, *The Shilov boundary for a local operator system*, Theorem
  3.16, supplies local Shilov existence and stage-boundary kernel
  description. Her result gives only coordinate inclusion in general;
  (12a)--(12f) supply new derived exact sequence and acyclicity theorem.
- Joi\c{t}a--\c{S}imon, *On the Shilov boundary ideal for Fréchet local
  operator systems* (2026), characterizes the local Shilov ideal through
  \(\Gamma\)-boundary representations but contains no inverse/projective
  limit, \(\varprojlim^1\), or envelope-continuity theorem.
- Phillips, *Representable K-theory for \(\sigma\)-\(C^*\)-algebras*,
  Theorem 3.2, supplies only the classical Milnor sequence used after
  Theorem B; it has no operator-system or Shilov-boundary input.
- Searches through 2026-08-03 covering operator-system quotients,
  complete-order lifting, nc convex quotients, local Shilov ideals,
  \(C^*\)-supports, and recent local \(C^*\)-envelopes found no source
  defining escape/deficit pair, proving its spectral and matricial
  characterizations, proving right-exact composition law, or realizing
  every separable unital \(C^*\)-algebra as split zero-escape deficit,
  proving Shilov \(\varprojlim^1\)-acyclicity, preserving countable inverse
  limits, or prescribing an arbitrary sequence of cancelling deficits.

## Renewed hostile universal-law verdict (2026-08-03)

**Verdict: PASS to Stage 2.** Corrected theorem package is
dependency-closed and plausibly publishable in a renowned general journal
at the *Advances in Mathematics* / *Mathematische Annalen* level, subject
to full manuscript execution and independent final review. It is not being
presented as an Annals/JAMS-level breakthrough.

Hostile checks:

1. **No pointwise/global conflation.** Earlier converse was false and is
   explicitly withdrawn. Literal Roos sequence identifies exact global
   obstruction; Lean proves injectivity, middle exactness, and surjectivity.
2. **No circular acyclicity.** Exact sequence is proved before envelope
   continuity. Acyclicity then follows independently because
   \(\varprojlim C_e^*(S_n)\) is generated by limit system and has zero
   local Shilov ideal; local-envelope uniqueness identifies canonical map.
3. **Topology closes.** Countability and separability make all covers
   Fréchet. Intrinsic representative quotient and literal inverse limit are
   continuous bijections between Fréchet spaces, so open mapping supplies
   inverse continuity. No uniform cross-stage norm bound is assumed.
4. **Tower realization is genuine.** Future sentinels are full unitaries at
   every earlier stage; current zero image exposes central summand; generator
   blocks generate arbitrary \(K_m\); essential ideals kill all boundary
   ideals. Thus every prescribed \(D_m\) occurs while global comparison is
   exact.
5. **Novelty is theorem-level.** Current primary sources supply quotient
   lifting, spectral closure, local Shilov existence, and general Milnor
   sequences separately. Searches through 2026-08-03 found no maximal
   zero-escape category, countable envelope continuity, Shilov
   \(\varprojlim^1\)-acyclicity, defect composition exactness, or prescribed
   cancellation tower.
6. **Significance survives short proofs.** Arbitrary noncommutative deficits
   rule out a formal-kernel repackaging. Main result imposes a new homological
   constraint on Shilov ideal pro-systems and gives representable K-theory and
   faithful-positive-representation consequences.

Remaining risks are expository and formal, not an open mathematical core:
paper must state category/topology carefully, cite exact versions of local
envelope uniqueness and Phillips' Milnor sequence, and keep defect
realizability visibly tied to acyclicity rather than as detached example.

## Superseded hostile paper-proof verdict (2026-08-03)

**Historical verdict before universal-law correction: PASS to Stage 2; superseded.** Publication significance remained conditional
on manuscript-level synthesis and formal audit.** All stated implications
reduce to cited boundary theorems plus explicit ideal arguments; no step
assumes \(\alpha(J_S)=J_T\), ordinary closure in place of spectral closure,
or a uniform inverse-limit lifting bound. Split square-to-segment example
kills tempting false functoriality claim. Independent commutative and
noncommutative realizations show deficit is not notation for a forced-zero
kernel: it carries arbitrary separable unital \(C^*\)-algebra structure.

Current result is stronger than a specialist observation but not yet a
general-journal paper. Manuscript must make arbitrary-deficit realization,
spectral criterion, local exactness, and categorical composition one coherent
boundary-migration theory; include complete proofs and exact source ancestry;
and survive independent hostile review after Lean validation.

## Manuscript and final internal hostile audit (2026-08-03)

Manuscript package completed at
`docs/drafts/manuscripts/shilov-boundary-migration/`:

- `main.tex` and compiled 11-page `main.pdf`;
- `CLAIM_TRACE.md`, separating every paper theorem, imported input, Lean
  status, and falsifier;
- `LITERATURE_AUDIT.md`, recording primary-source ancestry, exact collision
  searches, novelty package, and residual priority risk;
- `HOSTILE_REVIEW.md`, recording objections, resolutions, verification, and
  venue-calibrated verdict.

Final internal hostile verdict: **PASS at credible Advances in Mathematics /
Mathematische Annalen submission quality**, not Annals/JAMS level and not a
claim of external human acceptance. During review, source checking found and
fixed a real citation defect: KPTT Theorem 3.7 alone does not identify the
universal quotient; Corollary 3.9 is also required. Proofs of essentiality and
graph Shilov minimality were expanded, a false claim of logical independence
was removed, and leaked TeX tokens were eliminated.

Final verification:

- Tectonic compiles with no warning, undefined reference, underfull box, or
  overfull box;
- PDF visual and extracted-text audits pass;
- `lake env lean
  GaloisForLFunctions/HTGeometry/ShilovBoundaryMigrationDefect.lean` passes;
- final targeted `lake build
  GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect` passes
  (`2997/2997`);
- main Lean theorems use only `propext`, `Classical.choice`, and `Quot.sound`;
- new module has no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe`
  declaration and is imported by the HTGeometry umbrella;
- global lint still fails only on unrelated pre-existing unreachable modules;
  the new module is reachable;
- repository-wide `git diff --check` is blocked only by unrelated pre-existing
  trailing whitespace in
  `docs/drafts/pipeline/1-in-progress/residue-corrected-determinant-cofinal-torsion-spectrum.md`.

Formal boundary remains explicit rather than theatrical: current mathlib has
completely positive maps between C*-algebras but lacks operator systems,
Shilov ideals, C*-envelopes, boundary representations, and locally C*-algebras.
The exact algebraic derived law and defect calculus are unconditional Lean;
the analytic boundary theory is dependency-closed on paper using the cited
primary theorems. No structure or hypothesis restates an unformalized analytic
conclusion.
