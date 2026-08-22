# Source-linear essential superselection no-sewing

- **ID:** `source-linear-essential-superselection-no-sewing`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** CLOSED-OPERATOR THEOREM / SOURCE-SPECIFIC NO-GO / RH INTERFACE
- **Scientific status:** `[PAPER-PROVED] [PARENT REPRESENTATION THEORY]`
  `[STRICTLY SHARPENS FINITE-REES NO-SEWING] [NOT RH]`
- **Parents:**
  - `prime-poisson-superselection-screen.md`;
  - `../../1-in-progress/prime-valuation-hellinger-rees-reflection-fracture.md`;
  - `../new_scientific_knowledge/prime-wold-accelerated-type-modular-drift-law.md`;
  - `../../1-in-progress/source-modular-drift-realization-equivalence-law.md`.

## Frontier statement

The all-orders-flat theorem proves that no bounded operator family of fixed finite Rees order can
sew the two reflected off-critical sectors.  It leaves open an essentially singular operator.
Source linearity closes that escape completely.

Let
\[
 X=\mathbb T^{\mathbb P},\qquad A=C(X),
\]
and let \(\mu_s\) be the ordinary-prime product-Poisson measure from
`prime-poisson-superselection-screen.md`.  Write
\[
 H_s=L^2(X,\mu_s),\qquad
 \pi_s(f)\xi=f\xi,\qquad
 \tau(s)=1-\overline s.
\]
The corpus proves
\[
 \mu_s\sim\mu_{\tau(s)}
 \quad\Longleftrightarrow\quad
 \Re s=\frac12,
\tag{1}
\]
and mutual singularity otherwise.

The new recut is:

> **Theorem — source-linear essential no-sewing.**
> If \(\Re s\ne\tfrac12\), every closed densely defined operator
> \[
> T:H_s\longrightarrow H_{\tau(s)}
> \]
> satisfying
> \[
> \pi_s(f)\operatorname{Dom}T\subseteq\operatorname{Dom}T,
> \qquad
> T\pi_s(f)\xi=\pi_{\tau(s)}(f)T\xi
> \tag{2}
> \]
> for every \(f\in A\) and \(\xi\in\operatorname{Dom}T\) is zero.
> The same conclusion holds for a closed source-linear operator between any nonzero reducing
> subrepresentations.

No bound on \(\|T\|\), no Rees order, and no dimension hypothesis occurs.  In particular, an
essentially singular norm does not sew disjoint reflected sectors if the map remains a closed
operator over the same ordinary-prime cylinder algebra.

At \(\Re s=\tfrac12\), the measures in `(1)` are equal and the identity operator gives a nonzero
closed source-linear sewing.  Hence
\[
\boxed{
\begin{array}{c}
\text{nonzero closed source-linear reflected sewing exists}\\
\Longleftrightarrow \Re s=\tfrac12.
\end{array}}
\tag{3}
\]

## Proof

Mutually singular measures give disjoint multiplication representations.  Indeed, choose a Borel
set \(E\subset X\) with
\[
\mu_s(E)=1,\qquad \mu_{\tau(s)}(E)=0.
\]
Any bounded intertwiner \(V:H_s\to H_{\tau(s)}\) also intertwines the spectral projections of the
two multiplication representations.  Therefore
\[
V=V\pi_s(\mathbf1_E)
  =\pi_{\tau(s)}(\mathbf1_E)V
  =0.
\tag{4}
\]

Now let \(T\) satisfy `(2)`.  For every unitary \(u\in A\), applying `(2)` to \(u\) and \(u^*\)
shows that \(\pi_s(u)\operatorname{Dom}T=\operatorname{Dom}T\) and
\[
\|T\pi_s(u)\xi\|
=\|\pi_{\tau(s)}(u)T\xi\|
=\|T\xi\|.
\tag{5}
\]
Hence the closed quadratic form of \(T^*T\) is invariant under \(\pi_s(u)\), so
\[
|T|\pi_s(u)=\pi_s(u)|T|
\tag{6}
\]
on the natural domain.  In the Hilbert-space polar decomposition
\[
T=V|T|,
\tag{7}
\]
the partial isometry \(V\) consequently satisfies
\[
V\pi_s(u)=\pi_{\tau(s)}(u)V.
\tag{8}
\]
Unitary elements linearly generate \(A\), so \(V\) is a bounded \(A\)-intertwiner.  Equation
`(4)` gives \(V=0\), hence \(T=0\).

For a closed operator between reducing subrepresentations, apply the same proof after restricting
the two multiplication representations to the closures of its initial and final supports.
Disjoint representations have no equivalent nonzero subrepresentations, so the polar partial
isometry again vanishes.  This proves the theorem.

## Exact strengthening of the Rees trilemma

The finite-Rees theorem left three possible off-line escapes:

1. essentially singular operator norm;
2. nonclosable, multivalued, or distributional correspondence;
3. loss of the distinguished source conormal.

The theorem above splits the first escape:

```text
essential but closed and source-linear:
  impossible off line;

essential and closed but source-twisted:
  possible external modular retuning;

source-linear but nonclosable/multivalued:
  possible singular relation;

closed source-linear nonzero graph:
  critical line only.
```

This explains the standard adelic/Iwahori counterexample.  Its essential Weyl intertwiner can join
off-line complementary-series sectors only by changing the module action, equivalently by
retuning the source modular class.  It is not a counterexample to `(3)`.

It also explains why infinite rank is irrelevant.  Disjointness is a statement about central
support of representations, not dimension or operator growth.  The polar part of any nonzero
closed operator would already be a forbidden bounded intertwiner.

## RH-bearing source theorem

The remaining theorem is no longer a finite-Rees estimate.

`[OPEN CORE — XI_CLOSED_SOURCE_MODULE_GRAPH_LANDING]`

Before zero-fibre decomposition, construct the ordinary-integer Euler--Gamma/co-Poisson
producer--reporter round trip so that:

1. its producer legs are the multiplication representations of the fixed ordinary-prime cylinder
   algebra \(A=C(\mathbb T^{\mathbb P})\);
2. after strict Xi Cartier base change, every nontrivial zero \(\rho\) supplies a nonzero closed
   graph from a reducing subrepresentation of \(H_\rho\) to one of \(H_{\tau(\rho)}\);
3. the round-trip graph is \(A\)-linear, even if the individual Fourier/Poisson legs exchange
   polarizations;
4. the top multiplicity conormal survives in the initial and final support of that graph; and
5. the algebra action and graph are fixed before \(\rho\) is known.

Then `(3)` gives
\[
\Re\rho=\frac12
\]
for every nontrivial Xi zero, hence RH.

This target is strictly weaker than finite-Rees moderation and strictly stronger than existence
of an essential correspondence.  The norm may have arbitrary essential growth.  What cannot be
lost is closed source-module structure.

## Hostile audit

1. **Not a zero-to-sector theorem.**  The corpus does not prove that a Xi conormal produces the
   graph in the open core.  That landing remains load-bearing.
2. **Fourier is not multiplication-linear.**  Additive Fourier exchange of multiplication and
   convolution does not satisfy `(2)` on an individual leg.  Only the producer--reporter
   round trip may reasonably be \(A\)-linear.  Assuming linearity of Fourier itself would be
   false.
3. **A twisted intertwiner is allowed off line.**  If
   \(T\pi_s(f)=\pi_{\tau(s)}(\alpha(f))T\) for a retuning automorphism \(\alpha\), the theorem
   compares \(\mu_s\) with the pulled-back target measure.  A zero-dependent \(\alpha\) can fit any
   fibre and is excluded by clause 5, but a fixed source automorphism must be audited separately.
4. **A relation can evade polar decomposition.**  A genuinely multivalued or nonclosable
   correspondence has no bounded polar partial isometry.  The theorem identifies that escape; it
   does not declare it impossible.
5. **No positivity.**  No positive kernel, Julia orientation, Weil inequality, or UCP recovery is
   used.
6. **No growth criterion.**  Finite Rees, accelerated type, and essential type are irrelevant once
   source-linear closedness is proved.
7. **Generalized-prime falsifier.**  A generalized-prime off-line system may carry an external
   reflection correspondence.  It falsifies this mechanism only if it also carries the same
   ordinary-prime cylinder algebra and a nonzero closed untwisted round-trip graph.

## Literature and novelty boundary

The parent facts are standard:

- mutually singular measures give disjoint multiplication representations;
- disjoint representations admit no nonzero bounded intertwiner;
- a closed densely defined Hilbert-space operator has a polar decomposition.

The proof above is their direct combination.  No standalone external novelty is claimed.  The
source-specific advance is the removal of the last operator-growth escape from the exact
ordinary-prime superselection screen and the resulting replacement of finite-Rees moderation by
one closed module-graph landing theorem.

## Lean decision

The formal tree does not yet contain the infinite prime torus, product-Poisson measures, their
Kakutani singularity classification, direct-integral multiplication representations, or polar
decomposition of unbounded operators.  Formalizing a finite-dimensional statement that disjoint
supports have no matrix intertwiner would not formalize the source theorem.  No Lean wrapper is
added.

## Gates

- [x] prime product-Poisson reflection measure classes inherited
- [x] bounded intertwiner obstruction proved
- [x] arbitrary closed densely defined source-linear obstruction proved
- [x] essential-growth escape removed
- [x] source-twisted and nonclosable escape clauses isolated
- [x] parent-literature boundary audited
- [ ] construct producer--reporter round-trip graph before zero specialization
- [ ] prove fixed ordinary-prime \(A\)-linearity
- [ ] prove closedness after cofinal completion
- [ ] prove strict Xi conormal and multiplicity landing
- [ ] RH
- [ ] unconditional Lean formalization after analytic interfaces exist

## 2026-07-30 strengthening: closed module relations also split

The multivalued escape in Hostile audit 4 can be closed more sharply.

Let \(\pi_i:A\to B(H_i)\), \(i=1,2\), be disjoint representations of a unital
\(C^*\)-algebra.  Regard a linear relation from \(H_1\) to \(H_2\) as a linear subspace
\[
 {\cal R}\subseteq H_1\oplus H_2.
\]
Call it \(A\)-linear when it is invariant under
\(\pi_1(a)\oplus\pi_2(a)\) for every \(a\in A\).

> **Theorem — closed disjoint-sector relations split.**
> Every closed \(A\)-linear relation has the form
> \[
> {\cal R}
> =
> {\cal R}_1\oplus{\cal R}_2,
> \qquad
> {\cal R}_1\subseteq H_1\oplus0,\quad
> {\cal R}_2\subseteq0\oplus H_2.
> \tag{9}
> \]
> In particular it contains no coupled input--output component.  This includes arbitrary
> multivalued closed relations and imposes no graph, domain-density, dimension, or growth
> hypothesis.

Because \(A\) is self-adjoint, invariance under every
\(\pi_1(a)\oplus\pi_2(a)\) also gives invariance of \({\cal R}^{\perp}\).  Hence the orthogonal
projection \(P_{\cal R}\) belongs to the commutant of \(\pi_1\oplus\pi_2\).  In block form its
off-diagonal entries intertwine \(\pi_1\) and \(\pi_2\).  Disjointness makes both entries zero, so
\(P_{\cal R}\) is block diagonal and `(9)` follows.

For the reflected prime-Poisson representations this yields
\[
 \Re s\ne\frac12
 \Longrightarrow
 \text{every closed source-linear reflected relation is uncoupled}.
 \tag{10}
\]
At the critical line the diagonal graph is a coupled closed relation.  Thus allowing a closed
multivalued correspondence does not evade the superselection screen.  The only relation-level
escapes are nonclosedness, loss/twisting of the fixed \(A\)-action, or passage to a relative
extension before the \(A\)-boundary quotient.

## Meyer/co-Poisson type audit and correction of the RH interface

The direct open core above is not yet a typed theorem about Meyer's actual quotient.
Meyer's
\[
 M_\zeta=H_-/Z(H_\cap)
\]
is a nuclear Fréchet representation of positive-real dilation.  Its generalized zero jets live
in the strong dual and carry the algebraic centered character
\[
 q\longmapsto q^{\rho-1/2}.
\]
The locally convex dilation action is not a Hilbert \(*\)-representation of
\[
 C^*(\mathbb Q_{>0}^{\times})\simeq C(\mathbb T^{\mathbb P}).
\]
Indeed nonunitary algebraic characters are allowed in the Meyer strong dual; excluding them by
unitary \(C^*\)-boundary continuity or prime-Schwartz temperedness is already equivalent to
placing \(\rho\) on the critical line.

Consequently `XI_CLOSED_SOURCE_MODULE_GRAPH_LANDING` is retired as a supposedly weaker direct
Meyer construction target.  It becomes valid only after one has built the missing positive/star
or tempered boundary landing, which is itself RH-bearing.  Meyer's strict nuclear quotient,
Poisson identity, and generalized-eigenjet theorem do not supply that upgrade.

The non-circular conclusion is instead categorical:

```text
closed boundary operator:
  cannot couple disjoint reflected sectors;

closed boundary relation:
  splits and cannot couple them either;

Meyer nuclear quotient:
  retains off-line algebraic characters but has no canonical C*-boundary action;

viable essential sewing:
  must live before boundary descent, as a relative class for
  0 -> J_Gamma -> T_Gamma -> C(T^P) -> 0.
```

Thus “essential singularity” cannot mean only fast operator-norm growth.  It means failure of the
source anomaly class to descend to a closed spatial correspondence after quotienting the
Wold--Gamma/BV ideal.  Proving that the literal Xi conormal relative class nevertheless has a
nonzero coupled boundary descent would prove RH; assuming that descent merely re-encodes it.

The theorem `(9)` is parent representation theory.  Its value here is the exact closure of the
multivalued loophole and the correction of the open core, not a standalone novelty claim.

## Actual first-trace source test: ordinary closure is already the split endpoint

The formal source graph does not evade `(9)`.  The unconditional theorem
`primeFirstTraceClock_pair_mem_graphClosure_iff` computes its ordinary Hilbert graph closure:
\[
 \overline{\operatorname{Graph}(\operatorname{FirstTrace})}
 =
 H_{\rm source}\oplus H_{{\rm response},0},
\tag{11}
\]
where \(H_{{\rm response},0}\) is the zero-vacuum Hardy hyperplane.  Every source vector pairs
with every vector in that response hyperplane.  Thus `(11)` has lost all input--output
correlation and is exactly a block-split closed relation.

The algebraic first-trace graph is coupled but nonclosable.  Its actual-prime null sequence has
source size \(a_p\asymp1/\log p\), response error \(b_p\asymp1/p\), and
\[
 a_p(-\log b_p)\longrightarrow1,\qquad
 b_p/a_p^N\longrightarrow0\quad(N\text{ fixed}).
\tag{12}
\]
Therefore ordinary closure forgets a nonzero exponential normal direction which every finite
Rees grade also forgets.

This forces the order of operations:

```text
ordinary closure, then source-normal blow-up:
  coupling already erased;

source-normal/exponential associated graded, then strict completion:
  only remaining place where coupling can survive.
```

The desired essential object is consequently a Bockstein/transgression of noncommutation between
normal specialization and closure.  It is not an unbounded operator hidden inside the ordinary
closed graph.  The source-specific open core is to construct this graded relative graph for the
literal Euler--Gamma/co-Poisson complex and prove that its Xi boundary descent is strict and
conormal-faithful.
