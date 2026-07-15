# Factorial blow-up hypertranscendence of digamma composed with Gamma

- **ID:** digamma-gamma-factorial-blowup-hypertranscendence
- **Stage:** 3-formalized
- **Type:** THEOREM · HYPERTRANSCENDENCE
- **Status:** `[PROVEN] [LEAN FORMALIZED]`
- **Statement:** The composite
  \[
  h(z)=\psi(\Gamma z)
  \]
  is hypertranscendental over \(\mathbb C(z)\).  Its factorial affine microscopes at the
  negative integers converge locally holomorphically to the Möbius pullback
  \(x\mapsto\psi(-1/x)\), and any ADE for \(h\) would force a nonzero autonomous ADE for that
  hypertranscendental limit.

## Goal

Close the full hypertranscendence problem for \(\psi\circ\Gamma\), not only a bounded-order or
leading-pole layer.  The argument is source-pure: it uses the exact reciprocal-Gamma recurrence,
the factorial scale forced by the derivative of \(1/\Gamma\) at \(-n\), and a static initial-form
operation on a hypothetical algebraic differential constraint.

The abstract rescaling/initial-form mechanism is parent mathematics, not the novelty claim.  The
candidate new result is the concrete factorial microscope and its application to the non-plane-
meromorphic composite \(\psi\circ\Gamma\).

## Gates

- [x] 0 → 1 in-progress: exact scale, fixed regular domain, limiting carrier, and contradiction
  mechanism isolated
- [x] 1 → 2 fully-proven: analytic-continuation and Möbius local-HT lemmas independently checked;
  broad literature search finds no prior theorem for this composite
- [x] 2 → 3 formalized: Lean theorem, targeted module builds green, formal lint and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone theorem and proof with explicit parent-theory comparison

## Exact factorial microscope

Put
\[
H(z)=\frac1{\Gamma(z)},\qquad
a_n=-n,\qquad
s_n=\frac{(-1)^{n+1}}{n!}.
\]
The Gamma recurrence gives the exact identity
\[
H(-n+\delta)
=\prod_{j=1}^{n}(\delta-j)H(\delta)
=(-1)^n n!\,H(\delta)\prod_{j=1}^{n}\left(1-\frac\delta j\right).
\tag{1}
\]
Since \(H(0)=0\) and \(H'(0)=1\), substituting \(\delta=s_nx\) into `(1)` gives, locally
uniformly in \(x\),
\[
H(a_n+s_nx)\longrightarrow -x.
\tag{2}
\]
Indeed, \(H(s_nx)/(s_nx)\to1\), while
\[
\sum_{j=1}^{n}\left|\frac{s_nx}{j}\right|
\leq |s_nx|(1+\log n)\longrightarrow0,
\]
so the finite product in `(1)` tends locally uniformly to \(1\).

Take the fixed disk
\[
U=\{x:|x+1|<1/4\}.
\]
It is separated from \(0\), and \(-1/x\) remains in \(|z-1|<1/3\), away from every digamma
pole.  By `(2)`, for all sufficiently large \(n\), \(H(a_n+s_nx)\) is nonzero on each compact
subset of \(U\), and hence
\[
\Gamma(a_n+s_nx)\longrightarrow -\frac1x,
\qquad
g_n(x):=\psi(\Gamma(a_n+s_nx))\longrightarrow F(x):=\psi(-1/x)
\tag{3}
\]
locally uniformly on \(U\).  All derivatives in `(3)` converge locally uniformly by the
holomorphic convergence theorem.

## Factorial initial-form lemma

Let \(h\) be analytic at every \(a_n+s_nU\), where \(a_n=-n\), and suppose its affine zooms
\(g_n(x)=h(a_n+s_nx)\) have locally uniform all-jet limit \(F\) on \(U\).  If \(h\) satisfies an
ADE over \(\mathbb C(z)\), clear denominators and write it as
\[
0=P(z,h,\ldots,h^{(r)})
=\sum_{q,\alpha}c_{q,\alpha}z^q\prod_{j=0}^{r}(h^{(j)})^{\alpha_j}.
\tag{4}
\]
For a jet monomial put
\[
w(\alpha)=\sum_{j=0}^{r}j\alpha_j.
\]
Let \(W\) be the greatest weight occurring in `(4)`, and let \(E\) be the greatest \(q\) among
the terms of weight \(W\).  Since
\[
h^{(j)}(a_n+s_nx)=s_n^{-j}g_n^{(j)}(x),
\]
multiplication of `(4)` by \(s_n^W/(n+1)^E\) gives a finite sum.  Every term of weight below \(W\)
vanishes because \(|s_n|\) beats every fixed power of \(n\); among the weight-\(W\) terms, every
coefficient degree below \(E\) vanishes.  Passing to the all-jet limit leaves
\[
Q(F,F',\ldots,F^{(r)})=0\quad\hbox{on }U,
\tag{5}
\]
where
\[
Q(Y_0,\ldots,Y_r)
=(-1)^E\sum_{\alpha}c_{E,\alpha}Y^\alpha,
\quad
\alpha\text{ restricted to weight }W.
\tag{6}
\]
The polynomial in `(6)` is nonzero: distinct \(\alpha\) remain distinct jet monomials, and the
definition of \(E\) supplies at least one nonzero coefficient.  Thus a factorial affine blow-up
limit of a DA function must satisfy a nonzero autonomous ADE on its regular limiting domain.

## Why the limiting carrier is locally hypertranscendental

Suppose a nonzero \(Q\in\mathbb C[Y_0,\ldots,Y_r]\) satisfied `(5)` for
\(F(x)=\psi(-1/x)\).  Under the involution \(x=-1/z\),
\[
F^{(j)}(-1/z)=\left(z^2\frac d{dz}\right)^j\psi(z).
\tag{7}
\]
The jet substitution in `(7)` is triangular, with the coefficient of \(\psi^{(j)}\) equal to
\(z^{2j}\); it is therefore injective over \(\mathbb C(z)\).  Consequently `(5)` becomes a
nonzero algebraic differential equation over \(\mathbb C(z)\) for \(\psi\) on a neighborhood of
\(z=1\).  The evaluated differential polynomial is meromorphic, so the identity theorem extends
the relation throughout the regular domain of \(\psi\), contradicting the hypertranscendence of
digamma.  Hence no such \(Q\) exists.

Combining this with `(3)` and the initial-form lemma contradicts every hypothetical ADE `(4)` for
\(h=\psi\circ\Gamma\).

## Analytic-continuation boundary

The regular set of \(\psi\circ\Gamma\) is the complement of the Gamma poles and the preimages of
the digamma poles.  This excluded set is countable; its complement is path connected.  Therefore an
ADE holding for one analytic element of the explicit single-valued composite continues to all
regular zoom disks used above.  This continuation step is formalized explicitly;
the composite is not meromorphic on the plane because the inverse-Gamma pole clusters accumulate at
the Gamma poles.

## Parent and rediscovery audit

- The fact that an analytic DA function satisfies an autonomous ADE is classical
  differential algebra (Ostrowski; used explicitly by Rubel--Singer).
- Coherent-family and Poincaré-function proofs use affine rescaling and highest-weight limits of
  differential polynomials.  Aschenbrenner--Bergweiler provide a close parent technique.
- Huang--Ng prove composition criteria with a hypertranscendental outer function and a nonconstant
  **entire** inner function using Steinmetz reduction and Nevanlinna growth.  Their theorem does not
  apply to the meromorphic inner Gamma function or to this non-plane-meromorphic composite.
- No located source states the factorial microscope `(2)` as a hypertranscendence detector or proves
  the hypertranscendence of \(\psi\circ\Gamma\).  The broad pipeline literature gate is complete;
  as with every negative priority search, publication-level priority remains subject to expert
  review.

## Lean realization

1. `DigammaGammaFactorialBlowUp.lean` formalizes the exact reciprocal-Gamma recurrence, factorial
   compact-open limit, all-jet convergence, highest-weight/point-degree initial form, injective
   Möbius jet pullback, and `hypertranscendental_digamma_comp_Gamma`.
2. `DigammaGammaLocalHypertranscendence.lean` proves that the regular set is open, has countable
   complement, and is path connected; it propagates any local relation and proves
   `no_local_differential_relation_digamma_comp_Gamma` on every nonempty regular open patch.
3. `GammaFactorialComposition.lean` derives the same capstone from the generic left/right
   half-plane composition principle.
4. All checks were module-scoped.  No full build was run.

## Log

- 2026-07-15 — factorial microscope and initial-form contradiction isolated; exact recurrence,
  fixed regular disk, and all-order limiting carrier checked on paper.
- 2026-07-15 — parent collision recorded: the abstract rescaling mechanism is classical/coherent-
  family mathematics; novelty restricted to the Gamma-factorial composite application.
- 2026-07-15 — full theorem and local regular-patch strengthening formalized.  Targeted module
  builds, formal lint, and axiom audits pass; the audited capstones use only `propext`,
  `Classical.choice`, and `Quot.sound`.
