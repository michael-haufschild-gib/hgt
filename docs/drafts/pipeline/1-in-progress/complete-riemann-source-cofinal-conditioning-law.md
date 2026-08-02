# Cofinal collapse and inverse conditioning of the complete Riemann source

- **ID:** complete-source-cofinal-conditioning
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md`, Route R source-conversion boundary
- **Statement:** Each finite complete-resolution source map is injective and divisor-faithful, but the maps converge pointwise in their canonical \(\ell^1\) norm to one universal atom; consequently every uniformly Lipschitz, possibly nonlinear and label-sensitive, cofinal observer loses all fixed spectral separation, while inverse conditioning between distinct points diverges.

## Goal

Close the frontier map's broad “genuinely nonlinear” regular escape hatch.  Existing work
classifies bounded label-blind linear observers.  This theorem asks what remains true without
linearity or label blindness.  It proves that ordinary uniform metric regularity alone is already
fatal along the cofinal shell direction.

The result is source-pure.  It uses only the predeclared largest-valuation resolution
\[
 E_K(s)=\left(\zeta(Ks)^{-1},H_K(s),H_{K+1}(s),\ldots\right),
 \qquad
 H_m(s)=\zeta((m+1)s)^{-1}-\zeta(ms)^{-1},
\]
on \(\operatorname{Re}s>0\), not any zero location or RH-equivalent premise.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack and non-circularity audited
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [ ] 2 → 3 formalized: promote scratch theorem module and audit axioms
- [ ] 3 → 4 publication-ready: integrate as sole conditioning addition to the conservation law and pass hostile review

## Theorem

Let \(X=\ell^1(\mathbb N_0;\mathbb C)\), let \(e_0=(1,0,\ldots)\), and let
\(\Sigma:X\to\mathbb C\) be coordinate summation.  For every \(s\) with
\(\operatorname{Re}s>0\):

1. \(\Sigma E_K(s)=1\) for every \(K\).
2. \(E_K(s)\to e_0\) in \(X\) as \(K\to\infty\).
3. For every finite \(K\), \(s\mapsto E_K(s)\) is injective.
4. Therefore, for \(s\ne t\),
   \[
   \|E_K(s)-E_K(t)\|\to0,\qquad
   \|E_K(s)-E_K(t)\|^{-1}\to\infty .
   \]
5. Let \(F\) be any metric space and \(T_K:X\to F\) any maps, with no linearity or
   label-symmetry assumption.  If one constant \(C\) satisfies
   \[
   d(T_Kx,T_Ky)\le C\|x-y\|\quad\text{for every }K,x,y,
   \]
   then
   \[
   d(T_KE_K(s),T_KE_K(t))\to0.
   \]
   Hence no uniformly Lipschitz family retains a fixed positive separation between two spectral
   points.
6. For \(K\ge12\) and \(\operatorname{Re}\rho\ge1/2\), at least one coordinate of
   \(E_K\) preserves the exact analytic order of \(\xi\) at \(\rho\).  Thus full divisor landing
   coexists with metric collapse.
7. In the open critical strip the functional-equation displacement
   \(E_K(s)-E_K(1-\bar s)\) is nonzero at every finite \(K\) exactly off the critical line, tends
   to zero cofinally, and has inverse norm tending to infinity.
8. Collapse has a canonical singular resolution.  If the prime-two asymptotic atom is removed
   before the second ratio is formed, then
   \[
   \left(
   \sqrt2\,\frac{H_{K+1}(s)}{H_K(s)},\
   \sqrt3\,\frac{\widetilde H_{K+1}(s)}{\widetilde H_K(s)}
   \right)
   \longrightarrow
   \left(2^{1/2-s},3^{1/2-s}\right),
   \]
   and the limiting two-clock chart is injective.
9. This chart is necessarily singular relative to the source norm.  For every \(s\ne t\), no
   finite \(C\) satisfies
   \[
   d(B_K(s),B_K(t))
   \le C\|E_K(s)-E_K(t)\|_1
   \qquad\text{for every }K.
   \]
10. Stronger source-pointed form.  Let \(X_K=E_K(\{\operatorname{Re}s>0\})\).  There is an
    injective reader \(N_K:X_K\to\mathbb C^2\) with
    \[
    N_K(E_K(s))=(2^{1/2-s},3^{1/2-s}).
    \]
    Its first coordinate is the cofinal adjacent-coordinate ratio inside the single vector
    \(E_K(s)\); its second is the corresponding ratio after exact removal of the first
    prime-normal atom.  Thus no external spectral label is needed.  For every fixed \(s\ne t\),
    \(d(N_KE_K(s),N_KE_K(t))\) is a positive constant while
    \(\|E_K(s)-E_K(t)\|_1\to0\), so this infinite source reader admits no shell-independent
    Lipschitz bound.
11. Maximal vertical boundary.  Relative to \(s_0=1/2\), the points \(s_1=3/2\) and \(s_2=5/2\)
    give two source differences tending to zero, while their exact two-clock reader differences
    are
    \[
    v_1=(-1/2,-2/3),\qquad v_2=(-3/4,-8/9),
    \]
    with determinant \(-1/18\).  Thus \(v_1,v_2\) span \(\mathbb C^2\).  Every closed linear
    relation containing these cofinal graph directions has full vertical fibre
    \(\{0\}\times\mathbb C^2\), and no such relation is single-valued at the collapsed source
    point.

## Proof

For \(a_{K,0}(s)=\zeta(Ks)^{-1}\) and
\(a_{K,j+1}(s)=H_{K+j}(s)\), the \(\ell^1\) norm has the exact split
\[
 \|E_K(s)-e_0\|_1
 =
 |\zeta(Ks)^{-1}-1|
 +
 \sum_{j\ge0}|H_{K+j}(s)|.
\]
The first term tends to zero because \(\zeta(Ks)\to1\) on every ray
\(\operatorname{Re}s>0\).  The shell family is absolutely summable there, so its translated
tails tend to zero.  This proves (2).  The telescoping identity gives (1).

Finite-\(K\) injectivity is the existing two-clock theorem: adjacent shell ratios recover
\(2^{-s}\); after removing that atom, the next residual ratio recovers \(3^{-s}\); the
incommensurable logarithms determine \(s\).  This gives (3), hence the norms in (4) are positive
for every \(K\).  Combining positivity with convergence to zero and applying reciprocal
continuity from the positive side proves inverse divergence.

For (5), the uniform Lipschitz inequality gives
\[
 0\le d(T_KE_K(s),T_KE_K(t))
 \le C\|E_K(s)-E_K(t)\|\longrightarrow0.
\]
The squeeze theorem proves observer collapse without linearity, additivity, positivity, or label
blindness.

Statement (6) is the already proved summable conormal-landing theorem applied at each \(K\).
Statement (7) combines the reflection fixed-point theorem with (2)--(4).
For (8), the least-prime shell asymptotic gives the first projective ratio.  Exact subtraction
of its prime-two atom exposes the prime-three shell asymptotic and the second ratio.  Moduli fix
\(\operatorname{Re}s\); irrationality of \(\log3/\log2\) removes the remaining phase alias.
For (9), chart distance converges to the distance between two distinct limiting two-prime
characters, hence to a positive number, while source distance tends to zero.  A uniform
Lipschitz estimate would force the positive limit to be zero.
For (10), finite-stage injectivity gives a unique spectral preimage for each \(x\in X_K\), so
\(N_K\) is well-defined and injective.  The prime-two and prime-three shell asymptotics identify
its two coordinates with internal tail ratios.  The final singularity statement follows from
constant positive reader separation and cofinal source collapse.
For (11), the displayed character values follow by evaluating
\((2^{1/2-s},3^{1/2-s})\) at \(s_0,s_1,s_2\).  Closedness sends each convergent graph sequence
\((E_K(s_j)-E_K(s_0),v_j)\) to \((0,v_j)\).  Linearity then puts every linear combination of
\(v_1,v_2\) in the vertical fibre.

## New scientific knowledge

The complete source does not lose spectral or divisor information at any finite stage; it stores
that information in a transverse direction whose canonical norm collapses cofinally.  Therefore
the missing Route-R conversion is not merely “nonlinear rather than linear.”  Any successful
cofinal consumer must have unbounded local conditioning, fail uniform continuity on the source
image, or change topology.  This is a class-complete obstruction for all uniformly Lipschitz
nonlinear and label-sensitive consumers.

The two-clock chart supplies the positive survivor: the required singular geometry is the
projective normal blow-up of the universal atom.  Ordinary \(\ell^1\) topology collapses the
source, but its first two prime normal directions retain the full complex spectral coordinate.
This replaces the vague instruction “use a singular consumer” by an explicit, source-defined
singular resolution, and proves that singularity is unavoidable rather than a feature of one
chosen formula.

The maximal-vertical theorem is the exact topological form: at cofinal depth, spectral rank is not
destroyed but converted from horizontal source separation into multivalued graph rank.  It
connects the complete source to the corpus's actual-prime first-trace graph closure, Hedenmalm
dense radical, nonclosable shell codiagonal, and finite-Rees fracture.  Abstract closed-linear-
relation theory is prior art; candidate novelty is the explicit two-clock Riemann source whose
entire target becomes the forced vertical fibre.

The law strengthens the paper's current consumer classification:

- bounded label-blind linear descent is exactly blind at each stage;
- arbitrary uniformly Lipschitz descent becomes blind cofinally;
- divisor fidelity survives in vanishing transverse channels;
- reflected orientation survives algebraically but requires divergent inverse conditioning to
  remain metrically visible.

Thus Hedenmalm dense radicals, Hilbert codiagonal nonclosability, Sonin/Calkin compact
equalization, fixed-observer horizon escape, finite-Rees failure, and bounded Ward capacity are
different regularity shadows of one conservation--conditioning conflict.

## Novelty audit

Elementary ingredients receive no novelty credit: translated tails of an absolutely summable
series vanish; an injective family may converge pointwise to a constant map; a uniform Lipschitz
bound contracts collapsing pairs.

Targeted primary-source searches covered \(k\)-free Dirichlet series, reciprocal-zeta dilation
differences, partitions of unity, Euler-product approximants, \(\ell^1\) spectral embeddings, and
inverse conditioning.  Gonek's Euler-product approximation work concerns approximating functions
and their zeros, not this largest-valuation mass-one embedding or its finite-faithful/cofinally
collapsing geometry.  Standard \(k\)-free literature treats individual
\(\zeta(s)/\zeta(ks)\), not the complete injective divisor-replicating vector and its observer
theorem.  No exact collision was found.  Search failure is evidence, not proof of priority.

Defensible novelty is the exact Riemann-source synthesis: an explicit mass-one family which is
simultaneously finite-stage injective, multiplicity-preserving for the completed zeta divisor,
and cofinally norm-collapsing, together with the resulting class-complete no-go for every
uniformly Lipschitz nonlinear observer.

## RH status

This theorem does not prove RH.  It narrows the missing operation: a successful source-pointed
common-test factorization must realize a quantitatively singular inverse to the collapsing
source direction and then prove the four-unit Ward/Weil sign.  The theorem proves necessity of
that singularity, not existence or sign.

## Log

- 2026-08-02 — conjectured from tension between finite-\(K\) source injectivity and cofinal
  reciprocal-zeta convergence.
- 2026-08-02 — dependency-closed proof completed in Lean scratch; nonlinear observer theorem and
  reflected inverse-conditioning corollary compile with `lake env lean`.
- 2026-08-02 — canonical two-clock projective blow-up identified and proved to converge to the
  injective \((2^{1/2-s},3^{1/2-s})\) chart.
- 2026-08-02 — proved pairwise inevitable singularity: no finite uniform Lipschitz constant can
  compare separated blow-up charts with the cofinally collapsing source metric.
- 2026-08-02 — strengthened the chart to an infinite source-pointed normal reader on the actual
  source image. Proof is written in scratch; foreground check is pending because another agent's
  umbrella build temporarily removed a required dependency object.
- 2026-08-02 — derived maximal two-clock vertical boundary and generic closed-relation
  specialization; proof written in scratch, same dependency-build check pending.
