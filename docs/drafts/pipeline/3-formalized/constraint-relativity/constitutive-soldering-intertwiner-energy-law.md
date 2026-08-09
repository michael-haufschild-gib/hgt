# Constitutive soldering intertwiner-energy law

- **ID:** `constitutive-soldering-intertwiner-energy-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / NONTRIVIAL SOURCE-HISTORY CURVATURE / CLASSIFICATION
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [CLASSICAL REPRESENTATION PARENT]`
  `[BLG INFRASTRUCTURE] [NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Field card:** `../../1-in-progress/constraint-relativity/source-soldering-bivariant-law-geometry.md`.

## Statement

Let `G` be finite group and let

\[
 \rho_K:G\to U(V),
 \qquad
 \rho_T:G\to U(W)
 \tag{1}
\]

be finite-dimensional unitary representations with `dim V=dim W=n`. Regard one-object groupoid
`BG` as source-history category. Constitutive solderings are unitary isomorphisms

\[
 \mathscr S=U(V,W).
 \tag{2}
\]

For `s in mathscr S`, define transport defect

\[
 Q_s(g)=\rho_T(g)s-s\rho_K(g).
 \tag{3}
\]

Then

\[
 Q_s(gh)=\rho_T(g)Q_s(h)+Q_s(g)\rho_K(h).
 \tag{4}
\]

Define Reynolds intertwiner projection on `Hom(V,W)` by

\[
 \Pi(s)=\frac1{|G|}\sum_{g\in G}\rho_T(g)s\rho_K(g)^{-1}.
 \tag{5}
\]

With Hilbert--Schmidt norm, constitutive curvature energy is

\[
 \boxed{
 \mathcal E(s)
 :=\frac1{2|G|}\sum_{g\in G}\|Q_s(g)\|_{\mathrm{HS}}^2
 =\|s\|_{\mathrm{HS}}^2-\|\Pi(s)\|_{\mathrm{HS}}^2.}
 \tag{6}
\]

Consequently following are equivalent:

1. some constitutive soldering has zero curvature;
2. some unitary `s:V->W` intertwines `rho_K` and `rho_T`;
3. representations `rho_K` and `rho_T` are unitarily equivalent.

If representations are not equivalent, compactness of `U(V,W)` gives sharp positive gap

\[
 \boxed{
 \varepsilon(\rho_K,\rho_T)
 :=\min_{s\in U(V,W)}\mathcal E(s)>0.}
 \tag{7}
\]

Thus local constitutive isomorphisms exist at unique source object, yet no globally natural
constitutive soldering exists precisely when source-history representations differ.

## Proof

Expanding `(3)` and using representation laws gives

\[
\begin{aligned}
 \rho_T(g)Q_s(h)+Q_s(g)\rho_K(h)
 &=\rho_T(g)\rho_T(h)s-\rho_T(g)s\rho_K(h)\\
 &\quad+\rho_T(g)s\rho_K(h)-s\rho_K(g)\rho_K(h)\\
 &=Q_s(gh),
\end{aligned}
\]

proving `(4)`.

Operators `U_g(s)=rho_T(g)s rho_K(g)^(-1)` form unitary representation of `G` on Hilbert space
`Hom(V,W)` with Hilbert--Schmidt inner product. Therefore average `Pi=|G|^(-1)sum_g U_g` is
orthogonal projection onto fixed subspace, exactly intertwiner space. Unitary invariance gives

\[
 \|Q_s(g)\|_{\mathrm{HS}}
 =\|s-U_g(s)\|_{\mathrm{HS}}.
\]

Hence

\[
\begin{aligned}
 \mathcal E(s)
 &=\frac1{2|G|}\sum_g
   \left(2\|s\|^2-2\operatorname{Re}\langle s,U_g(s)\rangle\right)\\
 &=\|s\|^2-\operatorname{Re}\langle s,\Pi(s)\rangle\\
 &=\|s\|^2-\|\Pi(s)\|^2,
\end{aligned}
\]

because `Pi` is orthogonal projection. This proves `(6)`. Energy vanishes exactly when
`Pi(s)=s`, equivalently `s` is unitary intertwiner. If no such intertwiner exists, continuous
positive function `E` has positive minimum on compact `U(V,W)`, proving `(7)`. QED.

## Smallest nonflat source history

Let `G=C_2={1,g}`, `V=W=C`, `rho_K(g)=1`, and `rho_T(g)=-1`. Every constitutive soldering is
scalar `s` with `|s|=1`, while

\[
 Q_s(g)=-2s,
 \qquad
 \Pi(s)=0,
 \qquad
 \mathcal E(s)=1.
 \tag{8}
\]

This is exact nonzero BLG curvature. Zero soldering would flatten history but is excluded by
constitutive normalization `(2)`. Example is deliberately minimal and carries no arithmetic claim.

## Consequence for field definition

Transport cocycle alone is not field theory: unconstrained zero comparison always trivializes it.
Nonzero content begins with source-derived constitutive space `mathscr S_A`. In groupoid chart,
field invariant is equivalence obstruction between two source-history representations, and
`(6)` supplies quantitative energy.

For trace/cotangent applications, `rho_K` and `rho_T` must be induced from literal source actions on
deformation and trace laws. Choosing unrelated representations after fact would be theatre. The RH
gate remains construction of those actions and prescribed constitutive class from arithmetic
source, independently of zero displacement.

## Conjecture--attack loops

1. **Cocycle alone prevents trivial flattening.** False: `s=0`.
2. **Local vector-space isomorphism implies global law equivalence.** False by `(8)`.
3. **Curvature energy depends on coordinates.** False: `(6)` is unitary invariant.
4. **Positive energy proves arithmetic selection.** False: representations may be chosen freely.
5. **Positive survivor:** source-derived constitutive normalization converts naturality failure into
   exact representation-equivalence obstruction with quantitative gap.

## Novelty and Lean-return boundary

Reynolds projection, unitary intertwiners, and finite-group representation equivalence are
classical. Card is dependency-closed BLG infrastructure, not novelty claim. No Lean work authorized.

## Gates

- [x] nonzero constitutive class
- [x] exact cocycle
- [x] exact curvature energy
- [x] zero-curvature classification
- [x] explicit nonflat example
- [ ] literal arithmetic trace/cotangent representation
- [x] Lean formalization

## Log

- 2026-08-08 -- zero-soldering hostile attack forced constitutive normalization; finite-group
  chart then yielded exact intertwiner-energy and positive curvature gap.

## Formalized companion

`constitutive-soldering-intertwiner-energy-law-formalized.md` (same directory).
