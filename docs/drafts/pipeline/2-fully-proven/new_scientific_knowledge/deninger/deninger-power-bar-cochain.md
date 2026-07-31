# Deninger normalized power-semigroup cochain skeleton

- **ID:** `deninger-power-bar-cochain`
- **Stage:** 2-fully-proven
- **Type:** SOURCE COMPLEX LEMMA
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean status:** direct check passes in `DeningerArithmeticPowerBar.lean`

## Statement

Let \(M\) be a monoid acting additively on an abelian group \(V\); write \(T_m v=m\cdot v\).
The first three inhomogeneous bar coboundaries are
\[
\begin{aligned}
 (Q^0v)(n)
   &=T_n v-v,\\
 (Q^1\phi)(m,n)
   &=T_m\phi(n)-\phi(mn)+\phi(m),\\
 (Q^2\psi)(\ell,m,n)
   &=T_\ell\psi(m,n)-\psi(\ell m,n)
     +\psi(\ell,mn)-\psi(\ell,m).
\end{aligned}                                                     \tag{1}
\]
They satisfy
\[
 Q^1Q^0=0,\qquad Q^2Q^1=0.                                       \tag{2}
\]
Consequently
\[
 C^0=V,\qquad C^1=\operatorname{Map}(M,V),\qquad
 C^2=\ker Q^2                                                     \tag{3}
\]
with differentials \(Q^0,Q^1\) is the good degree-two truncation of the bar cochain complex.
It retains the genuine degree-two cocycle condition instead of creating spurious \(H^2\) by
brutal truncation.

For Deninger's source take
\[
 M_S=\left\{\prod_{p\in S}p^{e_p}:e_p\in\mathbb N\right\}
\]
acting through the coherently oriented framed power transfers \(T_n\).  At finite weight \(N\),
restrict a \(k\)-cochain to non-unit tuples
\((n_1,\ldots,n_k)\) with
\(\sum_i\sum_{p\in S}v_p(n_i)\le N\).  Every face either composes adjacent entries, preserving
total weight, or drops an entry, decreasing it.  Thus `(1)` restricts to a finite-dimensional
cochain skeleton whenever the coefficient packet \(V_{S,N,A}\) is finite-dimensional.

## Proof

For \(v\in V\),
\[
\begin{aligned}
(Q^1Q^0v)(m,n)
 &=T_m(T_nv-v)-(T_{mn}v-v)+(T_mv-v)\\
 &=T_mT_nv-T_mv-T_{mn}v+v+T_mv-v\\
 &=0
\end{aligned}
\]
because \(T_mT_n=T_{mn}\).

For \(\phi:M\to V\), expand:
\[
\begin{aligned}
(Q^2Q^1\phi)(\ell,m,n)
={}&T_\ell T_m\phi(n)-T_\ell\phi(mn)+T_\ell\phi(m)\\
 &-T_{\ell m}\phi(n)+\phi(\ell mn)-\phi(\ell m)\\
 &+T_\ell\phi(mn)-\phi(\ell mn)+\phi(\ell)\\
 &-T_\ell\phi(m)+\phi(\ell m)-\phi(\ell).
\end{aligned}
\]
All terms cancel, using \(T_\ell T_m=T_{\ell m}\) and associativity
\((\ell m)n=\ell(mn)\).  This proves `(2)`.  Since \(Q^2Q^1=0\), \(Q^1\) lands in
\(\ker Q^2\), proving `(3)`.

For the bounded power monoid, composing \(n_i,n_{i+1}\) replaces
\[
\sum_p v_p(n_i)+\sum_p v_p(n_{i+1})
\]
by
\[
\sum_p v_p(n_in_{i+1}),
\]
which is equal by additivity of valuations.  The remaining faces drop a nonnegative summand.
The finite-weight restriction is therefore a sub-semisimplicial system and inherits `(2)`.

## Consequence for arithmetic cohomology

The finite differential in `deninger-mw-gamma-brst-complex` is no longer an unspecified
"incidence boundary."  Its algebraic skeleton is `(1)`.  Remaining source data are:

1. coefficient packet \(V_{S,N,A}\) from integral Milnor--Witt/\(\mathrm{ko}\) and Gamma
   boundary data;
2. framed transfer action \(T_n\);
3. chain cup/trace;
4. fixed positive Gamma metric and its adjoint.

Nilpotence is then formal from the transfer composition law.  Hodge-flow compatibility remains
separate and cannot be inserted into `(1)`.

## Hostile audit

- Using \(C^2=\operatorname{Map}(M^2,V)\) and stopping there would make every 2-cochain a
  cocycle.  The good truncation \(C^2=\ker Q^2\) is mandatory.
- A cutoff by the size \(n\le N\) is not stable under the inner face \(mn\).  The additive
  valuation-weight cutoff is stable and must be used.
- Projecting a transfer back into an analytic cutoff can destroy \(T_mT_n=T_{mn}\).  The
  algebraic bar differential must be formed before analytic compression.

## Novelty audit

Bar coboundaries are standard.  New content is the dependency-closed extraction of the exact
good truncation and the valuation-stable finite filtration needed by Deninger's power
correspondences.  No broader novelty is claimed.
