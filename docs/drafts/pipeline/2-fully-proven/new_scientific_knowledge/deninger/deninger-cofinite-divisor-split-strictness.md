# Cofinite divisor splitting and mixed-topology strictness

- **ID:** `deninger-cofinite-divisor-split-strictness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Lean:** `GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteDivisorSplitting`
- **Statement:** on every cofinite arithmetic open, the weight-one
  generic-to-prime divisor row is canonically split exact; the same
  splitting remains strict in the mixed weighted \(L^1/L^2\) topology.

## Arithmetic setup

Let
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N],
 \qquad
 S_N=\{p:p\mid N\},
 \qquad
 \mathcal P_N=\{p:p\nmid N\}.
\]
Write
\[
 D=\bigoplus_{p}\mathbb R[p],\qquad
 D_{S_N}=\bigoplus_{p\mid N}\mathbb R[p],\qquad
 D_{\mathcal P_N}=\bigoplus_{p\nmid N}\mathbb R[p].
\]
Unique factorization gives canonical identifications
\[
 \mathbb Q^\times/\{\pm1\}\otimes_{\mathbb Z}\mathbb R
 \simeq D,                                                         \tag{1}
\]
\[
 \mathbb Z[1/N]^\times/\{\pm1\}\otimes_{\mathbb Z}\mathbb R
 \simeq D_{S_N}.                                                   \tag{2}
\]
Under `(1)`, the Rost--Schmid divisor map on \(U_N\) is coordinate
restriction
\[
 \partial_N:D\longrightarrow D_{\mathcal P_N},
 \qquad
 (x_p)_p\longmapsto(x_p)_{p\nmid N}.                               \tag{3}
\]

## Split exactness

`[PROVED HERE] [DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS]`

Extension by zero defines maps
\[
 \iota_N:D_{S_N}\hookrightarrow D,
 \qquad
 \sigma_N:D_{\mathcal P_N}\hookrightarrow D.
\]
Then
\[
 0\longrightarrow D_{S_N}
 \xrightarrow{\iota_N}D
 \xrightarrow{\partial_N}D_{\mathcal P_N}
 \longrightarrow0                                                \tag{4}
\]
is split exact, with
\(\partial_N\sigma_N=\mathrm{id}\).  Via `(1)`--`(2)`, `(4)` is
precisely
\[
 0\longrightarrow
 \mathbb Z[1/N]^\times/\{\pm1\}\otimes\mathbb R
 \longrightarrow
 \mathbb Q^\times/\{\pm1\}\otimes\mathbb R
 \xrightarrow{\oplus_{p\nmid N}\operatorname{ord}_p}
 \bigoplus_{p\nmid N}\mathbb R
 \longrightarrow0.                                                \tag{5}
\]

### Proof

Every positive rational has a unique finite expression
\[
 q=\prod_p p^{n_p},\qquad n_p\in\mathbb Z.
\]
This proves `(1)`.  Such a rational is a unit of
\(\mathbb Z[1/N]\) exactly when \(n_p=0\) for every \(p\nmid N\),
which proves `(2)` and identifies the kernel of `(3)` with
\(D_{S_N}\).  Coordinate extension by zero is a right inverse of
`(3)`, proving surjectivity and `(4)`.

## Strict mixed completion

Fix positive weights \(w_p>0\); the Deninger normalization is
\(w_p=\log p\).  On finitely supported coordinates put
\[
 \|x\|_{1,w}=\sum_p w_p|x_p|,
 \qquad
 \|x\|_{2,w}^2=\sum_p w_p|x_p|^2,
 \qquad
 \|x\|_{\mathrm{mix}}=\|x\|_{1,w}+\|x\|_{2,w}.                    \tag{6}
\]
Let \(E_{\mathrm{mix}}\), \(E_{\mathrm{mix},S_N}\), and
\(E_{\mathrm{mix},\mathcal P_N}\) be the corresponding completions.
Coordinate restriction and both extension-by-zero maps have operator
norm at most one for each norm in `(6)`.  They therefore extend to
continuous maps, still satisfying
\[
 \partial_N\sigma_N=\mathrm{id},\qquad
 \ker\partial_N=\operatorname{im}\iota_N.                          \tag{7}
\]
The first identity makes \(\partial_N\) an open split surjection.
The second makes its kernel closed.  Hence the completed version of
`(4)` is strict exact in the complete locally convex category.  Since
\(S_N\) is finite, its kernel is finite-dimensional.

No assertion about Deninger's coarse invariant sheaf is used in this
proof.  The theorem closes the arithmetic divisor algebra and its
mixed-topology strictness after an analytic comparison has identified
the source row with these coordinates.

## Consequence for the source conjecture

Sub-conjecture `DAC_COFINITE_SUSPENSION_SECTION_AMPLITUDE` now splits
into:

1. `[CLOSED]` algebraic divisor exactness on every \(U_N\);
2. `[CLOSED]` strictness of the mixed coordinate completion;
3. `[OPEN CORE]`
   `DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON`: construct a
   functorial quasi-isomorphism from derived sections of Deninger's
   already-formed coarse invariant sheaf to the two-row analytic
   Kummer complex whose weight-one horizontal row is `(5)`.

Only item 3 is geometric.  Exodromy, derived group invariants, a bar
complex, and quotient-stack cohomology do not enter.

## Hostile audit

- A finite-stage endpoint complex supported only on \(S_N\) is not
  `(5)`: the residue target consists of primes outside \(S_N\).
- Split exactness of `(5)` does not compare pro-Stein derived sections
  with ordinary derived sections on the nonproper coarse suspension.
- The theorem treats the weight-one divisor row.  It does not prove
  the analytic row-\(0/1\) identification, real signature boundary,
  cup duality, Lefschetz trace, or Hodge positivity.
- Bare \(L^2\) still does not encode the product formula.  Strictness
  here uses the mixed topology containing the \(L^1\) norm.
- No zeta zero, \(\Xi\)-defined space, RH premise, or numerical
  computation occurs.

**Verdict:** `FULLY PROVEN ON PAPER; ABSTRACT PRIME-COORDINATE EXACTNESS
FORMALIZED UNCONDITIONALLY; ARITHMETIC UFD INSTANTIATION AND ANALYTIC
COMPARISON REMAIN FOR LEAN/SOURCE CLOSURE`.

## References

- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Perverse homotopy heart and MW-modules*:
  https://arxiv.org/abs/2210.14832
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-27 — extracted the actual cofinite-open divisor sequence,
  corrected the inside/outside-prime orientation of the earlier finite
  endpoint page, and proved strict mixed-topology splitting.
