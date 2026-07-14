# Prime--archimedean Bernstein Abel selection law

- **ID:** prime-arch-bernstein-abel-selection-law
- **Stage:** 3-formalized
- **Type:** bridge theorem
- **Status:** `[PROVEN; FORMALIZED]`
- **Primary formalization:** `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelSusceptibility.lean`

## Theorem

Let `Pi_n` be the squared `l2` norm of the degree-`n` endpoint Bernstein coefficient vector of
the normalized completed Xi moment source, and define its positive Abel susceptibility by

\[
  \chi(t)=\sum_{n\ge0}\Pi_n t^n.
\]

Then:

1. `chi(t)` converges unconditionally for
   \[
     0\le t<\frac{250000}{251001};
   \]
2. every endpoint Bernstein coefficient of degree at most `13` is nonnegative, and the canonical
   total Bernstein negative mass is exactly zero through defect degree `12`;
3. the full unit-interval extension is equivalent to RH:
   \[
     \mathrm{RH}
     \iff
     \chi(t)<\infty\quad\text{for every }0\le t<1;
   \]
4. if RH is false, the source-attained exponential lower envelope selects a parameter
   `t in (0,1)` for which `chi(t)` diverges.

More sharply, there is a unique exact Abel radius `R_A` and it is reciprocal to the unique common
purity/dissipation exponent `E_*`:

\[
  \frac{250000}{251001}<R_A\le1,
  \qquad
  1\le E_*<\frac{251001}{250000},
  \qquad
  R_AE_*=1.
\]

Furthermore,

\[
  \mathrm{RH}\iff R_A=1\iff E_*=1.
\]

Under false RH, `E_* = B^2` and `R_A = B^{-2}` for an amplitude `B` attained by an actual
off-critical Xi divisor atom with `1 < B < 501/500`.

## Proof structure

The unconditional interval follows from the completed-divisor sector estimate

\[
  \Pi_n\le A_*^2\left(\frac{501}{500}\right)^{2n}
\]

and geometric comparison.  The finite positivity statement is the direct Bernstein-diagonal
image of the proved scaled Hausdorff rectangle `k <= 13`, `r <= 43`.

Under RH, every purity satisfies `Pi_n <= s_0^2`, so the Abel series converges throughout the open
unit interval.  If RH fails, there are `rho > 1`, `eta > 0` such that eventually

\[
  \eta\rho^n\le(n+1)\Pi_n.
\]

Choosing

\[
  t=\frac{1+\rho^{-1}}2
\]

gives `0 < t < 1`, `rho t > 1`, and

\[
  \Pi_n t^n\ge\frac{\eta(\rho t)^n}{n+1}\longrightarrow+\infty.
\]

Thus the susceptibility cannot be summable at that interior parameter.

## RH contribution

The missing source estimate is localized to the thin collar

\[
  \frac{250000}{251001}\le t<1.
\]

A successful source construction must extend the already-proved positive Abel chamber across
that collar.  This is strictly more precise than asking for unspecified positivity or boundedness,
but it remains an RH-equivalent endpoint obligation rather than an RH proof.

## Verification

The primary theorem and all supporting declarations elaborate without project-specific axioms.
The formal lint gate passes.

## Paper

The focused publication manuscript is
`docs/drafts/pipeline/4-publication-ready/prime-arch-abel-susceptibility-selection/main.tex`.

## Top-down Legendre--Pringsheim splice

The paper theorem
[`prime-arch-bernstein-legendre-double-source-kernel.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-legendre-double-source-kernel.md)
identifies the whole susceptibility germ with one endpoint-normalized prime--Gamma double moment
of an explicit Legendre square-root kernel.  For a conjugate source pair `u, conj(u)`, its
discriminant factors as

\[
 (1-(|u|+|1-u|)^2t)(1-(|u|-|1-u|)^2t).
\]

Thus the exact false-RH radius `B^(-2)` proved here is the positive reflected-kernel pinch attached
to the attained maximal amplitude `B`.

The companion
[`prime-arch-bernstein-pringsheim-collar-transfer.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-pringsheim-collar-transfer.md)
proves that an independent holomorphic prime--Gamma evaluation of this kernel on one connected
neighborhood of `[250000/251001,1)` forces `R_A=1` and hence RH.  The live source task is
[`prime-arch-bernstein-reflected-kernel-collar.md`](../../1-in-progress/prime-arch-bernstein-reflected-kernel-collar.md).
It is a continuation problem for one explicit double-kernel value, not a request to reprove the
coefficient-growth criterion in this card.

The additional paper value relation
[`prime-arch-bernstein-mobius-pullback-gutzmer-law.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-mobius-pullback-gutzmer-law.md)
gives a one-source form before the Legendre elimination:

\[
 \sum_{n\ge0}P_n(w)s^n
 =\frac1{1-s}M_R\!\left(\frac{s(w-1)}{1-s}\right),
\]

and recovers `chi(r^2)` as its exact double-torus Gutzmer norm.  This locates `R_A=B^(-2)` at the
first Möbius-pulled prime--Gamma pole reaching the torus radius `r=B^(-1)`.

## Paper-level meromorphic collar interface

The exact Abel radius selected here is sharpened in
[`prime-arch-bernstein-half-order-pringsheim-singularity.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-half-order-pringsheim-singularity.md).
If RH is false and the radius is `B^(-2)<1`, then

\[
 \sqrt{1-B^2t}\,\chi(t)\to c_B>0.
\]

Hence no single-valued meromorphic continuation exists at that radius. The top-down source
hypothesis can therefore be weakened from a holomorphic collar to a meromorphic collar while
retaining the implication to RH. This refinement is paper-proven and not yet formalized.
