# Groskin archimedean tail order without numerical certification

- **ID:** `groskin-archimedean-tail-order-no-computation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Akiva Groskin, arXiv:2607.02828, Lemma 3.1 and Theorem 3.2
- **Statement:** Past an analytically produced finite threshold, the omitted CCM archimedean tail is an explicit positive-semidefinite Cauchy--Stieltjes Gram increment; no numerical value of the digamma density is used.

## Goal

Import the exact finite tail-order mechanism used by Route B while respecting the corpus rule that
no numerical computation may discharge a sign. The theorem gives a source-defined Loewner-positive
archimedean correction against which the local rectangular boundary charge can be compared. It
does not assert Weil positivity or RH.

## Gates

- [x] 0 → 1 in-progress: source-faithful statement, exact carrier, analytic proof strategy
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, `lake env lean` and final module build green
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate

## Source objects

Put

\[
  h_+(T)=\Re\psi\!\left(\frac14+\frac{iT}{2}\right)-\log\pi.
\]

For a positive scale `rho`, a finite real node family `x_i`, and `T/rho` outside every node, put

\[
  p_T(i)=\frac1{T/\rho-x_i},\qquad
  q_T(i)=\frac1{T/\rho+x_i}.
\]

For `0 < L`, the exact Groskin density is

\[
  K_T(i,j)=
  \frac{h_+(T)\sin^2(LT/2)}{\pi^2\rho}
  \bigl(p_T(i)p_T(j)+q_T(i)q_T(j)\bigr).
\]

The tail increment on `[T1,T2]` is its entrywise integral.

## Paper proof

`[PROVED HERE]`

### 1. Eventual positivity of the literal digamma density

The corpus theorem `re_digamma_vertical_tendsto_atTop` gives

\[
  \Re\psi\!\left(\frac14+i t\right)\longrightarrow +\infty.
\]

Composition with `t=T/2`, which tends to `+∞`, and subtraction of the constant `log pi` give

\[
  h_+(T)\longrightarrow +\infty.
\]

Hence there is a finite `T0` such that `0 < h_+(T)` for every `T ≥ T0`. This replaces Groskin's
interval-certified value `h_+(7)>0` by a purely analytic, noncomputational threshold. It weakens
only the explicit cutoff `7`; the source density and all later identities are unchanged.

### 2. Pointwise Gram identity

For every coefficient vector `c`, direct expansion gives

\[
  \sum_{i,j}\overline{c_i}K_T(i,j)c_j
  =
  \frac{h_+(T)\sin^2(LT/2)}{\pi^2\rho}
  \left(
    \left|\sum_i c_i p_T(i)\right|^2+
    \left|\sum_i c_i q_T(i)\right|^2
  \right).
\]

Past `T0`, and while `T/rho` avoids the finite node set, every scalar factor is nonnegative.
Therefore `K_T` is positive semidefinite.

### 3. Integrated Loewner order

On a compact interval `[T1,T2]` lying strictly past the threshold and the node poles, every entry is
continuous and integrable. Entrywise integration preserves Hermitian positive semidefiniteness,
so

\[
  \Delta_{T_1,T_2}=\int_{T_1}^{T_2}K_T\,dT\succeq0.
\]

This is the unconditional Loewner-order part of Groskin Theorem 3.2. Strict positive definiteness
and strict total positivity are separate stronger claims requiring rational separation and the
Cauchy determinant/Andreief argument; they are not asserted by this card.

## Approach

1. Reuse the corpus's unconditional vertical-digamma limit.
2. Define the literal `h_+`, `p_T`, `q_T`, rank-two kernel, and compact-interval increment.
3. Reuse `HTGeometry.integralMatrixKernel_posSemidef` for the integrated order theorem.
4. Wire the finished module into `RHTower.lean`.

## No-go closure

- **Exact killing theorem/mechanism:** the published cutoff `7` depends on an interval evaluation of `h_+(7)` and is disallowed under the no-computation rule.
- **Strongest positive survivor:** eventual literal-density positivity and the exact source-specific Cauchy--Stieltjes Gram increment need no numerical input.
- **New insight:** Route B needs the tail's order and budget mechanism, not the special integer `7`; an analytic threshold preserves the mechanism.
- **Status:** dependency-closed paper proof of the semidefinite Loewner order; ready for Lean. Strictness and total positivity are separate follow-on claims.

## Log

- 2026-08-01 — created in 1-in-progress from exact external theorem; computation-certified cutoff replaced by analytic eventual threshold.
