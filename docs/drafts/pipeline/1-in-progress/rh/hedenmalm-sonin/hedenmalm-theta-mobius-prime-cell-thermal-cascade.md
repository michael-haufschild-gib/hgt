# Hedenmalm--theta Möbius prime-cell thermal cascade

- **ID:** P-G45
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** `rh-current-frontier-map.md` Route P; P-G41--P-G44 pole-unit endpoint geometry
- **Statement:** Every literal prime Euler factor of the normalized squarefree Möbius midpoint Gram is a Bernoulli Hellinger cell with one interior thermal defect peak; peak scales are strictly ordered by prime odds.

## Goal

Resolve the entire finite-temperature geometry between P-G42's strict hot-edge curvature and
P-G44's prime-two cold shell.  Test whether a global monotone source current can force Route-P
Julia saturation.  Required theorem must retain literal prime factors and must not assume an Xi
divisor location.

## Gates

- [x] 0 → 1 in-progress: source-pure cell, exact conjecture, proof, corpus collision audit
- [ ] 1 → 2 fully-proven: complete paper proof and hostile audit finalized after Lean check
- [ ] 2 → 3 formalized: module green, final build, lint, and axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem and external novelty audit

## Exact prime cell

Fix `0<x<z`, put

\[
 y=\frac{x+z}{2},\qquad \delta=\frac{z-x}{2},\qquad
 q_p=p^{-1},\qquad T=p^{\delta\varepsilon},\qquad r=\frac y\delta>1.
\]

The `p`-Euler factor of the finite squarefree midpoint Gram is

\[
 G_p(\varepsilon;x,z)
 =\frac{(1+p^{-1-y\varepsilon})^2}
 {(1+p^{-1-x\varepsilon})(1+p^{-1-z\varepsilon})}.
\tag{1}
\]

Writing `A=q_pT^{-r}=p^{-1-yε}`, equation `(1)` becomes

\[
 G(A,T)=\frac{(1+A)^2}{(1+AT)(1+A/T)}.
\tag{2}
\]

This is the squared Hellinger affinity of two Bernoulli laws whose odds are `AT` and `A/T`.
Its projective Julia defect odds are exactly

\[
 W(A,T):=G(A,T)^{-1}-1
 =\frac{A(T-1)^2}{T(1+A)^2}.
\tag{3}
\]

Thus `0<G_p<1` at every finite `ε>0` when `x≠z`, while `G_p(0)=1` and
`G_p(ε)→1` as `ε→∞`.  Every individual prime cell leaves saturation and later returns.

## P-G45 thermal-cascade theorem `[PROVED HERE]`

Along the forced thermal path `A(T)=qT^{-r}`, logarithmic differentiation of `(3)` gives

\[
 W'(T)=\frac{W(T)}{T(T-1)(1+A(T))}\,B_{q,r}(T),
\tag{4}
\]

where

\[
 B_{q,r}(T)
 =[(r+1)-(r-1)T]
 +qT^{-r}[(r+1)T-(r-1)].
\tag{5}
\]

Above the aperture threshold

\[
 T_0=\frac{r+1}{r-1}=\frac zx,
\]

the peak equation `B=0` is

\[
 qT^{-r}=R_r(T),\qquad
 R_r(T)=\frac{(r-1)T-(r+1)}{(r+1)T-(r-1)}.
\tag{6}
\]

Left side of `(6)` is strictly decreasing from a positive value to zero.  Right side is strictly
increasing from zero; indeed, for `T_1<T_2`, cross multiplication gives

\[
 R_r(T_2)-R_r(T_1)
 =\frac{4r(T_2-T_1)}
 {((r+1)T_1-(r-1))((r+1)T_2-(r-1))}>0.
\tag{7}
\]

Existence follows by the intermediate value theorem: at `T_0` mass exceeds `R_r=0`; at
`T_0+1`, `R_r` is positive, while `qT^{-r}` eventually falls below that fixed value.  Strict
opposite monotonicities give uniqueness.  Let `T_p^*` be this root.  Equations `(4)--(6)` give

\[
 W_p'(T)>0\quad(T<T_p^*),\qquad
 W_p'(T)<0\quad(T>T_p^*).
\tag{8}
\]

Hence every prime cell has exactly one defect maximum, equivalently exactly one Gram minimum.

If `p<\ell`, then `q_\ell<q_p`.  Decreasing the left side of `(6)` moves its intersection with
the increasing `R_r` strictly left:

\[
 T_\ell^*<T_p^*.
\tag{9}
\]

The physical peak temperature

\[
 \varepsilon_p^*=\frac{\log T_p^*}{\delta\log p}
\]

is therefore also strictly decreasing with `p`: numerator decreases while denominator increases.
Large primes peak arbitrarily close to the critical edge; prime two is the last infrared cell.

## Higher-principle interpretation

P-G41--P-G44 were endpoint shadows of one renormalization flow:

1. At each fixed prime, Bernoulli Hellinger defect is transient: zero → one peak → zero.
2. Peak locations form a strict prime-ordered cascade from ultraviolet to infrared.
3. The nontrivial P-G40 Hardy Gram at `ε→0+` is not one local defect.  It is accumulation of
   infinitely many prime peaks at the singular critical boundary.
4. P-G42 measures finite part of this ultraviolet accumulation after pole removal.
5. P-G44 detects last infrared exit through prime two.

This explains why both endpoint scalar strategies stalled.  They observe opposite ends of a
conservative cascade.  Any Route-P producer must supply a nonlocal prime differential that kills
the complete peak train before positive Euler multiplication.  Finite-prime cancellation,
endpoint monotonicity, and cold normalization cannot force same-fibre neutrality.

## Hostile audit / no-theatre boundary

- Bernoulli Hellinger affinity itself is corpus-known.  New content is its exact identification
  with the forced finite squarefree midpoint path, unique peak equation `(6)`, and strict
  prime-order law `(9)`.
- The theorem does not prove RH.  Every off-diagonal aperture produces the same cascade.
- It kills the conjecture that P-G42's positive edge curvature extends to a globally monotone
  primewise source correction.  Individual Euler factors initially move away from saturation.
- Product-level monotonicity is not inferred from cellwise behavior.  Ultraviolet accumulation is
  singular, so termwise differentiation at `ε=0` is forbidden.
- Existence of peaks uses only real Euler half-plane data, no computation and no Xi zeros.

## Lean certificate

Target module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellThermalCascade.lean
```

Target declarations:

- `one_div_bernoulliMidpointGramSq_sub_one`;
- `hasDerivAt_thermalBernoulliMidpointDefectOdds`;
- `existsUnique_thermalBernoulliPeak`;
- `deriv_thermalBernoulliMidpointDefectOdds_sign_of_root`;
- `squarefreeMobiusPrimeCellGramSq_eq_bernoulliMidpointGramSq`;
- `squarefreeMobiusPrimeCellPeak_ordered`.

## Exact survivor

Construct a genuinely nonseparable prime differential coupling neighboring peak cells before
Euler multiplication.  Required source law must not be a vertex-potential/coboundary, since newer
Route-J/L audits classify all separable clock ratios as flat or similarity-trivial.  It must
annihilate the complete peak train, not merely conserve its total defect.

## Log

- 2026-08-12 — global-monotonicity conjecture falsified at prime-cell level; exact defect odds,
  derivative balance, unique peak, and strict prime ordering proved on paper; Lean module started.
