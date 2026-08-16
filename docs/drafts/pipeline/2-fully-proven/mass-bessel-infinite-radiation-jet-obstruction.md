# Mass-Bessel infinite radiation-jet obstruction

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED] [NOVELTY UNVERIFIED]`

## 1. Exact theorem

Fix `a>0`, `\sigma>0`, and a nonnegative integer `m`.  Let `Q_{j,a}` be the
unique Poincare coefficient polynomials in

\[
 \frac{2atK_1(a\sqrt{t^2+x^2})}{\sqrt{t^2+x^2}}
 \sim \sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \sum_{j\ge0}Q_{j,a}(x^2)t^{-j}
\]

as `|t|\to\infty` in a fixed closed subsector containing the positive
imaginary direction.

For the dyadic shell `X<n\le2X`, define its order-`m` radiation remainder

\[
 \begin{aligned}
 R_{m,X}(t):={}&
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}B_a(t,\log n)\\
 &-\sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \sum_{j=0}^{m-1}t^{-j}
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{j,a}((\log n)^2),
 \end{aligned}
\]

where the second line is empty for `m=0`.  Put
`t_X=\sigma+i(\log X)^4`.  Then

\[
 R_{m,X}(t_X)
 =C_{a,\sigma,m}(X)\,
   \frac{\sqrt X}{(\log X)^{2m+2}},
\]

where `|C_{a,\sigma,m}(X)|` converges to a strictly positive constant.
Consequently

\[
 \lim_{X\to\infty}|R_{m,X}(t_X)|=+\infty
\]

for every finite `m`.

## 2. Coefficient classification

For every `j\ge0`,

\[
 \deg Q_{j,a}=j,
 \qquad [s^j]Q_{j,a}(s)=\frac{(-a/2)^j}{j!}.
\]

Indeed, put `s=x^2` and expand

\[
 \sqrt{t^2+s}
 =t+\frac{s}{2t}-\frac{s^2}{8t^3}+\cdots.
\]

At inverse order `t^{-j}`, the only contribution of `s`-degree `j` is the
`j`th power of `-as/(2t)` in
`\exp(-a(\sqrt{t^2+s}-t))`.  Every correction from `t/z`, `z^{-1/2}`, the
higher square-root terms, or the standard `K_1` coefficient series has smaller
`s`-degree at that order.  This proves the formula and nonvanishing.

## 3. Uniform shell asymptotic

Let `L=\log X`, `t=t_X`, and `x=\log n` for `X<n\le2X`.  Then `x=L+O(1)` and
`x^2/t=O(L^{-2})`.  The sectorial `K_1` expansion through order `m` and its
remainder are therefore uniform over the shell:

\[
 B_a(t,x)=\sqrt{2\pi a}\,e^{-at}t^{-1/2}
 \left(\sum_{j=0}^{m}Q_{j,a}(x^2)t^{-j}
 +O_m(L^{2m+2}|t|^{-m-1})\right).
\]

After subtracting the first `m` terms, the `j=m` contribution dominates the
uniform remainder by a factor tending to infinity.

The prime number theorem with partial summation gives

\[
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 Q_{m,a}((\log n)^2)
 =\frac{(-a/2)^m}{m!}
 2(\sqrt2-1)\sqrt X L^{2m}(1+o(1)).
\]

Since `|t|^{-m-1/2}=L^{-4m-2}(1+o(1))`, the asserted scale is
`\sqrt X L^{-2m-2}` with a nonzero limiting coefficient.

## 4. Dependency ledger

- all-orders sectorial Poincare expansion and fixed-order remainder for `K_1`;
- analytic binomial expansion of the principal square root;
- coefficient-degree bookkeeping;
- PNT partial summation for a fixed logarithmic polynomial weight;
- positivity of the von Mangoldt coefficients on a dyadic shell.

No zero-free region beyond the classical prime number theorem and no RH input
enters.

## 5. Scientific content

Finite prime apertures do not fail because one leading divergence was left
unsubtracted.  Their failure has infinite asymptotic rank.  Each removed
radiation coefficient exposes a new nonzero logarithmic moment whose prime
mass defeats the next power of vertical-time decay.

Thus any completion built from finitely many moments, jets, Rees layers, or
local counterterms is excluded.  The exact open core, if solvable through this
representation, requires an infinite-jet singular quotient and a canonical
source-only summation on that quotient.

## 6. Hostile significance audit

Wrong interpretation: this theorem does not supply the summation functional
and does not improve a zero-free region.  It is a no-go classification.

Positive content: it gives a parameterized sharp lower law for every finite
renormalization order and unifies route-specific Bessel behavior with the
corpus's independent finite-Rees and regular-completion obstructions.

Exact-priority search found the parent `K_1` asymptotics but no collision with
the prime-shell theorem.  Scientific priority remains
`[NOVELTY UNVERIFIED]` pending specialist review.

## 7. Lean target

Formal proof must construct, not assume:

1. mass-carrier Fourier integral and its all-fixed-orders deep-time expansion;
2. coefficient polynomials with exact leading coefficient;
3. PNT partial summation for logarithmic polynomial weights;
4. dyadic lower bound for every `m`.

Status: `[PAPER-PROVED]`; Lean proof absent.

## Lean progress -- item 3, the arithmetic input at every order

`formal/GaloisForLFunctions/RHTower/DyadicVonMangoldtLogWeighted.lean` (new, umbrella-wired,
axiom-clean) proves the PNT partial summation with logarithmic polynomial weights that section 3
uses, for every order `m`.

| Card item | Declaration |
|---|---|
| the dyadic prime mass weighted by `n^{-1/2}` and `(log n)^{2m}` | `dyadicSqrtVonMangoldtLogMass` |
| on a dyadic shell the logarithm lies between `log X` and `log X + log 2` | `log_mem_dyadic` |
| hence the weighted mass is squeezed between the two shell endpoints times the unweighted mass | `dyadicSqrtVonMangoldtLogMass_bounds` |
| the shell distortion factor `((log X + log 2)/log X)^{2m}` tends to one | `tendsto_logShellRatio` |
| **`∑_{X<n<=2X} Λ(n) n^{-1/2} (log n)^{2m} ~ 2(√2 − 1) √X (log X)^{2m}`** | `tendsto_dyadicSqrtVonMangoldtLogMass` |

The `m = 0` case is the sibling card's `tendsto_dyadicSqrtVonMangoldtMass_div_sqrt`
(`dyadicSqrtVonMangoldtLogMass_zero` records the identification), so no partial summation is
redone: on a dyadic shell the logarithm is *constant to within `log 2`*, and a two-sided squeeze
transports the whole asymptotic to every logarithmic weight at once.  This is exactly the
statement that after subtracting `m` Poincaré terms the surviving prime mass still grows like
`√X (log X)^{2m}`, so no finite jet can absorb it.

### What remains

Items 1 and 2: the all-orders sectorial Poincaré expansion of `K_1` with a fixed-order remainder,
and the coefficient polynomials `Q_{j,a}` with `deg Q_{j,a} = j` and
`[s^j]Q_{j,a} = (-a/2)^j/j!`.  The corpus already owns the order-zero sectorial bound
`RHTower.norm_besselK1C_sub_leading_le_norm` (error in `|w|`, not `Re w`) and the integration-by-
parts engine `HTGeometry.BesselOrderAbsoluteAsymptotic` that produced it; the all-orders statement
is the same integration by parts iterated, with the coefficient bookkeeping of section 2.
