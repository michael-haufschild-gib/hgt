# Exact theta-source sixth-moment inequality

**Stage:** 3-formalized. **Scope:** first nonconstant completed prime--Gamma Hankel minor. **RH:** open.

## Closed source theorem

For the actual theta-cusp source, let
`m_j = 2 integral_0^infinity x^(2j) Phi(x) dx`. Then

\[
3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2\ge0.
\]

Equivalently, every real linear-polynomial completed source Hankel test is nonnegative:

```
forall_primeArchSourceTraceHankel_linear_nonneg_stein :
  ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re
```

This theorem has no arithmetic, sign, moment-bound, or RH premises.

## Exact source certificate

Set
\[
\rho(x)=e^{5x/2-\pi e^{2x}},\qquad e=e^{-\pi},\qquad
L_k=\int_0^\infty x^k\rho(x)\,dx.
\]
The corpus's Ward identity gives the first-atom moments
\[
W_0=2e-L_0,\quad W_1=4L_1-L_2,\quad
W_2=8L_3-L_4,\quad W_3=12L_5-L_6.
\]

The new unconditional bounds are
\[
L_0\ge\frac{1697}{10000}e,\qquad
W_1\ge\frac{423}{5000}e,\qquad
W_2\le\frac{5457}{500000}e,\qquad
W_3\ge\frac{441}{200000}e.
\]
In particular, `W_0 <= (18303/10000)e`. These are direct Ward bounds; the older Morse-energy and tightly rounded essential-moment targets are not needed.

For a polynomial-exponential primitive
\[
q(x)=\sum_{j=1}^J r_j(x)e^{-2jx},\qquad
Bq=(2\pi e^{2x}-5/2)q-q',
\]
the exact score `rho'=(5/2-2pi exp(2x))rho` implies
\[
\int_0^\infty(Bq)\rho=q(0)e.
\]
Every summand of `q rho` tends to zero at infinity: the negative exponential tilt is bounded by one and polynomial multiples of the Gibbs density tend to zero. The derivative is integrable by the same polynomial-Gibbs bounds. At zero the boundary value is exactly `q(0)e`.

Writing `t=exp(-2x)` gives the exact remainder
\[
P-Bq=P-2\pi\sum_jr_j(x)t^{j-1}
 +\sum_j\bigl(r_j'(x)+(5/2-2j)r_j(x)\bigr)t^j.
\]
The Lean source supplies four explicit rational polynomial families. At both rational endpoints
`314159/100000 <= pi <= 3927/1250`, each signed remainder has a positive-coefficient expansion in
`(4x)^k t^i (1-t)^(J-i)`. Affine interpolation in pi and `0<=t<=1` prove its sign on the entire half-line. The mass primitive has exponential degree four; the three Ward primitives have degree eight. Every polynomial identity is checked by `ring`; every coefficient sign is ordinary kernel-checked rational arithmetic.

## Transfer to the full theta source

Put `c=3005/2997`. The exact rational margins are
\[
9\frac{423}{5000}\frac{441}{200000}
 -14c^2\left(\frac{5457}{500000}\right)^2
 =\frac{2940012677}{1247501250000000}>0,
\]
\[
45\left(\frac{423}{5000}\right)^2
 -16c^2\frac{18303}{10000}\frac{5457}{500000}
 =\frac{18695040767}{24950025000000}>0.
\]
Keeping `e²` symbolically gives
`14(c W_2)² <= 9 W_1 W_3` and `16(c W_0)(c W_2) <= 45 W_1²`.

The already proved all-order atom comparison is
`2pi W_j <= m_j <= c(2pi W_j)`. Consequently
\[
14m_2^2\le9m_1m_3,\qquad16m_0m_2\le45m_1^2.
\]
Their positive combination is precisely three times the target:
\[
m_0(9m_1m_3-14m_2^2)+m_2(45m_1^2-16m_0m_2)
=3(3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2).
\]

## Lean and discovery provenance

- `formal/GaloisForLFunctions/RHTower/ThetaGibbsSteinIntegral.lean`: exact improper-integral identity and polynomial remainder comparison.
- `formal/GaloisForLFunctions/RHTower/ThetaGibbsSteinSourceMinor.lean`: explicit rational decompositions, unconditional Ward bounds, ratio inequalities, and completed source Hankel theorem.
- Both modules pass scratch checks and their final individual `lake --old --log-level=error build <module>` audits, and are wired into `RHTower.lean`. No umbrella or full build was run.
- Scratch `#print axioms` for the integration identity, Ward bounds, ratio bounds, and final theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. A scratch application also checks the exact `ThetaCuspSixthMomentHankelInequality` conclusion.
- Formal indexes are refreshed. Global `scripts/formal_tools.py lint` reports one pre-existing wiring error: `CCMRestrictedWeilPoleDiagonalSharpConstant` is unreachable from the umbrella. Neither new module has proof debt or a wiring error.
- Runpod scripts, raw optimizer output, exact rational candidates, and a concise report: `docs/drafts/pipeline/2-fully-proven/computations/theta-gibbs-stein-certificates-2026-09-06/`.

Runpod supplied candidate coefficients only. No numerical integral estimate, optimizer assertion, external computation, added axiom, or oracle enters the Lean proof.

## Remaining mathematical problem

All-degree completed source Hankel positivity is still unproved. The finite certificate above does not construct a uniform family of source-positive remainders for arbitrary polynomial tests. Any negative central source test must now have polynomial degree at least two. RH is neither proved nor disproved by this result.
