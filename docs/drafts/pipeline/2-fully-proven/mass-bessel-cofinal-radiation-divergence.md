# Mass-Bessel cofinal radiation divergence

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED]`  
**Origin:** positive survivor of the uniform finite-aperture completion conjecture

## 1. Exact theorem

Fix `a>0` and `\sigma>0`.  For `X\ge2`, let

\[
 D_X(u)=
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 \frac{2a(\sigma+iu)
 K_1\!\left(a\sqrt{(\sigma+iu)^2+(\log n)^2}\right)}
 {\sqrt{(\sigma+iu)^2+(\log n)^2}}.
\]

Put `u_X=(\log X)^4`.  Then

\[
 D_X(u_X)=
 \sqrt{2\pi a}\,(\sigma+iu_X)^{-1/2}e^{-a(\sigma+iu_X)}
 \left(2(\sqrt2-1)\sqrt X+o(\sqrt X)\right).
\]

In particular, there are `c_{a,\sigma}>0` and `X_0` such that

\[
 |D_X(u_X)|\ge
 c_{a,\sigma}\frac{\sqrt X}{(\log X)^2}
 \qquad(X\ge X_0).
\]

Consequently

\[
 \limsup_{X\to\infty}\|D_X\|_{L^\infty(\mathbb R_u)}=+\infty,
\]

and the finite mass-Bessel prime apertures are not Cauchy in vertical sup norm.

## 2. Proof

Set `L=\log X`, `t=\sigma+iL^4`, and `x=\log n`.  On `X<n\le2X`,
`x=L+O(1)`, hence `x^2/t^2=O(L^{-6})`.  The principal square root is analytic
in a fixed neighborhood of `1`, so uniformly on the shell

\[
 z:=\sqrt{t^2+x^2}
 =t\sqrt{1+x^2/t^2}
 =t+\frac{x^2}{2t}+O(x^4/|t|^3)
 =t+O(L^{-2}).
\]

The points `az` stay in a closed subsector of `|\arg z|<3\pi/2`.  Uniform
large-argument asymptotics give

\[
 K_1(az)=\sqrt{\frac{\pi}{2az}}e^{-az}(1+O(|z|^{-1})).
\]

Using `z/t=1+O(L^{-6})` and `e^{-a(z-t)}=1+O(L^{-2})`, we obtain

\[
 \frac{2atK_1(az)}z
 =\sqrt{2\pi a}\,t^{-1/2}e^{-at}(1+O(L^{-2}))
\]

uniformly for the entire dyadic shell.  Because all coefficients
`\Lambda(n)/\sqrt n` are nonnegative, the relative error remains `O(L^{-2})`
after summation.

Partial summation from `\psi(x)=x+o(x)` gives

\[
 \sum_{X<n\le2X}\Lambda(n)n^{-1/2}
 =2(\sqrt2-1)\sqrt X+o(\sqrt X).
\]

Substitution proves the asymptotic.  Finally

\[
 |t|^{-1/2}=L^{-2}(1+o(1)),
 \qquad |e^{-at}|=e^{-a\sigma},
\]

which proves the lower bound and divergence.

## 3. Dependency ledger

- analytic expansion of the principal square root near `1`;
- uniform sectorial large-argument asymptotic for `K_1`;
- prime number theorem and partial summation;
- positivity of `\Lambda`.

No RH-equivalent estimate enters.

## 4. Scientific content

The divergence comes from the opposite regime to the light-cone saddle studied
previously.  At `u\gg(\log X)^2`, every prime in a fixed logarithmic aperture
has the same leading massive radiation phase.  Finite-source positivity then
amplifies rather than cancels.

Therefore the desired bounded full trace cannot be assembled uniformly from
bounded finite traces.  It requires cancellation with primes whose aperture
grows with observation time.  This makes the open core intrinsically cofinal.

## 5. Novelty audit

Parent ingredients are classical.  The exact dyadic cofinal divergence and its
interpretation as failure of regular source completion were not found in the
route corpus or exact-collision search.  Label remains `[LOCAL-RESEARCH]` until
a wider literature audit establishes priority.

## 6. Lean target

Required formal stack:

1. define the mass carrier by its Fourier integral, avoiding an unformalized
   `K_1` constant;
2. prove uniform deep-time stationary phase for `x` in a dyadic logarithmic
   shell;
3. import/formalize the needed PNT partial-summation consequence;
4. derive the explicit dyadic lower bound.

Status: `[PAPER-PROVED]`; no unconditional Lean theorem yet.
