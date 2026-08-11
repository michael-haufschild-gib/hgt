# Mass-shifted hard-edge Paley--Wiener compactification

- **ID:** `mass-shifted-hard-edge-paley-wiener-compactification`
- **Stage:** 2-fully-proven / needs specialist audit
- **Route:** U, cofinal shifted-Xi Hankel degree escape
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-parabolic-degree-horizon`,
  `gaussian-heat-trace-rh-criterion`, and the corpus Xi divisor strip/counting bounds

## Result

Write the squared Xi nodes as `w_q=alpha_q^2`, put

\[
 \lambda_{y,q}=(y+\alpha_q^2)^{-1},\qquad
 \Phi_y[p]=\Re\sum_q\lambda_{y,q}p(\lambda_{y,q})^2,
\]

and let `H_N(y)` be the leading `N` by `N` shifted reciprocal-Hankel block. If RH is false, define

\[
 D(y)=\min\{N\ge1:H_N(y)\not\succeq0\}.
\]

Then there are constants `0<c<C<infinity` and `Y>0` such that

\[
 \boxed{\qquad c\sqrt y<D(y)\le C\sqrt y\qquad(y\ge Y).\qquad}       \tag{HEPW.1}
\]

The lower bound is the universal parabolic degree horizon. The new upper bound is obtained by an
exact hard-edge lift of a negative Paley--Wiener divisor test. Thus Route U degree escape is not an
arbitrary noncompact phenomenon: after the unique scaling `N/sqrt(y)`, it compactifies to the
finite-exponential-type Weil test space.

RH is not proved. Equation (HEPW.1) replaces the unbounded moving-degree obstruction by a finite-
type limiting source problem.

## 1. Exact hard-edge coordinate

Put `a=sqrt(y)` and

\[
 z_a(\alpha)=2a^2(a^2+\alpha^2)^{-1}-1
             ={a^2-\alpha^2\over a^2+\alpha^2}.                    \tag{HEPW.2}
\]

For the first-kind Chebyshev polynomial `T_k`, the Cayley identity is

\[
 T_k(z_a(\alpha))
 ={1\over2}\left[
  \left({a+i\alpha\over a-i\alpha}\right)^k+
  \left({a-i\alpha\over a+i\alpha}\right)^k\right].              \tag{HEPW.3}
\]

Equivalently, on the principal local branch,

\[
 T_k(z_a(\alpha))=\cos\!\left(2k\arctan(\alpha/a)\right).          \tag{HEPW.4}
\]

If `k/a->s/2`, then (HEPW.3) gives locally uniformly on `C`

\[
 T_k(z_a(\alpha))\longrightarrow\cos(s\alpha).                    \tag{HEPW.5}
\]

This is the Chebyshev hard-edge Mehler--Heine law in the literal shifted-Xi coordinate, with no
asymptotic choice of spectral chart.

## 2. Every even Paley--Wiener test has a degree-`O(a)` lift

Let `A` be a real even smooth function supported in `[-sigma,sigma]`, and write

\[
 f(\alpha)=\int_{-\sigma}^{\sigma}A(s)e^{is\alpha}\,ds.
\]

Set `h=2/a` and sample `A` on `s_k=kh`. Using the symmetric samples, define a real polynomial
`P_a` by

\[
 P_a(X)=hA(0)+2h\sum_{1\le k\le\sigma/h}A(kh)T_k(X).             \tag{HEPW.6}
\]

Then

\[
 \deg P_a\le {\sigma a\over2}+1,\qquad
 P_a(z_a(\alpha))\longrightarrow f(\alpha)                       \tag{HEPW.7}
\]

locally uniformly. The convention in (HEPW.6) agrees exactly with the full symmetric Riemann sum
for the Fourier transform used above.

The useful fact is stronger than local convergence. Put

\[
 \xi_a(\alpha)=a\arctan(\alpha/a).
\]

Poisson summation applied to the sampled smooth function `A` gives the exact periodization

\[
 P_a(z_a(\alpha))
 =\sum_{m\in\mathbb Z}f(\xi_a(\alpha)+\pi a m)                    \tag{HEPW.8}
\]

up to the same fixed Fourier convention. Xi spectral points lie in a fixed horizontal strip.
On that strip, `Im xi_a` is uniformly bounded. Since `f` is Schwartz on every fixed horizontal
strip, for every `M` there is `C_M` such that

\[
 |P_a(z_a(\alpha))|
 \le C_M\bigl(1+\min(|\Re\alpha|,a)\bigr)^{-M}.                  \tag{HEPW.9}
\]

For `|Re alpha|>=a`, the right side may equivalently be replaced by `C_M a^(-M)`. This is the
coefficient-free tail estimate that a single Chebyshev amplifier does not provide.

## 3. Convergence of the complete Xi divisor form

Define the reciprocal polynomial

\[
 p_a(X)=P_a(2a^2X-1).                                             \tag{HEPW.10}
\]

It has the same degree as `P_a`, and

\[
 p_a(\lambda_{a^2,q})=P_a(z_a(\alpha_q)).                        \tag{HEPW.11}
\]

The corpus strip and sector bounds give

\[
 \left|{a^2\over a^2+\alpha_q^2}\right|
 \le C{a^2\over a^2+(\Re\alpha_q)^2}.                           \tag{HEPW.12}
\]

Together with the zero-count bound `N(T)=O(T log T)`, (HEPW.9) and (HEPW.12) justify passage through
the complete multiplicity-exact divisor sum. Explicitly, split at `|Re alpha|=a`.

- Below `a`, (HEPW.9) gives a summable majorant `C_M(1+|Re alpha|)^(-2M)`.
- Above `a`, (HEPW.9) and (HEPW.12) give

  \[
  O\!\left(a^{2-2M}\sum_{|\Re\alpha_q|\ge a}|\alpha_q|^{-2}\right)
  =O(a^{1-2M}\log a)=o(1).                                      \tag{HEPW.13}
  \]

Therefore

\[
 \boxed{\quad
 a^2\Phi_{a^2}[p_a]
 \longrightarrow \Re\sum_q f(\alpha_q)^2.
 \quad}                                                         \tag{HEPW.14}
\]

This is the hard-edge compactification theorem. It is an equality of the actual Xi divisor forms,
not convergence of an abstract moment model.

## 4. RH failure supplies a negative finite-type limit

The Gaussian heat criterion already proves that RH failure gives a real polynomial `Q` and `t>0`
such that, with

\[
 g(\alpha)=Q(\alpha^2)e^{-t\alpha^2/2},
\]

one has

\[
 \Re\sum_q g(\alpha_q)^2<0.                                     \tag{HEPW.15}
\]

The Fourier transform of `g` on the real line is Schwartz and has Gaussian decay. Choose real
even smooth cutoffs `chi_R` tending to one and let `f_R` be the inverse Fourier transform of
`chi_R \widehat g`. Then `f_R` is real, even, Paley--Wiener, and Schwartz on horizontal strips.
Gaussian Fourier decay gives convergence to `g` in every such strip-Schwartz seminorm. The Xi
zero-count bound therefore permits passage through the divisor square sum, so

\[
 \Re\sum_q f_R(\alpha_q)^2\longrightarrow
 \Re\sum_q g(\alpha_q)^2.                                      \tag{HEPW.16}
\]

Fix `R` for which the left side is negative and denote the Fourier support radius by `sigma`.
Apply (HEPW.14). For all sufficiently large `a`, the polynomial `p_a` has degree at most
`sigma a/2+1` and satisfies

\[
 \Phi_{a^2}[p_a]<0.                                             \tag{HEPW.17}
\]

Hence

\[
 D(a^2)\le\deg p_a+1\le {\sigma\over2}a+2,                     \tag{HEPW.18}
\]

which is the upper half of (HEPW.1). The lower half follows from
`mass-shifted-parabolic-degree-horizon`.

## 5. Converse and compactified Route U frontier

Under RH, every `alpha_q` is real, so every shifted reciprocal atom is positive real and every
`H_N(y)` is positive definite. Thus (HEPW.14)--(HEPW.18) also give the exact cofinal criterion

\[
 \mathrm{RH}
 \Longleftrightarrow
 \text{no negative hard-edge Paley--Wiener limit occurs}.        \tag{HEPW.19}
\]

The value of (HEPW.1) is not the equivalence (HEPW.19). It is the two-sided scale theorem: a
hypothetical first defect cannot hide at `o(sqrt(y))`, and it never needs degree
`omega(sqrt(y))`. Any cofinal first-contact sequence has, after a subsequence, bounded nonzero
scaled degree `N/sqrt(y)` and a finite-exponential-type limiting test.

To finish Route U one must now exclude a finite-type limit that also inherits the canonical
first-contact null incidence and real-rooted Schur boundary structure. Generic Paley--Wiener/Weil
positivity would be RH itself. The next producer must use those inherited boundary constraints and
the literal completed prime--Gamma source.

## Conjecture--failure--pivot audit

1. **Critical Gamma clock is coefficient-independent.** **Failed.** The polynomial factor changes
   the effective Gamma clock. The universal `N^2/y` theorem is a worst-case domination law, not a
   literal concentration statement for every coefficient vector.
2. **One Cayley--Chebyshev amplifier forces a negative Hankel square.** **Failed.** Off-line norm
   amplification is phase-blind and already belongs to the corpus Cayley-visibility receiver. It
   does not orient the complete Hankel sum.
3. **Smooth Paley--Wiener packet lift.** **Proved.** Poisson-summed Chebyshev packets retain phase,
   have uniform divisor tails, and lift every finite-type Weil test at degree `O(sqrt(y))`.
4. **Arbitrary cofinal degree escape remains possible.** **Falsified.** Under RH failure, least
   defect degree is trapped between two positive multiples of `sqrt(y)`.

## Higher universal principle

Far-right reciprocal collapse sends every fixed spectral point to the endpoint `1` of the arcsine
chart at distance `alpha^2/y`. Degree `N` resolves an endpoint layer of width `N^(-2)`. Matching
these scales forces

\[
 N^{-2}\asymp y^{-1},\qquad N\asymp\sqrt y.
\]

At this scale Chebyshev waves become Fourier waves in `alpha`; polynomial degree becomes
exponential type. The earlier fixed-degree arcsine recession, heat action `td`, Cayley visibility,
and moving null-face obstruction are four coordinate shadows of this single hard-edge
compactification.

## Novelty audit

Corpus searches found fixed-degree arcsine recession, the heat degree--time wedge, generic Cayley
visibility, and the Gaussian Weil criterion, but no theorem identifying their cofinal
`N/sqrt(y)` limit or proving the two-sided defect law (HEPW.1). Literature searches found classical
Mehler--Heine hard-edge asymptotics, Paley--Wiener theory, and semiclassical Weil frameworks, but no
shifted-Xi reciprocal-Hankel compactification or least-bad-block `Theta(sqrt(y))` theorem. No
priority claim is made without specialist audit.

## Lean status

No Lean declaration is claimed. A faithful formalization must include the literal Chebyshev--Cayley
evaluation, sampled smooth Fourier packet, Poisson-summation tail estimate on the Xi strip,
multiplicity-exact divisor limit, Fourier truncation of the existing negative Gaussian witness,
and the final shifted-Hankel specialization. Formalizing an abstract convergence implication with
these source facts as premises would be theorem theatre and is intentionally excluded.
