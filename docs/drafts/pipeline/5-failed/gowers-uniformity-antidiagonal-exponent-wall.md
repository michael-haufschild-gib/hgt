# Fixed-order Gowers uniformity misses the Mertens antidiagonal by one power

- **ID:** `gowers-uniformity-antidiagonal-exponent-wall`
- **Stage:** 5-failed
- **Type:** LITERATURE-INPUT NO-GO; classical Fourier consequence
- **Source:** `OPEN-SOURCE-001` in `../1-in-progress/mobius-additive-frontier-research-ledger.md`
- **Statement:** Current quantitative Gowers uniformity gives only logarithmic suppression of the
  natural cubic antidiagonal scale; the exact Fourier dual inequality still misses the RH source by
  one polynomial power.

## Exact norm comparison

Let `f(n)=mu(n)` on an interval of length comparable to `N`, let

```text
F(alpha)=sum_(n<=N) f(n)e(alpha n),
W_N(alpha)=sum_(t<=N) (N-t+1)e(alpha t).
```

Up to harmless endpoint conventions, the integrated additive convolution is

```text
U(N)=integral_0^1 F(alpha)^2 W_N(-alpha) d alpha.        (1)
```

Cauchy--Schwarz and Parseval give

```text
|U(N)|
 <= (integral |F|^4)^(1/2) (integral |W_N|^2)^(1/2)
 << N^3 ||f||_(U^2[N])^2.                               (2)
```

Here the normalized `U^2` convention is used: the fourth Fourier moment has scale
`N^3||f||_U2^4`, while `sum_(t<=N)(N-t+1)^2` has scale `N^3`.

Tao--Teräväinen prove, for every fixed order, quantitative Möbius Gowers decay of
logarithmic--iterated-logarithmic strength; at order two it has the form

```text
||mu||_(U^2[N]) << (log log N)^(-c)                     (3)
```

for some fixed `c>0`.  Combining `(2)` and `(3)` yields only

```text
|U(N)| << N^3 (log log N)^(-2c),                        (4)
```

whereas `OPEN-SOURCE-001` requires `N^(2+epsilon)` for every `epsilon>0`.  Arbitrary fixed
logarithmic savings do not replace the missing factor `N`.

Higher fixed Gowers orders do not alter this conclusion.  Their known decay remains
logarithmic, and applying generalized von Neumann or Hölder inequalities to a kernel of natural
antidiagonal mass suppresses the cubic scale only by that fixed logarithmic factor.  The recent
short-interval higher-uniformity theorem is qualitative (and almost-all-interval); its authors
explicitly note that prospective quantified errors would be very weak.  Neither theorem supplies a
cutoff-pointwise growing-reflection estimate.

## No-go closure

- **Exact killing theorem/mechanism:** Fourier duality `(2)` converts current `U^2` decay into
  logarithmic savings on `N^3`, not the polynomial saving to `N^(2+o(1))`.
- **Strongest positive survivor:** exact norm interface `(2)`.  A source theorem of strength
  `||mu||_U2 <= N^(-1/2+epsilon)` would suffice through this route, but that is vastly stronger than
  current uniformity and is not assumed.
- **New insight:** modern higher-order uniformity attacks structured finite-complexity patterns;
  the signed antidiagonal is instead dominated by its low-frequency, growing-reflection channel.
  Fixed-order logarithmic pseudorandomness is quantitatively the wrong scale.
- **Status:** classical bridge/no-go, not new scientific knowledge and Lean-ineligible.

## Primary literature

- T. Tao and J. Teräväinen, *Quantitative bounds for Gowers uniformity of the Möbius and von
  Mangoldt functions*, JEMS 27 (2025), 1321--1384, DOI 10.4171/JEMS/1404.
- K. Matomäki, M. Radziwiłł et al., *Higher uniformity of arithmetic functions in short intervals
  II. Almost all intervals*, Invent. Math. (2026), DOI 10.1007/s00222-026-01408-6.

## Log

- 2026-07-22 — exact antidiagonal `U^2` loss audited against current quantitative and
  short-interval Gowers theorems; route retired.
