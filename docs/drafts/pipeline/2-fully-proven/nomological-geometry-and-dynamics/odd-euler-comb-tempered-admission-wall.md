# Odd Euler comb: sharp tempered-admission wall

- **ID:** `ngd-odd-euler-comb-tempered-admission-wall`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [ADMISSION HORIZON] [USES PNT] [NOT RH]`
  `[NO LEAN WRITTEN]`

## 1. Statement

For real `b`, define the odd locally finite distribution

\[
 D_b=\sum_{n\ge2}\Lambda(n)n^{-b}
       (\delta_{\log n}-\delta_{-\log n}).
\tag{1}
\]

### Theorem 1.1 — exact admission threshold

\[
 \boxed{D_b\in\mathcal S'(\mathbb R)\quad\Longleftrightarrow\quad b\ge1.}
\tag{2}
\]

For every real `b`, `D_b` belongs to `D'(R)`.

## 2. Proof

Local finiteness of the support `{+-log n}` proves `D_b in D'(R)`.

### Case `b>1`

Since `Lambda(n)<=log n`,

\[
 \sum_{n\ge2}\Lambda(n)n^{-b}<\infty.
\]

Thus `D_b` is a finite signed measure and hence tempered.

### Case `b=1`

Let

\[
 A(x)=\sum_{n\le x}\frac{\Lambda(n)}n.
\]

Chebyshev's estimate `psi(x)=sum_{n<=x}Lambda(n)=O(x)` and partial summation give

\[
 A(x)=\frac{\psi(x)}x+
      \int_1^x\frac{\psi(u)}{u^2}\,du
 =O(\log x).
\tag{3}
\]

For `phi in S(R)`, group atoms with `k<=log n<k+1`. More directly, Chebyshev gives

\[
 \sum_{e^k\le n<e^{k+1}}\frac{\Lambda(n)}n
 \le e^{-k}\psi(e^{k+1})=O(1).
\]

Hence

\[
 |\langle D_1,\phi\rangle|
 \le C\sum_{k\ge0}
   \sup_{k\le |t|<k+1}|\phi(t)|<\infty,
\]

continuously in a Schwartz seminorm. Therefore `D_1 in S'(R)`.

### Case `b<1`

Choose a nonnegative `eta in C_c^infty((-1/4,1/4))` with `eta(0)>0`, and define translated
test functions `eta_T(t)=eta(t-T)`. Every Schwartz seminorm of `eta_T` grows at most polynomially
in `T`.

By the prime number theorem, for all sufficiently large `X`,

\[
 \sum_{X<n\le e^{1/8}X}\Lambda(n)\ge cX
\tag{4}
\]

with an absolute `c>0`. Put `T=log X` and choose the fixed bump so that it is positive on the
corresponding logarithmic interval. Only the positive atoms contribute there, and

\[
 \langle D_b,\eta_T\rangle
 \ge c'X^{-b}X
 =c'e^{(1-b)T}.
\tag{5}
\]

This grows exponentially, while continuity of a tempered distribution would bound it by a fixed
polynomial in the translation parameter. Contradiction. Thus `D_b` is not tempered for `b<1`.
Together the three cases prove `(2)`. ∎

## 3. Consequences

### Corollary 3.1 — Route-L admission horizon

Under the exact half-density weld

\[
 \mathcal L\kappa_a\mathcal L^{-1}=C_{D_{a+1/2}},
\]

the distributional coefficient exists for every `a`, but its tempered realization exists exactly
when

\[
 a\ge\frac12.
\]

Thus the path from regular `a>1/2` to the critical value `a=0` crosses a genuine admission wall at
`a=1/2`. At `a=0`, `D_{1/2}` is locally finite but non-tempered.

### Corollary 3.2 — torque current

The derivative

\[
 XK_{\rm pr}=-\sum_{n\ge2}\Lambda(n)(\log n)n^{-1/2}
 (\delta_{\log n}-\delta_{-\log n})
\]

is not tempered. The additional logarithm only strengthens the translated-bump lower bound.

### Corollary 3.3 — three distinct geometric states

This family separates:

1. an admitted comparison cell (`b>=1` in `S'`);
2. an existing but nonadmitted cell (`b<1` in `D'` but not `S'`);
3. a noninvertible admitted comparison cell.

Only the third has a canonical stable-category cofiber. Conflating states 2 and 3 creates a false
curvature object.

## 4. Hostile audit

- No Xi zero or RH estimate enters. PNT suffices.
- Threshold is sharp, including endpoint `b=1`.
- The theorem does not say the Möbius-cancelled Gamma/Stokes distribution is non-tempered; it
  concerns the bare odd Euler comb.
- The theorem supplies topology/admission geometry, not source selection.

## 5. Formalization notes

No Lean was written or built. Existing formal PNT/Chebyshev files can support `(3)` and `(4)`.
Formalization should first state polynomial-growth equivalence for discrete measures on the log
axis, then instantiate it with the von Mangoldt partial sums.
