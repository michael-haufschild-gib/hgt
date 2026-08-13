# Odd Euler comb: sharp tempered-admission wall

- **ID:** `ngd-odd-euler-comb-tempered-admission-wall`
- **Stage:** 3 — formalised in Lean 4
- **Status:** `[PAPER-PROVED] [ADMISSION HORIZON] [USES PNT] [NOT RH]`
  `[FORMALIZED] [LEAN-CHECKED] [AXIOM-AUDITED]`

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

Hence, with `p_2(phi)=sup_t (1+|t|)^2|phi(t)|`,

\[
 |\langle D_1,\phi\rangle|
 \le C p_2(\phi)\sum_{k\ge0}(1+k)^{-2}.
\]

Therefore `D_1 in S'(R)`. The prime number theorem `psi(x)=x+o(x)` and partial summation sharpen
`(3)` to

\[
 \sum_{n\le x}\frac{\Lambda(n)}n=\log x+o(\log x),
\]

so its total variation is infinite. Only polynomial mass growth is needed for temperedness.

### Case `b<1`

Choose a nonnegative `eta in C_c^infty((-1/4,1/4))` with
`eta(t)>=c_0>0` on `[0,1/8]`, and define translated test functions
`eta_T(t)=eta(t-T)`. Every Schwartz seminorm of `eta_T` grows at most polynomially in `T`.

By the prime number theorem, for all sufficiently large `X`,

\[
 \sum_{X<n\le e^{1/8}X}\Lambda(n)\ge cX
\tag{4}
\]

with an absolute `c>0`. Put `T=log X`. Only the positive atoms contribute there. If `b>=0`, then
on this interval `n^(-b)>=e^(-b/8)X^(-b)`; if `b<0`, then `n^(-b)>=X^(-b)`. Consequently

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

the coefficient distribution is an object of `S'` exactly when

\[
 a\ge\frac12.
\]

For `a>1/2` it has finite total variation; at `a=1/2` it is tempered with infinite total
variation; for `a<1/2` it is locally finite but non-tempered. Thus the path to `a=0` crosses a
genuine coefficient-object admission wall at `a=1/2`.

### Corollary 3.2 — torque current

The derivative

\[
 XK_{\rm pr}=-\sum_{n\ge2}\Lambda(n)(\log n)n^{-1/2}
 (\delta_{\log n}-\delta_{-\log n})
\]

is not tempered. The additional logarithm only strengthens the translated-bump lower bound.

### Corollary 3.3 — admission is not noninvertibility

This family proves exactly two coefficient-object statuses:

1. `b>=1`: `D_b in S'`;
2. `b<1`: `D_b in D' setminus S'`.

It constructs no noninvertible admitted morphism. In a stable category an admitted equivalence has
canonical zero cofiber, an admitted non-equivalence has a canonical generally nonzero cofiber, and
an absent morphism has no cofiber. Conflating nonadmission with noninvertibility creates a false
curvature object.

## 4. Hostile audit

- No Xi zero or RH estimate enters. PNT suffices.
- Threshold is sharp, including endpoint `b=1`.
- The theorem does not say the Möbius-cancelled Gamma/Stokes distribution is non-tempered; it
  concerns the bare odd Euler comb.
- The theorem supplies topology/admission geometry, not source selection.

## 5. Formalization notes

Formalized in
`formal/GaloisForLFunctions/HTGeometry/OddEulerCombTemperedAdmissionWall.lean`.

Closed gates:

1. literal coefficients `Lambda(n)n^{-b}` and positive/reflected logarithmic atom measures;
2. local finiteness and an exact `D'(R)` odd distribution for every real `b`;
3. exact atomic integration and test-function/Schwartz pairing formulas;
4. polynomial-growth equivalence for the atomic measures and sharp threshold `b >= 1`;
5. actual `S'(R)` realization for every admitted parameter;
6. finite total variation for `b > 1`, tempered infinite variation at `b = 1`;
7. Route-L threshold `a >= 1/2`, strict finite-variation side, endpoint, and subcritical failure;
8. full signed torque-current nonadmission.

The formal nonadmission proof uses the existing unconditional divergence of a prime
residue-class subseries of `sum Lambda(n)/n`, together with the fact that every fixed logarithmic
power is eventually dominated by `n^(1-b)`. This is stronger arithmetic infrastructure than the
paper's PNT block argument and uses no RH input.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/OddEulerCombTemperedAdmissionWall.lean`
- `lake build +GaloisForLFunctions.HTGeometry.OddEulerCombTemperedAdmissionWall`
- `scripts/formal_tools.py lint`
- `#print axioms` on capstones: only `propext`, `Classical.choice`, `Quot.sound`

Wired through `formal/GaloisForLFunctions/HTGeometry.lean`.
