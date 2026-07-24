# Bernstein divided-power square and cofinal stability law

- **ID:** `bernstein-divided-power-cofinal-stability`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** After the signed divided-power transform, the scale-covariant Bernstein purity chart is exactly polynomial squaring; on the natural `1/N` scale its positive square-root inverse is uniformly stable for bounded atomic moment sources with pointed mass bounded away from zero.

## Goal

Answer the paper's quantitative inversion question without hiding the conditioning in an
unspecified triangular matrix.  The target is an exact factorisation and a cofinal inverse bound
whose constant is independent of the Bernstein degree `N`.

## Gates

- [x] 0 → 1 in-progress: exact statement and hostile attack recorded
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem(s), narrow leaf build, axiom audit
- [ ] 3 → 4 publication-ready: integrated into the single master theorem of the paper

## Exact claim

For

```text
P_(N,m)(X) = sum_(k=0)^N (T_m b_(N,k))(X)^2,
F_(N,m)(T) = sum_(r=0)^N binom(N,r) m_r T^r/r!,
```

one has the coefficient identity

```text
(-1)^r [X^r]P_(N,m)
  = sum_(a+b=r) binom(r,a) binom(N,a) binom(N,b) m_a m_b,
```

and hence the exact divided-power square law

```text
sum_r (-1)^r [X^r]P_(N,m) T^r/r! = F_(N,m)(T)^2.
```

The positive pointed source is therefore the unique formal square root with constant term
`m_0 > 0`.

For bounded atomic moments `|m_r| <= A M^r`, put `t = rho/N`.  If `m_0,m'_0 >= mu > 0` and

```text
A (exp(M rho)-1) <= theta mu,       0 <= theta < 1,
```

for both sources, then the tails of `F_(N,m)` and `F_(N,m')` on `|T| <= rho/N` are at most
`theta mu`, uniformly in `N`.  Consequently the positive square-root inverse satisfies

```text
sup_|T|<=rho/N |F_(N,m)(T)-F_(N,m')(T)|
 <= [2(1-theta)mu]^-1
    sup_|T|<=rho/N |F_(N,m)(T)^2-F_(N,m')(T)^2|.
```

The bound is cofinal in `N`.  Degeneration at `mu=0` is unavoidable because the zeroth coordinate
is exactly the positive square-root map `m_0 = sqrt([X^0]P)`.

## Approach

Expand each Bernstein row in the monomial basis, sum its square, and apply Vandermonde's identity
`sum_k binom(a,k)binom(b,k)=binom(a+b,a)`.  The stability estimate is the factorisation
`F^2-G^2=(F-G)(F+G)` plus the uniform tail estimate

```text
sum_(r>=1) binom(N,r) N^-r |m_r| rho^r/r!
 <= A sum_(r>=1) (M rho)^r/(r!)^2
 <= A (exp(M rho)-1).
```

## Hostile audit

- `[BRIDGE]` Exponential generating functions turn binomial convolution into multiplication; this
  parent mechanism is classical.
- The exact Bernstein-purity factorisation was not found in the targeted Bernstein generating-
  function comparison, but novelty is unverified.
- The uniform estimate is not a disguised pullback norm: it is in the ordinary supremum norm on a
  degree-dependent physical disk and has a constant independent of `N`.
- The result does not control inversion as `m_0 -> 0`; it proves that this is the exact unavoidable
  singular locus.

## Log

- 2026-07-19 — created in Stage 1 after the paper's first open question was isolated.

## Complete paper proof

### The divided-power square

Write

```text
b_(N,k)(X)=binom(N,k) X^k(1-X)^(N-k)
```

and let `T_m` multiply the coefficient of `X^a` by `m_a`.  For `0 <= k <= a <= N`,

```text
[X^a] T_m b_(N,k)
 = (-1)^(a-k) binom(N,k)binom(N-k,a-k)m_a
 = (-1)^(a-k) binom(N,a)binom(a,k)m_a.                 (1)
```

The coefficient is zero outside this range.  Put `y_r=[X^r]P_(N,m)`.  Expanding the square of
all rows and using (1) gives

```text
y_r
 = sum_(a+b=r) (-1)^r binom(N,a)binom(N,b)m_a m_b
     sum_k binom(a,k)binom(b,k).
```

Vandermonde's identity, after replacing `binom(b,k)` by `binom(b,b-k)`, is

```text
sum_k binom(a,k)binom(b,k)=binom(a+b,a)=binom(r,a).
```

Therefore

```text
(-1)^r y_r
 = sum_(a+b=r) binom(r,a)binom(N,a)binom(N,b)m_a m_b.  (2)
```

On the other hand, the coefficient of `T^r` in

```text
F_(N,m)(T)^2,
F_(N,m)(T)=sum_(a=0)^N binom(N,a)m_a T^a/a!,
```

is

```text
sum_(a+b=r) binom(N,a)binom(N,b)m_a m_b/(a!b!).
```

Multiplication by `r!` and (2) prove

```text
sum_(r=0)^(2N) (-1)^r y_r T^r/r! = F_(N,m)(T)^2.      (3)
```

If `m_0>0`, then `F_(N,m)(0)=m_0>0`.  If two such polynomials have the same square, their
product difference is

```text
(F-G)(F+G)=0.
```

The real polynomial ring is an integral domain and `F+G` has positive constant coefficient, so
`F=G`.  Its coefficient of `T^r` is `binom(N,r)m_r/r!`, which recovers every `m_r`, `r<=N`.
Thus (3) is a global positive square-root inverse, not only a recursive triangular inverse.

### Uniform cofinal stability

Assume `N>=1`, `|m_r|<=A M^r`, and `|T|<=rho/N`.  Since

```text
binom(N,r)/N^r <= 1/r!,
```

we have

```text
|F_(N,m)(T)-m_0|
 <= sum_(r=1)^N binom(N,r)|m_r|(rho/N)^r/r!
 <= A sum_(r=1)^N (M rho)^r/(r!)^2
 <= A (exp(M rho)-1).                                  (4)
```

The last step uses `(r!)^2 >= r!`.  Apply (4) to `m` and `m'`.  Under the hypotheses in the exact
claim, both tails are at most `theta mu`.  Hence throughout the disk,

```text
|F_(N,m)(T)+F_(N,m')(T)|
 >= m_0+m'_0-2 theta mu
 >= 2(1-theta)mu.                                      (5)
```

Pointwise factorisation and (5) give

```text
|F_(N,m)(T)-F_(N,m')(T)|
 <= |F_(N,m)(T)^2-F_(N,m')(T)^2|/[2(1-theta)mu].       (6)
```

Taking suprema proves the stated estimate.  Its constant and the admissible value of `rho` do not
depend on `N`; the observation disk contracts at the canonical scale `1/N`.  Thus (6) is a genuine
cofinal stability estimate.

For an absolutely summable atomic presentation with `|z_i|<=M`,

```text
|m_r| = |sum_i c_i z_i^r| <= (sum_i |c_i|)M^r,
```

so the assumed exponential moment bound follows with `A=sum_i|c_i|`.

Finally, no Lipschitz estimate with a constant independent of the pointed mass can hold at the
origin.  The zeroth data coordinate is `y_0=m_0^2`, so its positive inverse is `m_0=sqrt(y_0)`.
For any proposed constant `C>0`, taking `0<y_0<C^-2` gives

```text
sqrt(y_0)/y_0 = 1/sqrt(y_0) > C.
```

The singularity `mu downarrow 0` is therefore sharp and unavoidable.

### Abel-side completion

For the same source-radius bound `M` and every `R>M`, the already established exact confocal collar
is

```text
0 <= R(B(R)^2-1)-2 Delta
   <= M^2/(R-M)+4M^2/R.                                (7)
```

Equations (6) and (7) give the requested two-scale theory: the source inverse is uniform along the
cofinal Bernstein scale `N -> infinity` on `T=O(1/N)`, while the geometric recession is uniform
along `R -> infinity`, with both constants expressed by the same source bounds `(A,M,mu)`.

## Paper-proof verdict

`[PAPER-PROVED]`.  Every estimate follows from finite identities, the exponential series, and the
existing dependency-closed confocal collar.  The exact formal statement must include `N>=1`,
`mu>0`, `0<=theta<1`, nonnegative `A,M,rho`, and the displayed moment bounds.

- 2026-07-24 — **Formalization gate `(2 -> 3)` complete** (found already fully formalized on audit,
  unconditional, axioms `[propext, Classical.choice, Quot.sound]`).  Module
  `RHTower/ScaleCovariantBernsteinDividedPowerStability.lean` (reachable via
  `PositiveFieldBicompletionLaw`):
  * `coeff_bernsteinPolynomial_closed` — coefficient formula `(1)`.
  * `sum_choose_mul_choose_eq_choose_add` — the Vandermonde collapse `sum_k C(a,k)C(b,k)=C(a+b,a)`.
  * `coeff_bernsteinScalePurityPolynomial_closed` — the coefficient identity `(2)`.
  * `bernsteinDividedPowerRoot` / `coeff_bernsteinDividedPowerRoot` and
    `bernsteinScalePurityPolynomial_coeff_dividedPower_square` — the exact divided-power square law `(3)`.
  * `moment_prefix_eq_of_bernsteinDividedPowerRoot_sq_eq`,
    `bernsteinScalePurityPolynomial_eq_iff_moment_prefix_eq` — positive square-root inversion / moment recovery.
  * `bernsteinDividedPowerTailNorm`, `bernsteinDividedPowerChart_sub_mass_le_tailNorm`,
    `positive_squareRoot_chamber_stability`, `bernsteinDividedPowerChart_stability` — the uniform tail
    bound `(4)` and the cofinal, degree-independent stability constant.
  Moved to `3-formalized/needs-audit`.
